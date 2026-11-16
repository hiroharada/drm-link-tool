# -*- coding: utf-8 -*-
r"""
JARTIC(都道府県警察の車両感知器)の断面交通量と、センサス(令和3年度)時間交通量との比較

  python server.py --update-jartic   … 社内SQL Server(zaa61055-3)の最新月から集計して jartic.json を作る

・交通量: SQL Server zaa61055-3 の DB「JARTIC{年}」・表「断面交通量_{都道府県}_{年}年{月}月」(5分値)。
  読み取り(SELECT)のみ。Windowsのログインで接続(既存の「JARTICデータ抽出マクロ」と同じ)。
  最新の月の平日(土日・祝日・お盆・年末年始を除く)について、地点・時間帯ごとの1時間交通量の平均をSQL側で集計。
  1時間交通量 = その時間の5分値の合計(10個以上ある時間のみ。欠けている分は個数で補正)。
・位置: 日本交通管理技術協会の計測地点位置データ(2020年版)の写し
  (DRMデータフォルダ\JARTIC計測地点\全国_計測地点_都道府県情報付与.shp, 全国_矢印.shp)。
  情報源コード＋計測地点番号で対応付け。番号が同じでも名称が変わった地点は、移設の可能性があるため除外。
・方向: 矢印(進行方向)に沿ったDRMリンクを選び、そのリンクを通る向きと管起点Nから上り/下りを決める。
"""
import calendar
import collections
import concurrent.futures
import datetime
import json
import math
import os
import struct
import subprocess
import tempfile
import threading
import time

import torakan   # 平日判定・センサス時間交通量の読込・比較を共用

SQL_SERVER = 'zaa61055-3'
SNAP_M = 30
# 都道府県名(計測地点位置データの「都道府県」属性, 例「愛知」) → 都道府県コード。表名「断面交通量_23愛知_...」の組立に使う
_PREF_ORDER = ['北海道', '青森', '岩手', '宮城', '秋田', '山形', '福島', '茨城', '栃木', '群馬',
               '埼玉', '千葉', '東京', '神奈川', '新潟', '富山', '石川', '福井', '山梨', '長野',
               '岐阜', '静岡', '愛知', '三重', '滋賀', '京都', '大阪', '兵庫', '奈良', '和歌山',
               '鳥取', '島根', '岡山', '広島', '山口', '徳島', '香川', '愛媛', '高知', '福岡',
               '佐賀', '長崎', '熊本', '大分', '宮崎', '鹿児島', '沖縄']
PREF_CODE = {name: i + 1 for i, name in enumerate(_PREF_ORDER)}


def _norm(s):
    return (s or '').replace(' ', '').replace('　', '')


# ---------------------------------------------------------------------------
#  SQL Server(読み取りのみ)。Python標準にはSQL Serverの接続機能が無いため、PowerShell(.NET)経由で実行
# ---------------------------------------------------------------------------
def sql_rows(query, database='master', timeout=1800):
    with tempfile.TemporaryDirectory() as td:
        qf, of = os.path.join(td, 'q.sql'), os.path.join(td, 'out.tsv')
        with open(qf, 'w', encoding='utf-8-sig') as f:
            f.write(query)
        ps = ("$ErrorActionPreference='Stop';"
              "$q=[IO.File]::ReadAllText('%s',[Text.Encoding]::UTF8);"
              "$cn=New-Object System.Data.SqlClient.SqlConnection 'Server=%s;Database=%s;Integrated Security=SSPI;Connect Timeout=30;ApplicationIntent=ReadOnly';"
              "$cn.Open();$c=$cn.CreateCommand();$c.CommandTimeout=%d;$c.CommandText=$q;$r=$c.ExecuteReader();"
              "$w=New-Object IO.StreamWriter('%s',$false,(New-Object Text.UTF8Encoding $false));"
              "while($r.Read()){$v=for($i=0;$i -lt $r.FieldCount;$i++){([string]$r[$i]).Trim()};$w.WriteLine(($v -join [char]9))};"
              "$w.Close();$cn.Close()") % (qf, SQL_SERVER, database, timeout, of)
        r = subprocess.run(['powershell', '-NoProfile', '-NonInteractive', '-Command', ps],
                           capture_output=True, timeout=timeout + 60)
        if r.returncode != 0:
            raise RuntimeError('SQL Server の読込に失敗: ' + r.stderr.decode('cp932', 'replace')[-500:])
        with open(of, encoding='utf-8') as f:
            return [line.rstrip('\r\n').split('\t') for line in f if line.strip()]


def latest_month(log):
    dbs = [r[0] for r in sql_rows("SELECT name FROM sys.databases WHERE name LIKE 'JARTIC[0-9][0-9][0-9][0-9]' ORDER BY name")]
    for db in reversed(dbs):
        rows = sql_rows("SELECT name FROM sys.tables WHERE name LIKE N'断面交通量[_]%' AND name NOT LIKE N'%元データ'", db)
        months = sorted({n[0][-8:] for n in rows if n[0].endswith('月')})   # 'YYYY年MM月'
        if months:
            ym = months[-1]
            tables = [n[0] for n in rows if n[0].endswith(ym)]
            log('JARTIC: 最新月 %s (%d 表)' % (ym, len(tables)))
            return db, int(ym[:4]), int(ym[5:7]), tables
    raise RuntimeError('SQL Server に JARTIC の断面交通量の表がありません')


def _db_months(db):
    rows = sql_rows("SELECT name FROM sys.tables WHERE name LIKE N'断面交通量[_]%' AND name NOT LIKE N'%元データ'", db)
    return sorted({(int(n[0][-8:-4]), int(n[0][-3:-1])) for n in rows if n[0].endswith('月')})


def available_range(log):
    """SQL Serverに断面交通量の表がある範囲(最初の月の初日, 最後の月の末日)。無ければ None"""
    dbs = [r[0] for r in sql_rows("SELECT name FROM sys.databases WHERE name LIKE 'JARTIC[0-9][0-9][0-9][0-9]' ORDER BY name")]
    if not dbs:
        return None
    first, last = _db_months(dbs[0]), _db_months(dbs[-1])
    if not first or not last:
        return None
    log('JARTIC: データ範囲 %d年%d月 ～ %d年%d月' % (first[0][0], first[0][1], last[-1][0], last[-1][1]))
    return datetime.date(*first[0], 1), datetime.date(*last[-1], calendar.monthrange(*last[-1])[1])


_TABLES = {'t': 0, 'rows': None}


def _all_tables():
    """全年DBの断面交通量の表 [(DB名, 表名, 都道府県コード, 年, 月)]。10分間は使い回す"""
    if _TABLES['rows'] is None or time.time() - _TABLES['t'] > 600:
        dbs = [r[0] for r in sql_rows("SELECT name FROM sys.databases WHERE name LIKE 'JARTIC[0-9][0-9][0-9][0-9]' ORDER BY name")]
        q = ' UNION ALL '.join("SELECT '%s', name FROM %s.sys.tables WHERE name LIKE N'断面交通量[_]%%' AND name NOT LIKE N'%%元データ'"
                               % (db, db) for db in dbs)
        rows = []
        for db, name in (sql_rows(q) if dbs else []):
            if name.endswith('月') and name[6:8].isdigit():
                rows.append((db, name, int(name[6:8]), int(name[-8:-4]), int(name[-3:-1])))
        _TABLES.update(t=time.time(), rows=rows)
    return _TABLES['rows']


_AVAIL_LOCK = threading.Lock()


def availability(pts_by_id, ids, cache_path, log):
    """各地点のデータがある期間 {id: {'from','to','days','months'}}。
    月ごとの表を、各日12時の5分値があるかで調べる(表の索引(日時,計測地点番号)で引けるので全件は読まない)。
    確定した過去の月の結果は cache_path に保存して使い回す(初回は都道府県あたり十数秒)"""
    with _AVAIL_LOCK:
        try:
            with open(cache_path, encoding='utf-8') as f:
                cache = json.load(f)       # id -> {'YYYYMM': [日数, 最初の日, 最後の日] or 0}
        except (OSError, ValueError):
            cache = {}
        tables = _all_tables()
        latest = max((y * 100 + m for _, _, _, y, m in tables), default=0)
        targets = {}                       # id -> (情報源コード, 計測地点番号, 都道府県コード)
        for i in ids:
            p = pts_by_id.get(i)
            if not p or '-' not in i or not PREF_CODE.get(p['pref']):
                continue
            src, no = i.split('-', 1)
            if no.isdigit():
                targets[i] = (src, int(no), PREF_CODE[p['pref']])
        # 表ごとに、まだ調べていない地点を集めて年(DB)ごとに1回の問い合わせにまとめる
        per_db = collections.defaultdict(list)
        for db, name, pc, y, m in tables:
            ym = '%d%02d' % (y, m)
            need = [t for i, t in targets.items() if t[2] == pc and (ym not in cache.get(i, {}) or y * 100 + m == latest)]
            if not need:
                continue
            days = ','.join("'%04d-%02d-%02d 12:00'" % (y, m, d) for d in range(1, calendar.monthrange(y, m)[1] + 1))
            nos = ','.join(sorted({str(t[1]) for t in need}))
            per_db[db].append((ym, need, "SELECT '%s', 情報源コード, 計測地点番号, COUNT(*), MIN(DAY(日時)), MAX(DAY(日時)), "
                                          "SUM(POWER(CAST(2 AS bigint), DAY(日時) - 1)) "
                                          "FROM %s.dbo.[%s] WITH (NOLOCK) WHERE 日時 IN (%s) AND 計測地点番号 IN (%s) "
                                          "GROUP BY 情報源コード, 計測地点番号" % (ym, db, name, days, nos)))
        if per_db:
            n_tab = sum(len(v) for v in per_db.values())
            log('JARTIC: %d 地点の収録期間を確認中(%d 表)' % (len(targets), n_tab))

            def run(db):
                return db, sql_rows(' UNION ALL '.join(q for _, _, q in per_db[db]))
            with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:
                results = list(ex.map(run, list(per_db)))
            id_of = {(t[0], t[1]): i for i, t in targets.items()}
            for db, rows in results:
                for ym, need, _ in per_db[db]:
                    for src, no, _pc in need:
                        cache.setdefault(id_of[(src, no)], {})[ym] = 0
                for ym, src, no, n, d0, d1, bits in rows:
                    i = id_of.get((src.strip(), int(no)))
                    if i:
                        cache.setdefault(i, {})[ym] = [int(n), int(d0), int(d1), int(bits)]
            try:
                tmp = cache_path + '.%d.tmp' % os.getpid()
                with open(tmp, 'w', encoding='utf-8') as f:
                    # 最新月はまだ取り込み途中かもしれないので保存しない
                    json.dump({i: {ym: v for ym, v in c.items() if int(ym) < latest} for i, c in cache.items()},
                              f, separators=(',', ':'))
                os.replace(tmp, cache_path)
            except OSError as e:
                log('JARTIC: 収録期間のキャッシュを保存できません(%s)' % e)
    out = {}
    for i in targets:
        have = sorted((ym, v) for ym, v in cache.get(i, {}).items() if v)
        if not have:
            out[i] = {'from': None, 'to': None, 'days': 0, 'months': 0, 'mask': {}}
            continue
        (ym0, v0), (ym1, v1) = have[0], have[-1]
        out[i] = {'from': '%s-%s-%02d' % (ym0[:4], ym0[4:], v0[1]), 'to': '%s-%s-%02d' % (ym1[:4], ym1[4:], v1[2]),
                  'days': sum(v[0] for _, v in have), 'months': len(have), 'mask': {ym: v[3] for ym, v in have}}
    return out


def export_range(pts_by_id, ids, date_from, date_to, log):
    """選択した地点・期間の生データ(5分値)を社内SQL Serverから取り出す"""
    groups = collections.defaultdict(list)   # 都道府県名 -> [(情報源コード, 計測地点番号, id)]
    for i in ids:
        p = pts_by_id.get(i)
        if not p or '-' not in i:
            continue
        src, no = i.split('-', 1)
        try:
            groups[p['pref']].append((src, int(no), i))
        except ValueError:
            continue
    out = []
    y, m = date_from.year, date_from.month
    while (y, m) <= (date_to.year, date_to.month):
        mstart = datetime.date(y, m, 1)
        mend = (mstart.replace(day=28) + datetime.timedelta(days=4)).replace(day=1) - datetime.timedelta(days=1)
        d0, d1 = max(date_from, mstart), min(date_to, mend)
        db = 'JARTIC%d' % y
        for pref, items in groups.items():
            code = PREF_CODE.get(pref)
            if not code:
                log('JARTIC出力: 都道府県コードが不明のためスキップ: %s' % pref)
                continue
            table = '断面交通量_%02d%s_%d年%02d月' % (code, pref, y, m)
            id_of = {(src, no): i for src, no, i in items}
            cond = ' OR '.join("(情報源コード='%s' AND 計測地点番号=%d)" % (src, no) for src, no, _ in items)
            q = ("SELECT 情報源コード, 計測地点番号, 計測地点名称, 日時, 断面交通量, リンク番号 FROM dbo.[%s] WITH (NOLOCK) "
                 "WHERE (%s) AND 日時 >= '%s' AND 日時 < '%s' ORDER BY 計測地点番号, 日時"
                 % (table, cond, d0.isoformat(), (d1 + datetime.timedelta(days=1)).isoformat()))
            try:
                rows = sql_rows(q, db)
            except Exception as e:
                log('JARTIC出力: %s を取得できません(%s)' % (table, e))
                continue
            for src, no, name, dt, vol, link in rows:
                try:
                    key_no = int(no)
                except ValueError:
                    key_no = None
                out.append([id_of.get((src, key_no), '%s-%s' % (src, no)), name, dt, int(vol) if vol else 0, link])
            log('JARTIC出力: %d年%d月 %s: %d 行' % (y, m, pref, len(rows)))
        y, m = (y + 1, 1) if m == 12 else (y, m + 1)
    return out


def hourly_weekday_avg(db, tables, days, log):
    """{(情報源コード, 計測地点番号): {'avg':[24], 'days':[24]}}"""
    dl = ','.join("'%s'" % d.isoformat() for d in days)
    out = {}
    for i, t in enumerate(sorted(tables), 1):
        q = """
SELECT 情報源コード, 計測地点番号, h, AVG(v), COUNT(*) FROM (
  SELECT 情報源コード, 計測地点番号, CONVERT(date, 日時) d, DATEPART(hour, 日時) h,
         SUM(CAST(断面交通量 AS float)) * 12.0 / COUNT(*) v
  FROM dbo.[%s] WITH (NOLOCK)
  WHERE 断面交通量 >= 0 AND CONVERT(date, 日時) IN (%s)
  GROUP BY 情報源コード, 計測地点番号, CONVERT(date, 日時), DATEPART(hour, 日時)
  HAVING COUNT(*) >= 10) x
GROUP BY 情報源コード, 計測地点番号, h""" % (t, dl)
        rows = sql_rows(q, db)
        for src, no, h, av, n in rows:
            e = out.setdefault((src, int(no)), {'avg': [None] * 24, 'days': [0] * 24})
            e['avg'][int(h)] = round(float(av), 1)
            e['days'][int(h)] = int(n)
        log('JARTIC: [%d/%d] %s 集計 %d 行' % (i, len(tables), t, len(rows)))
    return out


def acquisition_rate(db, ym):
    rows = sql_rows("SELECT 情報源コード, 計測地点番号, 取得率 FROM dbo.データ状態_計測地点 WHERE 年月 = N'%s'" % ym, db)
    return {(r[0], int(r[1])): float(r[2]) for r in rows if r[2]}


# ---------------------------------------------------------------------------
#  計測地点の位置・進行方向(シェープファイルを直接読む)
# ---------------------------------------------------------------------------
def _read_dbf(path):
    raw = open(path, 'rb').read()
    n, hl, rl = struct.unpack('<IHH', raw[4:12])
    fl, pos = [], 32
    while raw[pos] != 0x0D:
        x = raw[pos:pos + 32]
        fl.append((x[:11].split(b'\0')[0].decode('cp932'), x[16]))
        pos += 32
    recs = []
    for r in range(n):
        rec = raw[hl + r * rl: hl + (r + 1) * rl]
        o, row = 1, {}
        for name, ln in fl:
            row[name] = rec[o:o + ln].decode('cp932', 'replace').strip()
            o += ln
        recs.append(row)
    return recs


def _read_shp_geoms(path):
    data = open(path, 'rb').read()
    sp, out = 100, []
    while sp + 8 <= len(data):
        clen = struct.unpack('>i', data[sp + 4:sp + 8])[0] * 2
        c = data[sp + 8:sp + 8 + clen]
        sp += 8 + clen
        st = struct.unpack('<i', c[:4])[0]
        if st == 1:
            out.append([struct.unpack('<2d', c[4:20])])
        elif st == 3:
            nparts, npts = struct.unpack('<ii', c[36:44])
            xy = struct.unpack('<%dd' % (2 * npts), c[44 + 4 * nparts:44 + 4 * nparts + 16 * npts])
            out.append([(xy[2 * k], xy[2 * k + 1]) for k in range(npts)])
        else:
            out.append([])
    return out


def load_points(data_dir):
    d = os.path.join(data_dir, 'JARTIC計測地点')
    pts = _read_dbf(os.path.join(d, '全国_計測地点_都道府県情報付与.dbf'))
    arrows_attr = _read_dbf(os.path.join(d, '全国_矢印.dbf'))
    arrows_geom = _read_shp_geoms(os.path.join(d, '全国_矢印.shp'))
    arrow = {}
    for a, g in zip(arrows_attr, arrows_geom):
        if len(g) >= 2:
            arrow[(a['地点番号'], a['地点名称'], a['リンク番号'], a['メッシュ'])] = g
    out = {}
    for p in pts:
        try:
            key = (p['情報源コー'], int(p['地点番号']))
            lon, lat = float(p['経度']), float(p['緯度'])
        except ValueError:
            continue
        g = arrow.get((p['地点番号'], p['地点名称'], p['リンク番号'], p['メッシュ']))
        out[key] = {'name': p['地点名称'], 'lon': lon, 'lat': lat, 'pref': p['都道府県'],
                    'arrow': (g[0], g[-1]) if g else None}
    return out


# ---------------------------------------------------------------------------
#  計測地点 → DRMリンク(位置が近く、進行方向に沿ったもの)
# ---------------------------------------------------------------------------
def snap_directed(drm, lon, lat, vec, link_cell, scale):
    """(距離m, リンク番号, 正方向に通るか) または None。vec: 進行方向(東, 北)の単位ベクトル"""
    k = math.cos(math.radians(lat)) * 111320
    X, Y = lon * scale, lat * scale
    c = link_cell
    best = None
    co, cof = drm.coords, drm.c_off
    for cx in (int(lon // c) - 1, int(lon // c), int(lon // c) + 1):
        for cy in (int(lat // c) - 1, int(lat // c), int(lat // c) + 1):
            for i in drm.link_grid.get((cx, cy), ()):
                s = co[cof[i]:cof[i + 1]]
                seg = None
                for j in range(0, len(s) - 2, 2):
                    ax, ay = (s[j] - X) / scale * k, (s[j + 1] - Y) / scale * 111320
                    bx, by = (s[j + 2] - X) / scale * k, (s[j + 3] - Y) / scale * 111320
                    dx, dy = bx - ax, by - ay
                    L2 = dx * dx + dy * dy
                    t = 0 if L2 == 0 else max(0, min(1, -(ax * dx + ay * dy) / L2))
                    dd = math.hypot(ax + t * dx, ay + t * dy)
                    if seg is None or dd < seg[0]:
                        seg = (dd, dx, dy, math.sqrt(L2))
                if seg is None or seg[0] > SNAP_M or seg[3] == 0:
                    continue
                dd, dx, dy, ln = seg
                cos_ = (dx * vec[0] + dy * vec[1]) / ln
                if abs(cos_) < 0.7:          # 進行方向と交差する道路は除く
                    continue
                fwd = cos_ > 0
                reg = drm.l_reg[i]
                wrong = reg in ((5, 7) if fwd else (4, 6))   # 一方通行に逆らう向き
                score = dd + (0 if drm.l_cen[i] else 15) + (40 if wrong else 0)
                if best is None or score < best[0]:
                    best = (score, dd, i, fwd)
    return best and best[1:]


def update(drm, census_info, data_dir, out_path, log, link_cell, scale):
    db, y, m, tables = latest_month(log)
    first = datetime.date(y, m, 1)
    last = (first.replace(day=28) + datetime.timedelta(days=4)).replace(day=1) - datetime.timedelta(days=1)
    days = [first + datetime.timedelta(days=i) for i in range((last - first).days + 1)]
    weekdays = [d for d in days if torakan.is_weekday(d)]
    log('JARTIC: %d年%d月 の平日 %d 日を集計します' % (y, m, len(weekdays)))
    vol = hourly_weekday_avg(db, tables, weekdays, log)
    ym = '%d年%02d月' % (y, m)
    try:
        rate = acquisition_rate(db, ym)
    except Exception as e:
        log('JARTIC: 取得率の表を読めませんでした:', e)
        rate = {}
    # 現在の地点名称(名称の変わった地点＝移設の可能性を除くため)
    names = {}
    for src, no, nm in sql_rows("SELECT 情報源コード, 計測地点番号, MAX(計測地点名称) FROM dbo.データ状態_計測地点 WHERE 年月 = N'%s' GROUP BY 情報源コード, 計測地点番号" % ym, db):
        names[(src, int(no))] = nm
    pts = load_points(data_dir)
    log('JARTIC: センサス時間交通量を読込中')
    sec2unit, hourly = torakan.load_census_hourly(data_dir)

    stat = collections.Counter()
    out_pts = []
    for key, v in vol.items():
        src, no = key
        if no == 0:
            stat['地点番号0'] += 1
            continue
        p = pts.get(key)
        if p is None:
            stat['位置データに無い'] += 1
            continue
        if key in names and _norm(names[key]) != _norm(p['name']):
            stat['名称が変わった(移設の可能性)'] += 1
            continue
        if not p['arrow']:
            stat['進行方向が不明'] += 1
            continue
        (x0, y0), (x1, y1) = p['arrow']
        kx = math.cos(math.radians(p['lat']))
        vx, vy = (x1 - x0) * kx, (y1 - y0)
        n = math.hypot(vx, vy) or 1
        vec = (vx / n, vy / n)
        bearing = round(math.degrees(math.atan2(vec[0], vec[1])) % 360)
        pt = {'id': '%s-%d' % (src, no), 'name': p['name'], 'pref': p['pref'], 'lat': round(p['lat'], 6), 'lon': round(p['lon'], 6),
              'bearing': bearing, 'sensor': v['avg'], 'days': v['days'], 'rate': rate.get(key)}
        sn = snap_directed(drm, p['lon'], p['lat'], vec, link_cell, scale)
        if sn:
            dist, lid, fwd = sn
            ci = census_info(drm, lid, fwd)
            pt.update(linkMc=drm.mc[lid], linkDist=round(dist, 1), cen=ci['cen'], cenName=ci['cenName'], dir=ci['cenDir'])
            unit = sec2unit.get(ci['cen']) if ci['cen'] else None
            ce = hourly.get(unit) if unit else None
            if ce and ci['cenDir']:
                pt['census'] = {'date': ce['date'], 'kind': ce['kind'], 'values': ce['dirs'][ci['cenDir']]}
                cmp_ = torakan.compare(v['avg'], ce['dirs'][ci['cenDir']])
                if cmp_:
                    pt.update(cmp_)
        stat['表示'] += 1
        out_pts.append(pt)
    out = {'source': 'JARTIC 断面交通量情報(都道府県警察)・社内SQL Server %s より集計。計測地点位置: 日本交通管理技術協会(2020年版)' % SQL_SERVER,
           'generated': datetime.datetime.now().strftime('%Y-%m-%d %H:%M'), 'month': '%d-%02d' % (y, m),
           'period': [str(first), str(last)], 'weekdays': len(weekdays), 'drmVer': drm.ver, 'points': out_pts}
    tmp = out_path + '.%d.tmp' % os.getpid()
    with open(tmp, 'w', encoding='utf-8') as f:
        json.dump(out, f, ensure_ascii=False, separators=(',', ':'))
    os.replace(tmp, out_path)
    log('JARTIC: %s / センサスと比較 %d 地点 → %s' % (dict(stat), sum(1 for p in out_pts if p.get('err') is not None), out_path))
    return out
