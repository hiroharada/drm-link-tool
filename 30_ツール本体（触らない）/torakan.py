# -*- coding: utf-8 -*-
r"""
国交省トラカン(交通量API)の取得・集計と、センサス(令和3年度)時間交通量との比較

  python server.py --update-torakan   … 直近1か月の平日データを取得して torakan.json を作る(月1回程度)
                                         あわせて1時間値の生データ(全日)を DRMデータフォルダ\トラカン国交省\YYYY-MM.zip に保存

・交通量API(国土交通省・JARTIC提供, https://www.jartic-open-traffic.org/)の1時間値
  (様式2: 常設トラカン / 様式4: CCTVトラカン)を、平日1日ずつ間隔を空けて取得する。
・欠測・停電・機器異常の時間は除外し、方向(上り/下り)・時間帯ごとの平日平均を求める。
・トラカン位置に最も近いDRMリンク(既定の版)から、センサス基本区間 → 交通量調査単位区間 →
  時間帯別交通量(観測した区間のみ)を引き、方向別に比べる。
  誤差率 = (トラカン合計 − センサス合計) ÷ センサス合計 (センサスが観測した時間帯だけで集計)
・上り/下りの定義はAPI・センサスとも同じ(区間番号が増える方向が下り)。
"""
import collections
import csv
import datetime
import glob
import io
import json
import math
import os
import threading
import time
import urllib.parse
import urllib.request
import zipfile

API = 'https://api.jartic-open-traffic.org/geoserver'
LAYERS = [('t_travospublic_measure_1h', '常設'), ('t_travospublic_measure_1h_img', 'CCTV')]
ROAD_TYPES = ('3', '1')          # 3:一般国道 1:高速自動車国道
JAPAN_BBOX = (122, 20, 154, 46)
REQUEST_INTERVAL = 2.0           # 秒。規約の「短時間の大量アクセス禁止」に配慮
SNAP_M = 40                      # トラカン位置からこの距離以内のDRMリンクに対応付け
DIRS = ('上り', '下り')
MIN_HOUR_RATIO = 0.8             # センサス観測時間帯のうちトラカンに値がある割合がこれ未満なら比較しない


# ---------------------------------------------------------------------------
#  平日判定(土日・祝日・振替休日・国民の休日・お盆(8/13-16)・年末年始(12/29-1/3)を除く)
# ---------------------------------------------------------------------------
def _nth_monday(y, m, n):
    d = datetime.date(y, m, 1)
    d += datetime.timedelta(days=(0 - d.weekday()) % 7)
    return d + datetime.timedelta(weeks=n - 1)


def jp_holidays(y):
    h = {datetime.date(y, m, d) for m, d in ((1, 1), (2, 11), (2, 23), (4, 29), (5, 3), (5, 4), (5, 5),
                                              (8, 11), (11, 3), (11, 23))}
    h |= {_nth_monday(y, 1, 2), _nth_monday(y, 7, 3), _nth_monday(y, 9, 3), _nth_monday(y, 10, 2)}
    n = y - 1980
    h.add(datetime.date(y, 3, int(20.8431 + 0.242194 * n - n // 4)))   # 春分の日
    h.add(datetime.date(y, 9, int(23.2488 + 0.242194 * n - n // 4)))   # 秋分の日
    for d in sorted(h):                                                  # 国民の休日(祝日に挟まれた平日)
        m = d + datetime.timedelta(days=1)
        if m + datetime.timedelta(days=1) in h and m not in h and m.weekday() != 6:
            h.add(m)
    for d in sorted(h):                                                  # 振替休日
        if d.weekday() == 6:
            s = d + datetime.timedelta(days=1)
            while s in h:
                s += datetime.timedelta(days=1)
            h.add(s)
    return h


def is_weekday(d):
    if d.weekday() >= 5 or d in jp_holidays(d.year):
        return False
    if d.month == 8 and 13 <= d.day <= 16:
        return False
    if (d.month == 12 and d.day >= 29) or (d.month == 1 and d.day <= 3):
        return False
    return True


# ---------------------------------------------------------------------------
#  交通量APIの取得
# ---------------------------------------------------------------------------
def _request(layer, road, t0, t1, log):
    q = {'service': 'WFS', 'version': '2.0.0', 'request': 'GetFeature', 'typeNames': layer,
         'srsName': 'EPSG:4326', 'outputFormat': 'csv', 'exceptions': 'application/json',
         'cql_filter': "道路種別='%s' AND 時間コード>=%s AND 時間コード<=%s AND BBOX(ジオメトリ,%s,%s,%s,%s,'EPSG:4326')"
                       % ((road, t0, t1) + JAPAN_BBOX)}
    url = API + '?' + urllib.parse.urlencode(q)
    for attempt in range(4):
        try:
            body = urllib.request.urlopen(url, timeout=300).read().decode('utf-8-sig')
            break
        except Exception as e:
            log('  取得失敗(%d回目) %s %s-%s: %s' % (attempt + 1, layer, t0, t1, e))
            time.sleep(10 * (attempt + 1))
    else:
        raise RuntimeError('交通量APIから取得できませんでした')
    if body.startswith('{'):
        j = json.loads(body)
        if 'Size' in str(j.get('errorType', '')) or 'size' in str(j.get('errorMessage', '')):
            return None          # 返却量の上限超え → 呼び出し側で期間を分割
        raise RuntimeError('交通量APIのエラー: %s' % body[:300])
    if body.startswith('"'):
        body = json.loads(body)  # CSVがJSON文字列として返る
    return list(csv.DictReader(io.StringIO(body)))


def fetch_day(layer, road, day, log):
    """1日分(0～23時)。上限を超えたら時間帯を分割して取り直す"""
    def get(h0, h1):
        rows = _request(layer, road, day.strftime('%Y%m%d') + '%02d00' % h0, day.strftime('%Y%m%d') + '%02d59' % h1, log)
        time.sleep(REQUEST_INTERVAL)
        if rows is None:
            if h0 == h1:
                raise RuntimeError('1時間分でも返却量の上限を超えました')
            m = (h0 + h1) // 2
            return get(h0, m) + get(m + 1, h1)
        return rows
    return get(0, 23)


def _int(v):
    v = (v or '').strip()
    return int(float(v)) if v else None


def row_volume(row, d, kind):
    """方向 d の1時間交通量。欠測・停電・機器異常は None"""
    if kind == '常設':
        for f in ('欠測', '停電', 'ループ異常', '超音波異常'):
            if (row.get('%s・%s' % (d, f)) or '0').strip() == '1':
                return None
        parts = [_int(row.get('%s・%s交通量' % (d, k))) for k in ('小型', '大型', '車種判別不能')]
        if parts[0] is None or parts[1] is None:
            return None
        return sum(p or 0 for p in parts)
    return _int(row.get('%s・自動車交通量' % d))


# ---------------------------------------------------------------------------
#  センサス 時間帯別交通量(zkntrf)と 基本区間→交通量調査単位区間 の対応(kasyo)
# ---------------------------------------------------------------------------
def _read_cp932_csv(path):
    raw = open(path, 'rb').read()
    try:
        text = raw.decode('cp932')
    except UnicodeDecodeError:
        text = raw.decode('utf-8-sig')
    return list(csv.reader(io.StringIO(text)))


def load_census_hourly(data_dir):
    files = sorted(glob.glob(os.path.join(data_dir, '**', 'kasyo[0-9][0-9].csv'), recursive=True))
    sec2unit = {}
    for f in files:
        rows = _read_cp932_csv(f)
        ci = {n: i for i, n in reversed(list(enumerate(rows[0])))}
        i_no, i_tc, i_tu = ci['交通調査基本区間番号'], ci['交通量／都道府県指定市コード'], ci['交通量／調査単位区間番号']
        for r in rows[1:]:
            if len(r) > i_tu and r[i_no].strip() and r[i_tc].strip() and r[i_tu].strip():
                sec2unit[r[i_no].strip().zfill(11)] = (int(r[i_tc]), int(r[i_tu]))
    hourly = {}
    for f in sorted(glob.glob(os.path.join(data_dir, '**', 'zkntrf[0-9][0-9].csv'), recursive=True)):
        rows = _read_cp932_csv(f)
        for r in rows[1:]:
            if len(r) < 35 or not r[0].strip():
                continue
            if r[4].strip() != '1':          # 令和3年度に観測した区間だけを真値とする
                continue
            key = (int(r[0]), int(r[1]))
            ent = hourly.setdefault(key, {'date': r[7].strip(), 'kind': '24時間' if r[6].strip() == '2' else '12時間',
                                           'dirs': {d: [None] * 24 for d in DIRS}})
            d = DIRS[0] if r[9].strip() == '1' else DIRS[1]
            arr = ent['dirs'][d]
            for i in range(24):             # 列は 7時台 … 23時台, 0時台 … 6時台
                v = _int(r[11 + i])
                if v is not None:
                    h = (7 + i) % 24
                    arr[h] = (arr[h] or 0) + v   # 車種区分(小型・大型)を合計
    return sec2unit, hourly


# ---------------------------------------------------------------------------
#  トラカン位置 → DRMリンク
# ---------------------------------------------------------------------------
def snap_link(drm, lon, lat, link_cell, scale, prefer_cls=()):
    """近いリンクを探す。(距離m, リンク番号) または None
    優先順: ①トラカンと同じ道路種別(国道/高速)のリンク ②センサス区間を持つリンク ③一番近いリンク
    (直轄国道のトラカンが近くの県道等に対応付くのを防ぐ)"""
    k = math.cos(math.radians(lat)) * 111320
    X, Y = lon * scale, lat * scale
    c = link_cell
    best = best_cen = best_cls = None
    co, cof = drm.coords, drm.c_off
    for cx in (int(lon // c) - 1, int(lon // c), int(lon // c) + 1):
        for cy in (int(lat // c) - 1, int(lat // c), int(lat // c) + 1):
            for i in drm.link_grid.get((cx, cy), ()):
                s = co[cof[i]:cof[i + 1]]
                dmin = None
                for j in range(0, len(s) - 2, 2):
                    ax, ay, bx, by = (s[j] - X) / scale * k, (s[j + 1] - Y) / scale * 111320, (s[j + 2] - X) / scale * k, (s[j + 3] - Y) / scale * 111320
                    dx, dy = bx - ax, by - ay
                    L2 = dx * dx + dy * dy
                    t = 0 if L2 == 0 else max(0, min(1, -(ax * dx + ay * dy) / L2))
                    dd = math.hypot(ax + t * dx, ay + t * dy)
                    dmin = dd if dmin is None or dd < dmin else dmin
                if dmin is None or dmin > SNAP_M:
                    continue
                if best is None or dmin < best[0]:
                    best = (dmin, i)
                if drm.l_cen[i] and (best_cen is None or dmin < best_cen[0]):
                    best_cen = (dmin, i)
                if drm.l_cls[i] in prefer_cls:
                    # 同じ種別ならセンサス区間を持つものを優先、その中で近いもの
                    key = (0 if drm.l_cen[i] else 1, dmin)
                    if best_cls is None or key < best_cls[0]:
                        best_cls = (key, (dmin, i))
    return (best_cls and best_cls[1]) or best_cen or best


# ---------------------------------------------------------------------------
#  比較
# ---------------------------------------------------------------------------
def compare(sensor, census):
    """sensor/census: 24時間の配列(None=値なし)。(誤差率, 比較した時間数, 相関) または None"""
    hours = [h for h in range(24) if census[h] is not None]
    if not hours:
        return None
    use = [h for h in hours if sensor[h] is not None]
    if len(use) < MIN_HOUR_RATIO * len(hours):
        return None
    s, c = sum(sensor[h] for h in use), sum(census[h] for h in use)
    if c <= 0:
        return None
    xs, ys = [sensor[h] for h in use], [census[h] for h in use]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    vx = sum((x - mx) ** 2 for x in xs)
    vy = sum((y - my) ** 2 for y in ys)
    r = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / math.sqrt(vx * vy) if vx > 0 and vy > 0 else None
    return {'err': round((s - c) / c, 4), 'hours': len(use), 'sensorSum': round(s), 'censusSum': c,
            'r': round(r, 3) if r is not None else None}


# ---------------------------------------------------------------------------
#  生データの保存(1時間値・全日)。<DRMデータフォルダ>\トラカン国交省\YYYY-MM.zip に 日付_種別_道路種別.csv
#  APIは1時間値を過去約3か月分しか持たないため、毎回まだ保存していない日をさかのぼって保存する
# ---------------------------------------------------------------------------
ARCHIVE_DIR_NAME = 'トラカン国交省'
ARCHIVE_DAYS_BACK = 92
RECENT_DAYS = 2           # 昨日・一昨日は24時間分そろったときだけ保存する
LOCK_NAME = '_更新中.lock'
LOCK_STALE_SEC = 3 * 3600  # これより古いロックは前回の異常終了の残りとみなす


def _member(day, kind, road):
    return '%s_%s_道路種別%s.csv' % (day.strftime('%Y%m%d'), kind, road)


def archived_members(arch_dir):
    names = set()
    for f in glob.glob(os.path.join(arch_dir, '*.zip')):
        try:
            with zipfile.ZipFile(f) as z:
                names.update(z.namelist())
        except zipfile.BadZipFile:
            pass
    return names


def archive_rows(arch_dir, day, kind, road, rows):
    os.makedirs(arch_dir, exist_ok=True)
    buf = io.StringIO()
    if rows:
        w = csv.DictWriter(buf, fieldnames=list(rows[0].keys()), lineterminator='\r\n')
        w.writeheader()
        w.writerows(rows)
    with zipfile.ZipFile(os.path.join(arch_dir, day.strftime('%Y-%m') + '.zip'), 'a', zipfile.ZIP_DEFLATED) as z:
        z.writestr(_member(day, kind, road), '﻿' + buf.getvalue())   # Excelで開けるようBOM付きUTF-8


def read_archived(arch_dir, day, kind, road):
    p = os.path.join(arch_dir, day.strftime('%Y-%m') + '.zip')
    with zipfile.ZipFile(p) as z:
        text = z.read(_member(day, kind, road)).decode('utf-8-sig')
    return list(csv.DictReader(io.StringIO(text)))


def archive_missing_days(arch_dir, log):
    """まだ保存していない日(昨日から約3か月前まで)をAPIから取得して保存する"""
    have = archived_members(arch_dir)
    today = datetime.date.today()
    todo = []
    for back in range(1, ARCHIVE_DAYS_BACK + 1):
        day = today - datetime.timedelta(days=back)
        for layer, kind in LAYERS:
            for road in ROAD_TYPES:
                if _member(day, kind, road) not in have:
                    todo.append((day, layer, kind, road))
    log('トラカン: 生データ未保存 %d 件(日×種別×道路種別)を取得して保存します' % len(todo))
    empty_old = set()
    for k, (day, layer, kind, road) in enumerate(todo, 1):
        if day in empty_old:
            continue
        try:
            rows = fetch_day(layer, road, day, log)
        except Exception as e:
            log('トラカン: %s %s 道路種別%s を取得できません。次回また取りに行きます(%s)' % (day, kind, road, e))
            continue
        if not rows and road == '3' and (today - day).days > 80:
            # 提供期間(約3か月)より前 → 保存しない
            empty_old.add(day)
            log('トラカン: %s はAPIの提供期間外のため保存しません' % day)
            continue
        if (today - day).days <= RECENT_DAYS and len({r.get('時間帯') for r in rows}) < 24:
            # 直近の日はAPI側でまだ揃っていないことがある。途中までを保存すると以後取り直さないため、揃うまで待つ
            log('トラカン: %s %s 道路種別%s はまだ24時間分そろっていないため次回取得します' % (day, kind, road))
            continue
        archive_rows(arch_dir, day, kind, road, rows)
        log('トラカン: [%d/%d] %s %s 道路種別%s: %d 行を保存' % (k, len(todo), day, kind, road, len(rows)))


def available_range(arch_dir):
    """アーカイブ済みの日付の範囲(最初の日, 最後の日。'YYYY-MM-DD')。無ければ None"""
    days = set()
    for f in glob.glob(os.path.join(arch_dir, '*.zip')):
        try:
            with zipfile.ZipFile(f) as z:
                days.update(n[:8] for n in z.namelist())
        except zipfile.BadZipFile:
            pass
    if not days:
        return None
    ds = sorted(days)
    fmt = lambda s: '%s-%s-%s' % (s[:4], s[4:6], s[6:8])
    return fmt(ds[0]), fmt(ds[-1])


def _detail(row, d, kind):
    """方向dの内訳(小型,大型,判別不能,合計,備考)。欠測・異常なら合計=None"""
    if kind == '常設':
        bad = [f for f in ('停電', 'ループ異常', '超音波異常', '欠測') if (row.get('%s・%s' % (d, f)) or '0').strip() == '1']
        sm, lg, un = (_int(row.get('%s・%s交通量' % (d, k))) for k in ('小型', '大型', '車種判別不能'))
        if bad or sm is None or lg is None:
            return sm, lg, un, None, '・'.join(bad) if bad else '欠測'
        return sm, lg, un or 0, sm + lg + (un or 0), ''
    # CCTVトラカンには常設のような異常フラグ列が無く、カメラ異常時は各交通量が空欄になる(row_volume()と同じ判断)
    tot = _int(row.get('%s・自動車交通量' % d))
    sm = _int(row.get('%s・小型交通量' % d))
    lg = _int(row.get('%s・大型交通量' % d))
    un = _int(row.get('%s・小型大型判別不能交通量' % d))
    if tot is None:
        return sm, lg, un, None, 'カメラ異常等'
    return sm, lg, un, tot, ''


INDEX_NAME = '_地点別収録日.json'   # アーカイブ内の各CSV(1日分)に値がある常時観測点コードの一覧
_IDX = {'data': None}
_IDX_LOCK = threading.Lock()


def site_day_index(arch_dir, log):
    """{メンバー名: {常時観測点コード,...}}。保存済みの索引を読み、索引に無い日だけZIPを読んで追加する
    (全部読むと40秒ほどかかるため、索引はアーカイブと同じフォルダに保存して皆で使う)"""
    path = os.path.join(arch_dir, INDEX_NAME)
    with _IDX_LOCK:
        if _IDX['data'] is None:
            try:
                with open(path, encoding='utf-8') as f:
                    _IDX['data'] = {m: set(c) for m, c in json.load(f).items()}
            except (OSError, ValueError):
                _IDX['data'] = {}
        idx = _IDX['data']
        added = 0
        for zp in sorted(glob.glob(os.path.join(arch_dir, '*.zip'))):
            try:
                with zipfile.ZipFile(zp) as z:
                    for m in z.namelist():
                        if m in idx or not m.endswith('.csv'):
                            continue
                        kind = m.split('_')[1]
                        codes = set()
                        for row in csv.DictReader(io.StringIO(z.read(m).decode('utf-8-sig'))):
                            code = (row.get('常時観測点コード') or '').strip()
                            if code and code not in codes and any(_detail(row, d, kind)[3] is not None for d in DIRS):
                                codes.add(code)
                        idx[m] = codes
                        added += 1
            except zipfile.BadZipFile:
                continue
        if added:
            log('トラカン: 地点別収録日の索引に %d 日分を追加' % added)
            try:
                tmp = path + '.%d.tmp' % os.getpid()
                with open(tmp, 'w', encoding='utf-8') as f:
                    json.dump({m: sorted(c) for m, c in idx.items()}, f, ensure_ascii=False, separators=(',', ':'))
                os.replace(tmp, path)
            except OSError as e:
                log('トラカン: 索引を保存できません(%s)' % e)
        return idx


def availability(sites_by_id, ids, arch_dir, log):
    """各地点の生データがある期間 {id: {'from','to','days'}}。days は値がある日数(欠測の多い日も1日)"""
    idx = site_day_index(arch_dir, log)
    out = {}
    for i in ids:
        s = sites_by_id.get(i)
        if not s:
            continue
        suffix = '_%s_道路種別%s.csv' % (s['kind'], s['road'])
        days = sorted({m[:8] for m, codes in idx.items() if m.endswith(suffix) and s['code'] in codes})
        fmt = lambda x: '%s-%s-%s' % (x[:4], x[4:6], x[6:8])
        mask = collections.defaultdict(int)   # 'YYYYMM' -> 日のビット(1日=1)
        for x in days:
            mask[x[:6]] |= 1 << (int(x[6:8]) - 1)
        out[i] = ({'from': fmt(days[0]), 'to': fmt(days[-1]), 'days': len(days), 'mask': mask} if days
                  else {'from': None, 'to': None, 'days': 0, 'mask': {}})
    return out


def export(sites_by_id, ids, date_from, date_to, arch_dir, log):
    """選択した地点・期間の生データ(1時間値・方向別)を取り出す。アーカイブ済みの日だけが対象"""
    groups = collections.defaultdict(set)   # (kind, road) -> {常時観測点コード,...}
    id_of = {}                              # (kind, 常時観測点コード) -> id
    for i in ids:
        s = sites_by_id.get(i)
        if not s:
            continue
        groups[(s['kind'], s['road'])].add(s['code'])
        id_of[(s['kind'], s['code'])] = i
    out = []
    n_days = (date_to - date_from).days + 1
    for k in range(n_days):
        day = date_from + datetime.timedelta(days=k)
        for (kind, road), codes in groups.items():
            try:
                rows = read_archived(arch_dir, day, kind, road)
            except (FileNotFoundError, KeyError):
                continue
            for row in rows:
                code = (row.get('常時観測点コード') or '').strip()
                if code not in codes:
                    continue
                site_id = id_of[(kind, code)]
                h = int((row.get('時間帯') or '0').zfill(4)[:2])
                for d in DIRS:
                    sm, lg, un, tot, note = _detail(row, d, kind)
                    if sm is None and lg is None and tot is None:
                        continue
                    out.append([site_id, kind, day.isoformat(), h, d, sm, lg, un, tot, note])
        if (k + 1) % 10 == 0 or k + 1 == n_days:
            log('トラカン(国交省) 出力用データ作成: %d/%d 日' % (k + 1, n_days))
    return out


def update(drm, census_info, data_dir, out_path, log, link_cell, scale, days=30):
    """毎日タスクスケジューラから実行する想定。同時に2つ動かないようロックファイルを置く"""
    arch_dir = os.path.join(data_dir, ARCHIVE_DIR_NAME)
    os.makedirs(arch_dir, exist_ok=True)
    lock = os.path.join(arch_dir, LOCK_NAME)
    try:
        if time.time() - os.path.getmtime(lock) > LOCK_STALE_SEC:
            os.remove(lock)
    except OSError:
        pass
    try:
        fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError:
        log('トラカン: 別の更新が実行中のため終了します(%s)' % lock)
        return
    try:
        os.write(fd, ('%s %s\n' % (datetime.datetime.now().isoformat(timespec='seconds'), os.environ.get('COMPUTERNAME', ''))).encode())
        os.close(fd)
        _update(drm, census_info, arch_dir, out_path, log, link_cell, scale, days)
    finally:
        try:
            os.remove(lock)
        except OSError:
            pass


def _update(drm, census_info, arch_dir, out_path, log, link_cell, scale, days):
    data_dir = os.path.dirname(arch_dir)
    archive_missing_days(arch_dir, log)
    site_day_index(arch_dir, log)   # ダウンロード画面で地点ごとの収録期間をすぐ出せるように

    today = datetime.date.today()
    end = today - datetime.timedelta(days=1)
    start = end - datetime.timedelta(days=days - 1)
    daylist = [start + datetime.timedelta(days=i) for i in range(days)]
    weekdays = [d for d in daylist if is_weekday(d)]
    log('トラカン: 期間 %s～%s のうち平日 %d 日を集計します(保存済みの生データから)' % (start, end, len(weekdays)))

    acc = {}       # (種別, 観測点コード) → {lat, lon, sums{d:[24]}, cnts{d:[24]}}
    for day in weekdays:
        for layer, kind in LAYERS:
            for road in ROAD_TYPES:
                try:
                    rows = read_archived(arch_dir, day, kind, road)
                except (FileNotFoundError, KeyError):
                    continue   # 取得できなかった日(次回取り直す)
                for row in rows:
                    code = (row.get('常時観測点コード') or '').strip()
                    tc = (row.get('時間コード') or '').strip()
                    if not code or len(tc) < 10:
                        continue
                    h = int(tc[8:10])
                    key = (kind, code)
                    a = acc.get(key)
                    if a is None:
                        g = (row.get('ジオメトリ') or '').replace('MULTIPOINT', '').replace('(', ' ').replace(')', ' ').replace(',', ' ').split()
                        if len(g) < 2:
                            continue
                        a = acc[key] = {'lon': float(g[0]), 'lat': float(g[1]), 'road': road,
                                        'bureau': (row.get('地方整備局等番号') or '').strip(),
                                        'sums': {d: [0] * 24 for d in DIRS}, 'cnts': {d: [0] * 24 for d in DIRS}}
                    for d in DIRS:
                        v = row_volume(row, d, kind)
                        if v is not None:
                            a['sums'][d][h] += v
                            a['cnts'][d][h] += 1

    log('トラカン: センサス時間交通量を読込中')
    sec2unit, hourly = load_census_hourly(data_dir)
    sites = []
    for (kind, code), a in sorted(acc.items()):
        site = {'id': '%s-%s' % ('J' if kind == '常設' else 'C', code), 'kind': kind, 'code': code,
                'lat': round(a['lat'], 6), 'lon': round(a['lon'], 6), 'road': a['road'], 'bureau': a['bureau'],
                'dirs': {}}
        for d in DIRS:
            if sum(a['sums'][d]) == 0:   # その方向は観測していない(片方向だけのCCTV等)
                continue
            site['dirs'][d] = {'sensor': [round(a['sums'][d][h] / a['cnts'][d][h], 1) if a['cnts'][d][h] else None for h in range(24)],
                               'days': a['cnts'][d]}
        sn = snap_link(drm, a['lon'], a['lat'], link_cell, scale, (1, 2) if a['road'] == '1' else (3,))
        if sn:
            dist, lid = sn
            ci = census_info(drm, lid, True)
            site.update(linkMc=drm.mc[lid], linkDist=round(dist, 1), cen=ci['cen'], cenName=ci['cenName'])
            unit = sec2unit.get(ci['cen']) if ci['cen'] else None
            ce = hourly.get(unit) if unit else None
            if ce:
                site['census'] = {'date': ce['date'], 'kind': ce['kind'], 'unit': list(unit)}
                tot_s = [0] * 24
                tot_c = [0] * 24
                both = True
                for d in DIRS:
                    cd = ce['dirs'][d]
                    if d in site['dirs']:
                        site['dirs'][d]['census'] = cd
                        cmp_ = compare(site['dirs'][d]['sensor'], cd)
                        if cmp_:
                            site['dirs'][d].update(cmp_)
                    else:
                        both = False
                if both and all(site['dirs'][d].get('err') is not None for d in DIRS):
                    s_all = [None if any(site['dirs'][d]['sensor'][h] is None for d in DIRS) else sum(site['dirs'][d]['sensor'][h] for d in DIRS) for h in range(24)]
                    c_all = [None if any(ce['dirs'][d][h] is None for d in DIRS) else sum(ce['dirs'][d][h] for d in DIRS) for h in range(24)]
                    cmp_ = compare(s_all, c_all)
                    if cmp_:
                        site['err'] = cmp_['err']
                elif len(site['dirs']) == 1:
                    d = next(iter(site['dirs']))
                    if site['dirs'][d].get('err') is not None:
                        site['err'] = site['dirs'][d]['err']
        sites.append(site)
    out = {'source': '交通量API（国土交通省）機能による交通量(参考値)を加工して作成',
           'generated': datetime.datetime.now().strftime('%Y-%m-%d %H:%M'),
           'period': [str(start), str(end)], 'weekdays': len(weekdays), 'drmVer': drm.ver, 'sites': sites}
    tmp = out_path + '.%d.tmp' % os.getpid()
    with open(tmp, 'w', encoding='utf-8') as f:
        json.dump(out, f, ensure_ascii=False, separators=(',', ':'))
    os.replace(tmp, out_path)
    n_cmp = sum(1 for s in sites if s.get('err') is not None)
    log('トラカン: %d 地点(うちセンサスと比較できた地点 %d) → %s' % (len(sites), n_cmp, out_path))
    return out
