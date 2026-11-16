# -*- coding: utf-8 -*-
"""
DRMリンク拾いツール サーバ
  python server.py [DRMデータフォルダ] [--port=8765] [--shared-cache=共有の_cacheフォルダ] [--build-only]
  DRMデータフォルダ直下の 3503, 3603 … のフォルダを DRM版 として扱う(版ごとに別のネットワーク)。
起動するとブラウザで http://localhost:8765/ が開く。標準ライブラリのみで動作。
"""
import collections
import csv
import datetime
import gc
import glob
import heapq
import io
import json
import math
import os
import pickle
import re
import socketserver
import socket
import struct
import sys
import threading
import time
import webbrowser
import zipfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # UNCパス等で自動のパス追加が効かない場合があるため明示
import jartic    # JARTICトラカン(社内SQL Server)
import torakan   # 国交省トラカン(交通量API)
import usage as usage_log   # 利用状況の記録・集計
from array import array
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

HERE = os.path.dirname(os.path.abspath(__file__))
# DRMデータはツールフォルダの隣の「DRMコピー_こっちを使う」(設置場所が変わってもそのまま動くよう相対指定)
# 本体は 10_リンク拾いツール\30_ツール本体（触らない）\ にあるので、1つ上・2つ上の順に探す
DEFAULT_DATA_DIR = next((p for p in (os.path.normpath(os.path.join(HERE, *['..'] * k, 'DRMコピー_こっちを使う')) for k in (1, 2))
                         if os.path.isdir(p)), os.path.normpath(os.path.join(HERE, '..', 'DRMコピー_こっちを使う')))
PORT = 8765
CACHE_VERSION = 13
MAX_LOADED = 2     # 同時にメモリに置くDRM版の数(超えたら使っていない版から解放)
ALL_TYPES = {1, 2, 3, 4, 5, 6, 7, 9}
CLS_NAMES = {1: '高速自動車国道', 2: '都市高速道路', 3: '一般国道', 4: '主要地方道(都道府県道)',
             5: '主要地方道(指定市道)', 6: '一般都道府県道', 7: '指定市の一般市道', 9: 'その他の道路'}
PREF_NAMES = ['', '北海道', '青森県', '岩手県', '宮城県', '秋田県', '山形県', '福島県', '茨城県', '栃木県', '群馬県',
              '埼玉県', '千葉県', '東京都', '神奈川県', '新潟県', '富山県', '石川県', '福井県', '山梨県', '長野県',
              '岐阜県', '静岡県', '愛知県', '三重県', '滋賀県', '京都府', '大阪府', '兵庫県', '奈良県', '和歌山県',
              '鳥取県', '島根県', '岡山県', '広島県', '山口県', '徳島県', '香川県', '愛媛県', '高知県', '福岡県',
              '佐賀県', '長崎県', '熊本県', '大分県', '宮崎県', '鹿児島県', '沖縄県']
# 政令指定都市(行政CDの範囲)。指定市道の名称に使う
DESIGNATED_CITIES = [(1101, 1110, '札幌市'), (4101, 4105, '仙台市'), (11101, 11110, 'さいたま市'), (12101, 12106, '千葉市'),
                     (14101, 14118, '横浜市'), (14131, 14137, '川崎市'), (14151, 14153, '相模原市'), (15101, 15108, '新潟市'),
                     (22101, 22103, '静岡市'), (22131, 22140, '浜松市'), (23101, 23116, '名古屋市'), (26101, 26111, '京都市'),
                     (27102, 27128, '大阪市'), (27141, 27147, '堺市'), (28101, 28111, '神戸市'), (33101, 33104, '岡山市'),
                     (34101, 34108, '広島市'), (40101, 40109, '北九州市'), (40131, 40137, '福岡市'), (43101, 43105, '熊本市')]
NAME_FILE = os.path.join(HERE, '路線名称.csv')
# センサス(令和3年度 箇所別基本表)から作る対応表。DRMデータフォルダ内の kasyo01～47.csv から作成
CENSUS_FILE = os.path.join(HERE, 'census_r3.json')
# サーバのバージョン識別(server.py・index.html の更新日時)。古いサーバが動いていたら入れ替える
BUILD = '%d-%d' % tuple(int(os.path.getmtime(os.path.join(HERE, f))) for f in ('server.py', 'index.html'))
# 交通規制種別コード: 1規制無し 2通行禁止(条件無) 3通行禁止(条件付) 4一方通行(正,条件無) 5一方通行(逆,条件無)
#                     6一方通行(正,条件付) 7一方通行(逆,条件付) 8一方通行(正逆切替) 0未調査
# 正方向 = ノード1→ノード2。モードごとに「正方向に進めない」「逆方向に進めない」コード
ONEWAY_BLOCK = {
    'all':    ({2, 3, 5, 7}, {2, 3, 4, 6}),   # 条件付き規制も考慮
    'strict': ({2, 5}, {2, 4}),               # 条件無しの規制のみ考慮
    'off':    (set(), set()),                 # 規制を無視
}
# DRM 規制速度コード(O) → km/h。仕様書: 1=30km/h未満 2=40 3=50 4=60 5=70 6=80 7=100 0=未調査
# 1は「30km/h未満」のため20km/hで計算。8・9は仕様書の表に無いが、9は新東名等の120km/h区間に現れるため120とした
SPEED_KMH = {1: 20, 2: 40, 3: 50, 4: 60, 5: 70, 6: 80, 7: 100, 8: 110, 9: 120}
VMAX_KMH = 120


def default_kmh(cls, linkcd):
    """規制速度が未調査(0)のリンクの仮の速度"""
    if cls in (1, 2):                       # 高速・都市高速
        return 80 if linkcd in (1, 2) else 20 if linkcd == 7 else 40   # 本線 / SA等 / ランプ・渡り線
    if cls in (3, 4, 5, 6):                 # 国道・県道・主要地方道
        return 40
    return 30                               # 市道・その他


LINK_CELL = 0.02   # リンク空間インデックスのセルサイズ(度)
NODE_CELL = 0.01   # ノード空間インデックスのセルサイズ(度)
SCALE = 1e6        # 座標の整数化倍率


def log(*a):
    print(time.strftime('[%H:%M:%S]'), *a, flush=True)


def iter_geojson(path):
    """GDAL出力のGeoJSON(1行1フィーチャ)を省メモリで読む。形式が違えば丸ごと読む。"""
    n = 0
    with open(path, encoding='utf-8') as f:
        for line in f:
            s = line.strip()
            if not s.startswith('{ "type": "Feature"'):
                continue
            if s.endswith(','):
                s = s[:-1]
            n += 1
            yield json.loads(s)
    if n == 0:
        with open(path, encoding='utf-8') as f:
            yield from json.load(f)['features']


def iter_shapefile(path):
    """Shapefile(PolyLine)+DBFを読み、GeoJSONと同じ形の辞書を返す"""
    base = os.path.splitext(path)[0]
    enc = 'cp932'
    if os.path.exists(base + '.cpg'):
        cp = open(base + '.cpg', encoding='ascii', errors='ignore').read().strip().lower()
        if 'utf' in cp:
            enc = 'utf-8'
    with open(base + '.dbf', 'rb') as f:
        dbf = f.read()
    nrec, hlen, rlen = struct.unpack('<IHH', dbf[4:12])
    fields = []
    pos = 32
    while dbf[pos] != 0x0D:
        d = dbf[pos:pos + 32]
        fields.append((d[:11].split(b'\0')[0].decode(enc, 'replace'), chr(d[11]), d[16]))
        pos += 32
    with open(path, 'rb') as f:
        shp = f.read()
    sp = 100
    for r in range(nrec):
        rec = dbf[hlen + r * rlen: hlen + (r + 1) * rlen]
        props = {}
        o = 1
        for name, typ, ln in fields:
            v = rec[o:o + ln].decode(enc, 'replace').strip()
            o += ln
            if typ in 'NF':
                try:
                    v = int(v) if typ == 'N' and '.' not in v else float(v)
                except ValueError:
                    v = 0
            props[name] = v
        clen = struct.unpack('>i', shp[sp + 4:sp + 8])[0] * 2
        c = shp[sp + 8:sp + 8 + clen]
        sp += 8 + clen
        parts = []
        if struct.unpack('<i', c[:4])[0] != 0:
            nparts, npts = struct.unpack('<ii', c[36:44])
            idx = list(struct.unpack('<%di' % nparts, c[44:44 + 4 * nparts])) + [npts]
            xy = struct.unpack('<%dd' % (2 * npts), c[44 + 4 * nparts:44 + 4 * nparts + 16 * npts])
            parts = [[[xy[2 * k], xy[2 * k + 1]] for k in range(idx[j], idx[j + 1])] for j in range(nparts)]
        yield {'properties': props, 'geometry': {'type': 'MultiLineString', 'coordinates': parts}}


def find_sources(data_dir):
    """リンクデータ(GeoJSON/Shapefile)を探し、DRM版(4桁)ごとにまとめる → {版: [ファイル,...]}"""
    files = glob.glob(os.path.join(data_dir, '**', '*リンク*.geojson'), recursive=True)
    files += [f for f in glob.glob(os.path.join(data_dir, '**', '*.shp'), recursive=True) if 'ノード' not in os.path.basename(f)]
    out = collections.defaultdict(list)
    for f in sorted(files):
        # DRMは「4桁の版フォルダ(3503 等)」の中のものだけ。JARTIC計測地点など他のshpは対象外
        top = os.path.relpath(f, data_dir).split(os.sep)[0]
        if re.fullmatch(r'\d{4}', top):
            out[top].append(f)
    return dict(out)


def region_label(files):
    """ファイル名(…_04南関東 など)から収録地域を表示用にまとめる"""
    regions = []
    for f in files:
        stem = os.path.splitext(os.path.basename(f))[0]
        m = re.search(r'_(?:\d{2})?([^_]+)$', stem)
        if m and m.group(1) not in regions:
            regions.append(m.group(1))
    if len(regions) >= 9:
        return '全国'
    return '・'.join(regions) + 'のみ' if regions else ''


def reverse_mc(mc):
    """MATCHCODE(メッシュ-ノード1ノード2) → メッシュ-ノード2ノード1"""
    return mc[:-10] + mc[-5:] + mc[-10:-5]


class DRM:
    """1つのDRM版の道路ネットワーク"""

    def build(self, ver, sources, data_dir, prog):
        node_index = {}
        self.ver = ver
        self.node_key = []
        self.node_lon = array('i')
        self.node_lat = array('i')
        node_mesh = array('i')

        def node(mesh, nd, pt):
            key = '%d-%s' % (mesh, nd)
            i = node_index.get(key)
            if i is None:
                i = node_index[key] = len(self.node_key)
                self.node_key.append(key)
                self.node_lon.append(round(pt[0] * SCALE))
                self.node_lat.append(round(pt[1] * SCALE))
                node_mesh.append(mesh)
            return i

        def node_conflict(mesh, nd, pt):
            """既に読んだ同じノード番号が別の位置にあるか"""
            i = node_index.get('%d-%s' % (mesh, nd))
            return i is not None and (abs(self.node_lon[i] - pt[0] * SCALE) > 20 or abs(self.node_lat[i] - pt[1] * SCALE) > 20)

        self.mc = []
        self.l_n1 = array('i')
        self.l_n2 = array('i')
        self.l_len = array('f')
        self.l_cls = array('b')
        self.l_rno = array('i')
        self.l_reg = array('b')
        self.l_gyo = array('i')
        self.l_hw = array('b')   # 自動車専用道路・高速道路系なら1
        self.l_cen = array('q')  # 調査単位(センサス区間番号の下10桁。先頭は都道府県コードの一の位)。0=なし
        self.l_cyr = array('b')  # ｾﾝｻｽ年度(21=令和3年度, 15=平成27年度)
        self.l_kki = array('b')  # 管起点N(路線の起点側の端): 1=NODE1側 2=NODE2側 0=なし
        self.l_kmh = array('b')  # 経路探索に使う速度(km/h)。規制速度コードから。未調査は道路種別ごとの仮の値
        self.l_kmh_src = array('b')  # 1=規制速度から 0=仮の値
        self.l_time = array('f') # 所要時間(秒) = リンク長 / 速度
        self.coords = array('i')
        self.c_off = array('i', [0])
        # 地域ファイルは県境で分かれており、同じメッシュが複数ファイルに入る(中身は別のリンク)。
        # 地域の境目で同じリンクが両方に入っている場合はリンク(MATCHCODE)単位で除く。
        seen_mc = set()
        dup = collections.Counter()
        conflict = collections.Counter()
        for si, src in enumerate(sources):
            prog('データ変換: %s を読込中 (%d/%d)' % (os.path.basename(src), si + 1, len(sources)), 5 + 70 * si / len(sources))
            it = iter_shapefile(src) if src.lower().endswith('.shp') else iter_geojson(src)
            for ft in it:
                p = ft['properties']
                mesh = int(p['MESHCD'])
                if p['MATCHCODE'] in seen_mc:
                    dup[src] += 1
                    continue
                parts = ft['geometry']['coordinates']
                if ft['geometry']['type'] == 'LineString':
                    parts = [parts]
                pts = [pt for part in parts for pt in part]
                if len(pts) < 2:
                    continue
                if si and (node_conflict(mesh, p['NODE1'], pts[0]) or node_conflict(mesh, p['NODE2'], pts[-1])):
                    conflict[src] += 1
                    continue
                seen_mc.add(p['MATCHCODE'])
                for x, y in (pt[:2] for pt in pts):
                    self.coords.append(round(x * SCALE))
                    self.coords.append(round(y * SCALE))
                self.c_off.append(len(self.coords))
                length = p.get('リンク長') or 0
                if not length:
                    length = geo_len(pts)
                cls = int(p.get('種別CD') or 9)
                self.mc.append(p['MATCHCODE'])
                self.l_n1.append(node(mesh, p['NODE1'], pts[0]))
                self.l_n2.append(node(mesh, p['NODE2'], pts[-1]))
                self.l_len.append(float(length))
                self.l_cls.append(cls)
                self.l_rno.append(int(p.get('路線番号') or 0))
                self.l_reg.append(int(p.get('交通規制') or 0))
                self.l_gyo.append(int(p.get('行政CD') or 0))
                self.l_hw.append(1 if p.get('自専CD') == 1 or cls in (1, 2) else 0)
                try:
                    self.l_cen.append(int(p.get('調査単位') or 0))
                except ValueError:
                    self.l_cen.append(0)
                self.l_cyr.append(int(p.get('ｾﾝｻｽ年度') or 0))
                kn = str(p.get('管起点N') or '')
                self.l_kki.append(1 if kn == str(p['NODE1']) else 2 if kn == str(p['NODE2']) else 0)
                kmh = SPEED_KMH.get(int(p.get('規制速度') or 0))
                self.l_kmh_src.append(1 if kmh else 0)
                if not kmh:
                    kmh = default_kmh(cls, int(p.get('リンクCD') or 0))
                self.l_kmh.append(kmh)
                self.l_time.append(float(length) / (kmh / 3.6))
        del seen_mc
        for src, n in dup.items():
            log('DRM%s %s: 他の地域ファイルと重複する %d リンクを読み飛ばし' % (ver, os.path.basename(src), n))
        for src, n in conflict.items():
            log('DRM%s %s: ノード位置が食い違う %d リンクを読み飛ばし' % (ver, os.path.basename(src), n))

        # メッシュ境界(隣接メッシュで同じ座標)のノードを同一ノードとして統合
        prog('データ変換: メッシュ境界のノードを接続中', 78)
        parent = list(range(len(self.node_key)))

        def find(i):
            while parent[i] != i:
                parent[i] = parent[parent[i]]
                i = parent[i]
            return i
        TOL = 3          # 座標一致の許容(1e-6度単位, 約0.3m)
        bucket = collections.defaultdict(list)
        for i in range(len(self.node_key)):
            bucket[(self.node_lon[i] // 10, self.node_lat[i] // 10)].append(i)
        for (bx, by), members in bucket.items():
            for i in members:
                for dx in (-1, 0, 1):
                    for dy in (-1, 0, 1):
                        for j in bucket.get((bx + dx, by + dy), ()):
                            if j <= i or node_mesh[i] == node_mesh[j]:
                                continue
                            if abs(self.node_lon[i] - self.node_lon[j]) <= TOL and abs(self.node_lat[i] - self.node_lat[j]) <= TOL:
                                ri, rj = find(i), find(j)
                                if ri != rj:
                                    parent[max(ri, rj)] = min(ri, rj)
        del bucket
        self.node_rep = array('i', (find(i) for i in range(len(parent))))
        del parent
        for k in range(len(self.mc)):
            self.l_n1[k] = self.node_rep[self.l_n1[k]]
            self.l_n2[k] = self.node_rep[self.l_n2[k]]
        self.build_index(prog)
        log('DRM%s: リンク %d / ノード %d' % (ver, len(self.mc), len(self.node_key)))

    def build_index(self, prog):
        """隣接(CSR形式の配列)と空間インデックスを作る。変換時に作ってキャッシュに保存する。"""
        prog('データ変換: 検索用インデックス作成中', 85)
        n, nl = len(self.node_key), len(self.mc)
        n1, n2 = self.l_n1, self.l_n2
        deg = array('i', bytes(4 * (n + 1)))
        for i in range(nl):
            a, b = n1[i], n2[i]
            if a != b:
                deg[a] += 1
                deg[b] += 1
        off = array('i', bytes(4 * (n + 1)))
        s = 0
        for u in range(n):
            off[u] = s
            s += deg[u]
        off[n] = s
        to = array('i', bytes(4 * s))
        lid = array('i', bytes(4 * s))
        pos = array('i', off)
        for i in range(nl):
            a, b = n1[i], n2[i]
            if a != b:
                to[pos[a]] = b
                lid[pos[a]] = i
                pos[a] += 1
                to[pos[b]] = a
                lid[pos[b]] = i
                pos[b] += 1
        self.adj_off, self.adj_to, self.adj_lid = off, to, lid
        # リンクの空間インデックス(セル → リンク番号の配列)
        grid = collections.defaultdict(list)
        c = LINK_CELL * SCALE
        co, cof = self.coords, self.c_off
        for i in range(nl):
            xs = co[cof[i]:cof[i + 1]:2]
            ys = co[cof[i] + 1:cof[i + 1]:2]
            for cx in range(int(min(xs) // c), int(max(xs) // c) + 1):
                for cy in range(int(min(ys) // c), int(max(ys) // c) + 1):
                    grid[(cx, cy)].append(i)
        self.link_grid = {k: array('i', v) for k, v in grid.items()}
        # ノードの空間インデックス(リンクがつながる代表ノードのみ)
        grid = collections.defaultdict(list)
        c = NODE_CELL * SCALE
        for i in range(n):
            if self.node_rep[i] == i and off[i + 1] > off[i]:
                grid[(int(self.node_lon[i] // c), int(self.node_lat[i] // c))].append(i)
        self.node_grid = {k: array('i', v) for k, v in grid.items()}
        xs, ys = self.node_lon, self.node_lat
        self.bbox = [min(xs) / SCALE, min(ys) / SCALE, max(xs) / SCALE, max(ys) / SCALE]

    def after_load(self):
        self.key_index = {k: i for i, k in enumerate(self.node_key)}

    # ---- 問い合わせ ----
    def link_coords(self, i, reverse=False):
        s = self.coords[self.c_off[i]:self.c_off[i + 1]]
        pts = [(s[k], s[k + 1]) for k in range(0, len(s), 2)]
        return pts[::-1] if reverse else pts

    def links_in(self, w, s, e, n, max_cls, limit):
        c = LINK_CELL
        seen = set()
        out = []
        cls = self.l_cls
        for cx in range(int(w // c), int(e // c) + 1):
            for cy in range(int(s // c), int(n // c) + 1):
                for i in self.link_grid.get((cx, cy), ()):
                    if i in seen or cls[i] > max_cls:
                        continue
                    seen.add(i)
                    out.append(i)
        out.sort(key=lambda i: cls[i])
        return out[:limit], len(out) > limit

    def nodes_in(self, w, s, e, n, limit, types=None):
        c = NODE_CELL
        W, S, E, N = (round(v * SCALE) for v in (w, s, e, n))
        out = []
        for cx in range(int(w // c), int(e // c) + 1):
            for cy in range(int(s // c), int(n // c) + 1):
                for i in self.node_grid.get((cx, cy), ()):
                    if W <= self.node_lon[i] <= E and S <= self.node_lat[i] <= N and self.has_type(i, types):
                        out.append(i)
                        if len(out) >= limit:
                            return out
        return out

    def nearest_node(self, lon, lat, types=None):
        c = NODE_CELL
        cx0, cy0 = int(lon // c), int(lat // c)
        X, Y = lon * SCALE, lat * SCALE
        k = math.cos(math.radians(lat))
        best, bd = None, None
        for r in range(0, 30):
            ring = [(cx0 + dx, cy0 + dy) for dx in range(-r, r + 1) for dy in range(-r, r + 1)
                    if max(abs(dx), abs(dy)) == r]
            for cell in ring:
                for i in self.node_grid.get(cell, ()):
                    d = ((self.node_lon[i] - X) * k) ** 2 + (self.node_lat[i] - Y) ** 2
                    if (bd is None or d < bd) and self.has_type(i, types):
                        best, bd = i, d
            # 見つかったら1リング余分に見てから確定
            if best is not None and math.sqrt(bd) / SCALE < r * c * k:
                break
        return best

    def nearest_link(self, lon, lat, types=None):
        """点に最も近いリンク (リンク番号, 距離m, 線上の最寄り点(lon,lat))。近くに無ければ None"""
        c = LINK_CELL
        cx0, cy0 = int(lon // c), int(lat // c)
        k = math.cos(math.radians(lat)) * 111320 / SCALE
        ky = 111320 / SCALE
        X, Y = lon * SCALE, lat * SCALE
        co, cof, cls, n1, n2 = self.coords, self.c_off, self.l_cls, self.l_n1, self.l_n2
        best = None
        seen = set()
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for i in self.link_grid.get((cx0 + dx, cy0 + dy), ()):
                    if i in seen or n1[i] == n2[i] or (types is not None and cls[i] not in types):
                        continue
                    seen.add(i)
                    s = co[cof[i]:cof[i + 1]]
                    for j in range(0, len(s) - 2, 2):
                        ax, ay = (s[j] - X) * k, (s[j + 1] - Y) * ky
                        bx, by = (s[j + 2] - X) * k, (s[j + 3] - Y) * ky
                        vx, vy = bx - ax, by - ay
                        L2 = vx * vx + vy * vy
                        t = 0.0 if L2 == 0 else max(0.0, min(1.0, -(ax * vx + ay * vy) / L2))
                        px, py = ax + t * vx, ay + t * vy
                        dd = px * px + py * py
                        if best is None or dd < best[1]:
                            best = (i, dd, (X + px / k) / SCALE, (Y + py / ky) / SCALE)
        if best is None:
            return None
        return best[0], math.sqrt(best[1]), (best[2], best[3])

    def link_wp_json(self, lid, pt=None):
        """経由リンクの地点情報。key = 'L:リンク番号:MATCHCODE'(版が違うと番号が変わるためMATCHCODEで確認する)"""
        if pt is None:
            s = self.link_coords(lid)
            pt = (s[len(s) // 2][0] / SCALE, s[len(s) // 2][1] / SCALE) if len(s) > 2 else \
                 ((s[0][0] + s[-1][0]) / 2 / SCALE, (s[0][1] + s[-1][1]) / 2 / SCALE)
        return {'key': 'L:%d:%s' % (lid, self.mc[lid]), 'lon': pt[0], 'lat': pt[1], 'link': True, 'mc': self.mc[lid]}

    def link_of(self, key):
        """'L:リンク番号:MATCHCODE' → リンク番号(この版に無ければ None)"""
        try:
            _, lid, mc = key.split(':', 2)
            lid = int(lid)
        except ValueError:
            return None
        return lid if 0 <= lid < len(self.mc) and self.mc[lid] == mc else None

    def node_of(self, key):
        i = self.key_index.get(key)
        return None if i is None else self.node_rep[i]

    def has_type(self, i, types):
        """ノードiに指定道路種別のリンクが接続しているか"""
        if types is None:
            return True
        cls, lid = self.l_cls, self.adj_lid
        return any(cls[lid[k]] in types for k in range(self.adj_off[i], self.adj_off[i + 1]))

    def route_name(self, i):
        """路線名称。路線名称.csv に登録があればそれを、無ければ種別・路線番号・都道府県から組み立てる"""
        cls, rno, gyo = self.l_cls[i], self.l_rno[i], self.l_gyo[i]
        pref = gyo // 1000
        nm = NAMES.get(cls, rno, pref)
        if nm:
            return nm
        pname = PREF_NAMES[pref] if 0 < pref < len(PREF_NAMES) else ''
        if cls == 1:
            return '高速自動車国道(路線番号%d)' % rno
        if cls == 2:
            return '都市高速道路(路線番号%d)' % rno
        if cls == 3:
            return '国道%d号' % rno
        if cls in (4, 6):
            return '%s道%s' % (pname or '都道府県', '%d号' % rno if rno else '')
        if cls in (5, 7):
            city = next((nm for lo, hi, nm in DESIGNATED_CITIES if lo <= gyo <= hi), '指定市')
            return city + ('道(主要地方道)' if cls == 5 else '道')
        return ''

    def shortest(self, s, t, oneway='all', types=None, mode='time', allow=None):
        """A*。mode='time': 所要時間最短(規制速度) / 'dist': 距離最短。交通規制で進入できない向き・対象外の道路種別は通らない。
        allow: 通ってよいリンクの集合(None=制限なし)。リンクIDのリストを返す。"""
        if s == t:
            return []
        block_fwd, block_rev = ONEWAY_BLOCK.get(oneway, ONEWAY_BLOCK['all'])
        n1, reg, cls = self.l_n1, self.l_reg, self.l_cls
        off, to, lids = self.adj_off, self.adj_to, self.adj_lid
        lon, lat = self.node_lon, self.node_lat
        k = math.cos(math.radians(lat[t] / SCALE)) * 111320 / SCALE
        ky = 111320 / SCALE
        tx, ty = lon[t], lat[t]

        # 推定値: 直線距離(m) ÷ 最高速度 (所要時間のとき)。過大評価しないので最短が保証される
        hs = 0.95 / (VMAX_KMH / 3.6) if mode == 'time' else 0.95

        def h(v):
            return hs * math.hypot((lon[v] - tx) * k, (lat[v] - ty) * ky)
        g = {s: 0.0}
        prev = {}
        done = set()
        pq = [(h(s), 0.0, s)]
        L = self.l_time if mode == 'time' else self.l_len
        while pq:
            _, gu, u = heapq.heappop(pq)
            if u == t:
                break
            if u in done:
                continue
            done.add(u)
            for e in range(off[u], off[u + 1]):
                lid = lids[e]
                if reg[lid] in (block_fwd if n1[lid] == u else block_rev):
                    continue
                if types is not None and cls[lid] not in types:
                    continue
                if allow is not None and lid not in allow:
                    continue
                v = to[e]
                ng = gu + L[lid]
                if ng < g.get(v, 1e18):
                    g[v] = ng
                    prev[v] = (u, lid)
                    heapq.heappush(pq, (ng + h(v), ng, v))
        else:
            return None
        path = []
        v = t
        while v != s:
            u, lid = prev[v]
            path.append(lid)
            v = u
        return path[::-1]

    def node_json(self, i):
        return {'key': self.node_key[i], 'lon': self.node_lon[i] / SCALE, 'lat': self.node_lat[i] / SCALE}


def geo_len(pts):
    d = 0.0
    for (x1, y1), (x2, y2) in zip(pts, pts[1:]):
        k = math.cos(math.radians((y1 + y2) / 2))
        d += math.hypot((x2 - x1) * k, y2 - y1) * 111320
    return d


def thin(pts, tol):
    """直前に残した点から tol 未満の点を省く(始点・終点は残す)"""
    if tol <= 0 or len(pts) <= 2:
        return pts
    out = [pts[0]]
    for p in pts[1:-1]:
        if abs(p[0] - out[-1][0]) >= tol or abs(p[1] - out[-1][1]) >= tol:
            out.append(p)
    out.append(pts[-1])
    return out


def delta(pts):
    """座標列を差分エンコードしたフラット整数列にする"""
    out = []
    px = py = 0
    for x, y in pts:
        out.append(x - px)
        out.append(y - py)
        px, py = x, y
    return out


# ---------------------------------------------------------------------------
#  DRM版の管理(必要になった版だけ読み込み、使っていない版はメモリから外す)
# ---------------------------------------------------------------------------
class Store:
    def __init__(self, data_dir, shared_cache=None):
        self.data_dir = data_dir
        self.local_cache = os.path.join(HERE, '_cache')
        self.shared_cache = shared_cache if shared_cache and os.path.normcase(os.path.abspath(shared_cache)) != os.path.normcase(os.path.abspath(self.local_cache)) else None
        self.sources = find_sources(data_dir)
        if not self.sources:
            raise SystemExit('リンクデータ(geojson/shp)が見つかりません: ' + data_dir)
        self.labels = {v: region_label(fs) for v, fs in self.sources.items()}
        nat = sorted([v for v in self.sources if self.labels[v] == '全国'], reverse=True)
        self.default = nat[0] if nat else max(self.sources)
        # 版番号 = 平成換算の年度(上2桁) + 月(下2桁) の基準年月。1〜3月は翌年 (3803 → 平成38年度=2026年度の3月 = 2027年3月時点)
        for v in self.labels:
            mon = int(v[2:])
            if 1 <= mon <= 12:
                year = 1988 + int(v[:2]) + (1 if mon <= 3 else 0)
                self.labels[v] = '・'.join(x for x in (self.labels[v], '%d年%d月時点' % (year, mon)) if x)
        self.loaded = collections.OrderedDict()      # 版 → DRM (古い順)
        self.state = {v: {'stage': '未読込', 'pct': 0, 'ready': False, 'error': None, 'loading': False} for v in self.sources}
        self.lock = threading.Lock()                 # 読込は1版ずつ(メモリ節約)
        self._last = {}

    def versions(self):
        return [{'v': v, 'label': self.labels[v], 'loaded': v in self.loaded} for v in sorted(self.sources, reverse=True)]

    def prog(self, v, stage, pct=None):
        st = self.state[v]
        st['stage'] = stage
        if pct is not None:
            st['pct'] = round(pct, 1)
        last = self._last.get(v, -100)
        if pct is None or pct - last >= 10 or pct >= 100:
            log('DRM%s [%3d%%] %s' % (v, st['pct'], stage))
            self._last[v] = st['pct']

    def get(self, v):
        """読込済みなら返す。未読込なら読込を開始して None を返す"""
        v = v if v in self.sources else self.default
        d = self.loaded.get(v)
        if d is not None:
            self.loaded.move_to_end(v)
            return d
        st = self.state[v]
        if not st['loading'] and not st['error']:
            st['loading'] = True
            st['ready'] = False
            st['stage'], st['pct'] = '読込待ち', 0
            threading.Thread(target=self._load, args=(v,), daemon=True).start()
        return None

    def _load(self, v):
        try:
            with self.lock:
                # メモリ上限: 使っていない古い版から外す
                while len(self.loaded) >= MAX_LOADED:
                    old, _ = self.loaded.popitem(last=False)
                    self.state[old].update(ready=False, stage='未読込(メモリ節約のため解放)', pct=0)
                    log('DRM%s をメモリから解放' % old)
                    gc.collect()
                t = time.time()
                d = self.load_version(v)
                self.loaded[v] = d
                self.state[v].update(ready=True, loading=False)
                self.prog(v, '準備完了 (リンク %d / ノード %d, %.1f秒)' % (len(d.mc), len(d.node_key), time.time() - t), 100)
        except BaseException as e:   # SystemExit も画面に出す
            self.state[v].update(error=str(e), loading=False)
            log('DRM%s 読込エラー:' % v, e)

    def signature(self, v):
        files = []
        for src in self.sources[v]:
            base = os.path.splitext(src)[0]
            for ext in ('.shp', '.dbf', '.geojson'):
                f = base + ext
                if os.path.exists(f):
                    files.append(f)
        return [CACHE_VERSION, v] + [(os.path.relpath(f, self.data_dir), os.path.getsize(f), int(os.path.getmtime(f))) for f in sorted(files)]

    def _copy_from_shared(self, v, name):
        """共有フォルダの変換済みデータが新しければこのPCへコピー(進捗付き)"""
        if not self.shared_cache:
            return
        src = os.path.join(self.shared_cache, name)
        dst = os.path.join(self.local_cache, name)
        try:
            ss = os.stat(src)
        except OSError:
            return
        try:
            ds = os.stat(dst)
            if ds.st_size == ss.st_size and int(ds.st_mtime) == int(ss.st_mtime):
                return
        except OSError:
            pass
        os.makedirs(self.local_cache, exist_ok=True)
        tmp = dst + '.%d.tmp' % os.getpid()
        done, total = 0, ss.st_size
        with open(src, 'rb') as fi, open(tmp, 'wb') as fo:
            while True:
                b = fi.read(8 << 20)
                if not b:
                    break
                fo.write(b)
                done += len(b)
                self.prog(v, 'このPCへ変換済みデータをコピー中 (%d / %d MB・初回のみ)' % (done >> 20, total >> 20), 5 + 45 * done / total)
        os.utime(tmp, (ss.st_atime, ss.st_mtime))
        os.replace(tmp, dst)

    def load_version(self, v):
        name = 'drm_%s.pickle' % v
        cache = os.path.join(self.local_cache, name)
        sig = self.signature(v)
        self.prog(v, '変換済みデータを確認中', 2)
        try:
            self._copy_from_shared(v, name)
        except Exception as e:
            log('DRM%s 共有フォルダからのコピー失敗:' % v, e)
        if os.path.exists(cache):
            try:
                self.prog(v, '変換済みデータ読込中 (%.0f MB)' % (os.path.getsize(cache) / 1e6), 55)
                with open(cache, 'rb') as f:
                    csig = pickle.load(f)
                    if csig == sig:
                        state = pickle.load(f)
                        d = DRM()
                        d.__dict__.update(state)
                        del state
                        self.prog(v, 'ノード索引を作成中', 85)
                        d.after_load()
                        return d
                log('DRM%s: データが更新されているため変換し直します' % v)
            except Exception as e:
                log('DRM%s 変換済みデータ読込失敗(変換し直します):' % v, e)
        self.prog(v, 'データ変換開始(このデータでは初回のみ・数分かかります)', 5)
        d = DRM()
        d.build(v, self.sources[v], self.data_dir, lambda s, p=None: self.prog(v, s, p))
        self.prog(v, '変換済みデータを保存中', 95)
        os.makedirs(self.local_cache, exist_ok=True)
        # 複数人が同時に作っても壊れないよう、一時ファイルに書いてから置き換える
        tmp = '%s.%s.%d.tmp' % (cache, socket.gethostname(), os.getpid())
        with open(tmp, 'wb') as f:
            # 先頭に署名だけを書く(署名確認のために全体を読まずに済む)。中身はインスタンスでなく配列・リスト
            pickle.dump(sig, f, protocol=pickle.HIGHEST_PROTOCOL)
            pickle.dump(dict(d.__dict__), f, protocol=pickle.HIGHEST_PROTOCOL)
        try:
            os.replace(tmp, cache)
        except OSError:
            os.remove(tmp)
        d.after_load()
        return d


class NameBook:
    """任意: ツールフォルダに 路線名称.csv (種別CD,路線番号,都道府県CD,路線名称) を置くと路線名称を上書きできる。
    都道府県CD空欄は全都道府県に適用。ファイルが更新されたら自動で読み直す。"""
    def __init__(self, path):
        self.path, self.mtime, self.map = path, None, {}

    def _reload(self):
        try:
            mt = os.path.getmtime(self.path)
        except OSError:
            self.map = {}
            return
        if mt == self.mtime:
            return
        raw = open(self.path, 'rb').read()
        for enc in ('utf-8-sig', 'cp932'):
            try:
                text = raw.decode(enc)
                break
            except UnicodeDecodeError:
                continue
        m = {}
        for row in csv.reader(io.StringIO(text)):
            if len(row) < 4 or not row[3].strip():
                continue
            try:
                cls, rno = int(row[0]), int(row[1])
                pref = int(row[2]) if row[2].strip() else None
            except ValueError:
                continue  # 見出し行など
            m[(cls, rno, pref)] = row[3].strip()
        self.map, self.mtime = m, mt
        log('路線名称.csv 読込: %d 件' % len(m))

    def get(self, cls, rno, pref):
        self._reload()
        return self.map.get((cls, rno, pref)) or self.map.get((cls, rno, None))


NAMES = NameBook(NAME_FILE)


def parse_types(v):
    """'1,3,4' や [1,3,4] → 道路種別CDの集合。未指定・全種別ならNone(制限なし)"""
    if v is None or v == '':
        return None
    if isinstance(v, str):
        v = v.split(',')
    s = {int(x) for x in v if str(x).strip()}
    return None if s >= ALL_TYPES else s


def xcol(i):
    s = ''
    i += 1
    while i:
        i, r = divmod(i - 1, 26)
        s = chr(65 + r) + s
    return s


def xesc(v):
    return (str(v).replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;').replace('"', '&quot;'))


def make_xlsx(sheets):
    """標準ライブラリだけで .xlsx を作る。sheets = [{'name','header':[...],'rows':[[...]],'widths':[...]}]"""
    def sheet_xml(sh):
        rows = [sh['header']] + sh['rows']
        out = ['<?xml version="1.0" encoding="UTF-8" standalone="yes"?>',
               '<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">',
               '<sheetViews><sheetView workbookViewId="0"><pane ySplit="1" topLeftCell="A2" activePane="bottomLeft" state="frozen"/>'
               '</sheetView></sheetViews><cols>']
        for i, w in enumerate(sh.get('widths') or [14] * len(sh['header'])):
            out.append('<col min="%d" max="%d" width="%s" customWidth="1"/>' % (i + 1, i + 1, w))
        out.append('</cols><sheetData>')
        for r, row in enumerate(rows):
            cells = []
            for c, v in enumerate(row):
                ref = '%s%d' % (xcol(c), r + 1)
                st = ' s="1"' if r == 0 else ''
                if isinstance(v, (int, float)) and not isinstance(v, bool) and r > 0:
                    cells.append('<c r="%s"%s><v>%s</v></c>' % (ref, st, v))
                else:
                    cells.append('<c r="%s"%s t="inlineStr"><is><t xml:space="preserve">%s</t></is></c>' % (ref, st, xesc(v)))
            out.append('<row r="%d">%s</row>' % (r + 1, ''.join(cells)))
        out.append('</sheetData>')
        if rows:
            out.append('<autoFilter ref="A1:%s%d"/>' % (xcol(len(sh['header']) - 1), len(rows)))
        out.append('</worksheet>')
        return ''.join(out)

    n = len(sheets)
    ct = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
          '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
          '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
          '<Default Extension="xml" ContentType="application/xml"/>'
          '<Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>'
          '<Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/>'
          + ''.join('<Override PartName="/xl/worksheets/sheet%d.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>' % (i + 1) for i in range(n))
          + '</Types>')
    rels = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
            '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
            '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/>'
            '</Relationships>')
    wb = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
          '<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
          'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"><sheets>'
          + ''.join('<sheet name="%s" sheetId="%d" r:id="rId%d"/>' % (xesc(sh['name'][:31]), i + 1, i + 1) for i, sh in enumerate(sheets))
          + '</sheets>'
          + ''.join('<definedNames>%s</definedNames>' % ''.join(
              '<definedName name="_xlnm._FilterDatabase" localSheetId="%d" hidden="1">\'%s\'!$A$1:$%s$%d</definedName>'
              % (i, xesc(sh['name'][:31]), xcol(len(sh['header']) - 1), len(sh['rows']) + 1) for i, sh in enumerate(sheets)) for _ in [0])
          + '</workbook>')
    wbrels = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
              '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
              + ''.join('<Relationship Id="rId%d" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet%d.xml"/>' % (i + 1, i + 1) for i in range(n))
              + '<Relationship Id="rId%d" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/>' % (n + 1)
              + '</Relationships>')
    styles = ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
              '<styleSheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
              '<fonts count="2"><font><sz val="11"/><name val="游ゴシック"/><family val="3"/><charset val="128"/></font>'
              '<font><b/><sz val="11"/><name val="游ゴシック"/><family val="3"/><charset val="128"/></font></fonts>'
              '<fills count="3"><fill><patternFill patternType="none"/></fill><fill><patternFill patternType="gray125"/></fill>'
              '<fill><patternFill patternType="solid"><fgColor rgb="FFDDEBF7"/><bgColor indexed="64"/></patternFill></fill></fills>'
              '<borders count="1"><border><left/><right/><top/><bottom/><diagonal/></border></borders>'
              '<cellStyleXfs count="1"><xf numFmtId="0" fontId="0" fillId="0" borderId="0"/></cellStyleXfs>'
              '<cellXfs count="2"><xf numFmtId="0" fontId="0" fillId="0" borderId="0" xfId="0"/>'
              '<xf numFmtId="0" fontId="1" fillId="2" borderId="0" xfId="0" applyFont="1" applyFill="1"/></cellXfs>'
              '<cellStyles count="1"><cellStyle name="標準" xfId="0" builtinId="0"/></cellStyles></styleSheet>')
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, 'w', zipfile.ZIP_DEFLATED) as z:
        z.writestr('[Content_Types].xml', ct)
        z.writestr('_rels/.rels', rels)
        z.writestr('xl/workbook.xml', wb)
        z.writestr('xl/_rels/workbook.xml.rels', wbrels)
        z.writestr('xl/styles.xml', styles)
        for i, sh in enumerate(sheets):
            z.writestr('xl/worksheets/sheet%d.xml' % (i + 1), sheet_xml(sh))
    return buf.getvalue()


# ---------------------------------------------------------------------------
#  道路交通センサス(令和3年度)との対応
#   DRMの「調査単位」(10桁) = 都道府県コードの一の位(1) + 道路種別(1) + 路線番号(4) + 区間番号(4)
#   センサスの交通調査基本区間番号(11桁) = 都道府県コード(2) + 道路種別(1) + 路線番号(4) + 区間番号(4)
#   ｾﾝｻｽ年度=15(平成27年度)のDRMは、箇所別基本表の「平成27年度/交通調査基本区間番号」でR3の区間に読み替える。
#   方向: 管起点N(路線の起点側の端)から入る = 起点→終点 = 下り、反対 = 上り
# ---------------------------------------------------------------------------
CENSUS = {'r3': {}, 'h27': {}}


def build_census(data_dir):
    """kasyo01～47.csv(箇所別基本表) → census_r3.json(区間番号→路線名、H27番号→R3番号)"""
    files = sorted(glob.glob(os.path.join(data_dir, '**', 'kasyo[0-9][0-9].csv'), recursive=True))
    if not files:
        return False
    r3, h27 = {}, {}
    for f in files:
        raw = open(f, 'rb').read()
        try:
            text = raw.decode('cp932')
        except UnicodeDecodeError:
            text = raw.decode('utf-8-sig')
        rows = csv.reader(io.StringIO(text))
        head = next(rows)
        ci = {name: i for i, name in reversed(list(enumerate(head)))}
        i_no, i_name, i_h27 = ci['交通調査基本区間番号'], ci['路線名'], ci['平成２７年度／交通調査基本区間番号']
        for r in rows:
            if len(r) > i_h27 and r[i_no].strip():
                k = r[i_no].strip().zfill(11)          # CSVでは都道府県01～09の先頭0が落ちている
                r3[k] = r[i_name].strip()
                if r[i_h27].strip():
                    h27.setdefault(r[i_h27].strip().zfill(11), k)
    tmp = CENSUS_FILE + '.%d.tmp' % os.getpid()
    with open(tmp, 'w', encoding='utf-8') as fo:
        json.dump({'r3': r3, 'h27': h27}, fo, ensure_ascii=False, separators=(',', ':'))
    os.replace(tmp, CENSUS_FILE)
    log('センサス対応表を作成: R3区間 %d / H27対応 %d (%d ファイル)' % (len(r3), len(h27), len(files)))
    return True


def load_census(data_dir):
    global CENSUS
    if not os.path.exists(CENSUS_FILE) and not build_census(data_dir):
        log('センサスの箇所別基本表(kasyo01～47.csv)が無いため、センサス項目は空欄になります')
        return
    with open(CENSUS_FILE, encoding='utf-8') as f:
        c = json.load(f)
    # 下10桁 → 候補の都道府県コード(調査単位からの検索用)
    for name in ('r3', 'h27'):
        idx = collections.defaultdict(list)
        for k in c[name]:
            idx[k[1:]].append(k[:2])
        c[name + '_idx'] = idx
    CENSUS = c
    log('センサス対応表 読込: R3区間 %d' % len(c['r3']))


def census_key(us, pref, table, idx):
    """調査単位(10桁文字列)とリンクの都道府県から、表にある11桁の区間番号を探す"""
    own = '%02d' % pref
    if own[1] == us[0] and own + us[1:] in table:
        return own + us[1:]
    cand = [c for c in idx.get(us[1:], ()) if c[1] == us[0]]   # 県境をまたぐ区間など
    return cand[0] + us[1:] if cand else None


def census_info(d, lid, fwd):
    """リンクのセンサス基本区間番号(R3)・路線名称・方向(上り/下り)。fwd: NODE1→NODE2 に進むか"""
    u = d.l_cen[lid] if hasattr(d, 'l_cen') else 0
    if not u or not CENSUS['r3']:
        return {'cen': '', 'cenName': '', 'cenDir': ''}
    us = '%010d' % u
    pref = d.l_gyo[lid] // 1000
    k = None
    if d.l_cyr[lid] == 15:     # 平成27年度の区間番号 → R3 に読み替え
        h = census_key(us, pref, CENSUS['h27'], CENSUS['h27_idx'])
        k = CENSUS['h27'].get(h) if h else None
    if k is None:
        k = census_key(us, pref, CENSUS['r3'], CENSUS['r3_idx'])
    kki = d.l_kki[lid]
    cdir = '' if not kki else ('下り' if kki == (1 if fwd else 2) else '上り')
    if k is None:
        return {'cen': '', 'cenName': '', 'cenDir': ''}
    return {'cen': k, 'cenName': CENSUS['r3'].get(k, ''), 'cenDir': cdir}


# ---------------------------------------------------------------------------
#  ID検索(検算用): リンクMatchCode / ノード番号 / センサス区間番号 → リンク・ノード
# ---------------------------------------------------------------------------
FIND_MAX_TOKENS = 500
FIND_LOCK = threading.Lock()
RE_FIND_LINK = re.compile(r'(\d{6})-?([0-9A-Z]{5})([0-9A-Z]{5})')
RE_FIND_NODE = re.compile(r'(\d{6})-([0-9A-Z]{1,5})')


def node_key_of(mesh, nd):
    """ノード番号 → ノードのキー。MatchCodeの中は5桁(先頭0埋め)、キーは0を除いた形(523657-06395 → 523657-6395)"""
    return '%s-%s' % (mesh, nd.lstrip('0') or '0')


def find_norm(q):
    """全角→半角・大文字にし、空白・カンマ・改行で区切る"""
    import unicodedata
    s = unicodedata.normalize('NFKC', q).upper()
    s = re.sub('[‐‑‒–—―−ｰー]', '-', s)
    return [t for t in re.split(r'[\s,、;]+', s) if t]


def _cen_index(d):
    """調査単位(下10桁) → リンク番号。最初のセンサス検索時に作る(1～2秒)"""
    with FIND_LOCK:
        idx = getattr(d, '_cen_idx', None)
        if idx is None:
            idx = collections.defaultdict(list)
            for i, u in enumerate(d.l_cen):
                if u:
                    idx[u].append(i)
            d._cen_idx = idx
        if 'h27_rev' not in CENSUS:
            rev = collections.defaultdict(list)
            for h, k in CENSUS.get('h27', {}).items():
                rev[k].append(h)
            CENSUS['h27_rev'] = rev
    return idx


def find_link_json(d, lid):
    """検索結果のリンク。cenDown: センサスの下り(起点→終点)に通る向き(正/逆)"""
    kki = d.l_kki[lid]
    return dict({'id': lid, 'mc': d.mc[lid], 'cls': d.l_cls[lid], 'cname': CLS_NAMES.get(d.l_cls[lid], ''),
                 'rname': d.route_name(lid), 'reg': d.l_reg[lid], 'len': round(d.l_len[lid]), 'hw': d.l_hw[lid],
                 'cenDown': '正' if kki == 1 else '逆' if kki == 2 else '',
                 'c': delta(d.link_coords(lid))}, **census_info(d, lid, True))


def find_mc(d, mc):
    """MATCHCODE → (リンク番号, 正/逆)。ノード番号の順が逆(中部方式)でも探す"""
    for code, fwd in ((mc, True), (reverse_mc(mc), False)):
        i = d.node_of(node_key_of(code[:-11], code[-10:-5]))
        if i is None:
            continue
        for e in range(d.adj_off[i], d.adj_off[i + 1]):
            if d.mc[d.adj_lid[e]] == code:
                return d.adj_lid[e], fwd
    for code, fwd in ((mc, True), (reverse_mc(mc), False)):   # 始終点が同じノードのリンク(隣接に入らない)
        try:
            return d.mc.index(code), fwd
        except ValueError:
            pass
    return None


def find_ids(d, q):
    out = []
    toks = find_norm(q)
    seen = set()
    for t in toks[:FIND_MAX_TOKENS]:
        if t in seen:
            continue
        seen.add(t)
        r = {'q': t}
        m = RE_FIND_LINK.fullmatch(t)
        if m:
            mc = '%s-%s%s' % m.groups()
            r['kind'] = 'link'
            hit = find_mc(d, mc)
            if hit:
                r['links'] = [find_link_json(d, hit[0])]
                if not hit[1]:
                    r['msg'] = 'ノード番号を逆に並べたMatchCode(中部方式)として見つかりました'
            out.append(r)
            continue
        m = RE_FIND_NODE.fullmatch(t)
        if m:
            key = node_key_of(*m.groups())
            r['kind'] = 'node'
            i = d.key_index.get(key)
            if i is not None:
                rep = d.node_rep[i]
                lids = sorted({d.adj_lid[e] for e in range(d.adj_off[rep], d.adj_off[rep + 1])})
                r['node'] = dict(d.node_json(rep), key=key)
                r['links'] = [find_link_json(d, l) for l in lids]
                if rep != i:
                    r['msg'] = 'メッシュ境界のノード(%s と同じ位置)' % d.node_key[rep]
            out.append(r)
            continue
        if re.fullmatch(r'\d{10,11}', t):
            # 11桁 = R3センサスの交通調査基本区間番号 / 10桁 = DRMの調査単位
            r['kind'] = 'census'
            idx = _cen_index(d)
            if len(t) == 11:
                cand = set(idx.get(int(t[1:]), ()))
                for h in CENSUS.get('h27_rev', {}).get(t, ()):   # 平成27年度の番号を持つ版
                    cand.update(idx.get(int(h[1:]), ()))
                lids = sorted(l for l in cand if census_info(d, l, True)['cen'] == t)
                r['cenName'] = CENSUS['r3'].get(t, '')
                if not r['cenName'] and not lids:
                    r['msg'] = 'R3センサスの箇所別基本表にない区間番号です'
            else:
                lids = sorted(idx.get(int(t), ()))
            r['links'] = [find_link_json(d, l) for l in lids[:3000]]
            if len(lids) > 3000:
                r['msg'] = 'リンクが多いため先頭3000本のみ表示'
            out.append(r)
            continue
        r['kind'] = 'unknown'
        r['msg'] = '形式がわかりません（リンク：533946-061230B622 / ノード：533946-6123 / センサス区間：11桁の数字）'
        out.append(r)
    return out, len(toks) > FIND_MAX_TOKENS


# ---------------------------------------------------------------------------
#  センサス区間の番号表示・区間から経路を作る
# ---------------------------------------------------------------------------
CEN_LABEL_MAX = 2000


def census_labels(d, w, s, e, n):
    """表示範囲にあるセンサス区間の番号ラベル [区間番号, 路線名, 緯度, 経度]。
    区間ごとに、範囲内にあるリンクのうち中央に最も近いリンクの中点に置く"""
    W, S, E, N = (round(v * SCALE) for v in (w, s, e, n))
    ids, _ = d.links_in(w, s, e, n, 9, 10 ** 7)
    memo, groups = {}, collections.defaultdict(list)
    for lid in ids:
        u = d.l_cen[lid]
        if not u:
            continue
        mk = (u, d.l_gyo[lid] // 1000, d.l_cyr[lid])
        if mk not in memo:
            memo[mk] = census_info(d, lid, True)['cen']
        code = memo[mk]
        if not code:
            continue
        pts = d.link_coords(lid)
        x, y = pts[len(pts) // 2] if len(pts) > 2 else ((pts[0][0] + pts[-1][0]) // 2, (pts[0][1] + pts[-1][1]) // 2)
        if W <= x <= E and S <= y <= N:
            groups[code].append((x, y))
    if len(groups) > CEN_LABEL_MAX:
        return [], True
    out = []
    for code, ps in groups.items():
        cx = sum(p[0] for p in ps) / len(ps)
        cy = sum(p[1] for p in ps) / len(ps)
        x, y = min(ps, key=lambda p: (p[0] - cx) ** 2 + (p[1] - cy) ** 2)
        out.append([code, CENSUS['r3'].get(code, ''), y / SCALE, x / SCALE])
    return out, False


def census_section_links(d, code):
    idx = _cen_index(d)
    cand = set(idx.get(int(code[1:]), ()))
    for h in CENSUS.get('h27_rev', {}).get(code, ()):   # 平成27年度の番号を持つ版
        cand.update(idx.get(int(h[1:]), ()))
    return [l for l in cand if census_info(d, l, True)['cen'] == code]


def census_section_route(d, code, cdir, oneway, types, mode):
    """センサス区間を cdir(上り/下り)に通る経路の経由地。
    区間のリンクをその向きに並べて最も長くつながる列を作り、始終点(ノード)で経路を引く。
    区間のリンクを通らない所があれば、そのリンクを経由地に足して引き直す。"""
    if not re.fullmatch(r'\d{11}', code or '') or cdir not in ('上り', '下り'):
        raise RouteError('センサス区間番号(11桁)と方向(上り/下り)を指定してください')
    lids = census_section_links(d, code)
    if not lids:
        raise RouteError('DRM%s にセンサス区間 %s のリンクがありません' % (d.ver, code))
    blk_fwd, blk_rev = ONEWAY_BLOCK.get(oneway, ONEWAY_BLOCK['all'])
    want = 1 if cdir == '下り' else 2           # 管起点Nから入る向き = 下り
    out, indeg = collections.defaultdict(list), collections.Counter()
    for l in lids:
        kki = d.l_kki[l]
        for fwd in (True, False):
            if kki and kki != (want if fwd else 3 - want):
                continue
            if d.l_reg[l] in (blk_fwd if fwd else blk_rev):
                continue                          # 反対車線(一方通行の逆向き)
            a, b = (d.l_n1[l], d.l_n2[l]) if fwd else (d.l_n2[l], d.l_n1[l])
            out[a].append((b, l))
            indeg[b] += 1
    if not out:
        raise RouteError('センサス区間 %s を%s方向に通れるリンクがありません' % (code, cdir))
    # 最も長くつながるリンク列(閉路は除いて、トポロジカル順に最長路)
    nodes = set(out) | set(indeg)
    deg = {v: indeg[v] for v in nodes}
    order = [v for v in nodes if not deg[v]]
    for v in order:
        for b, _ in out.get(v, ()):
            deg[b] -= 1
            if not deg[b]:
                order.append(b)
    if not order:
        raise RouteError('センサス区間 %s のリンクが環状のため、始終点を決められません' % code)
    dist, prev = {v: 0.0 for v in order}, {}
    for v in order:
        for b, l in out.get(v, ()):
            if b in dist and dist[v] + d.l_len[l] > dist[b]:
                dist[b], prev[b] = dist[v] + d.l_len[l], (v, l)
    end = max(order, key=lambda v: dist[v])
    chain, v = [], end
    while v in prev:
        v, l = prev[v]
        chain.append(l)
    chain.reverse()
    start = v
    keys = [d.node_key[start], d.node_key[end]]
    for _ in range(30):
        legs, wp_json = plan_route(d, keys, oneway, types, mode)
        got = {l for leg in legs for l, _ in leg}
        miss = [l for l in chain if l not in got]
        if not miss:
            break
        lk = 'L:%d:%s' % (miss[0], d.mc[miss[0]])
        pos = chain.index(miss[0])
        # 経由リンクは区間内の並び順の位置に入れる
        at = 1 + sum(1 for k in keys[1:-1] if chain.index(d.link_of(k)) < pos)
        keys.insert(at, lk)
    sec_len = sum(d.l_len[l] for l in chain)
    return {'v': d.ver, 'code': code, 'name': CENSUS['r3'].get(code, ''), 'dir': cdir, 'waypoints': wp_json,
            'links': len(chain), 'len': round(sec_len), 'missing': len(miss),
            'partial': len(chain) < len({l for _, ls in out.items() for _, l in ls})}


STORE = None
USAGE = None   # 利用状況の記録(usage.Usage)。起動時に作る


def usage(ev, **kw):
    if USAGE:
        try:
            USAGE.record(ev, **kw)
        except Exception as ex:
            log('利用ログの記録に失敗:', ex)

# ---------------------------------------------------------------------------
#  国交省トラカン(torakan.json は --update-torakan で作る)
# ---------------------------------------------------------------------------
TORAKAN_FILE = os.path.join(HERE, 'torakan.json')
TORAKAN = {'mtime': None, 'data': None}


def torakan_data():
    """torakan.json を読む(更新されていたら読み直す)。無ければ None"""
    try:
        mt = os.path.getmtime(TORAKAN_FILE)
    except OSError:
        return None
    if TORAKAN['mtime'] != mt:
        with open(TORAKAN_FILE, encoding='utf-8') as f:
            d = json.load(f)
        d['byId'] = {s['id']: s for s in d['sites']}
        TORAKAN.update(mtime=mt, data=d)
    return TORAKAN['data']


JARTIC_FILE = os.path.join(HERE, 'jartic.json')
JARTIC = {'mtime': None, 'data': None}


def jartic_data():
    """jartic.json(--update-jartic で作る)を読む。更新されていたら読み直す。無ければ None"""
    try:
        mt = os.path.getmtime(JARTIC_FILE)
    except OSError:
        return None
    if JARTIC['mtime'] != mt:
        with open(JARTIC_FILE, encoding='utf-8') as f:
            d = json.load(f)
        d['byId'] = {p['id']: p for p in d['points']}
        grid = collections.defaultdict(list)          # 0.05度セル → 地点
        for p in d['points']:
            grid[(int(p['lon'] // 0.05), int(p['lat'] // 0.05))].append(p)
        d['grid'] = grid
        JARTIC.update(mtime=mt, data=d)
    return JARTIC['data']


# ---------------------------------------------------------------------------
#  経路の計算(経由地つき)と、逆方向の経路づくり
# ---------------------------------------------------------------------------
class RouteError(Exception):
    pass


def link_ends(d, lid, fwd):
    """リンクを fwd(True=NODE1→NODE2)の向きに通るときの (入るノード, 出るノード)"""
    return (d.l_n1[lid], d.l_n2[lid]) if fwd else (d.l_n2[lid], d.l_n1[lid])


def walk(d, start, lids):
    """始点ノードからリンク列をたどり [(リンク, 向き)] にする"""
    out, cur = [], start
    for lid in lids:
        fwd = d.l_n1[lid] == cur
        out.append((lid, fwd))
        cur = d.l_n2[lid] if fwd else d.l_n1[lid]
    return out


def plan_route(d, keys, oneway, types, mode):
    """経由地(ノード key または 経由リンク 'L:番号:MATCHCODE')を順に通る経路。
    戻り値: (区間ごとの [(リンク, 向き)], 地点情報)"""
    blk_fwd, blk_rev = ONEWAY_BLOCK.get(oneway, ONEWAY_BLOCK['all'])
    LC = d.l_time if mode == 'time' else d.l_len
    # 各地点の通り方の候補 (入るノード, 出るノード, 経由リンク or None)
    #   ノード: 1通り / 経由リンク: 通れる向きごと(一方通行なら1通り)
    states, wp_json = [], []
    for k in keys:
        if k.startswith('L:'):
            lid = d.link_of(k)
            if lid is None:
                raise RouteError('DRM%s に経由リンクが見つかりません(%s)。経由地を置き直してください' % (d.ver, k.split(':', 2)[-1]))
            a, b = d.l_n1[lid], d.l_n2[lid]
            st = ([(a, b, lid)] if d.l_reg[lid] not in blk_fwd else []) + ([(b, a, lid)] if d.l_reg[lid] not in blk_rev else [])
            if not st:
                raise RouteError('経由リンク %s はどちら向きにも通れません(交通規制)' % d.mc[lid])
            states.append(st)
            wp_json.append(d.link_wp_json(lid))
        else:
            if k[:3] in ('N1:', 'N2:'):   # 'N1:リンク番号:MATCHCODE' = そのリンクのノード1/2(リンク上の距離の起点)
                lid = d.link_of('L' + k[2:])
                n = None if lid is None else d.l_n1[lid] if k[1] == '1' else d.l_n2[lid]
            else:
                n = d.node_of(k)
            if n is None:
                raise RouteError('DRM%s にノードが見つかりません(%s)' % (d.ver, k.split(':', 2)[-1]))
            states.append([(n, n, None)])
            wp_json.append(d.node_json(n))
    memo = {}

    def sp(a, b):
        if (a, b) not in memo:
            p = d.shortest(a, b, oneway, types, mode)
            memo[(a, b)] = (p, sum(LC[x] for x in p)) if p is not None else (None, None)
        return memo[(a, b)]
    # 経由リンクの向きの組み合わせのうち、全体が最短になるものを選ぶ(動的計画法)
    best = [{j: ((LC[s[2]] if s[2] is not None else 0.0), None) for j, s in enumerate(states[0])}] if states else []
    for i in range(1, len(states)):
        cur_best = {}
        for j, s in enumerate(states[i]):
            for pj, (pc, _) in best[i - 1].items():
                p, c = sp(states[i - 1][pj][1], s[0])
                if p is None:
                    continue
                tot = pc + c + (LC[s[2]] if s[2] is not None else 0.0)
                if j not in cur_best or tot < cur_best[j][0]:
                    cur_best[j] = (tot, pj)
        if not cur_best:
            a, b = states[i - 1][0][1], states[i][0][0]
            msg = '経路が見つかりません(%s → %s)' % (keys[i - 1].split(':', 2)[-1], keys[i].split(':', 2)[-1])
            if types is not None and d.shortest(a, b, oneway) is not None:
                msg += '。選択した道路種別だけでは到達できません。道路種別のチェックを見直してください'
            elif oneway != 'off' and d.shortest(a, b, 'off', types) is not None:
                msg += '。一方通行を逆走しないと到達できません。始終点・経由地を見直してください'
            raise RouteError(msg)
        best.append(cur_best)
    chosen = []
    if states:
        j = min(best[-1], key=lambda x: best[-1][x][0])
        for i in range(len(states) - 1, -1, -1):
            chosen.append(states[i][j])
            j = best[i][j][1]
        chosen.reverse()
    legs = []
    for i in range(len(chosen) - 1):
        s, t = chosen[i], chosen[i + 1]
        seq = ([s[2]] if s[2] is not None else []) + sp(s[1], t[0])[0]
        if i == len(chosen) - 2 and t[2] is not None:
            seq.append(t[2])          # 終点が経由リンクのときは最後の区間に含める
        legs.append(walk(d, s[0], seq))
    return legs, wp_json


def legs_json(d, legs):
    ng_fwd, ng_rev = ONEWAY_BLOCK['all']
    out = []
    for leg in legs:
        links = []
        for lid, fwd in leg:
            reg = d.l_reg[lid]
            links.append({'id': lid, 'mc': d.mc[lid], 'dir': '正' if fwd else '逆',
                          'len': round(d.l_len[lid]), 'len1': round(d.l_len[lid], 1), 'cls': d.l_cls[lid], 'reg': reg,
                          'cname': CLS_NAMES.get(d.l_cls[lid], ''), 'rname': d.route_name(lid),
                          'hw': d.l_hw[lid],
                          'kmh': d.l_kmh[lid], 'kmhSrc': d.l_kmh_src[lid], 'sec': round(d.l_time[lid], 1),
                          **census_info(d, lid, fwd),
                          'mc2': d.mc[lid] if fwd else reverse_mc(d.mc[lid]),  # 中部方式: 上流→下流のノード順
                          'wrong': reg in (ng_fwd if fwd else ng_rev),  # 規制に反する向き(条件付含む)
                          'c': delta(d.link_coords(lid, reverse=not fwd))})
        out.append(links)
    return out


REV_BUF_M = 60        # 反対車線を探す範囲(往路の線からの距離)。一般道
REV_BUF_HW_M = 200    # 同・自専道/高速(上下線が離れていることがある)
REV_ROAD_K = 3        # 往路と同じ種別・路線番号の道路はこの倍まで離れていてよい(IC・JCT付近で上下線が大きく離れる)


def _corridor(d, run):
    """往路で逆向きに通れない区間(上下線分離など)の、反対車線を探してよいリンクの集合。
    ①往路と同じセンサス調査単位のリンク(上下線で共通) ②センサス区間の無いリンクは、同じ種別・路線番号で往路の線から近いもの"""
    lids = [l for l, _ in run]
    cens = {d.l_cen[l] for l in lids if d.l_cen[l]}
    crn = {(d.l_cls[l], d.l_rno[l]) for l in lids}
    buf = REV_BUF_HW_M if any(d.l_hw[l] for l in lids) else REV_BUF_M
    rbuf = buf * REV_ROAD_K
    pts = [p for l in lids for p in d.link_coords(l)]
    lat0 = pts[0][1] / SCALE
    kx = math.cos(math.radians(lat0)) * 111320 / SCALE
    ky = 111320 / SCALE
    bx, by = rbuf / kx, rbuf / ky
    segs = list(zip(pts, pts[1:])) or [(pts[0], pts[0])]
    # 往路の線分を rbuf(m) 四方のマス目に登録し、距離は近くのマスの線分とだけ測る
    # (長い経路で全線分と総当たりすると数分かかるため)
    G = float(rbuf)
    sgrid = collections.defaultdict(list)
    cells = set()                        # 往路の線から rbuf 以内にかかるリンク索引のマス
    c = LINK_CELL * SCALE
    for sg in segs:
        (ax, ay), (bx_, by_) = sg
        for gx in range(int(min(ax, bx_) * kx // G), int(max(ax, bx_) * kx // G) + 1):
            for gy in range(int(min(ay, by_) * ky // G), int(max(ay, by_) * ky // G) + 1):
                sgrid[(gx, gy)].append(sg)
        for cx in range(int((min(ax, bx_) - bx) // c), int((max(ax, bx_) + bx) // c) + 1):
            for cy in range(int((min(ay, by_) - by) // c), int((max(ay, by_) + by) // c) + 1):
                cells.add((cx, cy))

    def dist(q):
        """往路の線までの距離(m)。rbuf より遠いときは inf"""
        best = None
        gx, gy = int(q[0] * kx // G), int(q[1] * ky // G)
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for (ax, ay), (bx_, by_) in sgrid.get((gx + dx, gy + dy), ()):
                    ax_, ay_ = (ax - q[0]) * kx, (ay - q[1]) * ky
                    vx, vy = (bx_ - ax) * kx, (by_ - ay) * ky
                    L2 = vx * vx + vy * vy
                    t = 0.0 if L2 == 0 else max(0.0, min(1.0, -(ax_ * vx + ay_ * vy) / L2))
                    dd = (ax_ + t * vx) ** 2 + (ay_ + t * vy) ** 2
                    if best is None or dd < best:
                        best = dd
        return math.inf if best is None else math.sqrt(best)

    allow, loose, seen = set(), set(), set()
    for cell in cells:
        for l in d.link_grid.get(cell, ()):
            if l in seen:
                continue
            seen.add(l)
            if cens and d.l_cen[l] in cens:
                allow.add(l)
                continue
            s = d.link_coords(l)
            road = (d.l_cls[l], d.l_rno[l]) in crn
            lim = rbuf if road else buf
            m = 0.0
            for q in (s[0], s[len(s) // 2], s[-1]):
                m = max(m, dist(q))
                if m > lim:
                    break
            if m <= buf:
                loose.add(l)        # 往路の線の近く(道路の種類は問わない): ランプ・交差点内など
            if road and m <= rbuf:
                allow.add(l)
    return allow, allow | loose, buf


def _opposite_nodes(d, node, links, run, at_start, can, buf, limit=6):
    """始終点を反対車線側にずらすときの候補ノード。
    links のうち、往路を逆にたどる向き(run の端の進行方向)とおおむね同じ向きに通れるリンクの
    入口(at_start)/出口ノードで、①node から buf 以内のもの(近い順に limit 個)
    ②往路のこの端に最も近いセンサス区間と同じ区間のもの(近い順に limit 個。上下線で区間番号が共通なので、反対車線の同じ区間を起終点にできる)。
    往路側の車線のノードは向きが逆なので入らない"""
    kx = math.cos(math.radians(d.node_lat[node] / SCALE)) * 111320 / SCALE
    ky = 111320 / SCALE

    def vec(a, b):
        return (d.node_lon[b] - d.node_lon[a]) * kx, (d.node_lat[b] - d.node_lat[a]) * ky
    side = run[:3] if at_start else run[-3:]
    rx, ry = vec(link_ends(d, *side[0])[0], link_ends(d, *side[-1])[1])
    rl = math.hypot(rx, ry)
    on_run = {l for l, _ in run}
    cen = next((d.l_cen[l] for l, _ in (run if at_start else run[::-1]) if d.l_cen[l]), 0)
    near, same = {node: 0.0}, {}
    for l in links:
        if l in on_run:
            continue
        for g in (True, False):
            if not can(l, g):
                continue
            a, b = link_ends(d, l, g)
            vx, vy = vec(a, b)
            vl = math.hypot(vx, vy)
            if rl and vl and (vx * rx + vy * ry) / (vl * rl) < 0.5:
                continue
            n = a if at_start else b
            dist = math.hypot(*vec(node, n))
            if dist <= buf and dist < near.get(n, 1e18):
                near[n] = dist
            if cen and d.l_cen[l] == cen and dist < same.get(n, 1e18):
                same[n] = dist
    out = sorted(near, key=near.get)[:limit]
    return out + [x for x in sorted(same, key=same.get)[:limit] if x not in out]


def make_reverse(d, fwd_links, oneway, types, mode):
    """往路 [(リンク, 向き)] の逆方向の経路。
    双方向に通れるリンクは同じリンクを逆向きに通り、逆向きに通れない区間(上下線分離・ランプ等)だけ反対車線を探し直す。
    戻り値: (区間, 地点情報, 注記) … 経由地は始終点と、通常の経路探索で同じ経路になるよう自動で置いた経由リンク"""
    blk_f, blk_r = ONEWAY_BLOCK.get(oneway, ONEWAY_BLOCK['all'])
    can = lambda lid, f: d.l_reg[lid] not in (blk_f if f else blk_r)
    rev = [(l, not f) for l, f in reversed(fwd_links)]
    notes = []

    def note(kind, msg, lid):
        s = d.link_coords(lid)
        m = s[len(s) // 2]
        notes.append({'kind': kind, 'msg': msg, 'lat': m[1] / SCALE, 'lon': m[0] / SCALE})

    seq, i, n = [], 0, len(rev)
    start = link_ends(d, *rev[0])[0]
    cur = start
    while i < n:
        lid, f = rev[i]
        if can(lid, f):
            seq.append((lid, f))
            cur = link_ends(d, lid, f)[1]
            i += 1
            continue
        j = i
        while j + 1 < n and not can(*rev[j + 1]):
            j += 1
        run = rev[i:j + 1]
        T = link_ends(d, *run[-1])[1]
        allow, loose, buf = _corridor(d, run)
        # 始終点が分離区間内(高速など) → 反対車線側の、逆向きに通れるリンクの端へずらす
        srcs = _opposite_nodes(d, cur, loose, run, True, can, buf * REV_ROAD_K) if i == 0 else [cur]
        dsts = _opposite_nodes(d, T, loose, run, False, can, buf * REV_ROAD_K) if j == n - 1 else [T]
        run_cen = {d.l_cen[l] for l, _ in run if d.l_cen[l]}
        run_len = sum(d.l_len[l] for l, _ in run)

        def score(p):
            """往路と同じセンサス区間を過不足なく通り、延長が近いものほど良い"""
            pc = {d.l_cen[l] for l in p if d.l_cen[l]}
            return len(run_cen - pc), len(pc - run_cen), abs(sum(d.l_len[l] for l in p) - run_len)
        found = None
        # ①同じセンサス区間・同じ路線 → ②往路の近くの道路(種類問わず) → ③制限なし の順に探す
        for tier, lim in enumerate((allow, loose, None)):
            best = None
            for a in srcs:
                for b in dsts:
                    p = d.shortest(a, b, oneway, types, mode, lim)
                    if p:
                        sc = score(p)
                        if best is None or sc < best[0]:
                            best = (sc, (a, b, p))
                if tier == 2 and best:
                    break           # 制限なしは時間がかかるので最初に見つかった始点で打ち切る
            if best:
                found = best[1]
                if tier == 2:
                    note('warn', '往路の近くに反対方向の道路が見つからず、通常の最短経路で代用しました（%s 付近）' % d.route_name(run[0][0]), run[0][0])
                break
        if not found:
            raise RouteError('逆方向の経路が見つかりません（%s 付近）。一方通行を逆走しないと通れない可能性があります' % d.mc[run[0][0]])
        a, b, p = found
        if i == 0 and a != start:
            start = a
            note('info', '始点を反対車線側のノード %s にずらしました' % d.node_key[a], p[0])
        if j == n - 1 and b != T:
            note('info', '終点を反対車線側のノード %s にずらしました' % d.node_key[b], p[-1])
        seq += walk(d, a, p)
        cur = b
        i = j + 1
    end = cur
    # 同じリンクを行って戻るだけの所(分離区間のつなぎ目で起きる)は省く
    out = []
    for x in seq:
        if out and out[-1][0] == x[0] and out[-1][1] != x[1]:
            out.pop()
        else:
            out.append(x)
    seq = out

    # 通常の経路探索で同じ経路になるよう、ずれる箇所に経由リンクを置く
    vias = set()                         # 経由リンクにする seq の位置
    pos, c = 0, start
    for _ in range(200):
        if pos >= len(seq):
            break
        p = d.shortest(c, end, oneway, types, mode)
        rest = [l for l, _ in seq[pos:]]
        if p == rest:
            break
        m = 0
        while p is not None and m < len(p) and m < len(rest) and p[m] == rest[m]:
            m += 1
        if m >= len(rest):
            break
        vias.add(pos + m)
        c = link_ends(d, *seq[pos + m])[1]
        pos += m + 1
    # 実際に経路探索して食い違う所があれば、そこにも経由リンクを足す(同じ所要時間の別経路・経由リンクの向きの選び方の違い等)
    for _ in range(20):
        keys = [d.node_key[start]] + ['L:%d:%s' % (seq[k][0], d.mc[seq[k][0]]) for k in sorted(vias)] + [d.node_key[end]]
        legs, wp_json = plan_route(d, keys, oneway, types, mode)
        got = [x for leg in legs for x in leg]
        if got == seq:
            break
        m = next((k for k, (x, y) in enumerate(zip(got, seq)) if x != y), min(len(got), len(seq)))
        m = min(m, len(seq) - 1)
        if m in vias:
            m = next((k for k in range(m - 1, -1, -1) if k not in vias), None)
            if m is None:
                break
        vias.add(m)
    if got != seq:
        notes.append({'kind': 'warn', 'msg': '自動で置いた経由地では逆方向の経路を完全には再現できませんでした。地図で確認してください'})

    # 往路とセンサス区間の並びを比べる(同じ区間を逆順に通っているか)
    def cen_seq(links):
        out = []
        for lid, f in links:
            ci = census_info(d, lid, f)['cen']
            if ci and (not out or out[-1][0] != ci):
                out.append((ci, lid))
        return out
    fs, rs = cen_seq(fwd_links), cen_seq(got)
    fset, rset = {x for x, _ in fs}, {x for x, _ in rs}
    for ci, lid in fs:
        if ci not in rset:
            note('warn', '往路のセンサス区間 %s を逆方向では通っていません' % ci, lid)
    for ci, lid in rs:
        if ci not in fset:
            note('warn', '逆方向だけが通るセンサス区間 %s があります' % ci, lid)
    if fs and [x for x, _ in fs][::-1] == [x for x, _ in rs]:
        notes.insert(0, {'kind': 'ok', 'msg': '往路とセンサス区間の並びが一致しています（%d 区間を逆順に通過）' % len(fs)})
    return legs, wp_json, notes


class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *a, **kw):
        super().__init__(*a, directory=HERE, **kw)

    def log_message(self, fmt, *args):
        pass

    def end_headers(self):
        # 画面(index.html等)はブラウザに毎回確認させる。無いとツール更新後も古い画面が出ることがある
        if not self.path.startswith('/api/'):
            self.send_header('Cache-Control', 'no-cache')
        super().end_headers()

    def send_json(self, obj, code=200):
        body = json.dumps(obj, ensure_ascii=False, separators=(',', ':')).encode('utf-8')
        self.send_response(code)
        self.send_header('Content-Type', 'application/json; charset=utf-8')
        self.send_header('Content-Length', str(len(body)))
        self.send_header('Cache-Control', 'no-store')
        self.end_headers()
        self.wfile.write(body)

    def status_json(self, v):
        v = v if STORE and v in STORE.sources else (STORE.default if STORE else None)
        st = dict(STORE.state[v]) if STORE else {'stage': 'Python起動', 'pct': 0, 'ready': False, 'error': None}
        return dict(st, v=v, build=BUILD, label=STORE.labels.get(v, '') if STORE else '')

    def drm(self, v):
        """版のデータ。未読込なら読込を始めて 503(読込中)を返す"""
        d = STORE.get(v)
        if d is None:
            self.send_json(dict(self.status_json(v), error='DRM%s を読込中です' % v, loading=True), 503)
        return d

    def do_GET(self):
        u = urlparse(self.path)
        if not u.path.startswith('/api/'):
            if u.path.startswith('/_'):   # _cache・_利用ログ などは出さない
                return self.send_error(404)
            return super().do_GET()
        q = {k: v[0] for k, v in parse_qs(u.query).items()}
        v = q.get('v') or (STORE.default if STORE else None)
        if u.path == '/api/status':
            return self.send_json(self.status_json(v))
        if u.path == '/api/usage/me':
            # 初回起動時のアンケートが必要か(profile が null なら未回答)
            if not USAGE:
                return self.send_json({'enabled': False})
            return self.send_json({'enabled': True, 'uid': USAGE.uid, 'pc': USAGE.pc, 'profile': USAGE.profile(),
                                   'branches': usage_log.BRANCHES, 'roles': usage_log.ROLES})
        if u.path in ('/api/usage/summary', '/api/usage/raw'):
            if not USAGE:
                return self.send_json({'error': '利用状況の記録が無効です'}, 400)
            d0, d1 = q.get('from') or None, q.get('to') or None
            if u.path == '/api/usage/raw':
                return self.send_json({'rows': USAGE.raw(d0, d1)})
            return self.send_json(USAGE.summary(d0, d1))
        if u.path == '/api/versions':
            return self.send_json({'default': STORE.default, 'versions': STORE.versions(), 'build': BUILD})
        if u.path == '/api/load':
            STORE.get(v)
            return self.send_json(self.status_json(v))
        if u.path == '/api/torakan':
            # 地図表示用の一覧(位置・誤差率のみ)
            t = torakan_data()
            if not t:
                return self.send_json({'sites': [], 'error': 'トラカンのデータがありません'})
            return self.send_json({k: t[k] for k in ('source', 'generated', 'period', 'weekdays', 'drmVer')} | {'sites': [
                [s['id'], s['kind'], s['lat'], s['lon'], s.get('err'),
                 (s['dirs'].get('上り') or {}).get('err'), (s['dirs'].get('下り') or {}).get('err'), 1 if s.get('census') else 0]
                for s in t['sites']]})
        if u.path == '/api/jartic':
            # 表示範囲内の地点(位置・向き・誤差率のみ)
            t = jartic_data()
            if not t:
                return self.send_json({'points': [], 'error': 'JARTICのデータがありません'})
            meta = {k: t[k] for k in ('source', 'generated', 'month', 'period', 'weekdays')}
            meta['total'] = len(t['points'])
            if 'w' not in q:
                return self.send_json(dict(meta, points=[]))
            w, s, e, n = (float(q[k]) for k in ('w', 's', 'e', 'n'))
            pts = []
            for cx in range(int(w // 0.05), int(e // 0.05) + 1):
                for cy in range(int(s // 0.05), int(n // 0.05) + 1):
                    for p in t['grid'].get((cx, cy), ()):
                        if w <= p['lon'] <= e and s <= p['lat'] <= n:
                            pts.append([p['id'], p['lat'], p['lon'], p['bearing'], p.get('err'), 1 if p.get('census') else 0, p.get('dir', '')])
            return self.send_json(dict(meta, points=pts[:20000], truncated=len(pts) > 20000))
        if u.path == '/api/jartic/point':
            t = jartic_data()
            p = t and t['byId'].get(q.get('id', ''))
            usage('tk_view', src='jartic', id=q.get('id', ''))
            return self.send_json(dict(p, month=t['month'], period=t['period'], weekdays=t['weekdays'], source=t['source']) if p else {'error': 'not found'})
        if u.path == '/api/torakan/site':
            t = torakan_data()
            s = t and t['byId'].get(q.get('id', ''))
            usage('tk_view', src='mlit', id=q.get('id', ''))
            return self.send_json(dict(s, period=t['period'], weekdays=t['weekdays'], source=t['source']) if s else {'error': 'not found'})
        if u.path == '/api/torakan/range':
            # ダウンロード画面用: アーカイブ済み(保存済み)の生データの日付範囲
            r = torakan.available_range(os.path.join(STORE.data_dir, torakan.ARCHIVE_DIR_NAME))
            return self.send_json({'min': r[0], 'max': r[1]} if r else {'min': None, 'max': None})
        if u.path == '/api/jartic/range':
            # ダウンロード画面用: 社内SQL Serverにある断面交通量の表の範囲(多少時間がかかる)
            try:
                r = jartic.available_range(log)
            except Exception as ex:
                return self.send_json({'error': str(ex)})
            return self.send_json({'min': r[0].isoformat(), 'max': r[1].isoformat()} if r else {'min': None, 'max': None})
        d = self.drm(v)
        if d is None:
            return
        try:
            if u.path == '/api/info':
                return self.send_json({'v': d.ver, 'bbox': d.bbox, 'links': len(d.mc), 'nodes': len(d.node_key), 'build': BUILD})
            if u.path == '/api/links':
                w, s, e, n = (float(q[k]) for k in ('w', 's', 'e', 'n'))
                ids, trunc = d.links_in(w, s, e, n, int(q.get('cls', 9)), int(q.get('limit', 100000)))
                tol = round(float(q.get('tol', 0)) * SCALE)   # 広域表示時は形状点を間引く(度)
                return self.send_json({'v': d.ver, 'truncated': trunc, 'links': [
                    [i, d.mc[i], d.l_cls[i], d.l_rno[i], delta(thin(d.link_coords(i), tol)), d.l_reg[i], round(d.l_len[i], 1)]
                    for i in ids]})
            if u.path == '/api/nodes':
                w, s, e, n = (float(q[k]) for k in ('w', 's', 'e', 'n'))
                return self.send_json([[d.node_key[i], d.node_lon[i] / SCALE, d.node_lat[i] / SCALE]
                                       for i in d.nodes_in(w, s, e, n, 20000, parse_types(q.get('types')))])
            if u.path == '/api/nearest':
                i = d.nearest_node(float(q['lon']), float(q['lat']), parse_types(q.get('types')))
                return self.send_json(d.node_json(i) if i is not None else None)
            if u.path == '/api/nearestlink':
                # 経由地の候補: 最寄りノードと最寄りリンクの両方(どちらにするかは画面側が距離で決める)
                lon, lat, types = float(q['lon']), float(q['lat']), parse_types(q.get('types'))
                i = d.nearest_node(lon, lat, types)
                nl = d.nearest_link(lon, lat, types)
                return self.send_json({'node': d.node_json(i) if i is not None else None,
                                       'link': dict(d.link_wp_json(nl[0], nl[2]), dist=round(nl[1], 1),
                                                    c=delta(d.link_coords(nl[0]))) if nl else None})
            if u.path == '/api/linkinfo':
                # リンクをクリックした時の情報(両端のノード番号・路線・センサス区間)
                lid = d.link_of('L:%s:%s' % (q.get('id', ''), q.get('mc', '')))
                if lid is None:
                    return self.send_json({'error': 'DRM%s にリンクが見つかりません' % d.ver}, 400)
                c = census_info(d, lid, True)
                return self.send_json({'mc': d.mc[lid], 'n1': d.node_key[d.l_n1[lid]], 'n2': d.node_key[d.l_n2[lid]],
                                       'len': round(d.l_len[lid], 1), 'cname': CLS_NAMES.get(d.l_cls[lid], ''),
                                       'rname': d.route_name(lid), 'reg': d.l_reg[lid], 'cen': c['cen'], 'cenName': c['cenName']})
            if u.path == '/api/find':
                items, trunc = find_ids(d, q.get('q', ''))
                if not q.get('nolog'):   # 画面側の補助的な検索(センサス区間の強調など)は数えない
                    usage('find', v=d.ver, n=len(items), hit=sum(1 for r in items if r.get('links') or r.get('node')),
                          kinds=','.join(sorted({r['kind'] for r in items})), q=q.get('q', '')[:200])
                return self.send_json({'v': d.ver, 'items': items, 'truncated': trunc})
            if u.path == '/api/census':
                # 地図に出すセンサス区間番号のラベル
                w, s, e, n = (float(q[k]) for k in ('w', 's', 'e', 'n'))
                labels, trunc = census_labels(d, w, s, e, n)
                return self.send_json({'v': d.ver, 'labels': labels, 'truncated': trunc})
        except Exception as ex:
            return self.send_json({'error': str(ex)}, 400)
        self.send_error(404)

    def do_POST(self):
        u = urlparse(self.path)
        body = self.rfile.read(int(self.headers.get('Content-Length') or 0))
        if u.path == '/api/shutdown':
            self.send_json({'ok': True})
            threading.Thread(target=self.server.shutdown, daemon=True).start()
            return
        if u.path == '/api/usage/profile':
            # 初回起動時のアンケートの回答(支社・役職)。回答済みなら上書きしない
            if not USAGE:
                return self.send_json({'error': '利用状況の記録が無効です'}, 400)
            req = json.loads(body or b'{}')
            try:
                p = USAGE.save_profile(req.get('branch'), req.get('role'))
            except ValueError as ex:
                return self.send_json({'error': str(ex)}, 400)
            except OSError as ex:
                return self.send_json({'error': '保存できませんでした: %s' % ex}, 400)
            return self.send_json({'profile': p})
        if u.path == '/api/usage/log':
            # 画面側でしか分からない操作(画面を開いた・Excelを保存した)
            req = json.loads(body or b'{}')
            ev = req.pop('e', '')
            if ev in usage_log.CLIENT_EVENTS:
                usage(ev, **{k: v for k, v in req.items() if isinstance(v, (int, float, str)) and len(str(v)) <= 200})
            return self.send_json({'ok': True})
        if u.path == '/api/xlsx':
            data = make_xlsx(json.loads(body)['sheets'])
            self.send_response(200)
            self.send_header('Content-Type', 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet')
            self.send_header('Content-Length', str(len(data)))
            self.end_headers()
            self.wfile.write(data)
            return
        if u.path in ('/api/torakan/avail', '/api/jartic/avail'):
            # ダウンロード画面用: 選んだ地点ごとのデータがある期間
            ids = json.loads(body or b'{}').get('ids') or []
            if u.path == '/api/torakan/avail':
                t = torakan_data()
                if not t:
                    return self.send_json({'items': {}})
                items = torakan.availability(t['byId'], ids, os.path.join(STORE.data_dir, torakan.ARCHIVE_DIR_NAME), log)
                for i, a in items.items():
                    s = t['byId'][i]
                    a['name'] = '%s %s%s' % (s['kind'], s['code'], ' ' + s['cenName'] if s.get('cenName') else '')
                return self.send_json({'items': items})
            t = jartic_data()
            if not t:
                return self.send_json({'items': {}})
            cache_dir = STORE.shared_cache or STORE.local_cache
            try:
                items = jartic.availability(t['byId'], ids, os.path.join(cache_dir, 'jartic_avail2.json'), log)
            except Exception as ex:
                return self.send_json({'error': 'SQL Serverへの問い合わせに失敗しました: %s' % ex}, 400)
            for i, a in items.items():
                a['name'] = t['byId'][i]['name']
            return self.send_json({'items': items})
        if u.path in ('/api/torakan/export', '/api/jartic/export'):
            req = json.loads(body or b'{}')
            ids = req.get('ids') or []
            try:
                d0 = datetime.date.fromisoformat(req.get('from', ''))
                d1 = datetime.date.fromisoformat(req.get('to', ''))
            except ValueError:
                return self.send_json({'error': '期間の指定が不正です'}, 400)
            if d0 > d1:
                return self.send_json({'error': '開始日が終了日より後です'}, 400)
            if not ids:
                return self.send_json({'error': 'トラカンが選ばれていません'}, 400)
            if u.path == '/api/torakan/export':
                t = torakan_data()
                if not t:
                    return self.send_json({'error': 'トラカン(国交省)のデータがありません'}, 400)
                arch = os.path.join(STORE.data_dir, torakan.ARCHIVE_DIR_NAME)
                rows = torakan.export(t['byId'], ids, d0, d1, arch, log)
            else:
                t = jartic_data()
                if not t:
                    return self.send_json({'error': 'トラカン(JARTIC)のデータがありません'}, 400)
                try:
                    rows = jartic.export_range(t['byId'], ids, d0, d1, log)
                except Exception as ex:
                    return self.send_json({'error': 'SQL Serverからの取得に失敗しました: %s' % ex}, 400)
            return self.send_json({'rows': rows})
        if u.path == '/api/route':
            req = json.loads(body or b'{}')
            d = self.drm(req.get('v') or STORE.default)
            if d is None:
                return
            oneway = req.get('oneway', 'all')
            mode = 'dist' if req.get('mode') == 'dist' else 'time'
            types = parse_types(req.get('types'))
            if types is not None and not types:
                return self.send_json({'error': '道路種別が1つも選ばれていません'}, 400)
            wps = req.get('waypoints', [])
            ev = dict(v=d.ver, wp=len(wps), via_link=sum(1 for k in wps if str(k).startswith('L:')), mode=mode,
                      oneway=oneway, auto=1 if req.get('auto') else None)
            ename = 'dist' if req.get('dist') else 'route'   # リンク上の距離の計測は経路検索の回数に数えない
            try:
                legs, wp_json = plan_route(d, wps, oneway, types, mode)
            except RouteError as ex:
                usage(ename, ok=0, **ev)
                return self.send_json({'error': str(ex)}, 400)
            usage(ename, ok=1, links=sum(len(l) for l in legs), **ev)
            return self.send_json({'v': d.ver, 'legs': legs_json(d, legs), 'nodes': wp_json})
        if u.path == '/api/census/route':
            # センサス区間を上り/下りに通る経路の経由地(画面側はこれで経路を作って通常どおり引く)
            req = json.loads(body or b'{}')
            d = self.drm(req.get('v') or STORE.default)
            if d is None:
                return
            mode = 'dist' if req.get('mode') == 'dist' else 'time'
            try:
                r = census_section_route(d, str(req.get('code', '')), req.get('dir'), req.get('oneway', 'all'),
                                         parse_types(req.get('types')), mode)
            except RouteError as ex:
                usage('census_route', v=d.ver, ok=0, code=str(req.get('code', ''))[:11])
                return self.send_json({'error': str(ex)}, 400)
            usage('census_route', v=d.ver, ok=1, code=r['code'], dir=r['dir'], links=r['links'])
            return self.send_json(r)
        if u.path == '/api/reverse':
            # 経路の逆方向(上下線分離区間は反対車線)を作る
            req = json.loads(body or b'{}')
            d = self.drm(req.get('v') or STORE.default)
            if d is None:
                return
            oneway = req.get('oneway', 'all')
            mode = 'dist' if req.get('mode') == 'dist' else 'time'
            types = parse_types(req.get('types'))
            links = [(int(l), bool(f)) for l, f in req.get('links', [])]
            if not links:
                return self.send_json({'error': '逆方向にする経路のリンクがありません'}, 400)
            if any(not 0 <= l < len(d.mc) for l, _ in links):
                return self.send_json({'error': 'リンク番号が不正です(DRM版が違う可能性)'}, 400)
            try:
                legs, wp_json, notes = make_reverse(d, links, oneway, types, mode)
            except RouteError as ex:
                usage('reverse', v=d.ver, ok=0, links=len(links))
                return self.send_json({'error': str(ex)}, 400)
            usage('reverse', v=d.ver, ok=1, links=len(links), warn=sum(1 for x in notes if x.get('kind') == 'warn'))
            return self.send_json({'v': d.ver, 'legs': legs_json(d, legs), 'nodes': wp_json, 'notes': notes})
        self.send_error(404)


class FastServer(ThreadingHTTPServer):
    """標準の server_bind は自PC名をDNSで逆引きして数秒かかるため省略する"""
    allow_reuse_address = False   # Windowsでの二重起動防止

    def server_bind(self):
        socketserver.TCPServer.server_bind(self)
        self.server_name, self.server_port = 'localhost', self.server_address[1]


def main():
    global PORT, STORE, USAGE
    shared = None
    for a in sys.argv[1:]:
        if a.startswith('--port='):
            PORT = int(a.split('=', 1)[1])
        if a.startswith('--shared-cache='):
            shared = a.split('=', 1)[1]
    url = 'http://localhost:%d/' % PORT
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    data_dir = os.path.normpath(args[0]) if args else DEFAULT_DATA_DIR

    if '--update-jartic' in sys.argv:
        # JARTIC(県警の感知器)の最新月を社内SQL Serverから集計し、センサス時間交通量と比較して jartic.json を作る
        sys.path.insert(0, HERE)
        import jartic
        load_census(data_dir)
        st = Store(data_dir)
        d = st.load_version(st.default)
        jartic.update(d, census_info, data_dir, JARTIC_FILE, log, LINK_CELL, SCALE)
        return

    if '--update-torakan' in sys.argv:
        # 国交省トラカンの直近1か月(平日)を取得し、センサス時間交通量と比較して torakan.json を作る
        sys.path.insert(0, HERE)
        import torakan
        load_census(data_dir)
        st = Store(data_dir)
        d = st.load_version(st.default)
        torakan.update(d, census_info, data_dir, TORAKAN_FILE, log, LINK_CELL, SCALE)
        return

    if '--build-only' in sys.argv:
        # 全DRM版の変換済みデータ(キャッシュ)を作るだけ(共有先へ反映する前に使う)
        build_census(data_dir)
        st = Store(data_dir)
        for v in sorted(st.sources):
            d = st.load_version(v)
            log('DRM%s(%s) 準備完了: リンク %d' % (v, st.labels[v], len(d.mc)))
            del d
            gc.collect()
        # 使わなくなった変換済みデータを削除
        for f in glob.glob(os.path.join(st.local_cache, '*.pickle')):
            m = re.match(r'drm_(\d{4})\.pickle$', os.path.basename(f))
            if not m or m.group(1) not in st.sources:
                os.remove(f)
                log('不要な変換済みデータを削除:', os.path.basename(f))
        return

    # Windowsでは同じポートに二重に起動できてしまうため、起動済みならブラウザを開くだけにする
    import urllib.request
    with socket.socket() as sk:
        running = sk.connect_ex(('127.0.0.1', PORT)) == 0
    if running:
        info = {}
        for api in ('api/status', 'api/info'):
            try:
                info = json.load(urllib.request.urlopen(url + api, timeout=5))
                break
            except Exception:
                pass
        if info.get('build') == BUILD:
            log('既に起動しています:', url)
            if '--no-browser' not in sys.argv:
                webbrowser.open(url)
            return
        # 古いバージョンが動いている → 停止を依頼して入れ替える
        log('古いバージョンのサーバが動いているため停止します')
        try:
            urllib.request.urlopen(urllib.request.Request(url + 'api/shutdown', data=b'{}', method='POST'), timeout=5)
        except Exception:
            pass
        for _ in range(20):
            time.sleep(0.5)
            with socket.socket() as sk:
                if sk.connect_ex(('127.0.0.1', PORT)) != 0:
                    break
        else:
            log('古いサーバを停止できませんでした。古いツールの黒いウィンドウを閉じてから、もう一度起動してください。')
            input('Enterキーで終了します')
            return

    load_census(data_dir)
    # 利用状況は共有のツールフォルダ(--shared-cache の親。共有フォルダから直接起動したときはこのフォルダ)に記録
    if '--no-usage' not in sys.argv:
        USAGE = usage_log.Usage(os.path.dirname(os.path.abspath(shared)) if shared else HERE, log)
    # 先に画面を出し、データ(既定のDRM版)は裏で読み込む(読込の進捗はブラウザに表示)
    STORE = Store(data_dir, shared)
    log('DRM版: ' + ' / '.join('%s(%s)' % (x['v'], x['label']) for x in STORE.versions()) + '  既定: %s' % STORE.default)
    srv = FastServer(('127.0.0.1', PORT), Handler)
    STORE.get(STORE.default)
    log('起動しました:', url, '(終了は このウィンドウを閉じる)')
    if '--no-browser' not in sys.argv:
        threading.Thread(target=webbrowser.open, args=(url,), daemon=True).start()
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == '__main__':
    main()
