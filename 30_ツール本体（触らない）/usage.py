# -*- coding: utf-8 -*-
r"""
利用状況の記録と集計(標準ライブラリのみ)
  記録先は共有のツールフォルダの _利用ログ フォルダ
    利用者\<利用者ID>.json            … 初回起動時のアンケート(支社・役職)。1人1回だけ
    ログ\<年-月>\<利用者ID>_<PC名>.jsonl … 操作の記録(1行1操作)。人・PCごとに別ファイルなので同時に書いても壊れない
  利用者ID = Windowsのログオン名(同じ人なら別のPCでも同じID)。
  アンケートの回答はこのPCにも控え(%LOCALAPPDATA%\DRMリンク拾いツール_利用者.json)を置き、
  共有フォルダに書けなかった場合でも2回目以降は聞かない。
"""
import datetime
import glob
import json
import os
import re
import socket
import threading
import time

DIR_NAME = '_利用ログ'
BRANCHES = ['北海道', '東北', '東京', '中部', '大阪', '九州', 'その他']
ROLES = ['管理職', '一般職・契約社員', '派遣・アルバイト']
NO_ANSWER = '未回答'
# 操作の種類(ログの e) → 名称
EVENTS = {
    'open': 'アクセス(画面を開いた)',
    'route': '経路探索',
    'reverse': '逆方向を複製',
    'find': 'ID検索',
    'census_route': 'センサス区間から経路を作成',   # 続けて経路探索(route)も記録されるので集計表には足さない
    'link_out': 'リンクExcel出力',
    'tk_view': 'トラカン グラフ表示',
    'tk_out': 'トラカン ダウンロード',
}
# 集計表の列: (キー, 名称, 数える操作)
METRICS = [
    ('open', 'アクセス', {'open'}),
    ('route', 'リンク拾い 検索', {'route', 'reverse'}),
    ('find', 'ID検索', {'find'}),
    ('link_out', 'リンク拾い 出力', {'link_out'}),
    ('tk_view', 'トラカン 検索', {'tk_view'}),
    ('tk_out', 'トラカン 出力', {'tk_out'}),
]
# 画面から記録できる操作(それ以外はサーバー側で記録)
CLIENT_EVENTS = {'open', 'link_out', 'tk_out'}


def _safe(s):
    return re.sub(r'[^\w.\-]', '_', (s or '').strip().lower()) or 'unknown'


def _write_json(path, obj):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = '%s.%s.%d.tmp' % (path, socket.gethostname(), os.getpid())
    with open(tmp, 'w', encoding='utf-8') as f:
        json.dump(obj, f, ensure_ascii=False, indent=1)
    os.replace(tmp, path)


def _read_json(path):
    try:
        with open(path, encoding='utf-8') as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


class Usage:
    def __init__(self, root, log):
        self.dir = os.path.join(root, DIR_NAME)
        self.log = log
        self.uid = _safe(os.environ.get('USERNAME'))
        self.pc = _safe(os.environ.get('COMPUTERNAME') or socket.gethostname())
        self.local = os.path.join(os.environ.get('LOCALAPPDATA') or os.path.expanduser('~'), 'DRMリンク拾いツール_利用者.json')
        self.buf = []
        self.cv = threading.Condition()
        self.cache = {}            # ログファイル → ((サイズ, 更新日時), 行のリスト)
        self.cache_lock = threading.Lock()
        threading.Thread(target=self._writer, daemon=True).start()

    # ---- アンケート(支社・役職) ----
    def _shared_profile(self):
        return os.path.join(self.dir, '利用者', self.uid + '.json')

    def profile(self):
        """回答済みなら {'branch','role',...}、未回答なら None"""
        p = _read_json(self._shared_profile())
        if p and p.get('branch'):
            if not os.path.exists(self.local):
                try:
                    _write_json(self.local, p)
                except OSError:
                    pass
            return p
        p = _read_json(self.local)
        if p and p.get('branch'):
            try:   # 共有フォルダに無い(前回書けなかった) → 書き直す
                _write_json(self._shared_profile(), p)
            except OSError:
                pass
            return p
        return None

    def save_profile(self, branch, role):
        if branch not in BRANCHES or role not in ROLES:
            raise ValueError('支社・役職を選んでください')
        old = self.profile()
        if old:                    # 回答は1回だけ(上書きしない)
            return old
        p = {'uid': self.uid, 'branch': branch, 'role': role, 'pc': self.pc,
             'answered': datetime.datetime.now().isoformat(timespec='seconds')}
        _write_json(self.local, p)
        try:
            _write_json(self._shared_profile(), p)
        except OSError as e:
            self.log('利用者情報を共有フォルダに保存できませんでした(次回起動時に再保存します):', e)
        return p

    # ---- 操作の記録 ----
    def record(self, ev, **kw):
        row = {'t': datetime.datetime.now().isoformat(timespec='seconds'), 'u': self.uid, 'pc': self.pc, 'e': ev}
        row.update({k: v for k, v in kw.items() if v is not None})
        with self.cv:
            self.buf.append(row)
            del self.buf[:-20000]   # 書けない状態が続いても際限なく溜めない
            self.cv.notify()

    def _writer(self):
        while True:
            with self.cv:
                while not self.buf:
                    self.cv.wait()
            time.sleep(1)           # 続けて起きた操作はまとめて書く
            with self.cv:
                rows, self.buf = self.buf, []
            by_file = {}
            for r in rows:
                f = os.path.join(self.dir, 'ログ', r['t'][:7], '%s_%s.jsonl' % (self.uid, self.pc))
                by_file.setdefault(f, []).append(r)
            failed = []
            for f, rs in by_file.items():
                try:
                    os.makedirs(os.path.dirname(f), exist_ok=True)
                    with open(f, 'a', encoding='utf-8') as fo:
                        fo.write(''.join(json.dumps(r, ensure_ascii=False, separators=(',', ':')) + '\n' for r in rs))
                except OSError as e:
                    failed += rs
                    self.log('利用ログを書けませんでした(後で再試行):', e)
            if failed:
                time.sleep(30)
                with self.cv:
                    self.buf[:0] = failed

    # ---- 集計 ----
    def _profiles(self):
        out = {}
        for f in glob.glob(os.path.join(self.dir, '利用者', '*.json')):
            p = _read_json(f)
            if p and p.get('uid'):
                out[p['uid']] = p
        return out

    def _rows(self, m0, m1):
        """期間(年-月)のログファイルを読む(読んだファイルは変わるまで覚えておく)"""
        files = []
        for d in sorted(glob.glob(os.path.join(self.dir, 'ログ', '*'))):
            m = os.path.basename(d)
            if re.fullmatch(r'\d{4}-\d{2}', m) and (not m0 or m >= m0) and (not m1 or m <= m1):
                files += glob.glob(os.path.join(d, '*.jsonl'))
        out, nbytes = [], 0
        for f in files:
            try:
                st = os.stat(f)
            except OSError:
                continue
            sig = (st.st_size, int(st.st_mtime))
            nbytes += st.st_size
            with self.cache_lock:
                c = self.cache.get(f)
            if not c or c[0] != sig:
                rows = []
                try:
                    with open(f, encoding='utf-8') as fi:
                        for line in fi:
                            try:
                                rows.append(json.loads(line))
                            except ValueError:
                                pass   # 書きかけの行など
                except OSError:
                    continue
                c = (sig, rows)
                with self.cache_lock:
                    self.cache[f] = c
            out += c[1]
        return out, len(files), nbytes

    def summary(self, d0=None, d1=None):
        """支社×役職・月ごとの集計。d0/d1 = 'YYYY-MM-DD'(省略=全期間)"""
        prof = self._profiles()
        rows, nfiles, nbytes = self._rows(d0 and d0[:7], d1 and d1[:7])
        ev2m = {}
        for k, _, evs in METRICS:
            for e in evs:
                ev2m[e] = k
        cells, months = {}, {}
        for p in prof.values():   # 回答者数(期間に関係なく)
            c = cells.setdefault((p.get('branch', NO_ANSWER), p.get('role', NO_ANSWER)),
                                 {'registered': 0, 'users': set(), 'n': {k: 0 for k, _, _ in METRICS}})
            c['registered'] += 1
        first = last = None
        for r in rows:
            t = r.get('t', '')
            day = t[:10]
            if (d0 and day < d0) or (d1 and day > d1):
                continue
            k = ev2m.get(r.get('e'))
            if not k or r.get('auto'):   # 自動の再計算(起動時の経路の復元など)は数えない
                continue
            p = prof.get(r.get('u')) or {}
            key = (p.get('branch', NO_ANSWER), p.get('role', NO_ANSWER))
            c = cells.setdefault(key, {'registered': 0, 'users': set(), 'n': {m: 0 for m, _, _ in METRICS}})
            c['users'].add(r.get('u'))
            c['n'][k] += 1
            mo = months.setdefault(t[:7], {'users': set(), 'n': {m: 0 for m, _, _ in METRICS}})
            mo['users'].add(r.get('u'))
            mo['n'][k] += 1
            first = day if not first or day < first else first
            last = day if not last or day > last else last
        order = {b: i for i, b in enumerate(BRANCHES + [NO_ANSWER])}
        rorder = {b: i for i, b in enumerate(ROLES + [NO_ANSWER])}
        return {
            'metrics': [[k, nm] for k, nm, _ in METRICS],
            'branches': BRANCHES, 'roles': ROLES,
            'cells': [{'branch': b, 'role': ro, 'registered': c['registered'], 'users': len(c['users']), 'n': c['n']}
                      for (b, ro), c in sorted(cells.items(), key=lambda x: (order.get(x[0][0], 99), rorder.get(x[0][1], 99)))],
            'months': [{'month': m, 'users': len(c['users']), 'n': c['n']} for m, c in sorted(months.items())],
            'first': first, 'last': last, 'files': nfiles, 'bytes': nbytes, 'events': len(rows),
            'registered': len(prof),
        }

    def raw(self, d0=None, d1=None):
        """全ログの一覧(Excel出力用): 日時, 利用者ID, PC名, 支社, 役職, 操作, 詳細"""
        prof = self._profiles()
        rows, _, _ = self._rows(d0 and d0[:7], d1 and d1[:7])
        out = []
        for r in sorted(rows, key=lambda r: r.get('t', '')):
            day = r.get('t', '')[:10]
            if (d0 and day < d0) or (d1 and day > d1):
                continue
            p = prof.get(r.get('u')) or {}
            det = {k: v for k, v in r.items() if k not in ('t', 'u', 'pc', 'e')}
            out.append([r.get('t', '').replace('T', ' '), r.get('u', ''), r.get('pc', ''),
                        p.get('branch', NO_ANSWER), p.get('role', NO_ANSWER),
                        EVENTS.get(r.get('e'), r.get('e', '')),
                        json.dumps(det, ensure_ascii=False) if det else ''])
        return out
