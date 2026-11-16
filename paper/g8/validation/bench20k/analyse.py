"""analyse.py CORPUS_DIR OUT[,OUT...] [PREVIOUS_OUT[,PREVIOUS_OUT...]]: the solver's own account of a run of
solveall over the corpus, by group, and the comparison with the runs of another version (same discs? faster
or slower, case by case).  Several outputs of the same version, separated by commas: the time of a
polynomial is the smallest of its times (the machine is shared), and the discs must be the same in all."""
import json, statistics, sys
from pathlib import Path
BASE = Path(sys.argv[1]).resolve()
C = {str(BASE / c['path']): c for c in json.load(open(BASE / 'corpus.json'))['cases']}
def load_one(path):
    rows = []; cur = None
    for l in open(path):
        t = l.split()
        if t[0] == 'poly':
            c = C[t[1]]; cur = dict(id=c['id'], g=c['group'], n=int(t[2]), s=float(t[3]), complete=t[4] == '1', within=t[5] == '1', discs=int(t[6]), sw=int(t[7]), ex=int(t[8]), pr=int(t[9]), bits=int(t[10]), cnt=0, maxc=1, shape=[]); rows.append(cur)
        else:
            cur['cnt'] += int(t[3]) * int(t[4]); cur['maxc'] = max(cur['maxc'], int(t[4])); cur['shape'].append((int(t[3]), int(t[4])))
    for r in rows: r['shape'] = sorted(r['shape'])
    return rows
def load(paths):
    runs = [load_one(p) for p in paths.split(',')]
    for other in runs[1:]:
        for a, b in zip(runs[0], other):
            assert a['id'] == b['id'] and a['shape'] == b['shape'] and a['complete'] == b['complete'], ('two runs of one version differ', a['id'])
            a['s'] = min(a['s'], b['s'])
    return runs[0], [sum(r['s'] for r in run) for run in runs] if len(runs) == 1 else None
rows, _ = load(sys.argv[2]); tot = sum(r['s'] for r in rows)
print(f"{len(rows)} polynomials, {sum(r['n'] for r in rows)} roots: {tot:.2f} s in all, median {statistics.median(r['s'] for r in rows) * 1e6:.0f} us; complete {sum(r['complete'] for r in rows)}, within tolerance {sum(r['within'] for r in rows)}")
stage = lambda r: 'precise' if r['pr'] else 'exact' if r['ex'] else 'double'
print('deepest stage reached: ' + ', '.join(f"{k} {sum(stage(r) == k for r in rows)} ({sum(r['s'] for r in rows if stage(r) == k):.2f} s)" for k in ['double', 'exact', 'precise']))
old = None
if len(sys.argv) > 3:
    old = {r['id']: r for r in load(sys.argv[3])[0]}
print(f"{'group':13s} {'n':>5s} {'compl':>5s} {'within':>6s} {'shared':>6s} {'total_s':>8s} {'median_us':>9s} {'p90_us':>8s} {'max_s':>6s}" + (f" {'before_s':>8s} {'ratio':>5s}" if old else ''))
for g in sorted({r['g'] for r in rows}):
    v = [r for r in rows if r['g'] == g]; ts = sorted(r['s'] for r in v)
    extra = ''
    if old:
        b = sum(old[r['id']]['s'] for r in v); extra = f" {b:8.2f} {b / sum(ts):5.2f}"
    print(f"{g:13s} {len(v):5d} {sum(r['complete'] for r in v):5d} {sum(r['within'] for r in v):6d} {sum(r['maxc'] > 1 for r in v):6d} {sum(ts):8.2f} {statistics.median(ts) * 1e6:9.0f} {ts[int(0.9 * len(ts))] * 1e6:8.0f} {ts[-1]:6.2f}" + extra)
print('not complete:', [r['id'] for r in rows if not r['complete']][:20])
print('slowest:', [(r['id'], r['n'], round(r['s'], 3)) for r in sorted(rows, key=lambda r: -r['s'])[:12]])
if old:
    diff = [r['id'] for r in rows if r['shape'] != old[r['id']]['shape'] or r['complete'] != old[r['id']]['complete']]
    bt = sum(o['s'] for o in old.values())
    print(f"\nagainst {sys.argv[3]}: previous total {bt:.2f} s, ratio {bt / tot:.2f}; discs (multiplicities and counts) or completeness changed on {len(diff)} polynomials: {diff[:15]}")
    print('within tolerance lost:', [r['id'] for r in rows if old[r['id']]['within'] and not r['within']][:15], '| gained:', len([1 for r in rows if r['within'] and not old[r['id']]['within']]))
    big = [(r['s'] / old[r['id']]['s'], r['id'], old[r['id']]['s'], r['s']) for r in rows if max(r['s'], old[r['id']]['s']) > 2e-4]
    print('slower by more than 1.5:', len([b for b in big if b[0] > 1.5]), [(b[1], round(b[2] * 1e3, 2), round(b[3] * 1e3, 2)) for b in sorted(big, reverse=True)[:10] if b[0] > 1.5])
    print('faster by more than 1.5:', len([b for b in big if b[0] < 1 / 1.5]), 'of', len(big), 'that take more than 0.2 ms')
    for lo, hi in [(0, 20), (21, 100), (101, 400), (401, 2000)]:
        v = [r for r in rows if lo <= r['n'] <= hi]
        if v: print(f"degree {lo:4d} to {hi:4d}: {len(v):5d} polynomials, {sum(old[r['id']]['s'] for r in v):7.2f} s -> {sum(r['s'] for r in v):7.2f} s")
