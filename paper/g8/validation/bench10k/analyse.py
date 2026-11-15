"""analyse.py OUT [PREVIOUS_OUT]: the solver's own account of a run over the corpus, by group, and the
comparison with a previous run (same discs? faster or slower, case by case)."""
import json, statistics, sys
from pathlib import Path
C = {str(Path(__file__).resolve().parent / c['path']): c for c in json.load(open(Path(__file__).resolve().parent / 'corpus.json'))['cases']}
def load(path):
    rows = []; cur = None
    for l in open(path):
        t = l.split()
        if t[0] == 'poly':
            c = C[t[1]]; cur = dict(id=c['id'], g=c['group'], n=int(t[2]), s=float(t[3]), complete=t[4] == '1', within=t[5] == '1', discs=int(t[6]), sw=int(t[7]), ex=int(t[8]), pr=int(t[9]), bits=int(t[10]), cnt=0, maxc=1, shape=[]); rows.append(cur)
        else:
            cur['cnt'] += int(t[3]) * int(t[4]); cur['maxc'] = max(cur['maxc'], int(t[4])); cur['shape'].append((int(t[3]), int(t[4])))
    for r in rows: r['shape'] = sorted(r['shape'])
    return rows
rows = load(sys.argv[1]); tot = sum(r['s'] for r in rows)
print(f"{len(rows)} polynomials, {sum(r['n'] for r in rows)} roots: {tot:.2f} s in all, median {statistics.median(r['s'] for r in rows) * 1e6:.0f} us; complete {sum(r['complete'] for r in rows)}, within tolerance {sum(r['within'] for r in rows)}")
print(f"{'group':13s} {'n':>5s} {'compl':>5s} {'within':>6s} {'shared':>6s} {'total_s':>8s} {'median_us':>9s} {'p90_us':>8s} {'max_s':>6s}")
for g in sorted({r['g'] for r in rows}):
    v = [r for r in rows if r['g'] == g]; ts = sorted(r['s'] for r in v)
    print(f"{g:13s} {len(v):5d} {sum(r['complete'] for r in v):5d} {sum(r['within'] for r in v):6d} {sum(r['maxc'] > 1 for r in v):6d} {sum(ts):8.2f} {statistics.median(ts) * 1e6:9.0f} {ts[int(0.9 * len(ts))] * 1e6:8.0f} {ts[-1]:6.2f}")
print('not complete:', [r['id'] for r in rows if not r['complete']][:20])
print('slowest:', [(r['id'], r['n'], round(r['s'], 3)) for r in sorted(rows, key=lambda r: -r['s'])[:12]])
if len(sys.argv) > 2:
    old = {r['id']: r for r in load(sys.argv[2])}
    diff = [r['id'] for r in rows if r['shape'] != old[r['id']]['shape'] or r['complete'] != old[r['id']]['complete']]
    print(f"\nagainst {sys.argv[2]}: previous total {sum(o['s'] for o in old.values()):.2f} s; discs (multiplicities and counts) or completeness changed on {len(diff)} polynomials: {diff[:15]}")
    print('within tolerance lost:', [r['id'] for r in rows if old[r['id']]['within'] and not r['within']][:15], '| gained:', len([1 for r in rows if r['within'] and not old[r['id']]['within']]))
    big = [(r['s'] / old[r['id']]['s'], r['id'], old[r['id']]['s'], r['s']) for r in rows if max(r['s'], old[r['id']]['s']) > 2e-4]
    print('slower by more than 1.5:', len([b for b in big if b[0] > 1.5]), [(b[1], round(b[2] * 1e3, 2), round(b[3] * 1e3, 2)) for b in sorted(big, reverse=True)[:10] if b[0] > 1.5])
    print('faster by more than 1.5:', len([b for b in big if b[0] < 1 / 1.5]))
