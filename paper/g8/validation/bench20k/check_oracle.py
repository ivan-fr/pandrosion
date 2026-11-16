"""check_oracle.py CORPUS_DIR OUT: the discs of a run of solveall against the roots that are known exactly.

For the polynomials built from prescribed rational roots (corpus.json gives them with their multiplicities)
the check is made in exact rational arithmetic, on the doubles printed by solveall read as the binary
numbers they are: every root lies in one disc and only one, that disc has the multiplicity of the root,
every disc holds as many distinct roots as its `count`, a disc flagged real holds real roots only, and the
multiplicities add up to the degree.  Nothing here uses the solver or floating-point arithmetic."""
import json, sys
from fractions import Fraction as Q
from pathlib import Path
BASE = Path(sys.argv[1]).resolve()
C = {str(BASE / c['path']): c for c in json.load(open(BASE / 'corpus.json'))['cases']}
runs = []; cur = None
for l in open(sys.argv[2]):
    t = l.split()
    if t[0] == 'poly': cur = (C[t[1]], t, []); runs.append(cur)
    else: cur[2].append(t)
checked = roots_checked = discs_checked = shared = 0; bad = []; groups = {}
for c, head, discs in runs:
    if not c['oracle'] or c['oracle']['kind'] != 'rational': continue
    want = {}
    for a, b, mult in c['oracle']['roots']: want[(Q(a), Q(b))] = want.get((Q(a), Q(b)), 0) + mult
    D = []
    for t in discs:
        rad = float(t[2])
        if rad != rad or rad in (float('inf'), float('-inf')): bad.append((c['id'], 'radius not finite')); D = None; break
        D.append((Q(float(t[0])), Q(float(t[1])), Q(rad) ** 2, int(t[3]), int(t[4]), t[5] == '1', []))
    if D is None: continue
    ok = head[4] == '1' and sum(d[3] * d[4] for d in D) == c['degree'] == sum(want.values())
    if not ok: bad.append((c['id'], 'not complete, or the multiplicities do not add up to the degree'))
    for (a, b), mult in want.items():
        inside = [d for d in D if (d[0] - a) ** 2 + (d[1] - b) ** 2 <= d[2]]
        if len(inside) != 1: bad.append((c['id'], f'root {a} + {b} i lies in {len(inside)} discs')); ok = False; continue
        d = inside[0]; d[6].append((a, b))
        if d[3] != mult: bad.append((c['id'], f'root {a} + {b} i has multiplicity {mult}, its disc says {d[3]}')); ok = False
    for d in D:
        if len(d[6]) != d[4]: bad.append((c['id'], f'a disc holds {len(d[6])} roots, its count is {d[4]}')); ok = False
        if d[5] and any(b != 0 for a, b in d[6]): bad.append((c['id'], 'a disc flagged real holds a root that is not')); ok = False
    checked += 1; roots_checked += len(want); discs_checked += len(D); shared += any(d[4] > 1 for d in D)
    g = groups.setdefault(c['group'], [0, 0]); g[0] += 1; g[1] += ok
print(f"{checked} polynomials with exactly known roots: {roots_checked} distinct roots, {discs_checked} discs ({shared} polynomials with a disc shared by roots that doubles cannot separate)")
print('by group (checked, all right): ' + ', '.join(f"{g} {v[0]} {v[1]}" for g, v in sorted(groups.items())))
print(f"wrong: {len(bad)}", bad[:20])
sys.exit(1 if bad else 0)
