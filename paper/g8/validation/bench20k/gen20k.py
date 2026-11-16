"""Benchmark 20K: 10 000 more polynomials, of the same sixteen families as the benchmark 10K, from another
seed (20261117).  Run ../bench10k/add_extended_cases.py and ../bench10k/gen10k.py first, in this directory
(they write corpus.json and cases/ next to themselves: copy the two scripts here, or run all three from one
directory); this script then adds its cases, named m_*, to reach 20 000.

What differs from gen10k.py besides the seed: the families that gen10k.py builds without random numbers
would come out the same, so they are taken elsewhere - orthogonal polynomials at fifty other degrees,
truncated exponentials at the odd degrees, Kameny polynomials with c = 3 10^e, iterated maps with other
constants instead of the Mandelbrot polynomials - and the dense polynomials that fill the corpus are named
m_dense_extra_*.  Exact coefficients, deterministic."""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm, factorial, comb
import hashlib, json
import numpy as np

BASE = Path(__file__).resolve().parent
doc = json.loads((BASE / 'corpus.json').read_text())
doc['cases'] = [c for c in doc['cases'] if not c.get('second')]
assert len(doc['cases']) == 10000, 'run add_extended_cases.py and gen10k.py first'
OUT = BASE / 'cases'
new = []
rng = np.random.default_rng(20261117)

def from_roots(roots):
    p = [(Q(1), Q(0))]
    for ar, ai, mult in roots:
        ar, ai = Q(ar), Q(ai)
        for _ in range(mult):
            q = [(Q(0), Q(0)) for _ in range(len(p) + 1)]
            for i, (r, s) in enumerate(p):
                q[i] = (q[i][0] + r, q[i][1] + s)
                q[i + 1] = (q[i + 1][0] - r * ar + s * ai, q[i + 1][1] - r * ai - s * ar)
            p = q
    den = lcm(*(v.denominator for x in p for v in x))
    return [(int(r * den), int(s * den)) for r, s in p]
def pmul(a, b):
    r = [[0, 0] for _ in range(len(a) + len(b) - 1)]
    for i, (x, y) in enumerate(a):
        if x == 0 and y == 0: continue
        for j, (u, v) in enumerate(b):
            r[i + j][0] += x * u - y * v; r[i + j][1] += x * v + y * u
    return [tuple(x) for x in r]
FAST = {'real': 'random_real', 'complex': 'random_complex'}
def add(name, group, coeff, kind='I', oracle=None, tags=None):
    n = len(coeff) - 1
    assert n >= 1 and coeff[0] != (0, 0), name
    content = f'{kind} {n}\n' + ''.join(f'{r!r} {i!r}\n' if kind == 'F' else f'{r} {i}\n' for r, i in coeff)
    path = OUT / ('m_' + name + '.poly'); path.write_text(content)
    # the validation matches roots with mpmath for small families and with doubles for the large ones
    real = all(i == 0 for r, i in coeff)
    family = ('m_' + group) if n <= 300 else FAST['real' if real else 'complex']
    new.append(dict(id='m_' + name, family=family, group=group, degree=n, kind=kind, path=str(path.relative_to(BASE)),
                    sha256=hashlib.sha256(content.encode()).hexdigest(), oracle=oracle, tags=tags or [], supplemental=True, extended=True, generated=True, second=True))
def known(name, group, roots, tags=None):
    roots = [(str(Q(r)), str(Q(i)), m) for r, i, m in roots]
    add(name, group, from_roots(roots), oracle={'kind': 'rational', 'roots': roots}, tags=tags)
ints = lambda v: [(int(x), 0) for x in v]
ri = lambda a, b: int(rng.integers(a, b + 1))
def frac(scale=20, den=12):
    return Q(ri(-scale * den, scale * den), ri(1, den))
def distinct(count, complex_=True, scale=20):
    seen = set(); out = []
    while len(out) < count:
        z = (frac(scale), frac(scale) if complex_ and rng.random() < 0.6 else Q(0))
        if z not in seen: seen.add(z); out.append(z)
    return out

# 1. dense, Gaussian coefficients
DEG = [3, 4, 5, 6, 7, 8, 10, 12, 15, 20, 25, 30, 40, 50, 60, 80, 100, 120, 160, 200]
W = np.array([8, 8, 10, 8, 8, 8, 10, 8, 8, 10, 6, 6, 6, 5, 5, 4, 3, 2, 2, 1], dtype=float); W /= W.sum()
for k in range(2758):
    n = int(rng.choice(DEG, p=W)); cx = k % 2 == 1
    r = rng.standard_normal(n + 1); i = rng.standard_normal(n + 1) if cx else np.zeros(n + 1)
    add(f'dense_{k:04}', 'dense', list(zip(map(float, r), map(float, i))), 'F')
# 2. other laws for the coefficients
for k in range(1000):
    n = int(rng.choice(DEG[:17], p=W[:17] / W[:17].sum())); cx = k % 2 == 1; law = k % 5
    if law == 0:      # uniform on [-1, 1]
        r = rng.uniform(-1, 1, n + 1); i = rng.uniform(-1, 1, n + 1) if cx else np.zeros(n + 1)
        add(f'uniform_{k:04}', 'laws', list(zip(map(float, r), map(float, i))), 'F')
    elif law == 1:    # small integers
        r = rng.integers(-9, 10, n + 1); r[0] = ri(1, 9); i = rng.integers(-9, 10, n + 1) if cx else np.zeros(n + 1, dtype=int)
        add(f'int_small_{k:04}', 'laws', [(int(a), int(b)) for a, b in zip(r, i)])
    elif law == 2:    # integers of 40 digits
        big = lambda: int(''.join(str(ri(0, 9)) for _ in range(40))) * (1 if rng.random() < 0.5 else -1)
        add(f'int_big_{k:04}', 'laws', [(big() or 1, big() if cx else 0) for _ in range(n + 1)])
    elif law == 3:    # coefficients over 60 orders of magnitude
        r = rng.standard_normal(n + 1) * 10.0 ** rng.uniform(-30, 30, n + 1); i = rng.standard_normal(n + 1) * 10.0 ** rng.uniform(-30, 30, n + 1) if cx else np.zeros(n + 1)
        add(f'wide_{k:04}', 'laws', list(zip(map(float, r), map(float, i))), 'F')
    else:             # decaying coefficients (roots on several circles)
        e = np.cumsum(rng.uniform(-3, 3, n + 1)); r = rng.standard_normal(n + 1) * 10.0 ** e; i = rng.standard_normal(n + 1) * 10.0 ** e if cx else np.zeros(n + 1)
        add(f'walk_{k:04}', 'laws', list(zip(map(float, r), map(float, i))), 'F')
# 3. prescribed roots (exact rational, so the oracle is exact)
for k in range(1000):
    n = ri(3, 24); kind_ = k % 4
    if kind_ == 0: roots = [(a, b, 1) for a, b in distinct(n)]
    elif kind_ == 1: roots = [(a, 0, 1) for a, b in distinct(n, False)]
    elif kind_ == 2:   # on the unit circle: rational points (1 - t^2 + 2 t i) / (1 + t^2)
        ts = set()
        while len(ts) < n: ts.add(Q(ri(-40, 40), ri(1, 15)))
        roots = [((1 - t * t) / (1 + t * t), 2 * t / (1 + t * t), 1) for t in ts]
    else:              # conjugate pairs and real roots
        roots = []
        for a, b in distinct(n // 2):
            roots += [(a, b, 1), (a, -b, 1)] if b else [(a, 0, 1)]
    known(f'roots_{k:04}', 'roots', roots)
# 4. sparse
for k in range(500):
    n = int(rng.choice([20, 50, 100, 200, 400, 800, 1500])); cx = k % 2 == 1; terms = ri(3, 9)
    c = [(0, 0)] * (n + 1)
    for j in sorted(set([0, n, *rng.choice(n + 1, min(terms, n + 1), replace=False)])):
        c[j] = (ri(1, 9) * (1 if rng.random() < 0.5 else -1), ri(-9, 9) if cx else 0)
    add(f'sparse_{k:04}', 'sparse', c, tags=['sparse'])
# 5. multiplicities
for k in range(800):
    d = ri(2, 7); mx = int(rng.choice([2, 3, 5, 8, 12]))
    roots = [(a, b, ri(1, mx)) for a, b in distinct(d, k % 2 == 1, 8)]
    if sum(m for _, _, m in roots) > 60: roots = [(a, b, min(m, 6)) for a, b, m in roots]
    known(f'multiple_{k:04}', 'multiplicity', roots, ['multiple'])
# 6. clusters: K roots within eps of a centre, on a line, in the plane or on a ring; plus other roots
LAT = [(0, 0), (1, 0), (0, 1), (-1, 2), (2, -1), (-2, -1), (1, 3), (3, 1), (-3, 2)]
for k in range(1200):
    kk = int(rng.choice([2, 2, 3, 3, 4, 5, 6, 8])); step = int(rng.choice([4, 6, 8, 10, 12, 14, 16, 20, 25, 30, 40]))
    centre = (frac(4, 6), frac(4, 6) if rng.random() < 0.5 else Q(0))
    if centre == (0, 0): centre = (Q(1), Q(0))
    scale = max(abs(centre[0]), abs(centre[1])) * Q(1, 10 ** step)
    rest = [(a, b, 1) for a, b in distinct(ri(1, 6)) if (a, b) != centre]
    shape = k % 3
    if shape == 0:
        known(f'cluster_line_{k:04}', 'cluster', [(centre[0] + j * scale, centre[1], 1) for j in range(kk)] + rest, ['close_roots'])
    elif shape == 1:
        known(f'cluster_plane_{k:04}', 'cluster', [(centre[0] + a * scale, centre[1] + b * scale, 1) for a, b in LAT[:kk]] + rest, ['close_roots'])
    else:   # ring: (c q (w - p/q))^K = q^K, K roots on a circle of radius 1/c around p/q
        p, q = ri(-30, 30) or 1, ri(1, 9); c = 10 ** step
        pw = [(1, 0)]
        for _ in range(kk): pw = pmul(pw, [(c * q, 0), (-c * p, 0)])
        pw[-1] = (pw[-1][0] - q ** kk, 0)
        add(f'cluster_ring_{k:04}', 'cluster', pmul(pw, from_roots(rest)) if rest else pw, tags=['close_roots'])
# 7. Mignotte and its three-root variant
for k in range(300):
    n = ri(6, 80); a = 10 ** ri(1, 14)
    c = [(0, 0)] * (n + 1); c[0] = (1, 0)
    if k % 3 < 2:
        c[-3] = (-2 * a * a, 0); c[-2] = (4 * a, 0); c[-1] = (-2, 0); name = 'mignotte'
    else:
        for j, v in enumerate([-a ** 3, 3 * a * a, -3 * a, 1]): c[n - 3 + j] = (c[n - 3 + j][0] + v, 0)
        name = 'mignotte3'
    add(f'{name}_{k:04}', 'mignotte', c, tags=['close_roots'])
# 8. roots in arithmetic progression (Wilkinson-like)
for k in range(250):
    n = ri(5, 60); a0 = frac(5, 4); h = Q(ri(1, 12), ri(1, 6))
    known(f'progression_{k:04}', 'wilkinson', [(a0 + j * h, 0, 1) for j in range(n)])
# 9. orthogonal polynomials
def dense_terms(terms, n):
    c = [Q(0)] * (n + 1)
    for v, deg in terms: c[n - deg] += v
    den = lcm(*(x.denominator for x in c))
    return [(int(x * den), 0) for x in c]
def cheb(n, second):
    p0, p1 = [1], [2, 0] if second else [1, 0]
    for _ in range(2, n + 1):
        p2 = [2 * x for x in p1] + [0]
        for j, x in enumerate(p0): p2[j + len(p2) - len(p0)] -= x
        p0, p1 = p1, p2
    return ints(p1)
ORTHO = {'legendre': lambda n: dense_terms([(Q((-1) ** j * comb(n, j) * comb(2 * n - 2 * j, n)), n - 2 * j) for j in range(n // 2 + 1)], n),
         'hermite': lambda n: dense_terms([(Q((-1) ** j * factorial(n) * 2 ** (n - 2 * j), factorial(j) * factorial(n - 2 * j)), n - 2 * j) for j in range(n // 2 + 1)], n),
         'laguerre': lambda n: dense_terms([(Q((-1) ** j * factorial(n) * comb(n, j), factorial(j)), j) for j in range(n + 1)], n),
         'chebyshevT': lambda n: cheb(n, False), 'chebyshevU': lambda n: cheb(n, True)}
FIRST = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 55, 60, 65, 70, 75, 80, 85, 90, 95, 100, 105, 110, 115, 120, 130, 140, 150}
OTHER = sorted(int(x) for x in rng.choice([n for n in range(21, 150) if n not in FIRST], 50, replace=False))
for label, f in ORTHO.items():
    for n in OTHER:
        add(f'{label}_{n}', 'orthogonal', f(n))
# 10. z^n - c and (z - a)^n - b
for k in range(500):
    n = int(rng.choice([3, 5, 8, 12, 20, 30, 50, 80, 120, 200, 400])); cx = k % 2 == 1
    if k % 5 < 2:
        add(f'binomial_{k:04}', 'powers', [(1, 0)] + [(0, 0)] * (n - 1) + [(ri(-10 ** 6, 10 ** 6) or 1, ri(-10 ** 6, 10 ** 6) if cx else 0)])
    else:
        n = min(n, 60); a = (ri(-5, 5), ri(-5, 5) if cx else 0)
        p = [(1, 0)]
        for _ in range(n): p = pmul(p, [(1, 0), (-a[0], -a[1])])
        p[-1] = (p[-1][0] - (ri(-999, 999) or 1), p[-1][1] - (ri(-999, 999) if cx else 0))
        add(f'shifted_{k:04}', 'powers', p)
# 11. products of structured factors
for k in range(250):
    f1 = [(1, 0)] + [(0, 0)] * (ri(3, 30) - 1) + [(-(ri(1, 99)), 0)]
    f2 = ORTHO[['chebyshevT', 'legendre', 'hermite'][k % 3]](ri(3, 20))
    f3 = from_roots([(a, b, ri(1, 3)) for a, b in distinct(ri(1, 3))])
    add(f'product_{k:04}', 'products', pmul(pmul(f1, f2), f3))
# 12. the root zero
for k in range(200):
    z = ri(1, 30); rest = [(a, b, ri(1, 2)) for a, b in distinct(ri(0, 8)) if (a, b) != (0, 0)]
    known(f'zero_{k:04}', 'zero_roots', [(0, 0, z)] + rest, ['multiple'])
# 13. roots over many scales
for k in range(250):
    n = ri(4, 20); base = int(rng.choice([2, 10, 1000])); span = ri(2, 40)
    es = sorted(set(ri(-span, span) for _ in range(n)))
    known(f'scales_{k:04}', 'scales', [(Q(base) ** e * (1 if rng.random() < 0.7 else -1), 0, 1) for e in es], ['large_dynamic_range'])
# 14. palindromic, truncated exponential, Mandelbrot, Kameny
for k in range(120):
    n = 2 * ri(3, 60); half = [ri(-9, 9) for _ in range(n // 2 + 1)]; half[0] = ri(1, 9)
    add(f'palindromic_{k:04}', 'special', ints(half + half[-2::-1]))
for n in range(5, 125, 2): add(f'exp_{n}', 'special', [(factorial(n) // factorial(n - j), 0) for j in range(n + 1)])
for e in range(1, 13):
    c2 = 9 * 10 ** (2 * e); c = [(0, 0)] * 10; c[0] = (c2, 0); c[5] = (c2 * c2, 0); c[7] = (-6 * c2, 0); c[9] = (9, 0)
    add(f'kameny_{e}', 'special', c, tags=['close_roots'])
for k in range(8):   # iterated maps p <- z p^2 + c with a constant c other than 1
    p = [(1, 0)]
    for _ in range(4 + k % 2): p = pmul(pmul(p, p), [(1, 0), (0, 0)]); p[-1] = (p[-1][0] + ri(2, 9), ri(-3, 3))
    add(f'iterated_{k}', 'special', p)
# 15. at the edges of double precision: exact binary64 coefficients scaled by powers of two
for k in range(300):
    roots = [(Q(ri(-12, 12)) or Q(1), 0, 1) for _ in range(ri(2, 8))]
    roots = list({r[0]: r for r in roots}.values())
    c = from_roots(roots); e = ri(-1000, 900)
    if max(abs(x) for x, _ in c) >= 2 ** 50: continue
    add(f'edge_{k:04}', 'edges', [(float(x) * 2.0 ** e, 0.) for x, _ in c], 'F', oracle={'kind': 'rational', 'roots': [(str(a), '0', 1) for a, _, _ in roots]}, tags=['large_dynamic_range'])
# 16. dense, large degree
for k in range(120):
    n = [320] * 60 + [640] * 40 + [1024] * 14 + [2000] * 6
    n = n[k]; cx = k % 2 == 1
    r = rng.standard_normal(n + 1); i = rng.standard_normal(n + 1) if cx else np.zeros(n + 1)
    add(f'dense_large_{n}_{k:03}', 'dense_large', list(zip(map(float, r), map(float, i))), 'F')

# top up with dense polynomials to 20 000 in all
k = 0
while len(doc['cases']) + len(new) < 20000:
    n = int(rng.choice(DEG, p=W)); cx = k % 2 == 1
    r = rng.standard_normal(n + 1); i = rng.standard_normal(n + 1) if cx else np.zeros(n + 1)
    add(f'dense_extra_{k:04}', 'dense', list(zip(map(float, r), map(float, i))), 'F'); k += 1
new = new[:20000 - len(doc['cases'])]
allc = doc['cases'] + new
# the flags `timed` and `precise` of the first 10 000 are kept; the new cases get them by the same rule
seen = {}; cnt = {}
for c in new:
    g = c['group']; seen[g] = seen.get(g, 0) + 1
    c['timed'] = bool(c['group'] == 'dense_large' and c['degree'] <= 1024 and seen[g] % 3 == 0 or seen[g] % 5 == 0)
    c['precise'] = False
    if c['timed'] and c['degree'] <= 700:
        cnt[g] = cnt.get(g, 0) + 1
        c['precise'] = cnt[g] % 3 == 0 or c['group'] == 'dense_large'
doc['cases'] = allc
(BASE / 'corpus.json').write_text(json.dumps(doc) + '\n')
from collections import Counter
print(len(allc), 'cases |', dict(Counter(c['group'] for c in allc)))
print('timed', sum(c['timed'] for c in allc), '| precise', sum(c['precise'] for c in allc), '| with exact oracle', sum(bool(c['oracle']) for c in allc), '| roots', sum(c['degree'] for c in allc))
