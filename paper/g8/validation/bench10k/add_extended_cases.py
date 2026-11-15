"""Extended panel (benchmark v2): more families, more cluster shapes, larger degrees.

Appended to corpus.json after add_regression_cases.py.  Every case is marked `supplemental` (so that the
historical denominators, 462 polynomials and the sub-corpus of 100, do not move) and `extended`, with a
`group` used by aggregate_extended.py.  Coefficients are exact: Gaussian integers ('I') or binary64 ('F').
Deterministic (seed 20261115)."""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm, factorial, comb
import hashlib, json
import numpy as np

BASE = Path(__file__).resolve().parent
doc = json.loads((BASE / 'corpus.json').read_text())
doc['cases'] = [c for c in doc['cases'] if not c.get('extended')]
OUT = BASE / 'cases'
new = []

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
    r = [(0, 0)] * (len(a) + len(b) - 1)
    r = [list(x) for x in r]
    for i, (x, y) in enumerate(a):
        for j, (u, v) in enumerate(b):
            r[i + j][0] += x * u - y * v
            r[i + j][1] += x * v + y * u
    return [tuple(x) for x in r]

def add(name, group, family, coeff, kind='I', oracle=None, tags=None):
    n = len(coeff) - 1
    assert n >= 1 and coeff[0] != (0, 0), name
    content = f'{kind} {n}\n' + ''.join(f'{r!r} {i!r}\n' if kind == 'F' else f'{r} {i}\n' for r, i in coeff)
    path = OUT / ('x_' + name + '.poly'); path.write_text(content)
    new.append(dict(id='x_' + name, family=family, group=group, degree=n, kind=kind, path=str(path.relative_to(BASE)),
                    sha256=hashlib.sha256(content.encode()).hexdigest(), oracle=oracle, tags=(tags or []) + ['extended'],
                    supplemental=True, extended=True))

def known(name, group, roots, tags=None):
    roots = [(str(Q(r)), str(Q(i)), m) for r, i, m in roots]
    add(name, group, 'x_' + group, from_roots(roots), oracle={'kind': 'rational', 'roots': roots}, tags=tags)

ints = lambda v: [(int(x), 0) for x in v]
rng = np.random.default_rng(20261115)
others = [(-1, 0, 1), (2, 0, 1), (0, 1, 1)]

# 1. clusters of K roots on a line, K = 2, 3, 4, 8, at several separations
for k in [2, 3, 4, 8]:
    for step in [6, 12, 20, 40]:
        eps = Q(1, 10 ** step)
        known(f'cluster_line_K{k}_1e-{step}', 'cluster_line', [(1 + j * eps, 0, 1) for j in range(k)] + others, ['close_roots'])
# 2. clusters that are not on a line (Gaussian lattice points), and not near 1
lattice = [(0, 0), (1, 0), (0, 1), (-1, 2), (2, -1), (-2, -1), (1, 3), (3, 1)]
for k in [3, 5, 8]:
    for step in [8, 16, 30]:
        eps = Q(1, 10 ** step)
        known(f'cluster_plane_K{k}_1e-{step}', 'cluster_plane', [(Q(1, 2) + a * eps, Q(1, 3) + b * eps, 1) for a, b in lattice[:k]] + others, ['close_roots'])
for centre, label in [(1000, 'far'), (Q(1, 1000), 'near0')]:
    for step in [10, 25]:
        eps = Q(1, 10 ** step) * centre
        known(f'cluster_{label}_K4_1e-{step}', 'cluster_plane', [(centre + a * eps, b * eps, 1) for a, b in lattice[:4]] + others, ['close_roots'])
# 3. two and three clusters in one polynomial
for step in [8, 20]:
    eps = Q(1, 10 ** step)
    known(f'clusters_two_1e-{step}', 'cluster_several', [(1 + j * eps, 0, 1) for j in range(3)] + [(-2 + a * eps, b * eps, 1) for a, b in lattice[:4]] + [(0, 1, 1)], ['close_roots'])
    known(f'clusters_three_1e-{step}', 'cluster_several', [(1 + j * eps, 0, 1) for j in range(2)] + [(-2 + a * eps, b * eps, 1) for a, b in lattice[:3]] + [(a * eps, 3 + b * eps, 1) for a, b in lattice[:5]], ['close_roots'])
# 4. a shifted power inside a polynomial: K roots on a circle of radius 10^-step around 1
for k in [3, 5, 9]:
    for step in [5, 12, 25]:
        c = 10 ** step
        pw = [(1, 0)]
        for _ in range(k): pw = pmul(pw, [(c, 0), (-c, 0)])
        pw[-1] = (pw[-1][0] - 1, 0)
        add(f'power_ring_K{k}_1e-{step}', 'cluster_ring', 'x_cluster_ring', pmul(pmul(pw, [(1, 0), (2, 0)]), [(1, 0), (-3, 0)]), tags=['close_roots'])
# 5. Mignotte: more degrees and sizes, and three close roots z^n - (a z - 1)^3
for n in [8, 16, 32, 64]:
    for a in [10 ** 3, 10 ** 6, 10 ** 12]:
        c = [(0, 0)] * (n + 1); c[0] = (1, 0); c[-3] = (-2 * a * a, 0); c[-2] = (4 * a, 0); c[-1] = (-2, 0)
        add(f'mignotte_{n}_1e{len(str(a)) - 1}', 'mignotte', 'x_mignotte', c, tags=['close_roots'])
for n in [15, 30]:
    for a in [10 ** 3, 10 ** 6]:
        c = [(0, 0)] * (n + 1); c[0] = (1, 0)
        for j, v in enumerate([-a ** 3, 3 * a * a, -3 * a, 1]): c[n - 3 + j] = (c[n - 3 + j][0] + v, 0)
        add(f'mignotte3_{n}_1e{len(str(a)) - 1}', 'mignotte', 'x_mignotte', c, tags=['close_roots'])
# 6. Wilkinson at more degrees, and rounded to doubles
for n in [15, 25, 40, 60, 100]:
    known(f'wilkinson_{n}', 'wilkinson', [(j, 0, 1) for j in range(1, n + 1)])
for n in [15, 40]:
    add(f'wilkinson_rounded_{n}', 'wilkinson', 'x_wilkinson', [(float(r), 0.) for r, i in from_roots([(j, 0, 1) for j in range(1, n + 1)])], 'F')
# 7. orthogonal polynomials with integer coefficients
def legendre(n):   # 2^n P_n: integer coefficients
    return [(Q((-1) ** j * comb(n, j) * comb(2 * n - 2 * j, n)), n - 2 * j) for j in range(n // 2 + 1)]
def hermite(n):    # physicists' H_n
    return [(Q((-1) ** j * factorial(n) * 2 ** (n - 2 * j), factorial(j) * factorial(n - 2 * j)), n - 2 * j) for j in range(n // 2 + 1)]
def laguerre(n):   # n! L_n
    return [(Q((-1) ** j * factorial(n) * comb(n, j), factorial(j)), j) for j in range(n + 1)]
def dense(terms, n):
    c = [Q(0)] * (n + 1)
    for v, deg in terms: c[n - deg] += v
    den = lcm(*(x.denominator for x in c))
    return [(int(x * den), 0) for x in c]
for label, f in [('legendre', legendre), ('hermite', hermite), ('laguerre', laguerre)]:
    for n in [20, 40, 80]:
        add(f'{label}_{n}', 'orthogonal', 'x_orthogonal', dense(f(n), n))
p0, p1 = [1], [2, 0]   # Chebyshev of the second kind
for _ in range(2, 61):
    p2 = [2 * x for x in p1] + [0]
    for j, x in enumerate(p0): p2[j + len(p2) - len(p0)] -= x
    p0, p1 = p1, p2
add('chebyshev_U_60', 'orthogonal', 'x_orthogonal', ints(p1))
# 8. Mandelbrot polynomials p_{k+1} = z p_k^2 + 1 (degree 2^k - 1), a classical hard family
p = [(1, 0)]
for k in range(1, 9):
    p = pmul(pmul(p, p), [(1, 0), (0, 0)]); p[-1] = (p[-1][0] + 1, 0)
    if k >= 5: add(f'mandelbrot_{len(p) - 1}', 'mandelbrot', 'x_mandelbrot', p)
# 9. truncated exponential, n! sum z^j / j!
for n in [20, 40, 80, 160]:
    add(f'exp_{n}', 'exponential', 'x_exponential', [(factorial(n) // factorial(n - j), 0) for j in range(n + 1)])
# 10. Kameny: (c^2 z^2 - 3)^2 + c^2 z^9
for e in [1, 3, 6]:
    c2 = 10 ** (2 * e)
    c = [(0, 0)] * 10; c[0] = (c2, 0); c[5] = (c2 * c2, 0); c[7] = (-6 * c2, 0); c[9] = (9, 0)
    add(f'kameny_1e{e}', 'kameny', 'x_kameny', c, tags=['close_roots'])
# 11. few terms, large degree
for n in [100, 500, 2000]:
    c = [(0, 0)] * (n + 1); c[0] = (1, 0); c[-2] = (1, 0); c[-1] = (1, 0)
    add(f'trinomial_{n}', 'sparse', 'sparse_real', c, tags=['sparse'])
c = [(0, 0)] * 401; c[0] = (1, 0); c[400 - 17] = (3, 0); c[-1] = (-5, 0)
add('lacunary_400', 'sparse', 'sparse_real', c, tags=['sparse'])
c = [(0, 0)] * 301; c[0] = (1, 0); c[150] = (-1, 2); c[-1] = (3, 0)
add('lacunary_complex_300', 'sparse', 'sparse_complex', c, tags=['sparse'])
# 12. many scales
known('scales_10^k_21', 'scales', [(Q(10) ** k, 0, 1) for k in range(-10, 11)], ['large_dynamic_range'])
known('scales_clusters', 'scales', [(Q(1, 10 ** 6) * (1 + Q(j, 10 ** 9)), 0, 1) for j in range(3)] + [(1 + Q(j, 10 ** 9), 0, 1) for j in range(3)] + [(10 ** 6 + Q(j, 10 ** 3), 0, 1) for j in range(3)], ['large_dynamic_range', 'close_roots'])
# 13. multiplicities
known('multiple_30_20', 'multiplicity', [(1, 0, 30), (-1, 0, 20)], ['multiple'])
known('multiple_conjugate', 'multiplicity', [(0, 1, 10), (0, -1, 10), (2, 0, 5)], ['multiple'])
for k in range(4):
    vals = rng.choice(np.arange(-12, 13), 9, replace=False)
    known(f'multiple_random_big_{k}', 'multiplicity', [(int(x), int(rng.integers(-3, 4)), int(rng.integers(1, 9))) for x in vals], ['multiple'])
known('multiple_and_cluster', 'multiplicity', [(1, 0, 4), (1 + Q(1, 10 ** 10), 0, 1), (1 + Q(2, 10 ** 10), 0, 1), (-3, 0, 2)], ['multiple', 'close_roots'])
# 14. random real roots (ill-conditioned), palindromic polynomials
for n in [20, 40]:
    known(f'real_roots_{n}', 'real_roots', [(Q(int(rng.integers(-10 ** 6, 10 ** 6)), 10 ** 5), 0, 1) for _ in range(n)])
for n in [50, 100]:
    half = [int(x) for x in rng.integers(-9, 10, n // 2 + 1)]; half[0] = 1
    add(f'palindromic_{n}', 'palindromic', 'x_palindromic', ints(half + half[-2::-1]))
# 15. larger dense polynomials (same law as the main corpus), for the doubles and for high precision
for domain in ['real', 'complex']:
    for n, count in [(2000, 1), (640, 2), (320, 4)]:
        for j in range(count):
            r = rng.standard_normal(n + 1)
            i = rng.standard_normal(n + 1) if domain == 'complex' else np.zeros(n + 1)
            add(f'random_{domain}_{n}_{j}', 'dense_large', f'random_{domain}', list(zip(map(float, r), map(float, i))), 'F')
    for n in [320, 640]:
        r = rng.integers(-99, 100, n + 1); r[0] = 1
        i = rng.integers(-99, 100, n + 1) if domain == 'complex' else np.zeros(n + 1, dtype=int)
        add(f'integer_{domain}_{n}', 'dense_large', f'integer_{domain}', [(int(a), int(b)) for a, b in zip(r, i)])

doc['cases'] += new
doc['extended_cases'] = len(new)
(BASE / 'corpus.json').write_text(json.dumps(doc, indent=2) + '\n')
from collections import Counter
print(len(new), 'extended cases:', dict(Counter(c['group'] for c in new)), '| largest degree', max(c['degree'] for c in new))
