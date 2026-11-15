"""Stress test of the Rust crate at the edges of double precision: subnormal coefficients, coefficients and
roots near the underflow and overflow thresholds, mixed scales.  Every polynomial is taken with its double
precision coefficients as exact numbers; the reference roots are computed by mpmath with 400 digits.

A result is WRONG if complete = true and some disc does not contain exactly `count` roots of multiplicity
`mult` (this must never happen); it is WEAK if it is true but not sharp (complete = false, a disc with several
roots, or a relative radius above 1e-6).

    python3 underflow_check.py [path to the bench binary]
"""
import subprocess, sys, os
from fractions import Fraction
from math import lcm
import numpy as np, mpmath as mp
BIN = sys.argv[1] if len(sys.argv) > 1 and sys.argv[1] != 'precision' else os.path.join(os.path.dirname(os.path.abspath(__file__)), 'pandroots/target/release/bench')
os.makedirs('data', exist_ok=True)
mp.mp.dps = 400
SUB = 5e-324

def run(c, tol=None):
    with open('data/edge.txt', 'w') as f:
        if all(isinstance(x, int) for x in c): f.write('int: ' + ' '.join(str(x) for x in c) + '\n')
        else: f.write(' '.join('%r %r' % (float(np.real(x)), float(np.imag(x))) for x in c) + '\n')
    out = subprocess.run([BIN, 'data/edge.txt', '1', 'g8'] + ([repr(tol)] if tol else []), capture_output=True, text=True)
    if out.returncode != 0: return None, 'crash: ' + out.stderr.strip()[-200:]
    roots = []; complete = None
    for line in open('data/edge.txt.out'):
        t = line.split()
        if t[0] == 'poly': complete = t[2] == '1'
        else:
            # The crate prints the shortest decimal that reads back as the same double.  The disc is the one
            # of the double, not of that decimal: the two differ by up to 1e-16 of the centre, which is more
            # than the radius of some discs since 0.11.0 (revision 9; up to revision 8 the decimal was read
            # as an exact number, and every radius was far above that difference).  The decimal output with
            # a tolerance (digits beyond a double) is exact as printed and is read as such.
            exact = lambda s: mp.mpf(float(s)) if tol is None and mp.isfinite(mp.mpf(s)) and float(s) not in (float('inf'), float('-inf')) else mp.mpf(s)
            roots.append((exact(t[0]), exact(t[1]), exact(t[2]), int(t[3]), int(t[4]), t[5] == '1'))
    return (roots, complete), None

def exact_roots(c):
    """Distinct roots with multiplicities, from the exact double coefficients."""
    c = [x for x in c]
    while c and c[0] == 0: c = c[1:]
    n0 = 0
    while c and c[-1] == 0: c = c[:-1]; n0 += 1
    fr = lambda v: mp.mpf(v) if isinstance(v, int) else mp.mpf(Fraction(float(v)).numerator) / Fraction(float(v)).denominator
    coeffs = [mp.mpc(fr(x), 0) if isinstance(x, int) else mp.mpc(fr(np.real(x)), fr(np.imag(x))) for x in c]
    r = mp.polyroots(coeffs, maxsteps=2000, extraprec=4000) if len(coeffs) > 1 else []
    r = list(r) + [mp.mpc(0)] * n0
    groups = []
    for x in r:
        for g in groups:
            if abs(x - g[0]) <= mp.mpf(10) ** -150 * max(abs(x), abs(g[0])) or (x == 0 and g[0] == 0): g[1] += 1; break
        else: groups.append([x, 1])
    return groups

def judge(c, tol=None, true=None):
    res, err = run(c, tol)
    if err: return 'WEAK', err
    roots, complete = res
    if not complete: return 'WEAK', 'complete = false'
    true = true if true is not None else exact_roots(c); weak = None; want = tol if tol else 1e-6
    for (re, im, rad, mult, count, real) in roots:
        z = mp.mpc(re, im)
        if not mp.isfinite(rad): return 'WEAK', 'infinite radius'
        inside = [g for g in true if abs(g[0] - z) <= mp.mpf(rad)]
        if len(inside) != count or any(g[1] != mult for g in inside):
            return 'WRONG', 'disc %s radius %s: %d roots inside (mult %s), announced %d of mult %d' % (mp.nstr(z, 12), mp.nstr(rad, 3), len(inside), [g[1] for g in inside], count, mult)
        if real and any(mp.im(g[0]) != 0 for g in inside): return 'WRONG', 'root flagged real is not real'
        if count != 1: weak = 'a disc with %d roots' % count
        elif rad > want * abs(z) and abs(z) > 0: weak = 'relative radius %s' % mp.nstr(rad / abs(z), 3)
    if sum(m * k for (_, _, _, m, k, _) in roots) != sum(g[1] for g in true): return 'WRONG', 'the counts do not add up to the degree'
    return ('WEAK', weak) if weak else ('ok', '')

def cases():
    rng = np.random.default_rng(2026); out = []
    out.append(('z^2 - 1e-320 (subnormal constant)', [1, 0, -1e-320]))
    out.append(('all coefficients subnormal: 1e-310 (1, 3, -2)', [1e-310, 3e-310, -2e-310]))
    out.append(('4.9e-324 (z^2 - 3 z + 1) scaled to the smallest subnormals', [2 * SUB, -6 * SUB, 2 * SUB]))
    out.append(('z^3 - 1e-250 z (normal coefficients, values underflow)', [1, 0, -1e-250, 0]))
    out.append(('z^3 - 1e-250 z + 1e-320', [1, 0, -1e-250, 1e-320]))
    out.append(('z^4 - 1e-300 z^2 + 1e-320', [1, 0, -1e-300, 0, 1e-320]))
    out.append(('1e-320 z^2 - 1 (subnormal leading)', [1e-320, 0, -1]))
    out.append(('1e-320 z^3 + z - 1', [1e-320, 0, 1, -1]))
    out.append(('1e300 z^2 - 1e-300', [1e300, 0, -1e-300]))
    out.append(('z^2 - 1e300 z + 1e-300 (roots 1e300 and 1e-600)', [1, -1e300, 1e-300]))
    out.append(('1e-200 z^2 - 3e100 z + 1e300', [1e-200, -3e100, 1e300]))
    out.append(('z^2 + (1e-160 + 1e-160 i) z + 1e-320 i', [1, complex(1e-160, 1e-160), complex(0, 1e-320)]))
    out.append(('z^5 - 1e-320', [1, 0, 0, 0, 0, -1e-320]))
    out.append(('1e308 z^2 - 1e308', [1e308, 0, -1e308]))
    out.append(('1.7e308 z^3 + 1e308 z - 1.5e308', [1.7e308, 0, 1e308, -1.5e308]))
    for i in range(40):                                                    # random, all coefficients subnormal
        m = int(rng.integers(2, 9)); k = rng.integers(1, 2000, size=m + 1) * rng.choice([-1, 1], size=m + 1)
        out.append(('random subnormal integers x 4.9e-324, degree %d (#%d)' % (m, i), [float(x) * SUB for x in k]))
    for i in range(40):                                                    # random, complex, near the underflow threshold
        m = int(rng.integers(2, 9)); s = 10.0 ** rng.uniform(-323, -300)
        out.append(('random complex coefficients of size %.0e, degree %d (#%d)' % (s, m, i), list((rng.normal(size=m + 1) + 1j * rng.normal(size=m + 1)) * s)))
    for i in range(40):                                                    # roots of very small or very large modulus
        m = int(rng.integers(2, 7)); e = rng.uniform(-300, 300) / m; r = 10.0 ** e
        out.append(('random real, roots of modulus about 1e%+.0f, degree %d (#%d)' % (e, m, i), [float(rng.normal()) * r ** j for j in range(m + 1)]))
    for i in range(40):                                                    # wide coefficients
        m = int(rng.integers(2, 7))
        out.append(('random, coefficients from 1e-300 to 1e300, degree %d (#%d)' % (m, i), [float(rng.normal()) * 10.0 ** rng.uniform(-300, 300) for _ in range(m + 1)]))
    for i in range(20):                                                    # near overflow
        m = int(rng.integers(2, 7))
        out.append(('random, coefficients near 1e308, degree %d (#%d)' % (m, i), [float(rng.uniform(-1.7, 1.7)) * 1e308 for _ in range(m + 1)]))
    return out

def precision_cases():
    """Polynomials with integer coefficients, solved to 30 and 80 digits."""
    rng = np.random.default_rng(7); out = []
    def frompoly(rts):
        p = [Fraction(1)]
        for r in rts: p = [a - Fraction(r) * b for a, b in zip(p + [0], [0] + p)]
        d = 1
        for x in p: d = lcm(d, x.denominator)
        return [int(x * d) for x in p]
    for m in (5, 10, 20, 40):
        for i in range(5): out.append(('random integers in [-99, 99], degree %d (#%d)' % (m, i), [int(x) for x in rng.integers(-99, 100, size=m + 1)] ))
    for n in (10, 20, 30): out.append(('Wilkinson %d' % n, frompoly(range(1, n + 1))))
    out.append(('Mignotte z^12 - 2(100z-1)^2', [1] + [0] * 9 + [-20000, 400, -2]))
    out.append(('Mignotte z^20 - 2(10^6 z-1)^2', [1] + [0] * 17 + [-2 * 10**12, 4 * 10**6, -2]))
    out.append(('z^50 - 1', [1] + [0] * 49 + [-1]))
    out.append(('roots 1, 1 + 1e-20, 2 (closer than double precision)', frompoly([1, 1 + Fraction(1, 10**20), 2])))
    out.append(('roots 1 + k 1e-25, k < 4, and -1', frompoly([1 + Fraction(k, 10**25) for k in range(4)] + [-1])))
    out.append(('real pair sqrt(2) +- 1e-30 i (z^2 - 2)^2 + 8e-60 ...', [10**60, 0, -4 * 10**60, 0, 4 * 10**60 + 8]))
    out.append(('(z^2 - 2)(z^2 - 2 - 1e-40)', [10**40, 0, -4 * 10**40 - 1, 0, 4 * 10**40 + 2]))
    out.append(('exp truncated, degree 20 (times 20!)', [int(mp.factorial(20) / mp.factorial(k)) for k in range(20, -1, -1)]))
    out = [(n, c) for n, c in out if c[0] != 0 and c[-1] != 0]
    return out

if __name__ == '__main__':
    log = open('results_edge.txt', 'w')
    def say(*a):
        s = ' '.join(str(x) for x in a); print(s, flush=True); log.write(s + '\n')
    tally = {'ok': 0, 'WEAK': 0, 'WRONG': 0}
    for name, c in ([] if 'precision' in sys.argv else cases()):
        if not all(np.isfinite(complex(x)) for x in c): continue
        v, why = judge(c); tally[v] += 1
        if v != 'ok': say('%-5s %s | %s' % (v, name, why))
    say('edges of double precision, %d polynomials: %d sharp and right, %d true but weak, %d WRONG' % (sum(tally.values()), tally['ok'], tally['WEAK'], tally['WRONG']))
    tally = {'ok': 0, 'WEAK': 0, 'WRONG': 0}
    for name, c in ([] if 'precision' in sys.argv else cases()):                      # the same with 20 digits asked: multiprecision centres, any exponent
        if not all(np.isfinite(complex(x)) for x in c): continue
        v, why = judge(c, 1e-20); tally[v] += 1
        if v != 'ok': say('%-5s tol 1e-20 | %s | %s' % (v, name, why))
    say('the same polynomials with tolerance 1e-20 (decimal output): %d certified within the tolerance, %d true but weak, %d WRONG' % (tally['ok'], tally['WEAK'], tally['WRONG']))
    import time
    for tol in (1e-30, 1e-80):
        tally = {'ok': 0, 'WEAK': 0, 'WRONG': 0}; t0 = time.perf_counter(); tr = 0.0
        for name, c in precision_cases():
            true = exact_roots(c); t1 = time.perf_counter(); v, why = judge(c, tol, true); tr += time.perf_counter() - t1; tally[v] += 1
            if v != 'ok': say('%-5s tol %g | %s | %s' % (v, tol, name, why))
        say('tolerance %g, %d polynomials: %d certified within the tolerance, %d true but weak, %d WRONG (pandroots: %.1f s in all, process start included)' % (tol, sum(tally.values()), tally['ok'], tally['WEAK'], tally['WRONG'], tr))
