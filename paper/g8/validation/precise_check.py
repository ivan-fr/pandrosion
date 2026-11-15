"""Validation and timing of the precise functions of pandroots 0.5.0 (all_roots_exact_precise), default
step and Options::full_order, against reference roots computed independently with mpmath.

Part A: 30 polynomials with integer coefficients at the tolerances 1e-30 and 1e-80, both modes; references
by mpmath.polyroots at 200 digits.  Part B: one call on larger polynomials at 30, 80 and 280 digits, both
modes (best of REPS runs); references by Newton's method in mpmath from numpy's roots, or exact.

A disc passes when: the output is complete, every disc has count 1 and multiplicity 1, its radius is at
most tol |centre|, and it contains exactly one reference root, the matching being one to one.
Run from this folder:  python3 precise_check.py   (writes results_precise.txt)
"""
import os, subprocess, sys, time
from fractions import Fraction
from math import lcm
import numpy as np, mpmath as mp
from numpy.polynomial import chebyshev as Ch

HERE = os.path.dirname(os.path.abspath(__file__))
BIN = os.path.join(HERE, 'hp_bench/target/release/hp_bench')
DATA = os.path.join(HERE, 'data_precise'); os.makedirs(DATA, exist_ok=True)
LOG = open(os.path.join(HERE, 'results_precise.txt'), 'w')

def say(*a):
    s = ' '.join(str(x) for x in a); print(s, flush=True); LOG.write(s + '\n')

def frompoly(rts):
    p = [Fraction(1)]
    for r in rts: p = [a - Fraction(r) * b for a, b in zip(p + [0], [0] + p)]
    return p

def ints(c):
    c = [Fraction(x) for x in c]; d = 1
    for x in c: d = lcm(d, x.denominator)
    return [int(x * d) for x in c]

def run(polys, tol, mode, reps, tag):
    path = os.path.join(DATA, tag + '.txt')
    with open(path, 'w') as f:
        for c in polys: f.write('int: ' + ' '.join(str(x) for x in c) + '\n')
    out = subprocess.run([BIN, path, repr(tol), mode, str(reps)], capture_output=True, text=True, check=True).stdout.strip().split('\n')
    stats = [dict(zip(l.split()[0::2], map(float, l.split()[1::2]))) for l in out]
    res = []; cur = None
    for line in open(path + '.' + mode + '.out'):
        t = line.split()
        if t[0] == 'poly': cur = {'complete': t[2] == '1', 'discs': []}; res.append(cur)
        else: cur['discs'].append((mp.mpc(mp.mpf(t[0]), mp.mpf(t[1])), mp.mpf(t[2]), int(t[3]), int(t[4]), t[5] == '1'))
    return stats, res

def check(res, refs, referr, tol):
    """(passes, largest radius / (tol |centre|)): one reference root in each disc, one to one."""
    m = len(refs)
    ok = res['complete'] and len(res['discs']) == m and all(d[2] == 1 and d[3] == 1 for d in res['discs'])
    worst = mp.mpf(0); used = set()
    for z, r, _, _, _ in res['discs']:
        if abs(z) > 0: worst = max(worst, r / (tol * abs(z)))
        inside = [j for j, x in enumerate(refs) if abs(x - z) <= r + referr]
        if len(inside) != 1 or inside[0] in used: ok = False
        used.update(inside)
    return ok and worst <= 1 and len(used) == m, float(worst)

def ref_polyroots(c, dps=200):
    with mp.workdps(dps):
        r, err = mp.polyroots([mp.mpf(x) for x in c], maxsteps=2000, extraprec=4 * dps, error=True)
    assert err < mp.mpf(10) ** (-(dps - 40)), err
    return list(r), mp.mpf(10) ** (-(dps - 40))

def ref_newton(c, dps):
    """numpy's roots polished by Newton's method at dps digits; distinct and converged, so they are all the roots."""
    z0 = np.roots(np.array([float(x) for x in c]))
    with mp.workdps(dps + 20):
        cc = [mp.mpf(x) for x in c]; out = []
        for z in z0:
            z = mp.mpc(z)
            for _ in range(60):
                p, dp = mp.polyval(cc, z, derivative=True)
                h = p / dp; z -= h
                if abs(h) < mp.mpf(10) ** (-(dps + 5)) * max(1, abs(z)): break
            else: raise RuntimeError('Newton did not converge')
            out.append(z)
        sep = min(abs(a - b) for i, a in enumerate(out) for b in out[i + 1:])
        assert sep > mp.mpf(10) ** -8, 'two polished roots coincide'
    return out, mp.mpf(10) ** (-dps)

if __name__ == '__main__':
    mp.mp.dps = 340  # the centres have up to 290 digits: parse and compare them at full precision
    rng = np.random.default_rng(20261115)
    A = []
    for deg in (5, 10, 20, 40):
        for i in range(4): A.append(('random integer, degree %d' % deg, [int(rng.integers(1, 51))] + [int(x) for x in rng.integers(-50, 51, size=deg)]))
    for n in (10, 15, 20, 30): A.append(('Wilkinson %d' % n, ints(frompoly(range(1, n + 1)))))
    for n in (10, 20, 30): A.append(('Chebyshev %d' % n, [int(round(x)) for x in Ch.cheb2poly(np.r_[np.zeros(n), 1])[::-1]]))
    A.append(('Mignotte z^12 - 2(100z-1)^2', [1] + [0] * 9 + [-20000, 400, -2]))
    A.append(('Mignotte z^12 - 2(10^8 z-1)^2', [1] + [0] * 9 + [-2 * 10**16, 4 * 10**8, -2]))
    A.append(('roots 1, 1+10^-20, -2, 3, 1/2', ints(frompoly([1, 1 + Fraction(1, 10**20), -2, 3, Fraction(1, 2)]))))
    A.append(('roots 1, 1+10^-40, -1, 2', ints(frompoly([1, 1 + Fraction(1, 10**40), -1, 2]))))
    A.append(('four roots 10^-25 apart, and 5', ints(frompoly([1 + Fraction(k, 10**25) for k in range(4)] + [5]))))
    A.append(('roots 10^k, k < 10', ints(frompoly([10**k for k in range(10)]))))
    A.append(('z^50 - 1', [1] + [0] * 49 + [-1]))
    A.append(('z^2 - 2', [1, 0, -2]))
    say('=== A. %d polynomials with integer coefficients: all_roots_exact_precise against mpmath.polyroots (200 digits) ===' % len(A))
    refs = []
    for name, c in A: refs.append(ref_polyroots(c))
    for tol in (1e-30, 1e-80):
        for mode in ('default', 'full'):
            stats, res = run([c for _, c in A], tol, mode, 1, 'A_%g_%s' % (tol, mode))
            npass = 0; worst = 0; tot = 0; fails = []
            for (name, c), (rf, re_), st, r in zip(A, refs, stats, res):
                ok, w = check(r, rf, re_, tol); npass += ok; worst = max(worst, w); tot += st['ms']
                if not ok or st['within_tol'] != 1: fails.append('%s (pass %s, within_tol %d)' % (name, ok, st['within_tol']))
            say('tol %g, %-7s | %d/%d pass | largest radius / (tol |z|) %.2g | total %.0f ms | precise sweeps %s' % (
                tol, mode, npass, len(A), worst, tot, ' '.join(str(int(s['precise'])) for s in stats)))
            for f in fails: say('   FAIL', f)

    say('\n=== B. One call, best of 3 (ms); precise sweeps and largest number of bits in brackets ===')
    B = []
    for deg in (60, 160, 320): B.append(('dense integer, degree %d' % deg, [int(rng.integers(1, 101))] + [int(x) for x in rng.integers(-100, 101, size=deg)], (30, 80, 280)))
    B.append(('z^1000 - 1', [1] + [0] * 999 + [-1], (80, 280)))
    B.append(('Wilkinson 30', ints(frompoly(range(1, 31))), (80,)))
    B.append(('Mignotte z^12 - 2(10^8 z-1)^2', [1] + [0] * 9 + [-2 * 10**16, 4 * 10**8, -2], (30,)))
    say('polynomial | digits | default | full_order | both checked against the reference')
    for name, c, dl in B:
        for digits in dl:
            tol = 10.0 ** -digits; dps = digits + 30
            if name.startswith('z^1000'):
                with mp.workdps(dps + 20): rf = [mp.expjpi(mp.mpf(2 * k) / 1000) for k in range(1000)]
                re_ = mp.mpf(10) ** (-dps)
            elif name.startswith('dense'): rf, re_ = ref_newton(c, dps)
            else: rf, re_ = ref_polyroots(c, max(200, dps + 60))
            line = []; allok = True
            for mode in ('default', 'full'):
                stats, res = run([c], tol, mode, 3, 'B_%s_%d_%s' % (name.split(',')[0].replace(' ', '_').replace('^', ''), digits, mode))
                ok, w = check(res[0], rf, re_, tol); allok &= ok and stats[0]['within_tol'] == 1
                line.append('%9.1f (%d, %d)' % (stats[0]['ms'], stats[0]['precise'], stats[0]['bits']))
            say('%-30s | %3d | %s | %s | %s' % (name, digits, line[0], line[1], 'pass' if allok else 'FAIL'))
    LOG.close()
