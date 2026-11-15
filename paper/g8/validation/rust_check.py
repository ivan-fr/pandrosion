"""Validation and timing of the Rust crate against numpy.roots (same polynomials)."""
import subprocess, sys, time, os
from fractions import Fraction
from math import lcm
import numpy as np, mpmath as mp
from numpy.polynomial import chebyshev as Ch
BIN = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'pandroots/target/release/bench')
os.makedirs('data', exist_ok=True)

def write_float(path, polys):
    with open(path, 'w') as f:
        for c in polys: f.write(' '.join('%r %r' % (float(x.real), float(x.imag)) for x in np.asarray(c, dtype=complex)) + '\n')
def write_int(path, polys):
    with open(path, 'w') as f:
        for c in polys:
            c = [Fraction(x) for x in c]; d = 1
            for x in c: d = lcm(d, x.denominator)
            f.write('int: ' + ' '.join(str(int(x * d)) for x in c) + '\n')
def run(path, reps=5, mode='g8'):
    out = subprocess.run([BIN, path, str(reps), mode], capture_output=True, text=True, check=True).stdout.split()
    info = {out[i]: out[i + 1] for i in range(0, len(out), 2)}
    res = []; cur = None
    for line in open(path + '.out'):
        t = line.split()
        if t[0] == 'poly': cur = {'complete': t[2] == '1', 'sweeps': int(t[3]), 'certificates': int(t[4]), 'exact': int(t[5]), 'roots': []}; res.append(cur)
        else: cur['roots'].append((complex(float(t[0]), float(t[1])), float(t[2]), int(t[3]), int(t[4]), t[5] == '1'))
    return info, res
def frompoly(rts):
    p = [Fraction(1)]
    for r in rts: p = [a - Fraction(r) * b for a, b in zip(p + [0], [0] + p)]
    return p

if __name__ == '__main__':
    log = open('results_rust.txt', 'w')
    def say(*a):
        s = ' '.join(str(x) for x in a); print(s, flush=True); log.write(s + '\n')
    say('=== 1. Random polynomials: Rust G8 against numpy.roots (same polynomials; times in microseconds per polynomial, best of 5) ===')
    say('kind deg | certified (isolated, equal to numpy) | sweeps | time: G8 Rust (square-free + sweeps + certificate) | numpy.roots | LAPACK alone (eigvals of the companion matrix) | numpy.roots / G8')
    allok = True; FP = [0, 0]
    for kind in ('complex', 'real'):
        for deg, cnt in [(5, 400), (10, 400), (20, 300), (40, 150), (80, 40), (160, 10), (320, 4)]:
            rng = np.random.default_rng(100 + deg)
            polys = [rng.normal(size=deg + 1) + (1j * rng.normal(size=deg + 1) if kind == 'complex' else 0) for _ in range(cnt)]
            path = 'data/%s_%d.txt' % (kind, deg); write_float(path, polys)
            info, res = run(path)
            tn = 1e9; te = 1e9
            comps = [np.diag(np.ones(deg - 1, dtype=c.dtype), -1) for c in polys]
            for A, c in zip(comps, polys): A[0, :] = -c[1:] / c[0]
            for _ in range(5):
                t0 = time.perf_counter(); refs = [np.roots(c) for c in polys]; tn = min(tn, (time.perf_counter() - t0) / cnt)
                t0 = time.perf_counter(); [np.linalg.eigvals(A) for A in comps]; te = min(te, (time.perf_counter() - t0) / cnt)
            good = 0; realok = 0
            for ref, r in zip(refs, res):
                z = np.array([x[0] for x in r['roots']]); rad = np.array([x[1] for x in r['roots']])
                ok = r['complete'] and len(z) == deg and all(x[3] == 1 and x[2] == 1 for x in r['roots'])
                if ok:
                    d = np.abs(z[:, None] - ref[None, :])
                    ok = len(set(d.argmin(axis=1))) == deg and bool(np.all(d.min(axis=1) <= rad + 1e-7 * (1 + np.abs(z))))
                good += ok
                if kind == 'real': realok += sum(x[4] for x in r['roots']) == int(np.sum(np.abs(ref.imag) < 1e-7 * (1 + np.abs(ref))))
            allok &= good == cnt and (kind != 'real' or realok == cnt)
            tg = float(info['time_us']); FP[0] += int(info['fixed_point']); FP[1] += cnt
            say('%-7s %3d | %d/%d | %.2f | %.1f (%.1f + %.1f + %.1f) | %.1f | %.1f | x%.2f' % (kind, deg, good, cnt, float(info['sweeps']), tg, float(info['t_sqfree']), float(info['t_sweeps']), float(info['t_certify']), 1e6 * tn, 1e6 * te, 1e6 * tn / tg))
    say('all certified and equal to numpy, real roots counted right:', allok, '| final count = fixed-point certificate on every disc: %d/%d polynomials' % (FP[0], FP[1]))

    say('\n=== 2. Variants in Rust (microseconds per polynomial; mean sweeps) ===')
    say('kind deg | G8 (Gauss-Seidel, binomial start) | G8 Jacobi | G8 circle start | Ehrlich-Aberth (same code, support AK)')
    for kind in ('complex', 'real'):
        for deg in (10, 20, 40, 80, 160):
            path = 'data/%s_%d.txt' % (kind, deg); line = []
            for mode in ('g8', 'jacobi', 'circle', 'aberth'):
                info, _ = run(path, mode=mode); line.append('%.1f us, %.2f sw%s' % (float(info['time_us']), float(info['sweeps']), '' if info['isolated_complete'] == info['polys'] else ' (%s/%s)' % (info['isolated_complete'], info['polys'])))
            say('%-7s %3d | ' % (kind, deg) + ' | '.join(line))

    say('\n=== 3. Hard families (exact integer coefficients) ===')
    fam = [('z^50 - 1', [1] + [0] * 49 + [-1], 50, 2), ('(z-3)^12 - 5', [int(x) for x in (np.poly1d([1, -3])**12 - 5).c], 12, 2)]
    for n in (10, 15, 20, 30): fam.append(('Wilkinson %d' % n, frompoly(range(1, n + 1)), n, n))
    for n in (10, 20, 30): fam.append(('Chebyshev %d' % n, [int(round(x)) for x in Ch.cheb2poly(np.r_[np.zeros(n), 1])[::-1]], n, n))
    fam += [('Mignotte z^12 - 2(100z-1)^2', [1] + [0] * 9 + [-20000, 400, -2], 12, 4), ('roots 10^k, k < 10', frompoly([10**k for k in range(10)]), 10, 10),
            ('roots 2^k, k < 20', frompoly([2**k for k in range(20)]), 20, 20), ('close pair 1, 1+1e-6', frompoly([1, Fraction(1000001, 1000000), -2, Fraction(1, 2), 3]), 5, 5),
            ('cluster of 5 at 1e-4', frompoly([1 + Fraction(k, 10000) for k in range(5)] + [-1, 2]), 7, 7), ('1 + z + ... + z^30', [1] * 31, 30, 0),
            ('exp truncated, degree 20', [Fraction(1, int(mp.factorial(k))) for k in range(20, -1, -1)], 20, 0), ('wide coefficients', [1, 10**8, 1, Fraction(1, 10**8), 1, 10**8, 1], 6, 2)]
    famok = True; fpf = 0
    for name, c, nd, nreal in fam:
        write_int('data/fam.txt', [c]); info, res = run('data/fam.txt', reps=5); r = res[0]; fpf += int(info['fixed_point'])
        good = r['complete'] and len(r['roots']) == nd and all(x[3] == 1 for x in r['roots']) and sum(x[4] for x in r['roots']) == nreal
        famok &= good
        say('%-28s deg %2d | %2d isolated discs, %2d proved real | float sweeps %2d, certificates %2d | max rel. radius %.1e | %7.1f us %s' % (
            name, len(c) - 1, len(r['roots']), sum(x[4] for x in r['roots']), r['sweeps'], r['certificates'], max(x[1] / max(abs(x[0]), 1e-300) for x in r['roots']), float(info['time_us']), '' if good else ' <-- FAIL'))
    write_int('data/fam.txt', [frompoly(range(1, 21))]); info, res = run('data/fam.txt')
    w20 = all(abs(x[0] - (i + 1)) <= x[1] < 1e-9 and x[4] for i, x in enumerate(res[0]['roots'])) and len(res[0]['roots']) == 20
    say('hard families all isolated, certified, real roots proved real:', famok, '| Wilkinson 20 = 1..20:', w20, '| fixed-point certificate on every disc: %d/%d families' % (fpf, len(fam)))

    say('\n=== 4. Multiplicities ===')
    rng = np.random.default_rng(5); cnt = 0; good = 0
    polys = []; wants = []
    for _ in range(60):
        rts = [int(x) for x in rng.integers(-6, 7, size=4)]; mult = [int(x) for x in rng.integers(1, 4, size=4)]
        want = {}
        for r0, k in zip(rts, mult): want[r0] = want.get(r0, 0) + k
        polys.append(frompoly([r0 for r0, k in want.items() for _ in range(k)])); wants.append(want)
    write_int('data/mult.txt', polys); info, res = run('data/mult.txt', reps=1)
    for want, r in zip(wants, res):
        good += r['complete'] and len(r['roots']) == len(want) and all(abs(x[0] - round(x[0].real)) <= x[1] + 1e-12 and want.get(round(x[0].real)) == x[2] and x[4] for x in r['roots'])
    say('exact multiplicities on %d random integer polynomials: %d' % (len(polys), good))
    # complex example (z^2-2)^2 (z-i)^3 through the float interface
    c = np.polymul(np.polymul([1, 0, -2], [1, 0, -2]), np.poly([1j, 1j, 1j])); write_float('data/m2.txt', [c]); info, res = run('data/m2.txt', reps=1)
    say('(z^2-2)^2 (z-i)^3 ->', ', '.join('%s x%d (radius %.0e)' % (np.round(x[0], 12), x[2], x[1]) for x in res[0]['roots']))
    log.close()
