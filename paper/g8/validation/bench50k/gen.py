"""50,000 polynomials in eight families, coefficients written as exact doubles (highest degree first)."""
import numpy as np
rng = np.random.default_rng(20261116)
def w(f, c):
    c = np.asarray(c, complex); f.write(' '.join('%r %r' % (float(x.real), float(x.imag)) for x in c)+'\n')
def from_roots_int(roots):            # exact integer / Gaussian-integer arithmetic
    c = [1+0j]
    for r in roots:
        n = [0j]*(len(c)+1)
        for i, x in enumerate(c): n[i] += x; n[i+1] -= x*r
        c = n
    return c
fam = {}
def add(name, n, make):
    with open('fam_%s.txt' % name, 'w') as f, open('truth_%s.txt' % name, 'w') as g:
        for _ in range(n):
            c, truth = make(); w(f, c); g.write((' '.join('%r %r' % (z.real, z.imag) for z in truth) if truth is not None else '-')+'\n')
    fam[name] = n
add('real_gauss', 12000, lambda: (rng.standard_normal(rng.integers(2, 41)+1), None))
add('complex_gauss', 9000, lambda: ((lambda d: rng.standard_normal(d+1)+1j*rng.standard_normal(d+1))(rng.integers(2, 41)), None))
add('small_int', 6000, lambda: ((lambda c: c if c[0] != 0 else np.r_[1, c[1:]])(rng.integers(-9, 10, rng.integers(2, 31)+1).astype(float)), None))
add('kac_pm1', 5000, lambda: (rng.choice([-1.0, 1.0], rng.integers(5, 61)+1), None))
add('wide_scale', 5000, lambda: ((lambda d: rng.standard_normal(d+1)*10.0**rng.uniform(-20, 20, d+1))(rng.integers(2, 31)), None))
def int_roots():
    k = rng.integers(2, 9); r = [complex(int(x)) for x in rng.integers(-6, 7, k)]; return from_roots_int(r), r
add('integer_roots_mult', 6000, int_roots)        # repeated roots happen often
def gauss_roots():
    k = rng.integers(2, 7); r = [complex(int(a), int(b)) for a, b in rng.integers(-4, 5, (k, 2))]; return from_roots_int(r), r
add('gaussian_roots_mult', 4000, gauss_roots)
def cluster():
    k = rng.integers(3, 9); base = rng.integers(-3, 4); eps = 10.0**rng.uniform(-4, -1)
    r = [base+eps*j for j in range(k)]; return np.poly(r), None    # coefficients rounded: no exact truth
add('real_cluster', 3000, cluster)
print(fam, sum(fam.values()))
