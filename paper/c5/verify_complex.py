"""Numerical checks for 'Complex Geometric Root Calculators' (tests, not proofs)."""
import random, sympy as sp
from mpmath import mp, mpf, mpc, sqrt, log, exp, pi, fabs, arg, atan2, tan, re, im, conj, binomial
mp.dps = 400
random.seed(7)
OK = True
def check(name, cond, info=''):
    global OK
    OK = OK and bool(cond)
    print(('PASS ' if cond else 'FAIL ') + name + (' : ' + info if info else ''))

def coeffs(p):
    h = 1/mpf(p)
    return (1-2*h)/12, (1+h)*(3+h)/30, (121-185*h-67*h**2-h**3)/(840*(3+h))
def mfun(name, p, w):
    a, b, c = coeffs(p)
    if name == 'AD': return sqrt(w+4)/2
    if name == 'arc': return sqrt(1+a*w)
    return sqrt(1+a*w/sqrt(1+b*w/(1+c*w)))
def q(name, p, t):
    if name == 'AK': return mpf(1)
    if name == 'proj': return ((4*p+1)*t+2*p-1)/((p+1)*t+5*p-1)
    if name == 'AD': return (1+t)/2
    return sqrt(t)*mfun(name, p, (t-1)**2/t)
def phi(name, p, t):
    Q = q(name, p, t); return (t+(p-1)*Q)/(1+(p-1)*Q)
def T(name, p, t): return exp(log(t) - p*log(phi(name, p, t)))
eta = lambda t: (t-1)/(t+1)
def rnd_H():
    return exp(mpf(random.uniform(-7, 7)))*exp(mpc(0, mpf(random.uniform(-1, 1))*pi/2))
PS = [mpf('2.01'), 3, 4, 5, 7, 12, 40, 1000]

# 1. Half-plane theorem
for name, m in [('AD', 3), ('arc', 5), ('nest', 9)]:
    worst = mpf(100); inH = True
    for p in PS:
        for _ in range(600):
            t = rnd_H(); Tt = T(name, p, t)
            inH = inH and re(Tt) > 0
            worst = min(worst, log(fabs(eta(Tt)))/log(fabs(eta(t))))
    check(f'half-plane theorem, {name}', inH and worst >= m, f'min log|eta+|/log|eta| = {float(worst):.3f} >= {m}')

# 2. Boundary formulas (3.4) and the bound Arg phi(iy) in (0, pi/p]
for name in ['AD', 'arc', 'nest']:
    err = 0; lo = mpf(10); hi = mpf(0)
    for p in PS:
        for _ in range(300):
            y = exp(mpf(random.uniform(-9, 9))); t = mpc(0, y); nu = y - 1/y
            w = mpc(-2, nu); m = mfun(name, p, w); g = sqrt(w+4)
            ReN = (p-1)**2*fabs(m)**2 + (p-1)*re(conj(m)*g); ImN = 1 + (p-1)*re(m*g)
            A = arg(phi(name, p, t))
            err = max(err, fabs(A - atan2(ImN, ReN)))
            lo = min(lo, A*p/pi); hi = max(hi, A*p/pi)
            assert im(m)*im(g) >= 0
    check(f'boundary formulas and criterion, {name}', err < mpf(10)**(-300) and lo > 0 and hi <= 1,
          f'p*Arg(phi)/pi in ({float(lo):.2e}, {float(hi):.4f}]')

# 3. Circle invariance and reciprocity
bad = 0
for name in ['AD', 'arc', 'nest']:
    for p in PS:
        for _ in range(100):
            t = exp(mpc(0, mpf(random.uniform(-1, 1))*pi/2))
            bad = max(bad, fabs(fabs(phi(name, p, t)) - 1))
            t2 = rnd_H(); bad = max(bad, fabs(phi(name, p, 1/t2)*phi(name, p, t2) - 1))
check('reciprocity and invariance of the circle', bad < mpf(10)**(-300))

# 4. Constants for the nested support
hs = [mpf(i)/2000 for i in range(0, 1001)]
cs = [coeffs(1/h if h > 0 else mpf(10)**30)[2] for h in hs]
bs = [(1+h)*(3+h)/30 for h in hs]
check('c decreasing, 0 < c <= 121/2520, b <= 7/40 on h in [0,1/2]',
      all(cs[i+1] < cs[i] for i in range(1000)) and cs[-1] > 0 and cs[0] <= mpf(121)/2520 + mpf(10)**(-25) and max(bs) <= mpf(7)/40)
mn_rho = mpf(10); mn_m = mpf(10)
for _ in range(6000):
    p = 1/mpf(random.uniform(0.0005, 0.4999))
    w = mpc(-2 + exp(mpf(random.uniform(-6, 6))) - exp(mpf(-6)), mpf(random.uniform(-1, 1))*exp(mpf(random.uniform(-6, 9))))
    a, b, c = coeffs(p)
    rho2 = 1 + b*w/(1+c*w); m2 = 1 + a*w/sqrt(rho2)
    mn_rho = min(mn_rho, re(rho2)); mn_m = min(mn_m, re(m2))
check('nested: Re rho^2 > 0.61 and Re m^2 > 0.78 on Re w >= -2', mn_rho > 0.61 and mn_m > 0.78,
      f'min Re rho^2 = {float(mn_rho):.3f}, min Re m^2 = {float(mn_m):.3f}')

# 5. Newton on the disk: coefficients of 1 - (1-s)(1-s/p)^(-p)
for p in [mpf('1.5'), 3, 7]:
    al = [mpf(1)]
    for k in range(1, 400): al.append(al[-1]*(p+k-1)/(k*p))
    cf = [al[k-1]-al[k] for k in range(2, 400)]
    check(f'Newton coefficients nonnegative, partial sum <= 1 (p={p})', min(cf) >= 0 and sum(cf) <= 1)

# 6. Local constants  eta+ ~ 2^(m-1) c_m p^(1-m) eta^m
def c9(p):
    N9 = 21311*p**6+1650*p**5-21679*p**4-15532*p**3-4411*p**2-526*p-29
    return (p**2-1)*(p-2)*N9/(mpf(2)**11*3**4*5**3*7**2*(3*p+1))
for p in [3, 5, 11]:
    p = mpf(p); t = 1 + mpf(10)**(-12)*exp(mpc(0, 1))
    for name, m, cm in [('AD', 3, (p**2-1)/12), ('arc', 5, (p-2)*(p**2-1)*(3*p+1)/1440), ('nest', 9, c9(p))]:
        ratio = eta(T(name, p, t))/eta(t)**m
        check(f'local constant {name} p={p}', fabs(ratio/(2**(m-1)*cm*p**(1-m)) - 1) < mpf(10)**(-10))

# 7. Exact support, Laguerre, degree two
p = 5; t = mpc(mpf('0.7'), mpf('1.9')); c = exp(log(t)/p)
check('exact support is the mean of the mean proportionals',
      fabs((t-c)/((p-1)*(c-1)) - sum(c**k for k in range(1, p))/(p-1)) < mpf(10)**(-300))
X = mpc(2, -3); u = mpc(mpf('1.1'), mpf('0.4')); t = X/u**p; r = sqrt(t)
f, f1, f2 = u**p - X, p*u**(p-1), p*(p-1)*u**(p-2)
lag = u - p*f/(f1 + sqrt((p-1)**2*f1**2 - p*(p-1)*f*f2))
check('Laguerre iteration is the conic support a = 0',
      min(fabs(lag - u*(t+(p-1)*r)/(1+(p-1)*r)), fabs(lag - u*(t-(p-1)*r)/(1-(p-1)*r))) < mpf(10)**(-300))
r2 = sqrt(X); om = lambda v: (v-r2)/(v+r2)
okk = True
for name, m in [('AK', 2), ('AD', 3), ('proj', 4)]:
    okk = okk and fabs(om(u*phi(name, 2, X/u**2)) - om(u)**m) < mpf(10)**(-300)
check('degree two conjugacies w^2, w^3, w^4', okk)

# 8. Polynomials closing the arc case
P, R = sp.symbols('p r')
U0 = (P-1)**2*(5*P+2) - 2*P**2; B = 2*P*(P-3)*(P-1)
E = sp.expand((P-2)*U0**2 - B**2*(5*P+2)); E2 = sp.expand(2*(P-2)*(P-1)**2*U0 - B**2)
check('E, E2, U0 have nonnegative coefficients in r = p - 3',
      all(min(sp.Poly(sp.expand(e.subs(P, 3+R)), R).all_coeffs()) > 0 for e in (E, E2, U0)))

# 9. Universal start
okk = True
for p in range(2, 400):
    k = 1
    while not (mpf(2)*p/3 < 2**k < 2*p): k += 1
    okk = okk and abs(1 - mpf(p)/2**k) < mpf(1)/2
check('a power of two in (2p/3, 2p) for 2 <= p < 400', okk)
print('\nAll checks passed.' if OK else '\nSOME CHECKS FAILED')
