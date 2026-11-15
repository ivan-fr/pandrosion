"""Checks for the three-mean support in the complex plane (tests and exact recomputations).
Sections 1-7: 300-digit numerics on random samples. Section 8: exact polynomial certificates."""
import random, sympy as sp
from mpmath import mp, mpf, mpc, sqrt, log, exp, pi, fabs, arg, re, im, atanh, tan, atan2
mp.dps = 300
random.seed(29)
OK = True
def check(name, cond, info=''):
    global OK
    OK = OK and bool(cond)
    print(('PASS ' if cond else 'FAIL ') + name + (' : ' + info if info else ''))

def consts(p):
    p = mpf(p)
    m = (p-2)*(47*p**2+21*p+4)/(60*p*(4*p**2-1)); g = 16*(p+1)*(4*p**2-1)/(15*p*(5*p**2+4))
    n = 49*p*(p+1)*(p**2-4)/(10*(4*p**2-1)*(5*p**2+4)); d = (5*p**2+4)/(84*p**2)
    s4 = sqrt(1-4*d)
    return m, g, n, d, (1-2*d+s4)/(2*d), (1-2*d-s4)/(2*d)
def q_prod(p, t):      # the branch used in Lean and in the construction: three principal roots
    m, g, n, d, e1, e2 = consts(p)
    return m*(1+t) + g*sqrt(t) - n*sqrt(d)*sqrt(t+e1)*sqrt(t+e2)
def q_nat(p, t):       # sqrt(t) * m(w)
    m, g, n, d, e1, e2 = consts(p); z = sqrt(t)
    return z*(m*(z+1/z) + g - n*sqrt(1 + d*(t-1)**2/t))
def q_princ(p, t):     # formula (5.2) of V29 with principal roots
    m, g, n, d, e1, e2 = consts(p)
    return m*(1+t) + g*sqrt(t) - n*sqrt(t + d*(t-1)**2)
def phi(p, t, q=q_prod):
    Q = q(p, t); return (t+(p-1)*Q)/(1+(p-1)*Q)
def T(p, t): return exp(log(t) - p*log(phi(p, t)))
eta = lambda t: (t-1)/(t+1)
zeta = lambda t: (sqrt(t)-1)/(sqrt(t)+1)
PS = [mpf('2.001'), mpf('2.2'), 3, mpf('3.5'), 4, 5, 7, 12, 40, 1000]
def rnd_slit(amax=0.99999):
    return exp(mpf(random.uniform(-9, 9)))*exp(mpc(0, mpf(random.uniform(-1, 1))*pi*amax))
def rnd_H():
    return exp(mpf(random.uniform(-9, 9)))*exp(mpc(0, mpf(random.uniform(-1, 1))*pi/2))

# 1. the three writings of the support
err1 = err2 = 0
for p in PS:
    for _ in range(200):
        t = rnd_slit(); err1 = max(err1, fabs(q_prod(p, t)-q_nat(p, t))/(1+fabs(t)))
        t = rnd_H(); err2 = max(err2, fabs(q_prod(p, t)-q_princ(p, t))/(1+fabs(t)))
check('product form = sqrt(t) m(w) on the slit plane; = formula (5.2) of V29 on Re t > 0',
      err1 < mpf(10)**(-280) and err2 < mpf(10)**(-280))

# 2. slit-plane theorem
worst = mpf(100); inside = True; minreM = mpf(100)
for p in PS:
    m, g, n, d, e1, e2 = consts(p)
    for _ in range(900):
        t = rnd_slit(); Tt = T(p, t); z = sqrt(t)
        inside = inside and fabs(arg(Tt)) < pi and re(sqrt(Tt)) > 0
        minreM = min(minreM, re(q_prod(p, t)/z) - (g-n))
        if fabs(zeta(t)) > mpf(10)**(-25):
            worst = min(worst, log(fabs(zeta(Tt)))/log(fabs(zeta(t))))
check('slit-plane theorem: invariance, |zeta+| <= |zeta|^9, Re(q/z) >= g - n', inside and worst >= 9 and minreM >= 0,
      f'min log|zeta+|/log|zeta| = {float(worst):.3f}')

# 3. half-plane theorem and its boundary
worst = mpf(100); inH = True
for p in PS:
    for _ in range(700):
        t = rnd_H(); Tt = T(p, t); inH = inH and re(Tt) > 0
        if fabs(eta(t)) > mpf(10)**(-25):
            worst = min(worst, log(fabs(eta(Tt)))/log(fabs(eta(t))))
lo = mpf(10); hi = mpf(0); okm = True
for p in PS:
    m, g, n, d, e1, e2 = consts(p)
    for k in range(-1200, 1201):
        y = exp(mpf(k)/100); t = mpc(0, y)
        A = arg(phi(p, t))*p/pi; lo = min(lo, A); hi = max(hi, A)
        if y >= 1:
            mm = q_prod(p, t)/sqrt(t); okm = okm and im(mm) >= -mpf(10)**(-280) and re(mm) > im(mm)   # Im m = 0 at y = 1
check('half-plane theorem: invariance and |eta+| <= |eta|^9', inH and worst >= 9, f'min ratio = {float(worst):.3f}')
check('boundary Re t = 0: 0 < p Arg(phi)/pi <= 1 and 0 <= arg m < pi/4', lo > 0 and hi <= 1 and okm,
      f'range ({float(lo):.2e}, {float(hi):.4f}]')

# 4. the cut: regimes, formulas, strict inequalities
errf = 0; lo = mpf(10); hi = mpf(0); star = True; inside = True
for p in PS:
    m, g, n, d, e1, e2 = consts(p); c = p-1
    for k in range(-1500, 1501):
        tau = exp(mpf(k)/150); t = -tau**2            # principal roots of negative numbers: upper edge
        sig = tau+1/tau; dl = tau-1/tau
        if d*sig**2 <= 1:
            A = c*(g - n*sqrt(1-d*sig**2)); B = c*m*dl
        else:
            A = c*g; B = c*(m*dl - (1 if tau > 1 else -1)*n*sqrt(d*sig**2-1))
        ReN = A*A + B*B + B*dl - 1; ImN = A*sig
        f = phi(p, mpf(t)); a = arg(f)
        errf = max(errf, fabs(a - atan2(ImN, ReN)))
        lo = min(lo, a*p/(2*pi)); hi = max(hi, a*p/(2*pi))
        star = star and ReN > 0 and (p < 4 or p*ImN <= 6*ReN)
        inside = inside and fabs(pi - p*a) < pi
check('cut: boundary formulas, Re N > 0, p Im N <= 6 Re N for p >= 4, image strictly inside',
      errf < mpf(10)**(-250) and star and inside and lo > 0 and hi < 1,
      f'p Arg(phi)/(2 pi) in ({float(lo):.3f}, {float(hi):.4f})')

# 5. convergence from everywhere, including the cut; real degrees in the logarithmic chart
okc = True
for p in [3, 4, 5, 7, 12]:
    for _ in range(60):
        t = rnd_slit(1.0) if random.random() < 0.7 else -exp(mpf(random.uniform(-9, 9)))
        s = t
        for _ in range(8): s = T(p, s)
        okc = okc and fabs(s-1) < mpf(10)**(-200)
I = mpc(0, 1); okl = True
for p in [pi, sqrt(7), mpf('2.5'), mpf(17)/3, mpf('2.01'), mpf(40)]:
    for _ in range(40):
        L = mpc(random.uniform(-2, 2), random.uniform(-3.1, 3.1)); k = random.randint(-4, 4)
        x0 = mpc(random.uniform(-6, 6), random.uniform(-0.999, 0.999)*float(pi))
        l = (L + 2*pi*I*k - x0)/p; z0 = fabs(zeta(exp(x0)))
        for nstep in range(1, 4):
            l = l + log(phi(p, exp(L - p*l)))
            okl = okl and fabs(im(l) - im((L+2*pi*I*k)/p)) < pi/p
            bnd = z0**(9**nstep)
            if bnd > mpf(10)**(-250):
                okl = okl and fabs(l - (L+2*pi*I*k)/p) <= 4/p*atanh(bnd)*(1+mpf(10)**(-40))
check('convergence from random residuals of the slit plane and of the cut (integer p)', okc)
check('real degrees: full strips |Im l - Im l_k| < pi/p and the bound (4/p) artanh(|zeta0|^(9^n))', okl)

# 6. the circle: tan(|eps+|/4) <= tan(|eps|/4)^9 for |eps| < pi
okk = True
for p in PS:
    for _ in range(100):
        eps = mpf(random.uniform(-0.9999, 0.9999))*pi; t = exp(I*eps); Tt = T(p, t)
        okk = okk and fabs(fabs(Tt)-1) < mpf(10)**(-280) and tan(fabs(arg(Tt))/4) <= tan(fabs(eps)/4)**9*(1+mpf(10)**(-30))
check('circle: invariance and tan(|eps+|/4) <= tan(|eps|/4)^9', okk)

# 7. local constants
for p in [3, 5, 11]:
    p = mpf(p); cM = (p**2-1)*(p**2-4)*(4*p**2-1)*(17*p**2+8)/203212800
    t = 1 + mpf(10)**(-14)*exp(mpc(0, 1)); Tt = T(p, t)
    r1 = eta(Tt)/eta(t)**9/(2**8*cM/p**8); r2 = zeta(Tt)/zeta(t)**9/(4**8*cM/p**8)
    check(f'local constants 2^8 cM p^-8 (eta) and 4^8 cM p^-8 (zeta), p={p}', fabs(r1-1) < mpf(10)**(-10) and fabs(r2-1) < mpf(10)**(-10))

# 8. exact certificates of the boundary proof (the Lean proof uses the same polynomials)
P, R, E = sp.symbols('p r e')
m = (P-2)*(47*P**2+21*P+4)/(60*P*(4*P**2-1)); g = 16*(P+1)*(4*P**2-1)/(15*P*(5*P**2+4))
n = 49*P*(P+1)*(P**2-4)/(10*(4*P**2-1)*(5*P**2+4)); d = (5*P**2+4)/(84*P**2); c = P-1
kap = m - n*(2*d + sp.Rational(1, 8))
def pos_from(poly, p0):
    return all(x > 0 for x in sp.Poly(sp.expand(poly.subs(P, p0+E)), E).all_coeffs())
PK = 653*P**4-441*P**3+146*P**2-160; PG = 73*P**3+26*P**2-13*P+4
check('2m + g - n = 1,  (2d + 1/8)^2 - d = (2d - 1/8)^2', sp.simplify(2*m+g-n-1) == 0 and sp.simplify((2*d+sp.Rational(1,8))**2-d-(2*d-sp.Rational(1,8))**2) == 0)
check('kappa = m - n(2d + 1/8) > 0 for p > 2', sp.simplify(kap-(P-2)*PK/(240*P*(4*P**2-1)*(5*P**2+4))) == 0 and pos_from(PK, 2))
check('(p-1)(g-n) > 1 for p > 2', sp.simplify(c*(g-n)-1-(P-2)*PG/(30*P*(4*P**2-1))) == 0 and pos_from(PG, 2))
Km = c**2*m**2 + c*m
F = 6*(c**2*(g-n*R)**2 + Km*((1-R**2)/d - 4) - 1) - P*c*(g-n*R)*(1 + (1-R**2)/(4*d))
coef = [sp.together(sp.Poly(sp.expand(F), R).coeff_monomial(R**k)) for k in range(4)]
bern = [sum(sp.binomial(k, j)/sp.binomial(3, j)*coef[j] for j in range(k+1)) for k in range(4)]
Den = 150*P*(4*P**2-1)**2*(5*P**2+4)**2
check('middle regime: the four Bernstein coefficients are positive for p >= 4',
      all(sp.fraction(sp.cancel(b*Den))[1] == 1 and pos_from(sp.cancel(b*Den), 4) for b in bern))
K2 = c**2*kap**2 + c*kap
PO1 = 460027*P**10-5169283*P**8-179352*P**6+2001488*P**4+647680*P**2-307200
PO2 = 436765*P**12-4624114*P**10+2473133*P**8-3086952*P**6+1411024*P**4-80384*P**2-28672
D2 = P**2*(4*P**2-1)**2*(5*P**2+4)**2
check('outer regime: p c g <= 72 K2 and 3 p c g <= 6 (c^2 g^2 - 1) - 24 K2 for p >= 4',
      sp.simplify(72*K2 - P*c*g - (P-1)*(P+1)*PO1/(2400*D2)) == 0 and pos_from(PO1, 4)
      and sp.simplify(6*(c**2*g**2-1) - 24*K2 - 3*P*c*g - PO2/(800*D2)) == 0 and pos_from(PO2, 4))
print('\nAll checks passed.' if OK else '\nSOME CHECKS FAILED')
