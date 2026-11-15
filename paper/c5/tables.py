from mpmath import mp, mpf, mpc, sqrt, log, exp, pi, fabs, arg, nstr, root
mp.dps = 1300
def tm_consts(p):
    p = mpf(p)
    return ((p-2)*(47*p**2+21*p+4)/(60*p*(4*p**2-1)), 16*(p+1)*(4*p**2-1)/(15*p*(5*p**2+4)),
            49*p*(p+1)*(p**2-4)/(10*(4*p**2-1)*(5*p**2+4)), (5*p**2+4)/(84*p**2))
def q_tm(p, t):
    m, g, n, d = tm_consts(p); z = sqrt(t)
    return m*(1+t) + g*z - n*z*sqrt(1 + d*(t-1)**2/t)
def q(name, p, t):
    h = 1/mpf(p); a = (1-2*h)/12
    if name == 'AD': return (1+t)/2
    if name == 'tm': return q_tm(p, t)
    w = (t-1)**2/t
    if name == 'arc': return sqrt(t*(1+a*w))
    b = (1+h)*(3+h)/30; c = (121-185*h-67*h**2-h**3)/(840*(3+h))
    return sqrt(t*(1+a*w/sqrt(1+b*w/(1+c*w))))
def stepu(name, p, X, u):
    t = X/u**p; Q = q(name, p, t)
    return u*(t+(p-1)*Q)/(1+(p-1)*Q)
eta = lambda X, u, p: fabs((X-u**p)/(X+u**p))
def e10(x): return f"{float(log(x)/log(10)):.1f}" if x > 0 else "-inf"
for label, X, p in [('X = 2+2i, p = 3', mpc(2, 2), 3), ('X = exp(i pi/3), p = 3 (trisection of 60 degrees)', exp(mpc(0, pi/3)), 3),
                    ('X = -7+i, p = 5', mpc(-7, 1), 5)]:
    k = 1
    while not (mpf(2)/3 < mpf(2)**k/p < 2): k += 1
    u0 = exp(log(X)/2**k); r = exp(log(X)/p)
    print(label, ' start u0 = X^(1/2^%d)' % k, ' |eta0| =', nstr(eta(X, u0, p), 6))
    for name, m in [('AD', 3), ('arc', 5), ('nest', 9), ('tm', 9)]:
        u = u0; e0 = eta(X, u0, p); row = []
        for n in range(1, 4):
            u = stepu(name, p, X, u)
            row.append(f"n={n}: log10|eta|={e10(eta(X, u, p))} (bound {float(m**n*log(e0)/log(10)):.1f}), log10|u-r|={e10(fabs(u-r))}")
        print('  ', name, ' | '.join(row))
# trisection: angle error in degrees after one and two nested steps
X = exp(mpc(0, pi/3)); u = exp(log(X)/4)
for n in range(1, 3):
    u = stepu('nest', 3, X, u)
    print('nested, trisection of 60 deg: step', n, 'angle error (deg) =', nstr(fabs(arg(u) - pi/9)*180/pi, 5), ' | |u|-1 =', nstr(fabs(fabs(u)-1), 5))

# three means from u0 = 1: the residual t0 = X is anywhere in the slit plane
zeta = lambda X, u, p: fabs((sqrt(X/u**p)-1)/(sqrt(X/u**p)+1))
print('three means from u0 = 1 (coordinate zeta = (sqrt t - 1)/(sqrt t + 1)):')
for label, X, p in [('X = -7+i, p = 5', mpc(-7, 1), 5), ('X = -1+0.01i, p = 3', mpc(-1, mpf(1)/100), 3),
                    ('X = 1000i, p = 7', mpc(0, 1000), 7)]:
    u = mpf(1); z0 = zeta(X, u, p); r = exp(log(X)/p); row = []
    for n in range(1, 4):
        u = stepu('tm', p, X, u)
        row.append(f"n={n}: {e10(zeta(X, u, p))} ({float(9**n*log(z0)/log(10)):.2f})")
    print('  ', label, ' |zeta0| =', nstr(z0, 6), ' arg t0 (deg) =', nstr(arg(X)*180/pi, 5), ' | '.join(row), ' |u3-r| =', e10(fabs(u-r)))
# trisection with three means
X = exp(mpc(0, pi/3)); u = exp(log(X)/4)
for n in range(1, 3):
    u = stepu('tm', 3, X, u)
    print('three means, trisection of 60 deg: step', n, 'angle error (deg) =', nstr(fabs(arg(u) - pi/9)*180/pi, 5))
