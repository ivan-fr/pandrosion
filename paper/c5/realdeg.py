"""Real degrees: logarithmic chart. Examples and checks (400+ digits)."""
import random
from mpmath import mp, mpf, mpc, sqrt, log, exp, pi, fabs, re, im, nint, floor
mp.dps = 1300
random.seed(11)
def coeffs(p):
    h = 1/mpf(p)
    return (1-2*h)/12, (1+h)*(3+h)/30, (121-185*h-67*h**2-h**3)/(840*(3+h))
def tm_consts(p):
    p = mpf(p)
    return ((p-2)*(47*p**2+21*p+4)/(60*p*(4*p**2-1)), 16*(p+1)*(4*p**2-1)/(15*p*(5*p**2+4)),
            49*p*(p+1)*(p**2-4)/(10*(4*p**2-1)*(5*p**2+4)), (5*p**2+4)/(84*p**2))
def q_tm(p, t):
    m, g, n, d = tm_consts(p); z = sqrt(t)
    return m*(1+t) + g*z - n*z*sqrt(1 + d*(t-1)**2/t)
def q(name, p, t):
    a, b, c = coeffs(p)
    if name == 'AD': return (1+t)/2
    if name == 'tm': return q_tm(p, t)
    w = (t-1)**2/t
    if name == 'arc': return sqrt(t*(1+a*w))
    return sqrt(t*(1+a*w/sqrt(1+b*w/(1+c*w))))
def phi(name, p, t):
    Q = q(name, p, t); return (t+(p-1)*Q)/(1+(p-1)*Q)
def lstep(name, p, L, l):                 # logarithmic state
    return l + log(phi(name, p, exp(L - p*l)))
eta = lambda t: (t-1)/(t+1)
e10 = lambda x: f"{float(log(x)/log(10)):.1f}"
M = {'AD': 3, 'arc': 5, 'nest': 9, 'tm': 9}

if __name__ == '__main__':
    X = mpc(2, 2); L = log(X)
    # irrational degree, start l0 = L/4
    p = pi; l0 = L/4
    e0 = fabs(eta(exp(L - p*l0)))
    print('X = 2+2i, p = pi, start l0 = (1/4) Log X, |eta0| =', float(e0))
    for name in ['AD', 'arc', 'nest', 'tm']:
        l = l0; row = []
        for n in range(1, 4):
            l = lstep(name, p, L, l)
            row.append(f"n={n}: {e10(fabs(eta(exp(L-p*l))))} ({float(M[name]**n*log(e0)/log(10)):.1f}) |l-L/p|={e10(fabs(l-L/p))}")
        print('  ', name, ' | '.join(row))
    # rational degree p = 5/2 through the integer degree mu = 5 on Y = X^2, start u0 = X^(3/8)
    mu, nu = 5, 2; Y = X**nu; u0 = exp(3*L/8); t0 = Y/u0**mu; e0 = fabs(eta(t0))
    print('X = 2+2i, p = 5/2 via u^5 = X^2, start u0 = X^(3/8), |eta0| =', float(e0), ' Re t0 > 0:', re(t0) > 0)
    for name in ['AD', 'arc', 'nest', 'tm']:
        u = u0; row = []
        for n in range(1, 4):
            u = u*phi(name, mu, Y/u**mu)
            row.append(f"n={n}: {e10(fabs(eta(Y/u**mu)))} ({float(M[name]**n*log(e0)/log(10)):.1f}) |u-X^(2/5)|={e10(fabs(u-exp(2*L/5)))}")
        print('  ', name, ' | '.join(row))
    # checks: convergence to the predicted determination, for random real degrees and starts
    mp.dps = 400
    ok = True; worst = {n: mpf(100) for n in M}
    for p in [pi, sqrt(7), mpf('2.5'), mpf(17)/3, mpf('2.01'), mpf(40)]:
        for _ in range(60):
            L = mpc(random.uniform(-2, 2), random.uniform(-3.1, 3.1))
            k = random.randint(-4, 4)
            x0 = mpc(random.uniform(-5, 5), random.uniform(-1.55, 1.55))
            l0 = (L + 2*pi*mpc(0, 1)*k - x0)/p
            for name, m in M.items():
                l = l0; e = fabs(eta(exp(L - p*l))); e_start = e; done = 0
                for n in range(4):
                    if e < mpf(10)**(-40): break          # the next error would be below working precision
                    l = lstep(name, p, L, l); e_new = fabs(eta(exp(L - p*l))); done += 1
                    worst[name] = min(worst[name], log(e_new)/log(e)); e = e_new
                    ok = ok and fabs(im(l) - im((L + 2*pi*mpc(0, 1)*k)/p)) < pi/(2*p)
                ok = ok and fabs(l - (L + 2*pi*mpc(0, 1)*k)/p) <= 2/p*mp.atanh(e_start**(m**done))*(1 + mpf(10)**(-50))
    print('real degrees, logarithmic chart: determination, strip and bound:', 'PASS' if ok and all(worst[n] >= M[n] for n in M) else 'FAIL',
          {n: float(worst[n]) for n in M})
    # degree perturbation bound
    okp = True
    for _ in range(200):
        L = mpc(random.uniform(-3, 3), random.uniform(-3.1, 3.1)); p = mpf(random.uniform(1.1, 30)); pp = p*(1 + mpf(random.uniform(-1, 1))/50)
        d = fabs(L)*fabs(1/pp - 1/p)
        if d <= 1: okp = okp and fabs(exp(L/pp) - exp(L/p)) <= 2*fabs(exp(L/p))*d
    print('degree perturbation bound:', 'PASS' if okp else 'FAIL')
