"""Complex Pandrosion supports. q(t) is the normalized support (kappa-1)/(p-1);
the correction is phi = (t+(p-1)q)/(1+(p-1)q); one step is u+ = u*phi(X/u^p)."""
import numpy as np

def q_AK(p, t):  return np.ones_like(t)
def q_AD(p, t):  return (1 + t) / 2
def q_proj(p, t): return ((4*p + 1)*t + 2*p - 1) / ((p + 1)*t + 5*p - 1)
def q_arc(p, t):
    a = (p - 2) / (12*p)
    return np.sqrt(t + a*(t - 1)**2)
def q_nest(p, t):
    h = 1/p
    a = (1 - 2*h)/12; b = (1 + h)*(3 + h)/30
    c = (121 - 185*h - 67*h**2 - h**3)/(840*(3 + h))
    w = (t - 1)**2 / t
    return np.sqrt(t*(1 + a*w/np.sqrt(1 + b*w/(1 + c*w))))
def tm_consts(p):
    m = (p - 2)*(47*p**2 + 21*p + 4)/(60*p*(4*p**2 - 1))
    g = 16*(p + 1)*(4*p**2 - 1)/(15*p*(5*p**2 + 4))
    n = 49*p*(p + 1)*(p**2 - 4)/(10*(4*p**2 - 1)*(5*p**2 + 4))
    d = (5*p**2 + 4)/(84*p**2)
    return m, g, n, d
def q_tm(p, t):
    """Three-mean support of V29, natural branch: sqrt(t) * (m (z + 1/z) + g - n sqrt(1 + d w))."""
    m, g, n, d = tm_consts(p)
    z = np.sqrt(t)
    return m*(1 + t) + g*z - n*z*np.sqrt(1 + d*(t - 1)**2/t)
Q = {'AK': q_AK, 'AD': q_AD, 'proj': q_proj, 'arc': q_arc, 'nest': q_nest, 'tm': q_tm}
ORDER = {'AK': 2, 'AD': 3, 'proj': 4, 'arc': 5, 'nest': 9, 'tm': 9}

def phi(name, p, t):
    q = Q[name](p, t)
    return (t + (p - 1)*q) / (1 + (p - 1)*q)

def run(name, p, t0, nmax=60, tol=1e-12):
    """Iterate from u0=1, X=t0. Returns (u, t, steps): steps=-1 if not converged."""
    t0 = np.asarray(t0, dtype=complex)
    u = np.ones_like(t0); X = t0.copy()
    steps = -np.ones(t0.shape, dtype=int)
    with np.errstate(all='ignore'):
        for n in range(nmax):
            t = X / u**p
            done = (np.abs(t - 1) < tol) & (steps < 0)
            steps[done] = n
            u = np.where(steps >= 0, u, u*phi(name, p, t))
        t = X / u**p
    return u, t, steps
