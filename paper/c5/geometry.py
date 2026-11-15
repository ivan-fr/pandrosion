"""Ruler-and-compass protocols for complex arithmetic, with trace counting and numerical checks.

Points of the plane are complex numbers. Given: O = 0, E = 1 and the real axis. A *trace* is one
straight line through two constructed points (j) or one circle whose centre is a constructed point
and whose radius is the distance between two constructed points (c). As in V28, a parallel through
a point is a macro costing 2 j + 3 c. Every new point is an intersection of traced curves; when two
intersections exist the one prescribed by the stated geometric rule is taken, and each protocol is
checked against complex arithmetic.

Setup, traced once and shared by every operation: the unit circle and the imaginary axis.
Real constants (the coefficients a, b, c of the supports, and the coefficients of the projective
support) are points of the real axis prepared once; they are not counted in the cost of a step.
"""
import cmath, math, random

TOL = 1e-9

class Board:
    def __init__(self):
        self.j = 0; self.c = 0
        self.items = []                      # traced curves, for drawing
        self.O = 0j; self.E = 1 + 0j
        self.axis = (0j, 1 + 0j)             # given
    # ---- primitive traces ---------------------------------------------------------------
    def line(self, P, Q):
        assert abs(P - Q) > 1e-12
        self.j += 1; self.items.append(('line', P, Q)); return (P, Q)
    def circle(self, C, A, B):
        """Circle with centre C and radius |AB|."""
        r = abs(A - B); assert r > 1e-12
        self.c += 1; self.items.append(('circle', C, r)); return (C, r)
    def parallel(self, ln, P):
        """V28 macro: the parallel to `ln` through P costs 2 j + 3 c."""
        self.j += 2; self.c += 3
        d = ln[1] - ln[0]
        self.items.append(('par', P, P + d)); return (P, P + d)
    @property
    def traces(self): return self.j + self.c
    # ---- intersections (no trace) -----------------------------------------------------------
    @staticmethod
    def ll(l1, l2):
        (a, b), (c, d) = l1, l2
        u, v = b - a, d - c
        den = (u.conjugate()*v).imag
        assert abs(den) > 1e-12, 'parallel lines'
        s = ((c - a).conjugate()*v).imag/den
        return a + s*u
    @staticmethod
    def lc(ln, circ):
        (a, b), (C, r) = ln, circ
        u = (b - a)/abs(b - a)
        f = a - C
        bq = (f.conjugate()*u).real
        disc = bq*bq - (abs(f)**2 - r*r)
        assert disc > -1e-12, 'line misses circle'
        s = math.sqrt(max(disc, 0.0))
        return [a + (-bq + s)*u, a + (-bq - s)*u]
    @staticmethod
    def cc(c1, c2):
        (A, r1), (B, r2) = c1, c2
        d = abs(B - A); assert d > 1e-12
        x = (d*d + r1*r1 - r2*r2)/(2*d)
        h2 = r1*r1 - x*x
        assert h2 > -1e-10, 'circles do not meet'
        h = math.sqrt(max(h2, 0.0)); u = (B - A)/d
        return [A + x*u + 1j*h*u, A + x*u - 1j*h*u]

def pick(points, target):
    """The intersection prescribed by the geometric rule; `target` encodes that rule."""
    best = min(points, key=lambda P: abs(P - target))
    assert abs(best - target) < TOL*(1 + abs(target)), (best, target)
    return best

class Plane(Board):
    """Board with the shared setup: unit circle and imaginary axis."""
    def __init__(self):
        super().__init__()
        self.G = self.circle(self.O, self.O, self.E)                       # unit circle
        k1 = self.circle(self.E, self.E, -self.E)                          # two arcs for the
        k2 = self.circle(-self.E, self.E, -self.E)                         # perpendicular at O
        p1, p2 = self.cc(k1, k2)
        self.iaxis = self.line(p1, p2)
        self.setup = self.traces
    def cost(self): return self.traces - self.setup
    def unit(self, ln, Z):
        """Point of the unit circle on the ray OZ."""
        return pick(self.lc(ln, self.G), Z/abs(Z))
    # ---- operations ---------------------------------------------------------------------
    def prod(self, Z, W):
        """Z*W: rotate OZ by the angle EOW (a chord of the unit circle), then scale by |W|
        with the intercept theorem. 6 j + 5 c."""
        lz = self.line(self.O, Z); lw = self.line(self.O, W)
        Z1 = self.unit(lz, Z); W1 = self.unit(lw, W)
        U = pick(self.cc(self.circle(W1, self.E, Z1), self.G), Z1*W1)       # arc W1->U equals arc E->Z1
        lu = self.line(self.O, U)
        Z3 = pick(self.lc(lu, self.circle(self.O, self.O, Z)), abs(Z)*U)   # |OZ3| = |OZ| on the ray OU
        par = self.parallel(self.line(W1, Z3), W)
        return pick([self.ll(par, lu)], Z*W)
    def quot(self, Z, W):
        """Z/W: rotate OZ by minus the angle EOW, then scale by 1/|W|. 6 j + 5 c."""
        lz = self.line(self.O, Z); lw = self.line(self.O, W)
        Z1 = self.unit(lz, Z); W1 = self.unit(lw, W)
        U = pick(self.cc(self.circle(Z1, self.E, W1), self.G), Z1/W1)
        lu = self.line(self.O, U)
        Z3 = pick(self.lc(lu, self.circle(self.O, self.O, Z)), abs(Z)*U)
        par = self.parallel(self.line(W, Z3), W1)
        return pick([self.ll(par, lu)], Z/W)
    def sqrt(self, Z):
        """Principal square root: bisector of the angle EOZ and mean proportional of 1 and |Z|
        (Euclid VI.13). 3 j + 7 c."""
        lz = self.line(self.O, Z)
        Z1 = self.unit(lz, Z)
        b1, b2 = self.cc(self.circle(self.E, self.E, Z1), self.circle(Z1, self.E, Z1))
        lb = self.line(b1, b2)                                              # bisector, through O
        Z4 = pick(self.lc(self.axis, self.circle(self.O, self.O, Z)), -abs(Z))
        m1, m2 = self.cc(self.circle(Z4, Z4, self.E), self.circle(self.E, Z4, self.E))
        M = self.ll(self.line(m1, m2), self.axis)                           # midpoint of Z4 E
        H = pick(self.lc(self.iaxis, self.circle(M, M, self.E)), 1j*math.sqrt(abs(Z)))
        return pick(self.lc(lb, self.circle(self.O, self.O, H)), cmath.sqrt(Z))
    def add(self, Z, W):
        """Z + W: fourth vertex of the parallelogram, two arcs. 2 c."""
        return pick(self.cc(self.circle(Z, self.O, W), self.circle(W, self.O, Z)), Z + W)
    def sub(self, Z, W):
        """Z - W: two arcs. 2 c."""
        return pick(self.cc(self.circle(Z, self.O, W), self.circle(self.O, W, Z)), Z - W)
    def times_int(self, Z, n):
        """n*Z by stepping the compass along OZ. 1 j + (n-1) c."""
        ln = self.line(self.O, Z); P = Z
        for k in range(2, n + 1):
            P = pick(self.lc(ln, self.circle(P, self.O, Z)), k*Z)
        return P
    def times_real(self, Z, lam):
        """lam*Z for a prepared point lam > 0 of the real axis: intercept theorem. 4 j + 3 c."""
        lz = self.line(self.O, Z)
        par = self.parallel(self.line(self.E, Z), lam + 0j)
        return pick([self.ll(par, lz)], lam*Z)
    def midpoint(self, Z, W):
        """Midpoint: perpendicular bisector and the segment. 2 j + 2 c."""
        m1, m2 = self.cc(self.circle(Z, Z, W), self.circle(W, Z, W))
        return pick([self.ll(self.line(m1, m2), self.line(Z, W))], (Z + W)/2)

# ---- supports ---------------------------------------------------------------------------------
def coeffs(p):
    h = 1/p
    return (1 - 2*h)/12, (1 + h)*(3 + h)/30, (121 - 185*h - 67*h**2 - h**3)/(840*(3 + h))

def consts_tm(p):
    """Three-mean support of V29: weights m, g, n, conic parameter d, and the roots e1 >= e2 of
    d Z^2 - (1 - 2 d) Z + d, so that t + d (t-1)^2 = d (t + e1)(t + e2)."""
    m = (p - 2)*(47*p**2 + 21*p + 4)/(60*p*(4*p**2 - 1))
    g = 16*(p + 1)*(4*p**2 - 1)/(15*p*(5*p**2 + 4))
    n = 49*p*(p + 1)*(p**2 - 4)/(10*(4*p**2 - 1)*(5*p**2 + 4))
    d = (5*p**2 + 4)/(84*p**2)
    s4 = math.sqrt(1 - 4*d)
    return m, g, n, d, (1 - 2*d + s4)/(2*d), (1 - 2*d - s4)/(2*d)

def support(pl, name, p, t):
    """Construct q(t); returns the point."""
    a, b, c = coeffs(p)
    if name == 'AK': return pl.E
    if name == 'tm':                                          # three means, natural branch
        m, g, n, d, e1, e2 = consts_tm(p)                     # prepared real points
        z = pl.sqrt(t)
        R = pl.prod(pl.sqrt(pl.add(t, e1 + 0j)), pl.sqrt(pl.add(t, e2 + 0j)))
        lin = pl.add(pl.times_real(pl.add(pl.E, t), m), pl.times_real(z, g))
        return pl.sub(lin, pl.times_real(R, n*math.sqrt(d)))
    if name == 'AD': return pl.midpoint(pl.E, t)
    if name == 'proj':
        num = pl.add(pl.times_real(t, 4*p + 1), 2*p - 1 + 0j)
        den = pl.add(pl.times_real(t, p + 1), 5*p - 1 + 0j)
        return pl.quot(num, den)
    d = pl.sub(t, pl.E)
    d2 = pl.prod(d, d)
    if name == 'arc':
        return pl.sqrt(pl.add(t, pl.times_real(d2, a)))
    w = pl.quot(d2, t)
    if name == 'arcN':                                        # natural branch: sqrt(t) * sqrt(1 + a w)
        return pl.prod(pl.sqrt(t), pl.sqrt(pl.add(pl.E, pl.times_real(w, a))))
    rho = pl.sqrt(pl.add(pl.E, pl.quot(pl.times_real(w, b), pl.add(pl.E, pl.times_real(w, c)))))
    inner = pl.add(pl.E, pl.quot(pl.times_real(w, a), rho))
    if name == 'nestN':                                       # natural branch: sqrt(t) * sqrt(inner)
        return pl.prod(pl.sqrt(t), pl.sqrt(inner))
    return pl.sqrt(pl.prod(t, inner))

def step(name, p, X, u):
    """One complete step u -> u*phi(X/u^p) by ruler and compass. Returns (u_plus, cost, j, c)."""
    pl = Plane()
    up = u
    for _ in range(p - 1): up = pl.prod(up, u)                # u^p
    t = pl.quot(X, up)                                        # residual
    if name == 'AK':                                          # q = 1: phi = (t + p - 1)/p, real operands
        phi = pl.times_real(pl.add(t, p - 1 + 0j), 1/p)       # prepared real points p - 1 and 1/p
    else:
        q = support(pl, name, p, t)
        N = pl.times_int(q, p - 1)                            # (p-1) q
        phi = pl.quot(pl.add(t, N), pl.add(pl.E, N))
    return pl.prod(u, phi), pl.cost(), pl.j, pl.c, pl

def exact(name, p, X, u):
    a, b, c = coeffs(p); t = X/u**p
    if name == 'AK': q = 1
    elif name == 'AD': q = (1 + t)/2
    elif name == 'proj': q = ((4*p + 1)*t + 2*p - 1)/((p + 1)*t + 5*p - 1)
    elif name == 'arc': q = cmath.sqrt(t + a*(t - 1)**2)
    elif name == 'arcN': q = cmath.sqrt(t)*cmath.sqrt(1 + a*(t - 1)**2/t)
    elif name == 'tm':
        m, g, n, d, e1, e2 = consts_tm(p)
        z = cmath.sqrt(t)
        q = m*(1 + t) + g*z - n*z*cmath.sqrt(1 + d*(t - 1)**2/t)
    else:
        w = (t - 1)**2/t
        inner = 1 + a*w/cmath.sqrt(1 + b*w/(1 + c*w))
        q = cmath.sqrt(t)*cmath.sqrt(inner) if name == 'nestN' else cmath.sqrt(t*inner)
    return u*(t + (p - 1)*q)/(1 + (p - 1)*q)

ORDER = {'AK': 2, 'AD': 3, 'proj': 4, 'arc': 5, 'nest': 9, 'arcN': 5, 'nestN': 9, 'tm': 9}

if __name__ == '__main__':
    random.seed(5)
    rnd = lambda: cmath.rect(random.uniform(0.6, 1.7), random.uniform(-3.0, 3.0))
    # single operations
    costs = {}
    for _ in range(300):
        Z, W = rnd(), rnd()
        for name, f, val in [('product', lambda P: P.prod(Z, W), Z*W), ('quotient', lambda P: P.quot(Z, W), Z/W),
                             ('square root', lambda P: P.sqrt(Z), cmath.sqrt(Z)), ('sum', lambda P: P.add(Z, W), Z + W),
                             ('difference', lambda P: P.sub(Z, W), Z - W), ('midpoint', lambda P: P.midpoint(Z, W), (Z + W)/2),
                             ('real multiple', lambda P: P.times_real(Z, 0.37), 0.37*Z)]:
            P = Plane(); j0, c0 = P.j, P.c
            assert abs(f(P) - val) < 1e-8
            costs.setdefault(name, set()).add((P.j - j0, P.c - c0))
    for name, s in costs.items():
        assert len(s) == 1
        (j, c), = s
        print(f'{name:14s}: {j} j + {c} c = {j + c} traces   (300 random checks)')
    # complete steps
    table = {}
    for name in ORDER:
        for p in (3, 4, 5, 7):
            vals = set()
            for _ in range(40):
                r = rnd(); u = r*cmath.rect(random.uniform(0.85, 1.15), random.uniform(-0.25, 0.25)/p)
                X = r**p
                up, cost, j, c, _ = step(name, p, X, u)
                assert abs(up - exact(name, p, X, u)) < 1e-7, (name, p)
                vals.add((cost, j, c))
            assert len(vals) == 1
            table[(name, p)] = vals.pop()
    print('\ntraces per step (setup of 4 traces not included):')
    for name in ORDER:
        c3, c4, c5, c7 = (table[(name, p)][0] for p in (3, 4, 5, 7))
        slope = c4 - c3; const = c3 - 3*slope
        assert c5 == slope*5 + const and c7 == slope*7 + const
        print(f'  {name:6s}: {slope} p + {const}   (p=3: {c3}, j={table[(name,3)][1]}, c={table[(name,3)][2]})')
        table[name] = (slope, const)
    print('\nefficiency index log(order)/traces:')
    for p in (3, 5, 8, 12, 16):
        print('  p =', p, '  '.join(f"{name} {math.log(ORDER[name])/(table[name][0]*p + table[name][1]):.5f}" for name in ORDER))
    sa, ca = table['arc']; sn, cn = table['nest']
    pstar = (cn*math.log(5) - ca*math.log(9))/(sa*math.log(9) - sn*math.log(5))
    print(f'nested beats the arc for p > {pstar:.2f}')
    st, ct = table['tm']
    pt = (ct*math.log(5) - ca*math.log(9))/(sa*math.log(9) - st*math.log(5))
    print(f'three means beat the arc for p > {pt:.2f}; they cost {cn - ct} traces less than the nested support')
    print('ALL GEOMETRIC CHECKS PASSED')
