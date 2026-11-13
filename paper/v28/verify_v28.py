#!/usr/bin/env python3
"""Independent checks for "Geometric Root Calculators", V28.

Exact parts use SymPy rational arithmetic; numerical parts use mpmath.
Requires: sympy, mpmath.  Run:  python3 verify_v28.py
Every line printed must end with OK; the script exits non-zero otherwise.
"""
import sys
from math import log
import sympy as sp
import mpmath as mp

FAIL = []


def check(name, cond, info=""):
    print(f"{name:<58s} {info!s:<28s} {'OK' if cond else 'FAIL'}")
    if not cond:
        FAIL.append(name)


p, t, w, h, x, v, xi, e = sp.symbols("p t w h x v xi e", positive=True)
rho, yy = sp.symbols("rho yy", positive=True)

# ---------------------------------------------------------------- Section 2
kstar = (t - 1) / (t ** (1 / p) - 1)
S = (p - 2) * (t**2 + 1) + (10 * p + 4) * t
q5 = sp.sqrt(S / (12 * p))
Qproj = (p + 1) * t**2 + 2 * (2 * p - 1) * (p + 1) * t + (2 * p - 1) * (p - 1)
supports = {
    "AK": (p, 1, -(p - 1) / 2),
    "AD": ((p + 1 + (p - 1) * t) / 2, 2, (p**2 - 1) / 12),
    "proj": (2 * p * ((2 * p - 1) * t + p + 1) / ((p + 1) * t + 5 * p - 1), 3,
             -(p**2 - 1) * (2 * p - 1) / 72),
    "dec": (1 + (p - 1) * q5, 4, (p - 2) * (p**2 - 1) * (3 * p + 1) / 1440),
}
for name, (kap, om, const) in supports.items():
    ser = sp.series((kap - kstar).subs(t, 1 + xi), xi, 0, om + 1).removeO()
    low = all(sp.simplify(ser.coeff(xi, i)) == 0 for i in range(om))
    c = sp.simplify(ser.coeff(xi, om))
    check(f"Table 3: contact {om} and constant, {name}",
          low and sp.simplify(c * p ** (om - 1) - const) == 0)
    # direct expansion of the log-error map
    Phi = kap / (kap - 1 + t)
    se = sp.series(e + sp.log(Phi.subs(t, sp.exp(p * e))), e, 0, om + 2).removeO()
    check(f"Lemma 2.1 against direct series, {name}",
          sp.simplify(se.coeff(e, om + 1) - const) == 0)

# ---------------------------------------------------------------- Section 3
g = (p - 1) * q5
N1 = (p - 1) * (t**2 + 1) + (10 * p + 2) * t
N2 = (t + 1) * (6 * p * t - (t - 1) ** 2)
N3 = (p**2 - 5 * p - 2) * (t - 1) ** 2 + 12 * p * (3 * p + 1) * t
check("(3.4) q5^2 N1^2 - N2^2 identity",
      sp.expand(q5**2 * N1**2 - N2**2 - (p + 1) / (12 * p) * (t - 1) ** 4 * N3) == 0)
check("N3 rearrangement",
      sp.expand(N3 - 6 * p**2 * (p + 1) * t - (p**2 - 5 * p - 2) * ((t - 1) ** 2 - 6 * p * t)) == 0)
Lam = sp.log(t) / p + sp.log(1 + g) - sp.log(t + g)
dd = t * sp.diff(Lam, t) - (p - 2) * (p - 1) ** 2 * (q5 * N1 - N2) / (12 * p**2 * g * (1 + g) * (t + g))
vals = [abs(sp.N(dd.subs({p: a, t: b}), 40)) for a, b in
        [(3, 2), (sp.Rational(5, 2), sp.Rational(1, 7)), (11, 40)]]
check("(3.3) derivative identity at sample points", max(vals) < 1e-30)

# ---------------------------------------------------------------- Section 4
a9 = (1 - 2 * h) / 12
b9 = (h + 1) * (h + 3) / 30
c9h = (121 - 185 * h - 67 * h**2 - h**3) / (840 * (h + 3))
check("c9 numerator at h = 1/2 equals 93/8",
      (121 - 185 * h - 67 * h**2 - h**3).subs(h, sp.Rational(1, 2)) == sp.Rational(93, 8))
Y = ((sp.sinh((1 - h) * x / 2) / ((1 - h) * x / 2)) / (sp.sinh(h * x / 2) / (h * x / 2))) ** 2
Wx = 2 * (sp.cosh(x) - 1)
q2 = 1 + a9 * Wx / sp.sqrt(1 + b9 * Wx / (1 + c9h * Wx))
ser = sp.series(q2 - Y, x, 0, 10).removeO()
A2 = -(1 - 2 * h) * (h + 1) * (h + 3) / 720
A3 = (1 - 2 * h) * (h + 1) * (2 * h**3 + 8 * h**2 + 13 * h + 31) / 60480
serY = sp.series(Y - (1 + a9 * Wx + A2 * Wx**2 + A3 * Wx**3), x, 0, 8).removeO()
serQ = sp.series(q2 - (1 + a9 * Wx - a9 * b9 / 2 * Wx**2
                       + a9 * (b9 * c9h / 2 + 3 * b9**2 / 8) * Wx**3), x, 0, 8).removeO()
check("(4.6), (4.7) series through w^3", sp.simplify(serY) == 0 and sp.simplify(serQ) == 0)
n9 = 21311 + 1650 * h - 21679 * h**2 - 15532 * h**3 - 4411 * h**4 - 526 * h**5 - 29 * h**6
D4 = (1 - 2 * h) * (1 + h) * n9 / (2**10 * 3**4 * 5**3 * 7**2 * (h + 3))
check("(4.9) q9^2/t - Y = D4 x^8 + O(x^10)", sp.simplify(ser - D4 * x**8) == 0)
N9 = 21311 * p**6 + 1650 * p**5 - 21679 * p**4 - 15532 * p**3 - 4411 * p**2 - 526 * p - 29
c9 = (p**2 - 1) * (p - 2) * N9 / (2**11 * 3**4 * 5**3 * 7**2 * (3 * p + 1))
check("c9(p) = (p-1) p^7 D4 / 2",
      sp.simplify((p - 1) * p**7 * D4.subs(h, 1 / p) / 2 - c9) == 0)
shift = sp.Poly(sp.expand(N9.subs(p, rho + 2)), rho).all_coeffs()
check("N9(2+rho) has positive coefficients",
      shift == [21311, 257382, 1273481, 3286796, 4628741, 3325430, 926859])
check("c9(3) = 7/648, N9(3) = 13720000",
      c9.subs(p, 3) == sp.Rational(7, 648) and N9.subs(p, 3) == 13720000)
check("lim c9 p^-8 = 21311/3048192000",
      sp.limit(c9 / p**8, p, sp.oo) == sp.Rational(21311, 3048192000))

Dv = v**6 + 4 * v**3 + 1
Hv = v**8 + 10 * v**7 + 55 * v**6 + 268 * v**5 + 466 * v**4 + 268 * v**3 + 55 * v**2 + 10 * v + 1
check("(4.10) cubic identity, H(1) = 1134",
      sp.expand((v**2 + v + 1) ** 4 * (v**6 + 52 * v**3 + 1) - 729 * v**4 * Dv - (v - 1) ** 6 * Hv) == 0
      and Hv.subs(v, 1) == 1134)
hh = sp.Rational(1, 3)
ww = (t - 1) ** 2 / t
gen = t * (1 + a9.subs(h, hh) * ww / sp.sqrt(1 + b9.subs(h, hh) * ww / (1 + c9h.subs(h, hh) * ww)))
cub = t + (t - 1) ** 2 / 108 * sp.sqrt((t**2 + 52 * t + 1) / (t**2 + 4 * t + 1))
check("(4.5) cubic form of q9^2",
      all(abs(sp.N((gen - cub).subs(t, b), 40)) < 1e-30 for b in (2, sp.Rational(1, 5), 37)))

# small-degree counterexample
hc = sp.Rational(2, 3)
wc = sp.Rational(99**2, 100)
cc = c9h.subs(h, hc)
check("counterexample p = 3/2, t = 100",
      cc == sp.Rational(-25, 2376) and 1 + cc * wc == sp.Rational(-1, 32)
      and 1 + b9.subs(h, hc) * wc / (1 + cc * wc) == sp.Rational(-15947, 25))
check("norm 606419/151632 is not a rational square",
      4 - sp.Rational(109, 13) / 108**2 == sp.Rational(606419, 151632)
      and not sp.ntheory.primetest.is_square(606419 * 151632))

# certificate of Theorem 4.4
cE = 840 * p**2 * (3 * p + 1)
cC = 121 * p**3 - 185 * p**2 - 67 * p - 1
cD = 373 * p**3 + 235 * p**2 + 129 * p + 27
cU = cE + cC * w
cV = cE + cD * w
cJ = 4 * cU * cV - p * cE * (cD - cC) * w
cK = (-1728 * p**3 * cU * cV**3 + 48 * p * (p - 1) * (3 * p - 5) * cU**2 * cV**2 * w
      - 3 * p * cJ**2 * (4 + w) * w)
cM = (576 * p**2 * (3 * p - 4) * cU * cV + 144 * p**2 * cJ * (4 + w)
      + 4 * (p - 2) * (p - 1) ** 2 * cU**2 * w**2)
lhs = sp.expand((cV**2 * cM) ** 2 * cU - cK**2 * cV)
Pq, rem = sp.div(sp.Poly(lhs, w, p), sp.Poly(sp.expand((p + 1) * w**3 * cV), w, p))
cP = Pq.as_expr()
check("P(p,w): exact division, deg_w 9, deg_p 29",
      rem.is_zero and sp.Poly(cP, w).degree() == 9 and sp.Poly(cP, p).degree() == 29)
Px = sp.expand(sp.cancel(cP.subs(w, 30 * p * yy / (1 + yy)) * (1 + yy) ** 9))
Tj = sp.Poly(Px, yy).all_coeffs()
terms, pos = 0, True
for T in Tj:
    cs = [c for c in sp.Poly(sp.expand(T.subs(p, rho + 2)), rho).all_coeffs() if c != 0]
    terms += len(cs)
    pos &= all(c > 0 for c in cs)
check("Bernstein certificate positive", pos and len(Tj) == 10, f"{terms} terms")
check("Bernstein certificate has 345 terms", terms == 345)


def cert(expr, sub):
    cs = sp.Poly(sp.expand(expr.subs(sub, simultaneous=True)), rho, yy).coeffs()
    return all(c > 0 for c in cs), len(cs)


for nm, ex, sub, n in [("M", cM, {p: rho + 2, w: yy}, 49),
                       ("J", cJ, {p: rho + 2, w: yy + 30 * (rho + 2)}, 24),
                       ("w^2 J^2 - 576 p^2 U V^3", w**2 * cJ**2 - 576 * p**2 * cU * cV**3,
                        {p: rho + 2, w: yy + 30 * (rho + 2)}, 112)]:
    ok, cnt = cert(ex, sub)
    check(f"positive expansion of {nm}", ok and cnt == n, f"{cnt} terms")

# ---------------------------------------------------------------- numerics
mp.mp.dps = 60


def q9f(T, P):
    hh_ = 1 / P
    ww_ = (T - 1) ** 2 / T
    a = (1 - 2 * hh_) / 12
    b = (hh_ + 1) * (hh_ + 3) / 30
    c = (121 - 185 * hh_ - 67 * hh_**2 - hh_**3) / (840 * (hh_ + 3))
    return mp.sqrt(T * (1 + a * ww_ / mp.sqrt(1 + b * ww_ / (1 + c * ww_))))


def F(u, X, P):
    T = X / u**P
    q = q9f(T, P)
    return u * (T + (P - 1) * q) / (1 + (P - 1) * q)


r3 = mp.mpf(2) ** (mp.mpf(1) / 3)
u1 = F(mp.mpf(1), mp.mpf(2), mp.mpf(3))
check("first step u1 and relative error",
      mp.nstr(u1, 31) == "1.259921025755929084356362206281"
      and abs((u1 / r3 - 1) + mp.mpf("1.9159092613e-8")) < 1e-17)
qq = q9f(mp.mpf(2), mp.mpf(3))
# T9 = AD9 ∩ MB with W=6, H=4: A=(6,4), D9=(0,2-4q9), M=(0,2), B=(6,0)
sl1 = (4 - (2 - 4 * qq)) / 6
sl2 = mp.mpf(-2) / 6
Tx = ((2 - 4 * qq) - 2) / (sl2 - sl1)
Ty = 2 + sl2 * Tx
check("T9 and s1 of the first step",
      abs(Tx - mp.mpf("3.524406494288")) < 1e-11 and abs(Ty - mp.mpf("0.825197835237")) < 1e-11
      and abs((4 - Ty) / 4 - mp.mpf("0.79370054119068191329")) < 1e-19)
for P in ("2.5", "3", "4", "7", "20"):
    P_ = mp.mpf(P)
    rr = mp.mpf(2) ** (1 / P_)
    ee = mp.mpf("1e-4") / P_
    num = mp.log(F(rr * mp.e**ee, mp.mpf(2), P_) / rr) / ee**9
    exact = mp.mpf(sp.N(c9.subs(p, sp.Rational(P)), 50))
    check(f"c9({P}) against the iteration", abs(num / exact - 1) < 1e-6, mp.nstr(exact, 8))
bad = 0
for P in ("2.001", "2.1", "3", "5", "17", "100", "10000"):
    P_ = mp.mpf(P)
    rr = mp.mpf(2) ** (1 / P_)
    for k in range(-12, 13):
        if k == 0:
            continue
        T = mp.mpf(10) ** k
        u = (2 / T) ** (1 / P_)
        f = F(u, mp.mpf(2), P_)
        bad += not (min(u, rr) < f < max(u, rr))
check("monotone enclosure on the (p,t) grid", bad == 0)


def dprime_gap(P, T):
    P = mp.mpf(P)
    T = mp.mpf(T)
    Dl = lambda s: mp.log((s + (P - 1) * q9f(s, P)) / (1 + (P - 1) * q9f(s, P))) - mp.log(s) / P
    ww_ = (T - 1) ** 2 / T
    E_ = 840 * P**2 * (3 * P + 1)
    C_ = 121 * P**3 - 185 * P**2 - 67 * P - 1
    D_ = 373 * P**3 + 235 * P**2 + 129 * P + 27
    U_, V_ = E_ + C_ * ww_, E_ + D_ * ww_
    L_ = mp.sqrt(U_ / V_)
    J_ = 4 * U_ * V_ - P * E_ * (D_ - C_) * ww_
    A_ = 1 + (P - 1) * ww_ * L_ / (12 * P)
    B_ = 1 - J_ * ww_ * L_ / (24 * P * U_ * V_)
    q = q9f(T, P)
    rhs = -(P - 1) * (P - 2) * (2 * q * A_ - (T + 1) * B_) / (
        2 * P * q * (T + (P - 1) * q) * (1 + (P - 1) * q))
    return abs(mp.diff(Dl, T) - rhs) / abs(rhs), abs(q**2 / (T * (1 + (P - 2) * ww_ * L_ / (12 * P))) - 1)


gaps = [dprime_gap(a, b) for a, b in [(3, 2), ("2.5", "0.01"), (9, 300)]]
check("(4.16) derivative formula and q9^2 = t R", max(max(g_) for g_ in gaps) < 1e-25)

# ---------------------------------------------------------------- Section 5
check("inventory sums 32 j, 2p+3 par, 12 arcs",
      sum([1, 2, 5, 9, 2, 7, 2, 2, 1, 1]) == 32 and sum([0, 0, 2, 2, 3, 1, 3, 1, 0, 0]) == 12
      and sp.expand(32 + 2 * (2 * p + 3) + 12 + 3 * (2 * p + 3) - (10 * p + 59)) == 0)
thr = (59 * log(5) - 9 * log(9)) / (10 * log(9 / 5))
check("efficiency threshold", 12.79 < thr < 12.80, f"{thr:.4f}")
tab = {}
for P in (3, 5, 8, 12, 13, 20, 50):
    tab[P] = [round(1000 * log(o) / N, 2) for o, N in
              ((2, 10 * P + 7), (3, 10 * P + 9), (4, 10 * P + 9), (5, 10 * P + 9), (9, 10 * P + 59))]
check("Table 7 values",
      tab[3] == [18.73, 28.17, 35.55, 41.27, 24.69] and tab[12][3:] == [12.48, 12.27]
      and tab[13][3:] == [11.58, 11.63] and tab[20] == [3.35, 5.26, 6.63, 7.70, 8.48]
      and tab[50] == [1.37, 2.16, 2.72, 3.16, 3.93] and tab[5] == [12.16, 18.62, 23.50, 27.28, 20.16]
      and tab[8] == [7.97, 12.34, 15.58, 18.08, 15.81])


def steps(P, s0, ds, phi, dps):
    mp.mp.dps = dps
    P_ = mp.mpf(P)
    X = mp.mpf(2)
    al = X ** (-1 / P_)
    out = []
    for d in ds:
        s, k = mp.mpf(s0), 0
        while abs(s / al - 1) > mp.mpf(10) ** (-d):
            s = phi(s, X, P_)
            k += 1
        out.append(k)
    return out


def sup(kfun):
    def f(s, X, P):
        T = X * s**P
        kap = kfun(T, P)
        return s * kap / (kap - 1 + T)
    return f


maps = {
    "MA": lambda s, X, P: 1 - (X - 1) / (X * sum(s**j for j in range(int(P)))),
    "AK": sup(lambda T, P: P),
    "AD": sup(lambda T, P: (P + 1 + (P - 1) * T) / 2),
    "proj": sup(lambda T, P: 2 * P * ((2 * P - 1) * T + P + 1) / ((P + 1) * T + 5 * P - 1)),
    "dec": sup(lambda T, P: 1 + (P - 1) * mp.sqrt(((P - 2) * (T * T + 1) + (10 * P + 4) * T) / (12 * P))),
    "nest": sup(lambda T, P: 1 + (P - 1) * q9f(T, P)),
}
expect3 = {"MA": [8, 17, 44, 90], "AK": [3, 4, 5, 6], "AD": [2, 3, 3, 4],
           "proj": [2, 2, 3, 3], "dec": [1, 2, 2, 3], "nest": [1, 1, 2, 2]}
for nm, f in maps.items():
    got = steps(3, "0.75", (6, 12, 30, 60), f, 300)
    check(f"Table 6 steps, {nm}", got == expect3[nm], got)
got_d = steps(20, "0.75", (30, 60, 250, 1000, 2500), maps["dec"], 2600)
got_n = steps(20, "0.75", (30, 60, 250, 1000, 2500), maps["nest"], 2600)
check("Table 8 steps (p = 20)", got_d == [4, 5, 5, 6, 7] and got_n == [3, 3, 4, 5, 5], f"{got_d} {got_n}")

# ---------------------------------------------------------------- Section 4.5 / 6
mp.mp.dps = 40
th = 1 / mp.pi
for nu, mu, eta_s, bound_s in ((7, 22, "1.28e-4", "8.9e-5"), (113, 355, "2.70e-8", "1.9e-8")):
    eta = abs(mp.mpf(nu) / mu - th)
    bnd = mp.e ** (eta * mp.log(2)) - 1
    true = abs(mp.mpf(2) ** (mp.mpf(nu) / mu) / mp.mpf(2) ** th - 1)
    check(f"Remark 4.8, mu/nu = {mu}/{nu}",
          abs(eta / mp.mpf(eta_s) - 1) < 0.01 and bnd <= mp.mpf(bound_s) and true <= bnd,
          f"eta={mp.nstr(eta, 4)}")

tau, z, lam = sp.symbols("tau z lambda")
Pi = lambda s: 12 + 6 * (2 + s) * z + (s + 1) * (s + 2) * z**2
check("Pade differential identity",
      sp.expand((1 + z) * (sp.diff(Pi(tau), z) * Pi(-tau) - Pi(tau) * sp.diff(Pi(-tau), z))
                - tau * Pi(tau) * Pi(-tau) + tau * (1 - tau**2) * (4 - tau**2) * z**4) == 0)
UL = (1 + z) / ((Pi(lam) / Pi(-lam)) * (Pi(1 - lam) / Pi(lam - 1)))
check("(6.6) width equality",
      sp.simplify(UL - 1 - lam * (1 - lam) * (2 - lam) * (1 + lam) * z**5 / (Pi(lam) * Pi(1 - lam))) == 0)
check("(6.7) L5 evaluation form", sp.expand(Pi(lam) - Pi(-lam) - 6 * lam * z * (2 + z)) == 0)
depth_ok = True
for d, nH, nP, beta in ((6, 9, 2, sp.Rational(19, 100)), (8, 12, 4, sp.Rational(3, 40)),
                        (12, 19, 6, sp.Rational(3, 250)), (15, 24, 8, sp.Rational(3, 1000))):
    eps_ = sp.Rational(1, 10**d)
    depth_ok &= beta**5 / 256 <= eps_ and (1 + beta) ** (2**nP) >= 2
    depth_ok &= (1 + beta) ** (2 ** (nP - 1)) < 2 or nP == 0
    hA = lambda n: mp.sinh(mp.log(2) / 2 ** (n + 1)) ** 2
    depth_ok &= hA(nH) <= mp.mpf(10) ** (-d) < hA(nH - 1)
check("Table 10 depth certificates", bool(depth_ok))
dep = []
for d in (6, 12, 30, 60):
    n = 0
    while (mp.mpf(2) ** (mp.mpf(1) / 2**n) - 1) ** 5 / 256 > mp.mpf(10) ** (-d):
        n += 1
    dep.append((n, 15 * n + 63))
check("subdivision depths for d = 6, 12, 30, 60",
      dep == [(2, 93), (6, 153), (18, 333), (38, 633)], dep)
lam_ = mp.mpf(32) / 75
z_ = mp.mpf(2) ** (mp.mpf(1) / 16) - 1
Pf = lambda s: 12 + 6 * (2 + s) * z_ + (s + 1) * (s + 2) * z_**2
L5 = Pf(lam_) / Pf(-lam_)
U5 = (1 + z_) / (Pf(1 - lam_) / Pf(lam_ - 1))
true = mp.mpf(2) ** (mp.mpf(2) / 75)
check("p = 37.5 example enclosure",
      mp.mpf("1.0186558096") < L5 <= true <= U5 < mp.mpf("1.0186558103"))

# ---------------------------------------------------------------- appendices
phi = sp.symbols("phi")
Pp = (p - 1) ** 2 * S * (phi - 1) ** 2 - 12 * p * (t * phi - 1) ** 2
check("(C.1) quadratic relation", sp.simplify(Pp.subs(phi, (1 + g) / (t + g))) == 0)
serC = sp.series(Pp.subs({phi: (1 + xi) ** (-1 / p), t: 1 + xi}), xi, 0, 7).removeO()
check("contact six of the quadratic",
      sp.simplify(serC - (p - 2) * (p - 1) ** 2 * (p + 1) * (3 * p + 1) / (60 * p**4) * xi**6) == 0)
check("discriminants",
      sp.expand(sp.Poly(Pp, phi).discriminant() - 48 * p * (p - 1) ** 2 * (t - 1) ** 2 * S) == 0
      and sp.expand(sp.Poly(S, t).discriminant() - 96 * p * (p + 1)) == 0)
Wd, Hd, Xd, s_ = sp.symbols("W H X s", positive=True)
Zx = Wd * (1 + (5 * p - 1) / (2 * p * (2 * p - 1)))
Zy = Hd * (1 + (p + 1) / ((2 * p - 1) * Xd))
ly = Hd * (1 + (5 * p - 1) / ((p + 1) * Xd))
Ey = Hd * (1 - t / Xd)
Dx = Zx + (ly - Zy) * (Wd - Zx) / (Ey - Zy)
kproj = sp.simplify((ly - Hd) / (Dx - Wd) * Wd * Xd / Hd)
check("projective preparation gives kappa of Table 3", sp.simplify(kproj - supports["proj"][0]) == 0)
Tm = s_ * 2 * p * ((2 * p - 1) * Xd * s_**p + p + 1) / Qproj.subs(t, Xd * s_**p)
check("projective derivative",
      sp.simplify(sp.diff(Tm, s_) + 2 * p * (p**2 - 1) * (2 * p - 1) * (Xd * s_**p - 1) ** 3
                  / Qproj.subs(t, Xd * s_**p) ** 2) == 0)
# decentred-arc preparation
eta_ = (p - 1) * sp.sqrt((p - 2) / (12 * p))
zeta_ = (5 * p + 2) / (p - 2)
kap_arc = 1 + eta_ * sp.sqrt(t**2 + 2 * zeta_ * t + 1)
check("arc preparation gives 1 + (p-1) q5",
      all(abs(sp.N((kap_arc - 1 - g).subs({p: a, t: b}), 30)) < 1e-25 for a, b in [(3, 2), (7, sp.Rational(1, 3))]))

print()
if FAIL:
    print("FAILED:", FAIL)
    sys.exit(1)
print("All checks passed.")
