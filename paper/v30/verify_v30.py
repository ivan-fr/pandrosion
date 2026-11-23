#!/usr/bin/env python3
"""Independent checks for "Geometric Root Calculators", V30.

Exact parts use SymPy rational arithmetic; numerical parts use mpmath.
Requires: sympy, mpmath.  Run:  python3 verify_v30.py
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

# ---------------------------------------------------------------- numerics
mp.mp.dps = 60


def mean_coeffs(P):
    m_ = (P - 2) * (47 * P**2 + 21 * P + 4) / (60 * P * (4 * P**2 - 1))
    g_ = 16 * (P + 1) * (4 * P**2 - 1) / (15 * P * (5 * P**2 + 4))
    n_ = 49 * P * (P + 1) * (P**2 - 4) / (10 * (4 * P**2 - 1) * (5 * P**2 + 4))
    d_ = (5 * P**2 + 4) / (84 * P**2)
    return m_, g_, n_, d_


def qMf(T, P):
    m_, g_, n_, d_ = mean_coeffs(P)
    return m_ * (1 + T) + g_ * mp.sqrt(T) - n_ * mp.sqrt(T + d_ * (T - 1) ** 2)


# ---------------------------------------------------------------- Section 6
tab = {}
for P in (3, 5, 8, 12, 13, 20, 50):
    tab[P] = [round(1000 * log(o) / N, 2) for o, N in
              ((2, 10 * P + 7), (3, 10 * P + 9), (4, 10 * P + 9), (5, 10 * P + 9))]
tabM = [round(1000 * log(9) / (10 * P + 11), 2) for P in (3, 5, 8, 12, 13, 20, 50)]
check("Table 8, three-mean row", tabM == [53.59, 36.02, 24.15, 16.77, 15.58, 10.41, 4.30], tabM[0])
check("three-mean index exceeds the other supports, p = 3..2000",
      all(log(9) / (10 * P + 11) > max(log(o) / N for o, N in ((2, 10 * P + 7), (3, 10 * P + 9), (4, 10 * P + 9),
                                                              (5, 10 * P + 9))) for P in range(3, 2001))
      and 5**11 < 9**9 and abs(log(9) / log(5) * 39 / 41 - 1.30) < 0.005)
check("three-mean inventory sums 3 j, 2p+1 par, 3 arcs",
      sp.expand(3 + 2 * (2 * p + 1) + 3 + 3 * (2 * p + 1) - (10 * p + 11)) == 0)
check("Table 8 values, other rows",
      tab[3] == [18.73, 28.17, 35.55, 41.27] and tab[5] == [12.16, 18.62, 23.50, 27.28]
      and tab[8] == [7.97, 12.34, 15.58, 18.08] and tab[12] == [5.46, 8.52, 10.75, 12.48]
      and tab[13] == [5.06, 7.90, 9.97, 11.58] and tab[20] == [3.35, 5.26, 6.63, 7.70]
      and tab[50] == [1.37, 2.16, 2.72, 3.16])


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
    "MB": lambda s, X, P: 1 - (X - 1) / (X * sum(s**j for j in range(int(P)))),
    "AK": sup(lambda T, P: P),
    "AD": sup(lambda T, P: (P + 1 + (P - 1) * T) / 2),
    "proj": sup(lambda T, P: 2 * P * ((2 * P - 1) * T + P + 1) / ((P + 1) * T + 5 * P - 1)),
    "dec": sup(lambda T, P: 1 + (P - 1) * mp.sqrt(((P - 2) * (T * T + 1) + (10 * P + 4) * T) / (12 * P))),
    "mean": sup(lambda T, P: 1 + (P - 1) * qMf(T, P)),
}
expect3 = {"MB": [8, 17, 44, 90], "AK": [3, 4, 5, 6], "AD": [2, 3, 3, 4],
           "proj": [2, 2, 3, 3], "dec": [1, 2, 2, 3], "mean": [1, 1, 2, 2]}
for nm, f in maps.items():
    got = steps(3, "0.75", (6, 12, 30, 60), f, 300)
    check(f"Table 7 steps, {nm}", got == expect3[nm], got)
got_d = steps(20, "0.75", (30, 60, 250, 1000, 2500), maps["dec"], 2600)
got_m = steps(20, "0.75", (30, 60, 250, 1000, 2500), maps["mean"], 2600)
check("Table 9 steps (p = 20)", got_d == [4, 5, 5, 6, 7] and got_m == [3, 3, 4, 4, 5], f"{got_d} {got_m}")
check("Table 9 totals (p = 20)", [209 * k for k in got_d] == [836, 1045, 1045, 1254, 1463]
      and [211 * k for k in got_m] == [633, 633, 844, 844, 1055])

# ---------------------------------------------------------------- Sections 5 and 7
mp.mp.dps = 40
th = 1 / mp.pi
for nu, mu, eta_s, bound_s in ((7, 22, "1.28e-4", "8.9e-5"), (113, 355, "2.70e-8", "1.9e-8")):
    eta = abs(mp.mpf(nu) / mu - th)
    bnd = mp.e ** (eta * mp.log(2)) - 1
    true = abs(mp.mpf(2) ** (mp.mpf(nu) / mu) / mp.mpf(2) ** th - 1)
    check(f"Remark 5.4, mu/nu = {mu}/{nu}",
          abs(eta / mp.mpf(eta_s) - 1) < 0.01 and bnd <= mp.mpf(bound_s) and true <= bnd,
          f"eta={mp.nstr(eta, 4)}")

tau, z, lam = sp.symbols("tau z lambda")
Pi = lambda s: 12 + 6 * (2 + s) * z + (s + 1) * (s + 2) * z**2
check("Pade differential identity",
      sp.expand((1 + z) * (sp.diff(Pi(tau), z) * Pi(-tau) - Pi(tau) * sp.diff(Pi(-tau), z))
                - tau * Pi(tau) * Pi(-tau) + tau * (1 - tau**2) * (4 - tau**2) * z**4) == 0)
UL = (1 + z) / ((Pi(lam) / Pi(-lam)) * (Pi(1 - lam) / Pi(lam - 1)))
check("(7.6) width equality",
      sp.simplify(UL - 1 - lam * (1 - lam) * (2 - lam) * (1 + lam) * z**5 / (Pi(lam) * Pi(1 - lam))) == 0)
check("(7.7) L5 evaluation form", sp.expand(Pi(lam) - Pi(-lam) - 6 * lam * z * (2 + z)) == 0)
depth_ok = True
for d, nH, nP, beta in ((6, 9, 2, sp.Rational(19, 100)), (8, 12, 4, sp.Rational(3, 40)),
                        (12, 19, 6, sp.Rational(3, 250)), (15, 24, 8, sp.Rational(3, 1000))):
    eps_ = sp.Rational(1, 10**d)
    depth_ok &= beta**5 / 256 <= eps_ and (1 + beta) ** (2**nP) >= 2
    depth_ok &= (1 + beta) ** (2 ** (nP - 1)) < 2 or nP == 0
    hA = lambda n: mp.sinh(mp.log(2) / 2 ** (n + 1)) ** 2
    depth_ok &= hA(nH) <= mp.mpf(10) ** (-d) < hA(nH - 1)
check("Table 11 depth certificates", bool(depth_ok))
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


# ---------------------------------------------------------------- Section 4: three means
tau, Rr, rr_ = sp.symbols("tau Rr rr")
mC, gC, nC, dC = mean_coeffs(p)
check("4.1: 2m + g - n = 1; cubic 7/90, 64/63, 6/35, 7/108",
      sp.cancel(2 * mC + gC - nC - 1) == 0
      and [c_.subs(p, 3) for c_ in (mC, gC, nC, dC)]
      == [sp.Rational(7, 90), sp.Rational(64, 63), sp.Rational(6, 35), sp.Rational(7, 108)])
mH = (1 - 2 * h) * (4 * h**2 + 21 * h + 47) / (60 * (4 - h**2))
gH = 16 * (1 + h) * (4 - h**2) / (15 * (4 * h**2 + 5))
nH = 49 * (1 + h) * (1 - 4 * h**2) / (10 * (4 - h**2) * (4 * h**2 + 5))
dH = (4 * h**2 + 5) / 84
check("4.1: coefficients in h = 1/p",
      all(sp.cancel(a_.subs(p, 1 / h) - b_) == 0 for a_, b_ in ((mC, mH), (gC, gH), (nC, nH), (dC, dH))))
check("Sec. 5: p = 2 gives m = n = 0, g = 1, q_* = sqrt(t)",
      [sp.cancel(c_.subs(p, 2)) for c_ in (mC, gC, nC)] == [0, 1, 0]
      and sp.simplify(((t - t ** sp.Rational(1, 2)) / (t ** sp.Rational(1, 2) - 1)) - sp.sqrt(t)) == 0)
check("Sec. 5: m, n < 0 for 1/2 < p < 2",
      all(mC.subs(p, sp.Rational(k, 20)) < 0 and nC.subs(p, sp.Rational(k, 20)) < 0 for k in range(11, 40)))
check("Sec. 4: a_5 = (p-2)/(12p): q5^2 = t + a_5 (t-1)^2",
      sp.expand(q5**2 - t - (p - 2) / (12 * p) * (t - 1) ** 2) == 0)
SM = tau**2 + dC * (tau**2 - 1) ** 2
ellM = mC * (1 + tau**2) + gC * tau


def basis(P_):
    """palindromic quartic -> coefficients on (tau-1)^4, tau (tau-1)^2, tau^2"""
    P_ = sp.Poly(sp.expand(P_), tau)
    co = [P_.coeff_monomial(tau**k) for k in range(5)]
    c0, c1, c2 = co[0], sp.expand(4 * co[0] + co[1]), sp.expand(2 * co[0] + 2 * co[1] + co[2])
    assert sp.expand(c0 * (tau - 1) ** 4 + c1 * tau * (tau - 1) ** 2 + c2 * tau**2 - P_.as_expr()) == 0
    return c0, c1, c2


def shifted(cc):
    return sp.Poly(sp.expand(cc.subs(p, 2 + rr_)), rr_).all_coeffs()


PQ = sp.expand(sp.cancel((ellM**2 - nC**2 * SM) * 900 * p**2 * (4 * p**2 - 1) * (5 * p**2 + 4)))
Qc = basis(PQ)
check("(4.6): Q0, Q1, Q2 as stated, nonnegative for p >= 2",
      sp.expand(Qc[0] - (p - 2) ** 2 * (2 * p - 1) * (313 * p**3 + 272 * p**2 + 200 * p + 16)) == 0
      and sp.expand(Qc[1] - 60 * p * (p - 2) * (2 * p - 1) * (71 * p**3 + 74 * p**2 + 40 * p - 8)) == 0
      and sp.expand(Qc[2] - 180 * p**2 * (149 * p**4 + 49 * p**3 - 141 * p**2 - 196 * p - 20)) == 0
      and all(all(c_ >= 0 for c_ in shifted(q_)) for q_ in Qc) and shifted(Qc[2])[-1] > 0
      and sp.Poly(sp.expand((149 * p**4 + 49 * p**3 - 141 * p**2 - 196 * p - 20).subs(p, 2 + rr_)), rr_).all_coeffs()
      == [149, 1241, 3729, 4596, 1800])
cc_ = p - 1
qq_ = ellM - nC * Rr
NR = sp.expand(2 * tau**2 * (1 + cc_ * qq_) * Rr
               + cc_ * tau * (sp.diff(ellM, tau) * Rr - nC * sp.diff(SM, tau) / 2) * (1 - tau**2)
               - (2 / p) * (tau**2 + cc_ * qq_) * (1 + cc_ * qq_) * Rr)
An, Bn = 0, 0
for (k,), co in sp.Poly(NR, Rr).terms():
    if k % 2 == 0:
        An += co * SM ** (k // 2)
    else:
        Bn += co * SM ** ((k - 1) // 2)
kapM = (p**2 - 4) * (p**2 - 1)
QdM = p**3 * (4 * p**2 - 1) ** 2 * (5 * p**2 + 4) ** 2
Psi1 = sp.expand(sp.cancel(An * 1800 * QdM / (7 * kapM)))
Psi2 = sp.expand(sp.cancel(-Bn * 900 * QdM / kapM))
T4 = {
    "Psi1": [1175 * p**8 + 2755 * p**6 + 2352 * p**4 + 880 * p**2 + 128,
             5120 * p**8 - 3584 * p**6 - 3264 * p**4 + 1984 * p**2 - 256,
             -6635 * p**8 + 13877 * p**6 + 17808 * p**4 + 1808 * p**2 - 128,
             75776 * p**8 - 121856 * p**6 + 54912 * p**4 - 9344 * p**2 + 512],
    "Psi2": [30185 * p**8 + 32563 * p**6 + 16572 * p**4 + 8032 * p**2 + 128,
             54180 * p**8 + 100044 * p**6 + 85680 * p**4 + 32256 * p**2,
             262836 * p**8 - 335160 * p**6 + 310464 * p**4],
    "Psi3": [489845 * p**8 + 647956 * p**6 + 361344 * p**4 + 123904 * p**2 - 1024,
             804380 * p**8 + 1583824 * p**6 + 2050176 * p**4 + 1033216 * p**2 - 4096,
             3829896 * p**8 - 3081456 * p**6 + 2225664 * p**4 + 2128896 * p**2],
}
a0_, a1_, a2_, a3_ = T4["Psi1"]
check("(4.7): slope numerator, Psi1 as in Table 4",
      sp.expand(Psi1 - (a0_ * (tau**6 + 1) + a1_ * (tau**5 + tau) + a2_ * (tau**4 + tau**2) + a3_ * tau**3)) == 0)
B_ = basis(Psi2)
check("(4.7): Psi2 as in Table 4, coefficients positive for p >= 2",
      all(sp.expand(a_ - b_) == 0 for a_, b_ in zip(B_, T4["Psi2"]))
      and all(all(c_ > 0 for c_ in shifted(b_)) and len(shifted(b_)) == 9 for b_ in B_))
Dnum = 84 * p**2 * tau**2 + (5 * p**2 + 4) * (tau**2 - 1) ** 2
Psi3 = sp.cancel((4 * Psi2**2 * Dnum - 49 * 84 * p**2 * Psi1**2)
                 / (16 * (4 * p**2 - 1) ** 3 * (5 * p**2 + 4) ** 2 * (tau - 1) ** 8))
E_ = basis(Psi3)
check("(4.8): rationalization, Psi3 as in Table 4, positive",
      Psi3.is_polynomial(p, tau)
      and all(sp.expand(a_ - b_) == 0 for a_, b_ in zip(E_, T4["Psi3"]))
      and all(all(c_ > 0 for c_ in shifted(b_)) and len(shifted(b_)) == 9 for b_ in E_))
# local order: exact series in X = log t with symbolic h
Xs = sp.symbols("Xs")
ser10 = lambda e_: sp.series(e_, Xs, 0, 10).removeO()
Fstar = h * sp.sinh((1 - h) * Xs / 2) / ((1 - h) * sp.sinh(h * Xs / 2))
FM = 2 * mH * sp.cosh(Xs / 2) + gH - nH * sp.sqrt(1 + 4 * dH * sp.sinh(Xs / 2) ** 2)
dser = sp.expand(ser10(FM) - ser10(Fstar))
D4M = (2 - h) * (1 + h) * (2 + h) * (1 - 2 * h) * (1 + 2 * h) * (8 * h**2 + 17) / 203212800
check("(4.9): q_M - q_* = D4M w^4 sqrt(t) + ..., exact in h",
      all(sp.cancel(dser.coeff(Xs, k)) == 0 for k in range(8)) and sp.cancel(dser.coeff(Xs, 8) - D4M) == 0)
cM = (p**2 - 1) * (p**2 - 4) * (4 * p**2 - 1) * (17 * p**2 + 8) / 203212800
check("(4.5): c_M = (p-1) p^7 D4M, c_M(3) = 23/20736, denominator",
      sp.cancel((p - 1) * p**7 * D4M.subs(h, 1 / p) - cM) == 0 and cM.subs(p, 3) == sp.Rational(23, 20736)
      and 2**11 * 3**4 * 5**2 * 7**2 == 203212800)
check("Sec. 4: c_M p^-8 -> 17/(2^9 3^4 5^2 7^2) ~ 3.35e-7; arc -> 1/480",
      sp.limit(cM / p**8, p, sp.oo) == sp.Rational(17, 2**9 * 3**4 * 5**2 * 7**2)
      and sp.limit(supports["dec"][2] / p**4, p, sp.oo) == sp.Rational(1, 480))
# Section 1: the removed V29 nested constant c_9 is larger than c_M for every p > 2
N9 = 21311 * p**6 + 1650 * p**5 - 21679 * p**4 - 15532 * p**3 - 4411 * p**2 - 526 * p - 29
c9 = (p**2 - 1) * (p - 2) * N9 / (2**11 * 3**4 * 5**3 * 7**2 * (3 * p + 1))
ratio = sp.cancel(c9 / cM)
check("Sec. 1: c_M < c_9 (V29) for p > 2; inventory saving 48",
      all(ratio.subs(p, sp.Rational(2) + sp.Rational(k, 10)) > 1 for k in range(1, 2000))
      and sp.limit(ratio, p, sp.oo) > 1 and (10 * 3 + 59) - (10 * 3 + 11) == 48)
# Remark 5.2: one radical, order seven
m7 = (h + 3) * (1 - 2 * h) / (4 * (4 - h**2))
n7 = 5 * (1 + h) / (2 * (4 - h**2))
e7 = (1 - 4 * h**2) / 60
F7 = 2 * m7 * sp.cosh(Xs / 2) + n7 * sp.sqrt(1 - 4 * e7 * sp.sinh(Xs / 2) ** 2)
d7 = sp.expand(sp.series(F7, Xs, 0, 8).removeO() - sp.series(Fstar, Xs, 0, 8).removeO())
c7 = -(p**2 - 1) * (p**2 - 4) * (4 * p**2 - 1) / 302400
check("Remark 4.2: q7 has contact six, constant, cubic form",
      sp.cancel(2 * m7 + n7 - 1) == 0 and all(sp.cancel(d7.coeff(Xs, k)) == 0 for k in range(6))
      and sp.cancel((p - 1) * p**5 * d7.coeff(Xs, 6).subs(h, 1 / p) - c7) == 0
      and [v_.subs(h, sp.Rational(1, 3)) for v_ in (m7, n7, e7)]
      == [sp.Rational(1, 14), sp.Rational(6, 7), sp.Rational(1, 108)])
# Appendix C: the unconstrained quadratic approximant at p = 3
ys = sp.symbols("ys")
h3 = sp.Rational(1, 3)
Fx = sp.series(Fstar.subs(h, h3), Xs, 0, 14).removeO()
Yx = sp.series(2 * sp.cosh(Xs / 2) - 2, Xs, 0, 14).removeO()
coefs, rem, Ypow = [], sp.expand(Fx), sp.Integer(1)
for k in range(7):
    ck = rem.coeff(Xs, 2 * k) / (Ypow.coeff(Xs, 2 * k) if k else 1)
    coefs.append(ck)
    rem = sp.expand(rem - ck * Ypow)
    Ypow = sp.series(sp.expand(Ypow * Yx), Xs, 0, 14).removeO()
Fy = sum(coefs[k] * ys**k for k in range(7))
sig = ys + 2
ours = sp.Rational(7, 90) * sig + sp.Rational(64, 63) - sp.Rational(6, 35) * sp.sqrt(1 + sp.Rational(7, 108) * (sig**2 - 4))
free = sp.Rational(16, 33) - sig / 66 + sp.sqrt(5 * sig**2 + 736 * sig + 1424) / 99
so = sp.series(ours - Fy, ys, 0, 5).removeO()
sf = sp.series(free - Fy, ys, 0, 6).removeO()
check("App. C: three-mean error 23/354294 (sigma-2)^4 at p = 3",
      sp.expand(so - sp.Rational(23, 354294) * ys**4) == 0)
check("App. C: unconstrained form, error (sigma-2)^5/19131876",
      sp.expand(sf - ys**5 / 19131876) == 0)

# numerics for the three-mean support
mp.mp.dps = 60
Psi1f = sp.lambdify((p, tau), Psi1, "mpmath")
Psi2f = sp.lambdify((p, tau), Psi2, "mpmath")


def gapM(P, x_):
    m_, g_, n_, d_ = mean_coeffs(P)
    q_ = m_ * (1 + x_**2) + g_ * x_ - n_ * mp.sqrt(x_**2 + d_ * (x_**2 - 1) ** 2)
    return mp.log(x_**2 + (P - 1) * q_) - mp.log(1 + (P - 1) * q_) - 2 * mp.log(x_) / P


worst = 0
for P in ("2.1", "3", "4.5", "11", "100"):
    P_ = mp.mpf(P)
    m_, g_, n_, d_ = mean_coeffs(P_)
    for x_ in ("0.05", "0.5", "0.9", "1.2", "3", "40"):
        x_ = mp.mpf(x_)
        rho_ = mp.sqrt(x_**2 + d_ * (x_**2 - 1) ** 2)
        q_ = m_ * (1 + x_**2) + g_ * x_ - n_ * rho_
        formula = -(P_**2 - 4) * (P_**2 - 1) * (2 * Psi2f(P_, x_) * rho_ - 7 * Psi1f(P_, x_)) / (
            1800 * P_**3 * (4 * P_**2 - 1) ** 2 * (5 * P_**2 + 4) ** 2 * x_ * rho_
            * (x_**2 + (P_ - 1) * q_) * (1 + (P_ - 1) * q_))
        worst = max(worst, abs(formula / mp.diff(lambda y_: gapM(P_, y_), x_) - 1))
check("(4.7) against a numerical derivative, 30 points", worst < mp.mpf(10) ** (-25), mp.nstr(worst, 3))
for P in ("2.5", "3", "4", "7", "20"):
    P_ = mp.mpf(P)
    ee = mp.mpf("1e-5")
    T = mp.e ** (-P_ * ee)
    q_ = qMf(T, P_)
    num = (ee + mp.log((T + (P_ - 1) * q_) / (1 + (P_ - 1) * q_))) / ee**9
    exact = mp.mpf(sp.N(cM.subs(p, sp.Rational(P)), 50))
    check(f"c_M({P}) against the iteration", abs(num / exact - 1) < 1e-6, mp.nstr(exact, 8))
bad, tot = 0, 0
for P in ("2.001", "2.01", "2.1", "2.5", "3", "4", "5", "7", "10", "13", "20", "50", "100", "1000", "10000"):
    P_ = mp.mpf(P)
    for k in list(range(-240, 0)) + list(range(1, 241)):
        T = mp.mpf(10) ** (mp.mpf(k) / 20)
        q_ = qMf(T, P_)
        G_ = (T + (P_ - 1) * q_) / (1 + (P_ - 1) * q_)
        ex_ = T ** (1 / P_)
        tot += 1
        bad += not ((1 < G_ < ex_) if T > 1 else (ex_ < G_ < 1)) or q_ <= 0
check("three-mean enclosure on the (p,t) grid", bad == 0, f"{tot} points")


def mean_protocol(P, X, s, Hh, Wd=None):
    """Line and circle incidences of Section 4.2; Wd=None uses the shape (4.4)."""
    m_, g_, n_, d_ = mean_coeffs(P)
    lam = Hh / X
    zeta = 1 / (2 * d_) - 1
    aspect = Wd is None
    if aspect:
        Wd = lam * (n_ / m_) * mp.sqrt((1 - 4 * d_) / (4 * d_))
    gam = 1 + 2 * (P - 1) * m_
    xv = Wd * (1 - 1 / gam)
    Kg = (P - 1) * g_ * lam / gam
    Kn = (P - 1) * n_ * mp.sqrt(d_) * lam / gam
    x2, x3 = Wd * Kg / (2 * lam), Wd * Kn / lam
    T = X * s**P
    yM, yE, yP = Hh - lam, Hh - lam * T, Hh * (1 - s)
    sig_ = (yE - yM) / Wd
    onME = lambda xx: yM + sig_ * xx
    if aspect:
        x1 = (P - 1) * m_ * Wd / gam
        assert abs((xv - x1) - Kn * mp.sqrt(zeta**2 - 1)) < mp.mpf(10) ** (-40)
        J1 = (x1, onME(x1))
    else:                                   # one more join: project E from a prepared centre
        x1 = xv - Kn * mp.sqrt(zeta**2 - 1)
        r0 = (P - 1) * m_ / gam
        Cx, Cy = (x1 - r0 * Wd) / (1 - r0), Hh - lam
        J1 = (x1, Cy + (x1 - Cx) / (Wd - Cx) * (yE - Cy))
    J2, J3 = (x2, onME(x2)), (x3, onME(x3))
    G2, G3 = (x2, yM + Kg), (x3, yM + Kn * (1 + zeta))
    r1 = mp.sqrt((J3[0] - G3[0]) ** 2 + (J3[1] - G3[1]) ** 2)
    D1 = (xv, J1[1] + mp.sqrt(r1**2 - (xv - J1[0]) ** 2))             # arc 1, upper point on v
    r2 = mp.sqrt((J2[0] - G2[0]) ** 2 + (J2[1] - G2[1]) ** 2)
    Zx = x2 + mp.sqrt(r2**2 - (yM - J2[1]) ** 2)                       # arc 2 meets the horizontal of M
    DM = (xv, D1[1] - (Zx - x2))                                       # arc 3, lower point on v
    ksup = (Hh - DM[1]) / (Wd - DM[0])                                 # slope of A D_M
    xT = (yP - Hh + ksup * Wd - sig_ * Wd) / (ksup - sig_)
    yT = Hh + ksup * (xT - Wd)
    return (Hh - yT) / Hh


worstA, worstG, cnt = 0, 0, 0
for P in (3, 4, 5, 7, 12, 20):
    for X in ("2", "10", "0.3", "100"):
        for fac in ("0.2", "0.75", "0.99", "1.3", "5"):
            P_, X_ = mp.mpf(P), mp.mpf(X)
            s_ = X_ ** (-1 / P_) * mp.mpf(fac)
            T = X_ * s_**P_
            kap_ = 1 + (P_ - 1) * qMf(T, P_)
            scal = s_ * kap_ / (kap_ - 1 + T)
            worstA = max(worstA, abs(mean_protocol(P_, X_, s_, mp.mpf(4)) / scal - 1))
            worstG = max(worstG, abs(mean_protocol(P_, X_, s_, mp.mpf(4), mp.mpf(3)) / scal - 1))
            cnt += 1
check("4.2: three-arc protocol returns the scalar update", worstA < mp.mpf(10) ** (-40) and cnt == 120,
      mp.nstr(worstA, 3))
check("Prop. 6.1: arbitrary rectangle with one more join", worstG < mp.mpf(10) ** (-40), mp.nstr(worstG, 3))
ar = lambda P: float(mean_coeffs(P)[2] / mean_coeffs(P)[0]
                     * mp.sqrt((1 - 4 * mean_coeffs(P)[3]) / (4 * mean_coeffs(P)[3])))
ars = [ar(mp.mpf(2) + mp.mpf(k) / 50) for k in range(1, 5000)]
check("(4.4): shape 3.7256 at p = 3, decreasing, limit 2.238",
      abs(ar(mp.mpf(3)) - 3.7256) < 1e-4 and all(a_ > b_ for a_, b_ in zip(ars, ars[1:]))
      and abs(ar(mp.mpf(10) ** 9) - 2.238) < 1e-3)
W3 = ar(mp.mpf(3)) * 4 / 2
check("Figure 2: W = 7.451 for H = 4, X = 2", abs(W3 - 7.451) < 1e-3, f"{W3:.4f}")

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
