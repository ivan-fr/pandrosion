//! Exact part: values of S, S', S'' at Gaussian dyadic points with integers; the certificate and the sweeps
//! that continue it.
use crate::complex::{C, ZERO};
use crate::float::{coeffs3, frexp, ldexp, products, fixed_point, mirror, rectangle_step, Ev, EvalWs, Options, Poly, StepWs, U};
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

/// A polynomial with Gaussian integer coefficients, highest degree first.
pub type GPoly = Vec<(BigInt, BigInt)>;

/// v = n / 2^d exactly (n integer, d >= 0).
pub(crate) fn dyadic(v: f64) -> (BigInt, u64) {
    if v == 0.0 {
        return (BigInt::zero(), 0);
    }
    let bits = v.to_bits();
    let neg = bits >> 63 != 0;
    let ex = ((bits >> 52) & 0x7ff) as i64;
    let frac = bits & ((1u64 << 52) - 1);
    let (mut mant, mut e) = if ex == 0 { (frac, -1074i64) } else { (frac | (1u64 << 52), ex - 1075) };
    let tz = mant.trailing_zeros() as i64;
    mant >>= tz;
    e += tz;
    let mut n = BigInt::from(mant);
    if neg {
        n = -n;
    }
    if e >= 0 {
        (n << (e as u64), 0)
    } else {
        (n, (-e) as u64)
    }
}

/// n/d = f 2^e with a relative error below 2^-50 (d > 0).
pub(crate) fn fl2(n: &BigInt, d: &BigInt) -> (f64, i64) {
    if n.is_zero() {
        return (0.0, 0);
    }
    let sn = n.bits().saturating_sub(64);
    let sd = d.bits().saturating_sub(64);
    let a = (n >> sn).to_f64().unwrap();
    let b = (d >> sd).to_f64().unwrap();
    (a / b, sn as i64 - sd as i64)
}

/// (nr + i ni) / (dr + i di) * 2^ex as a complex float, from integers of any size.
fn cratio(nr: &BigInt, ni: &BigInt, dr: &BigInt, di: &BigInt, ex: i64) -> C {
    let one = BigInt::from(1);
    let pair = |r: &BigInt, i: &BigInt| {
        let (fr, er) = fl2(r, &one);
        let (fi, ei) = fl2(i, &one);
        let e = if fr == 0.0 {
            ei
        } else if fi == 0.0 {
            er
        } else {
            er.max(ei)
        };
        (C::new(ldexp(fr, er - e), ldexp(fi, ei - e)), e)
    };
    let (n, en) = pair(nr, ni);
    let (d, ed) = pair(dr, di);
    let q = n / d;
    C::new(ldexp(q.re, en - ed + ex), ldexp(q.im, en - ed + ex))
}

/// What is known of S at a point: S(z)/c = q 2^ex (exact value rounded, or an upper bound of the modulus
/// when `exact` is false), and the ratios a = S'/S, b = S''/S.
#[derive(Clone, Copy)]
pub struct Val {
    pub q: C,
    pub ex: i64,
    pub a: C,
    pub b: C,
    pub exact: bool,
}

/// S(z)/c, S'(z)/S(z), S''(z)/S(z) at a point with double precision coordinates, computed exactly with
/// integers and rounded at the end.
pub fn exact_values(ci: &GPoly, z: C) -> Val {
    let (nx, dx) = dyadic(z.re);
    let (ny, dy) = dyadic(z.im);
    let s = dx.max(dy);
    let x: BigInt = nx << (s - dx);
    let y: BigInt = ny << (s - dy);
    exact_values_xy(ci, &x, &y, s)
}

/// Exact Horner scheme at the point (x + i y) / 2^s: S, S', S''/2 as Gaussian integers scaled by 2^sh,
/// 2^(sh-s), 2^(sh-2s).  Returns (S, S', S''/2, sh).
pub(crate) fn exact_horner(ci: &GPoly, x: &BigInt, y: &BigInt, s: u64) -> ((BigInt, BigInt), (BigInt, BigInt), (BigInt, BigInt), u64) {
    let (mut pr, mut pi) = (ci[0].0.clone(), ci[0].1.clone());
    let (mut ar, mut ai, mut br, mut bi) = (BigInt::zero(), BigInt::zero(), BigInt::zero(), BigInt::zero());
    let mut sh: u64 = 0;
    let yzero = y.is_zero();
    for (a, b) in &ci[1..] {
        sh += s;
        if yzero {
            br = &br * x + &ar;
            bi = &bi * x + &ai;
            ar = &ar * x + &pr;
            ai = &ai * x + &pi;
            pr = &pr * x + (a << sh);
            pi = &pi * x + (b << sh);
        } else {
            let nbr = &br * x - &bi * y + &ar;
            let nbi = &br * y + &bi * x + &ai;
            let nar = &ar * x - &ai * y + &pr;
            let nai = &ar * y + &ai * x + &pi;
            let npr = &pr * x - &pi * y + (a << sh);
            let npi = &pr * y + &pi * x + (b << sh);
            br = nbr;
            bi = nbi;
            ar = nar;
            ai = nai;
            pr = npr;
            pi = npi;
        }
    }
    ((pr, pi), (ar, ai), (br, bi), sh)
}

/// The same at the point (x + i y) / 2^s, with integers x, y of any size.
pub fn exact_values_xy(ci: &GPoly, x: &BigInt, y: &BigInt, s: u64) -> Val {
    exact_val(ci, &exact_horner(ci, x, y, s), s)
}

/// The value from the result of `exact_horner`.
pub(crate) fn exact_val(ci: &GPoly, h: &((BigInt, BigInt), (BigInt, BigInt), (BigInt, BigInt), u64), s: u64) -> Val {
    let (c0r, c0i) = (&ci[0].0, &ci[0].1);
    let dn: BigInt = c0r * c0r + c0i * c0i;
    let ((pr, pi), (ar, ai), (br, bi), sh) = (&h.0, &h.1, &h.2, h.3);
    let (sh, s) = (sh as i64, s as i64);
    if pr.is_zero() && pi.is_zero() {
        return Val { q: ZERO, ex: 0, a: ZERO, b: ZERO, exact: true };
    }
    // p, d1, d2 are scaled by 2^sh, 2^(sh-s), 2^(sh-2s)
    let a = cratio(ar, ai, pr, pi, s);
    let b = cratio(br, bi, pr, pi, 2 * s).scale(2.0);
    let (fr, er) = fl2(&(pr * c0r + pi * c0i), &dn);
    let (fi, ei) = fl2(&(pi * c0r - pr * c0i), &dn);
    let e = if fr == 0.0 {
        ei
    } else if fi == 0.0 {
        er
    } else {
        er.max(ei)
    };
    Val { q: C::new(ldexp(fr, er - e), ldexp(fi, ei - e)), ex: e - sh, a, b, exact: true }
}

/// Round each point to 53 significant bits of its modulus.
pub fn quantize(z: C) -> C {
    let (_, e) = frexp(z.abs());
    let q = ldexp(1.0, e - 53);
    if !(q > 0.0) || !q.is_finite() {
        return z; // subnormal modulus (fewer than 53 bits already), or not a number
    }
    C::new((z.re / q).round() * q, (z.im / q).round() * q)
}

/// Upper bounds r_k >= m |W_k|.
fn smith(vals: &[Val], z: &[C]) -> Vec<f64> {
    let m = z.len();
    let prod = products(z);
    let mut r = vec![0.0; m];
    for k in 0..m {
        let v = &vals[k];
        if v.q.re == 0.0 && v.q.im == 0.0 {
            continue;
        }
        let (pf, pe) = prod[k];
        if pf == 0.0 || !v.q.is_finite() {
            r[k] = f64::INFINITY;
            continue;
        }
        let w = v.q.abs() / pf;
        let rk = m as f64 * ldexp(w, v.ex - pe) * (1.0 + (8.0 * m as f64 + 64.0) * U);
        // a radius near the underflow threshold is rounded upwards by hand
        // (an exact root, value zero, keeps the radius zero)
        let rk = if w == 0.0 { 0.0 } else if rk < 1e-290 { rk + 64.0 * 5e-324 } else { rk };
        r[k] = if rk.is_nan() { f64::INFINITY } else { rk };
    }
    r
}

pub struct Certified {
    pub z: Vec<C>,
    /// Smith radii
    pub r: Vec<f64>,
    /// fixed-point radii rho_k = 2 r_k / m
    pub rho: Vec<f64>,
    /// the disc D(z_k, rho_k) passes the fixed-point certificate: exactly one root
    pub one: Vec<bool>,
    /// every disc passes, is within the tolerance and (real coefficients) is decided
    pub strict: bool,
    /// the bounds of |S(z_k)| / |c| behind the radii (floating-point bound or ball evaluation)
    pub vals: Vec<Val>,
    /// where the value came from a ball evaluation: N = S/S' and beta = S S''/S'^2 in multiprecision
    pub parts: Vec<Option<(crate::precise::ZP, crate::precise::ZP)>>,
    pub certificates: usize,
    pub exact_sweeps: usize,
}

/// The certificate, and the sweeps that follow it when it asks for them (see the note G8, Section 4).
/// `ci` gives the exact coefficients; it is called only if the floating-point certificate is not enough.
/// `real`: the coefficients are real; a disc that touches the real axis is then fine only when its root is
/// proved real (its mirror image meets no other disc).
pub fn certify<'a>(ci: &dyn Fn() -> &'a GPoly, s: &Poly, z0: &[C], opt: &Options, real: bool) -> Certified {
    let m = s.degree();
    let mf = m as f64;
    let cf = coeffs3(mf);
    let floor = 8.0 * mf * U;
    // the radius compared with the tolerance is the one that may be printed: enlarged by the slack
    const SL: f64 = 1.0 + crate::float::SLACK;
    let passes = 30 + m;
    let mut z: Vec<C> = z0.iter().map(|&x| quantize(x)).collect();
    let mut bounds = Vec::new();
    s.bound_all(&z, &mut EvalWs::default(), &mut bounds);
    let mut vals: Vec<Val> = bounds.iter().map(|&(b, e)| Val { q: C::new(if b.is_nan() { f64::INFINITY } else { b }, 0.0), ex: e, a: ZERO, b: ZERO, exact: false }).collect();
    let state = |vals: &[Val], z: &[C]| {
        let r = smith(vals, z);
        let (rho, one) = fixed_point(z, &r);
        let mut nfine = 0usize;
        let mut rmax = 0.0f64;
        let fine: Vec<bool> = (0..z.len())
            .map(|k| {
                let a = z[k].abs();
                let f = r[k] <= floor * a
                    || (rho[k] * SL <= opt.tol * a && one[k] && (!real || z[k].im.abs() > rho[k] || ((rho[k] + z[k].im.abs()) * SL <= opt.tol * a && mirror(z, &rho, k, rho[k]))));
                nfine += f as usize;
                rmax = rmax.max(r[k]);
                f
            })
            .collect();
        (r, fine, (nfine, -rmax))
    };
    let (mut r, mut fine, mut score) = state(&vals, &z);
    let mut pv: Vec<Option<(crate::precise::ZP, crate::precise::ZP)>> = vec![None; m];
    let mut best = (z.clone(), r.clone(), score, vals.clone(), pv.clone());
    // values beyond the floating-point bound: ball evaluation in fixed point, as many bits as needed
    let cell: std::cell::OnceCell<crate::precise::BallPoly> = std::cell::OnceCell::new();
    let value = |zk: C| crate::precise::ball_auto(cell.get_or_init(|| crate::precise::BallPoly::new(ci(), opt.full_order)), &crate::precise::ZP::from_c(zk), 128, 4096, 53, 40, 0);
    let better = |a: (usize, f64), b: (usize, f64)| a.0 > b.0 || (a.0 == b.0 && a.1 > b.1);
    let (mut n, mut exact_sweeps) = (1usize, 0usize);
    let mut y = StepWs::default();
    let mut dz = vec![ZERO; m];
    while m > 1 && n < passes && !fine.iter().all(|&f| f) {
        let mut fresh = false;
        for k in 0..m {
            if !fine[k] && !vals[k].exact {
                let (v, _, p, _, _) = value(z[k]);
                vals[k] = v;
                pv[k] = p;
                fresh = true;
            }
        }
        if fresh {
            let st = state(&vals, &z);
            r = st.0;
            fine = st.1;
            score = st.2;
            if better(score, best.2) {
                best = (z.clone(), r.clone(), score, vals.clone(), pv.clone());
            }
            if fine.iter().all(|&f| f) {
                break;
            }
        }
        let ev: Vec<Ev> = (0..m).map(|k| Ev { a: vals[k].a, b: vals[k].b, done: fine[k] || (vals[k].q.re == 0.0 && vals[k].q.im == 0.0) }).collect();
        if (0..m).any(|k| !ev[k].done && !(ev[k].a.is_finite() && ev[k].b.is_finite())) {
            break;
        }
        rectangle_step(&z, &ev, &cf, opt, &mut y, &mut dz);
        if dz.iter().any(|d| !d.is_finite()) {
            break;
        }
        exact_sweeps += 1;
        let mut moved = false;
        for k in 0..m {
            let z2 = quantize(z[k] - dz[k]);
            if z2 != z[k] {
                moved |= (z2 - z[k]).abs() > 4.0 * U * z[k].abs();
                z[k] = z2;
                let (v, _, p, _, _) = value(z2);
                vals[k] = v;
                pv[k] = p;
            }
        }
        let st = state(&vals, &z);
        r = st.0;
        fine = st.1;
        score = st.2;
        n += 1;
        if better(score, best.2) {
            best = (z.clone(), r.clone(), score, vals.clone(), pv.clone());
        }
        if !moved {
            break;
        }
    }
    let (rho, one) = fixed_point(&best.0, &best.1);
    let strict = (0..m).all(|k| {
        let zk = best.0[k];
        one[k] && rho[k] * SL <= opt.tol * zk.abs() && (!real || zk.im.abs() > rho[k] || ((rho[k] + zk.im.abs()) * SL <= opt.tol * zk.abs() && mirror(&best.0, &rho, k, rho[k])))
    });
    Certified { z: best.0, r: best.1, rho, one, strict, vals: best.3, parts: best.4, certificates: n, exact_sweeps }
}

/// Gaussian integer coefficients -> double precision coefficients with a common scale.
pub fn to_float(ci: &GPoly) -> Vec<C> {
    let one = BigInt::from(1);
    let parts: Vec<((f64, i64), (f64, i64))> = ci.iter().map(|(a, b)| (fl2(a, &one), fl2(b, &one))).collect();
    let emax = parts.iter().flat_map(|(a, b)| [a, b]).filter(|x| x.0 != 0.0).map(|x| x.1).max().unwrap_or(0);
    parts.iter().map(|(a, b)| C::new(ldexp(a.0, a.1 - emax), ldexp(b.0, b.1 - emax))).collect()
}

/// Double precision coefficients -> Gaussian integers (exactly, up to a common power of two).
pub fn from_float(c: &[C]) -> GPoly {
    let parts: Vec<((BigInt, u64), (BigInt, u64))> = c.iter().map(|x| (dyadic(x.re), dyadic(x.im))).collect();
    let d = parts.iter().map(|(a, b)| a.1.max(b.1)).max().unwrap_or(0);
    parts.into_iter().map(|(a, b)| (a.0 << (d - a.1), b.0 << (d - b.1))).collect()
}

/// The polynomial in the variable u = z / 2^s (up to a constant factor): exact.
pub fn scale_variable(ci: &GPoly, s: i64) -> GPoly {
    if s == 0 {
        return ci.clone();
    }
    let m = ci.len() - 1;
    ci.iter()
        .enumerate()
        .map(|(j, (a, b))| {
            let k = if s > 0 { s as u64 * (m - j) as u64 } else { (-s) as u64 * j as u64 };
            (a << k, b << k)
        })
        .collect()
}

pub fn is_real(ci: &GPoly) -> bool {
    ci.iter().all(|(_, b)| b.is_zero())
}
