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
    // the usual case without a call: the modulus from the squares, the power of two from its bits
    // (the exponent may differ by one from that of the exact modulus when the modulus is within a
    // rounding of a power of two: the point then keeps 52 or 54 bits, which is as good)
    let n = z.norm_sqr();
    if n > 1e-200 && n < 1e200 {
        let e = ((n.sqrt().to_bits() >> 52) & 0x7ff) as i64; // |z| = f 2^(e - 1022), 1/2 <= f < 1
        let q = f64::from_bits(((e - 52) as u64) << 52); // 2^(e - 1022 - 53), as a biased exponent
        let iq = f64::from_bits(((2046 - (e - 52)) as u64) << 52); // 1 / q
        return C::new((z.re * iq).round_ties_even() * q, (z.im * iq).round_ties_even() * q);
    }
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
    certify_from(ci, s, z0, opt, real, None)
}

/// `certify`, with a second set of points to choose from (version 0.12.0).
///
/// When double precision was not enough for a quarter of the points or more, the sweeps that follow, with
/// values beyond double precision, cost hundreds of bits per evaluation, and their number depends on where
/// they start: on Laguerre 150 the points left by the double precision stage need 37 of them, those left
/// from the other start (`Start::Edges`) 20; on a Mandelbrot polynomial it is the other way round.  `alt`
/// gives the points of the other start; the two sets are compared by the median of their relative Smith
/// radii, from one evaluation each with a few bits of relative precision, and the sweeps go on from the
/// better one.  The comparison costs about two sweeps and is not made when double precision sufficed.
pub fn certify_from<'a>(ci: &dyn Fn() -> &'a GPoly, s: &Poly, z0: &[C], opt: &Options, real: bool, alt: Option<&dyn Fn() -> Vec<C>>) -> Certified {
    certify_pre(ci, s, z0, None, opt, real, alt)
}

/// `certify_from`; `pre` gives the bounds of |S| / |c| at the points `z0` when the sweeps have already
/// computed them (`float::simultaneous_bounds`, version 0.13.0): the points are then taken as they are.
pub(crate) fn certify_pre<'a>(ci: &dyn Fn() -> &'a GPoly, s: &Poly, z0: &[C], pre: Option<Vec<(f64, i64)>>, opt: &Options, real: bool, alt: Option<&dyn Fn() -> Vec<C>>) -> Certified {
    let m = s.degree();
    let mf = m as f64;
    let cf = coeffs3(mf);
    let floor = 8.0 * mf * U;
    // the radius compared with the tolerance is the one that may be printed: enlarged by the slack
    const SL: f64 = 1.0 + crate::float::SLACK;
    let passes = 30 + m;
    let (mut z, mut bounds) = match pre {
        Some(b) if b.len() == z0.len() => (z0.to_vec(), b),
        _ => {
            let z: Vec<C> = z0.iter().map(|&x| quantize(x)).collect();
            let mut bounds = Vec::new();
            s.bound_all(&z, &mut EvalWs::default(), &mut bounds);
            (z, bounds)
        }
    };
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
        (r, fine, (nfine, -rmax), (rho, one))
    };
    // (the fixed-point radii and flags of a state are kept with it: up to 0.12.0 those of the best state
    // were computed a second time at the end, 16 of the 72 ms of z^2000 + z + 1)
    let (mut r, mut fine, mut score, mut fp) = state(&vals, &z);
    let strict_of = |z: &[C], rho: &[f64], one: &[bool]| {
        (0..m).all(|k| {
            let zk = z[k];
            one[k] && rho[k] * SL <= opt.tol * zk.abs() && (!real || zk.im.abs() > rho[k] || ((rho[k] + zk.im.abs()) * SL <= opt.tol * zk.abs() && mirror(z, rho, k, rho[k])))
        })
    };
    if m <= 1 || fine.iter().all(|&f| f) {
        // nothing more to do (three polynomials in four): this state is returned as it is, not copied
        let (rho, one) = fp;
        let strict = strict_of(&z, &rho, &one);
        return Certified { z, r, rho, one, strict, vals, parts: vec![None; m], certificates: 1, exact_sweeps: 0 };
    }
    let mut pv: Vec<Option<(crate::precise::ZP, crate::precise::ZP)>> = vec![None; m];
    let mut best = (z.clone(), r.clone(), score, vals.clone(), pv.clone(), fp.clone());
    // values beyond the floating-point bound: ball evaluation in fixed point, as many bits as needed
    let cell: std::cell::OnceCell<crate::precise::BallPoly> = std::cell::OnceCell::new();
    // the same polynomial for the models of the clusters (their evaluations return S S''/S'^2 as well)
    let cellc: std::cell::OnceCell<crate::precise::BallPoly> = std::cell::OnceCell::new();
    // F of the last evaluation of each point: the next one starts there instead of at 128 bits (a point that
    // moves towards its root needs as many bits or more; one that needed fewer costs one evaluation too long)
    let fk: Vec<std::cell::Cell<u64>> = vec![std::cell::Cell::new(128); m];
    let value = |k: usize, zk: C| {
        let r = crate::precise::ball_auto(cell.get_or_init(|| crate::precise::BallPoly::new(ci(), opt.full_order)), &crate::precise::ZP::from_c(zk), fk[k].get(), 4096, 53, 40, 0);
        fk[k].set(if r.4 > 0 { r.4.max(128) } else if r.1 > 0 { r.1 } else { 128 });
        r
    };
    let better = |a: (usize, f64), b: (usize, f64)| a.0 > b.0 || (a.0 == b.0 && a.1 > b.1);
    if let Some(alt) = alt {
        let bad = fine.iter().filter(|&&f| !f).count();
        if m >= 16 && 4 * bad >= m {
            // A sample of 24 points at most.  The points left by the double precision stage are first
            // evaluated there as the sweeps would evaluate them (nothing is lost); only if they are far from
            // the roots (median relative Smith radius above 2^-10) is the other start computed and compared,
            // from evaluations with 8 bits of relative precision.  Each Smith radius has the product of
            // the distances to all the points.
            let stride = m.div_ceil(24);
            let median = |rr: &[f64], pts: &[C]| -> f64 {
                let mut l: Vec<f64> = (0..m).step_by(stride).map(|k| { let a = pts[k].abs(); if rr[k] == 0.0 { -1100.0 } else if rr[k].is_finite() && a > 0.0 { (rr[k] / a).log2() } else { 1e9 } }).collect();
                l.sort_by(|a, b| a.total_cmp(b));
                l[l.len() / 2]
            };
            for k in (0..m).step_by(stride) {
                if !fine[k] && !vals[k].exact {
                    let (v, _, p, _, _) = value(k, z[k]);
                    vals[k] = v;
                    pv[k] = p;
                }
            }
            let now = median(&smith(&vals, &z), &z);
            if now > -10.0 {
                let zb: Vec<C> = alt().iter().map(|&p| quantize(p)).collect();
                let distinct = zb.len() == m && zb.iter().all(|p| p.is_finite()) && { let mut t: Vec<(u64, u64)> = zb.iter().map(|p| (p.re.to_bits(), p.im.to_bits())).collect(); t.sort(); t.windows(2).all(|w| w[0] != w[1]) };
                let same = zb.len() == m && zb.iter().zip(&z).all(|(p, q)| p.re == q.re && p.im == q.im);
                if distinct && !same {
                    let bp = cell.get_or_init(|| crate::precise::BallPoly::new(ci(), opt.full_order));
                    let v: Vec<Val> = (0..m)
                        .map(|k| if k % stride == 0 { crate::precise::ball_auto(bp, &crate::precise::ZP::from_c(zb[k]), 128, 4096, 53, 8, 0).0 } else { Val { q: ZERO, ex: 0, a: ZERO, b: ZERO, exact: false } })
                        .collect();
                    // sixteen bits of margin: the other start is taken only when it is far better (with three
                    // bits it was also taken for shifted powers, where it then needed more sweeps)
                    if median(&smith(&v, &zb), &zb) + 16.0 < now {
                        z = zb;
                        s.bound_all(&z, &mut EvalWs::default(), &mut bounds);
                        vals = bounds.iter().map(|&(b, e)| Val { q: C::new(if b.is_nan() { f64::INFINITY } else { b }, 0.0), ex: e, a: ZERO, b: ZERO, exact: false }).collect();
                        pv = vec![None; m];
                        fk.iter().for_each(|c| c.set(128));
                    }
                }
            }
            let st = state(&vals, &z);
            r = st.0;
            fine = st.1;
            score = st.2;
            fp = st.3;
            best = (z.clone(), r.clone(), score, vals.clone(), pv.clone(), fp.clone());
        }
    }
    let (mut n, mut exact_sweeps) = (1usize, 0usize);
    let mut y = StepWs::default();
    let mut dz = vec![ZERO; m];
    while m > 1 && n < passes && !fine.iter().all(|&f| f) {
        let mut fresh = false;
        for k in 0..m {
            if !fine[k] && !vals[k].exact {
                let (v, _, p, _, _) = value(k, z[k]);
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
            fp = st.3;
            if better(score, best.2) {
                best = (z.clone(), r.clone(), score, vals.clone(), pv.clone(), fp.clone());
            }
            if fine.iter().all(|&f| f) {
                break;
            }
        }
        if !opt.isolate && n > 1 {
            // roots closer than the tolerance need not be separated: the multiprecision stage will find the
            // state good enough (same test) and return it
            let dist: Vec<f64> = (0..m * m).map(|i| (z[i / m] - z[i % m]).abs()).collect();
            let za: Vec<f64> = z.iter().map(|x| x.abs()).collect();
            if crate::precise::covered(m, &fine, &r, &dist, &za, opt.tol / (1.0 + crate::float::SLACK)) {
                break;
            }
        }
        let ev: Vec<Ev> = (0..m).map(|k| Ev { a: vals[k].a, b: vals[k].b, done: fine[k] || (vals[k].q.re == 0.0 && vals[k].q.im == 0.0) }).collect();
        if (0..m).any(|k| !ev[k].done && !(ev[k].a.is_finite() && ev[k].b.is_finite())) {
            break;
        }
        // Clusters.  One table of distances and one analysis of the components of the Smith discs per sweep
        // serve the two uses below (plain square roots: m^2 calls of `hypot` cost as much as the
        // multiprecision evaluations of a sweep at degree 100).
        let crowded = (0..m).any(|k| !ev[k].done);
        let (dist, comps) = if crowded {
            let fast = |c: C| { let s = (c.re * c.re + c.im * c.im).sqrt(); if s.is_normal() { s } else { c.abs() } };
            let dist: Vec<f64> = (0..m * m).map(|i| fast(z[i / m] - z[i % m])).collect();
            let comps = crate::precise::components(m, &r, &dist);
            (dist, comps)
        } else {
            (Vec::new(), Vec::new())
        };
        // The clusters, from one evaluation each with the cursor in multiprecision: a cluster wide enough for
        // the grid of doubles gets its points on the roots of its model; a cluster that the grid cannot
        // resolve is held, and once every point that is not done is held, or shares a component of Smith
        // discs no wider than 4096 units of the last place, the stage with more bits takes over.
        let mut held = vec![false; m];
        // (point, displacement, bits to add to its next evaluation: S shrinks like the K-th power of the distance)
        let mut cluster_dz: Vec<(usize, C, u64)> = Vec::new();
        if crowded {
            for comp in &comps {
                if comp.len() >= 2 && crate::precise::enclosing(m, comp, &r, &dist) <= 4096.0 * U * z[comp[0]].abs() {
                    comp.iter().for_each(|&k| held[k] = true);
                }
            }
        }
        if opt.cluster && crowded {
            let diff = |k: usize, l: usize| z[k] - z[l];
            let zp: Vec<crate::precise::ZP> = z.iter().map(|&c| crate::precise::ZP::from_c(c)).collect();
            for cl in crate::precise::tight_clusters(m, &comps, &r, &dist, &vals) {
                if cl.members.iter().any(|&i| ev[i].done || held[i]) {
                    continue;
                }
                let (from, k) = (cl.from, cl.members.len());
                // the K points must stay apart on the grid: a circle of 256 K units of the last place at least
                let grid = 256.0 * k as f64 * U * z[from].abs();
                let (u, rho, arg) = match crate::precise::double_cursor(m, &cl, &vals, &diff) {
                    Some(x) => x,
                    None => continue, // the points are not far from the cluster: the sweep
                };
                let more = |scale: f64| (k as f64 * -scale.log2()).clamp(0.0, 4096.0).ceil() as u64;
                let put = |cluster_dz: &mut Vec<(usize, C, u64)>, scale: f64| {
                    if let Some(moves) = crate::precise::place(&cl, u, scale, arg, &diff) {
                        cluster_dz.extend(moves.into_iter().map(|(i, off)| (i, z[i] - (z[from] + off), more(scale))));
                    }
                };
                if rho.powi(k as i32) >= crate::precise::CURSOR_NOISE {
                    // the double precision cursor is good: its circle, or the cluster is below the grid
                    if rho * u.abs() < grid {
                        cl.members.iter().for_each(|&i| held[i] = true);
                    } else {
                        put(&mut cluster_dz, rho);
                    }
                    continue;
                }
                // the cursor in multiprecision, to the bits that tell whether the cluster is above the grid
                let far = u.abs();
                let rel = if far > grid { (k as f64 * (far / grid).log2()).ceil() as u64 + 48 } else { 64 };
                let outside: Vec<&crate::precise::ZP> = (0..m).filter(|l| !cl.members.contains(l)).map(|l| &zp[l]).collect();
                let bpc = cellc.get_or_init(|| crate::precise::BallPoly::new(ci(), true));
                match crate::precise::cluster_model(bpc, &zp[from], &outside, k, rel.min(4096), 8192) {
                    Some(md) => {
                        let (scale, _) = md.radius(k);
                        if scale * md.u.to_c().abs() < grid {
                            // the cluster is below the grid (or not known to be above it)
                            cl.members.iter().for_each(|&i| held[i] = true);
                        } else if let Some((_, moves)) = crate::precise::model_moves(&cl, &md, &diff) {
                            let anchor = zp[from].sub(&md.u).to_c();
                            cluster_dz.extend(moves.into_iter().map(|(i, off)| (i, z[i] - (anchor + off), more(scale))));
                        }
                    }
                    // no model (S' vanishes at this precision): the double precision cursor with its floor
                    None => {
                        let scale = rho.max(ldexp(1.0, -30));
                        if scale * u.abs() >= grid {
                            put(&mut cluster_dz, scale);
                        }
                    }
                }
            }
        }
        if crowded && (0..m).all(|k| ev[k].done || held[k]) {
            break;
        }
        rectangle_step(&z, &ev, &cf, opt, &mut y, &mut dz);
        if dz.iter().any(|d| !d.is_finite()) {
            break;
        }
        // the points of a cluster go to the roots of its model instead
        let mut bumped = vec![false; m];
        for (k, v, more) in cluster_dz {
            if v.is_finite() {
                bumped[k] = true;
                dz[k] = v;
                fk[k].set((fk[k].get() + more).min(4096));
            }
        }
        exact_sweeps += 1;
        let mut moved = false;
        for k in 0..m {
            let z2 = quantize(z[k] - dz[k]);
            if z2 != z[k] {
                moved |= (z2 - z[k]).abs() > 4.0 * U * z[k].abs();
                // The bits its next value will ask for (version 0.14.0).  A point that moves by 2^-b of its
                // modulus has about b correct bits and, if the step keeps its order, at least 3 b after it,
                // 53 at most: S is that many bits smaller there, and F is raised by as many at once.  Without
                // this one evaluation in five of this stage was an attempt with too few bits, made again.
                // (The points of a cluster have been given their bits with their move.)
                let b = -((z2 - z[k]).abs() / z2.abs()).log2();
                if b.is_finite() && b > 0.0 && !bumped[k] {
                    fk[k].set((fk[k].get() + (53.0 - b).min(2.0 * b).max(0.0) as u64).min(4096));
                }
                z[k] = z2;
                let (v, _, p, _, _) = value(k, z2);
                vals[k] = v;
                pv[k] = p;
            }
        }
        let st = state(&vals, &z);
        r = st.0;
        fine = st.1;
        score = st.2;
        fp = st.3;
        n += 1;
        if better(score, best.2) {
            best = (z.clone(), r.clone(), score, vals.clone(), pv.clone(), fp.clone());
        }
        if !moved {
            break;
        }
    }
    let (rho, one) = best.5;
    let strict = strict_of(&best.0, &rho, &one);
    Certified { z: best.0, r: best.1, rho, one, strict, vals: best.3, parts: best.4, certificates: n, exact_sweeps }
}

/// The start from the dominant binomials read on the exact coefficients (version 0.11.0), for a polynomial
/// whose coefficients do not fit in double precision with one scale: roots over more orders of magnitude
/// than a double has.  An edge from i to k of the upper convex hull of the points (j, log |a_j|) announces
/// K = k - i roots of modulus |a_i / a_k|^(1/K): the K values of the K-th root of -a_i / a_k.  (The start of
/// the double precision stage adds the centroid of each group; here the scales are far apart and the
/// binomial alone is right to many digits.)  None if a root does not fit in a double.
pub fn scaled_start(ci: &GPoly) -> Option<Vec<C>> {
    let m = ci.len() - 1;
    let one = BigInt::from(1);
    // a_j (coefficient of z^j) as a complex mantissa and an exponent of two
    let parts: Vec<Option<(C, i64)>> = (0..=m)
        .map(|j| {
            let (re, im) = &ci[m - j];
            if re.is_zero() && im.is_zero() {
                return None;
            }
            let ((fr, er), (fi, ei)) = (fl2(re, &one), fl2(im, &one));
            let e = if fr == 0.0 { ei } else if fi == 0.0 { er } else { er.max(ei) };
            Some((C::new(ldexp(fr, er - e), ldexp(fi, ei - e)), e))
        })
        .collect();
    let la = |j: usize| parts[j].map(|(c, e)| c.abs().log2() + e as f64);
    let j0 = (0..=m).find(|&j| parts[j].is_some())?;
    let mut h: Vec<usize> = Vec::new();
    for j in j0..=m {
        let lj = match la(j) {
            Some(v) => v,
            None => continue,
        };
        while h.len() >= 2 {
            let (p, q) = (h[h.len() - 1], h[h.len() - 2]);
            if (la(p).unwrap() - la(q).unwrap()) * (j - q) as f64 <= (lj - la(q).unwrap()) * (p - q) as f64 {
                h.pop();
            } else {
                break;
            }
        }
        h.push(j);
    }
    let real = is_real(ci);
    let mut z: Vec<C> = vec![ZERO; j0];
    for w in h.windows(2) {
        let (i, k) = (w[0], w[1]);
        let kk = (k - i) as f64;
        let ((ci_, ei), (ck, ek)) = (parts[i].unwrap(), parts[k].unwrap());
        let q = ZERO - ci_ / ck; // -a_i / a_k, times 2^(ei - ek)
        let lr = (q.abs().log2() + (ei - ek) as f64) / kk; // log2 of the modulus of the roots
        if !(lr.abs() < 1000.0) {
            return None;
        }
        let r = lr.exp2();
        let th0 = q.im.atan2(q.re) / kk + if real && k - i > 1 { 0.1 * 2.0 * std::f64::consts::PI / kk } else { 0.0 };
        for j in 0..(k - i) {
            let th = th0 + 2.0 * std::f64::consts::PI * j as f64 / kk;
            z.push(C::new(r * th.cos(), r * th.sin()));
        }
    }
    (z.len() == m && z.iter().all(|x| x.is_finite())).then_some(z)
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The fast path of `quantize` gives a point within half a unit of the 53rd bit of the modulus, with
    /// coordinates that are multiples of that unit, and agrees with the general path away from the powers of two.
    #[test]
    fn quantize_keeps_53_bits_of_the_modulus() {
        let mut st = 0x9e3779b97f4a7c15u64;
        let mut next = || {
            st ^= st << 13;
            st ^= st >> 7;
            st ^= st << 17;
            (st >> 11) as f64 / (1u64 << 53) as f64
        };
        let mut same = 0;
        for t in 0..20000 {
            let scale = 2f64.powi((next() * 600.0) as i32 - 300);
            let z = C::new((next() - 0.5) * scale, if t % 5 == 0 { 0.0 } else { (next() - 0.5) * scale * 2f64.powi((next() * 80.0) as i32 - 40) });
            let (_, e) = frexp(z.abs());
            let q = ldexp(1.0, e - 53);
            let w = quantize(z);
            let slow = C::new((z.re / q).round() * q, (z.im / q).round() * q);
            // multiples of q/2 at least (the exponent may be one lower), within q/2 of z
            for (a, b) in [(z.re, w.re), (z.im, w.im)] {
                assert!((a - b).abs() <= q / 2.0 && (b / (q / 2.0)).fract() == 0.0, "case {t}: {z:?} {w:?}");
            }
            let f = z.abs() / ldexp(1.0, e);
            same += (w == slow) as usize;
            if f > 0.5000001 && f < 0.9999999 && (z.re / q).fract().abs() != 0.5 && (z.im / q).fract().abs() != 0.5 {
                assert!(w == slow, "case {t}: {z:?} {w:?} {slow:?}");
            }
        }
        assert!(same > 19500, "{same}");
    }
}
