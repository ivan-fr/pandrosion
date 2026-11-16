//! All the roots of a polynomial with their multiplicities, each in a certified disc (note G8).
//!
//! One path: the root zero is removed exactly (P = z^k Q); exact square-free decomposition; for each factor, the simultaneous rectangle (the three-mean
//! support of the Geometric Root Calculators, used twice per sweep) started from the dominant binomials;
//! the fixed-point certificate; if a disc fails or is not small enough, the same sweep continues with exact
//! values of S, S', S'' (fixed point with a rigorous rounding bound), first at double precision points, then
//! at points with as many bits as the tolerance asks for (module `precise`).
//!
//! Points that share a tight cluster of K roots are moved by the step of degree K on the polynomial deflated
//! of the points outside the cluster (`precise::cluster_moves`, version 0.9.0) instead of the sweep, which
//! approaches a cluster by a constant factor only.
//!
//! The variable is first scaled by an exact power of two (z = 2^s u), chosen so that the coefficients spread
//! over the fewest orders of magnitude (s = 0 for an ordinary polynomial), and the coefficients by another one: subnormal coefficients, and roots or coefficients near
//! the underflow and overflow thresholds, are handled like any others.
#![doc = include_str!("../README.md")]

pub mod complex;
pub mod exact;
pub mod float;
mod limbs;
pub mod precise;
pub mod sqfree;

pub use complex::C;
pub use exact::GPoly;
pub use float::{Announce, Options, Start, Support};
use float::{frexp, ldexp, simultaneous, Poly, ETA, U};
pub use float::{binomial_start, landing_circle};
pub use precise::{Radius, ZP};

/// The disc D(z, radius) contains exactly `count` distinct roots, each of multiplicity `mult`.
#[derive(Clone, Copy, Debug)]
pub struct Root {
    pub z: C,
    pub radius: f64,
    pub mult: usize,
    pub count: usize,
    /// the root is proved real (real polynomials only)
    pub real: bool,
}

/// The same with a centre of any precision and a radius of any size.
#[derive(Clone, Debug)]
pub struct PreciseRoot {
    pub z: ZP,
    pub radius: Radius,
    pub mult: usize,
    pub count: usize,
    pub real: bool,
}
impl PreciseRoot {
    /// Decimal strings (re, im, radius).  The centre has at least `digits` significant digits, and as many
    /// more as needed for its decimal rounding to be far below the radius; the radius is printed enlarged, so
    /// that the printed disc contains the certified one.
    pub fn decimal(&self, digits: usize) -> (String, String, String) {
        let zbits = self.z.re.bits().max(self.z.im.bits()) as i64 + self.z.e; // |coordinate| < 2^zbits
        let (rf, re) = frexp(self.radius.f);
        let (digits, radius) = if self.radius.f > 0.0 && self.radius.f.is_finite() {
            // decimal rounding of the centre below radius * SLACK / 4; with the rounding of the radius the
            // printed disc stays within the slack of the certificate (float::SLACK)
            let need = ((zbits - (re + self.radius.e)) as f64 * std::f64::consts::LOG10_2).ceil().max(0.0) as usize + 6;
            (digits.max(need).min(100_000), Radius { f: rf * (1.0 + float::SLACK / 4.0), e: re + self.radius.e })
        } else if self.radius.f == 0.0 {
            // an exact root: the radius printed is zero if the decimal centre is exact; otherwise the centre is
            // printed with two more digits and the radius is a bound of its rounding (each coordinate is off
            // by at most half a unit of its last digit), below 10^(-digits) times the modulus
            let (a, ea) = precise::decimal_checked(&self.z.re, self.z.e, digits);
            let (b, eb) = precise::decimal_checked(&self.z.im, self.z.e, digits);
            if ea && eb {
                return (a, b, "0".to_string());
            }
            (digits + 2, Radius { f: 1.0, e: zbits + ((-1.0 - digits as f64) * std::f64::consts::LOG2_10).ceil() as i64 })
        } else {
            (digits, self.radius)
        };
        let (a, b) = self.z.decimal(digits);
        (a, b, radius.decimal())
    }
    /// In double precision: the centre is rounded and the radius enlarged by the rounding.  The radius is
    /// infinite if the centre does not fit in a double.
    pub fn to_root(&self) -> Root {
        self.to_root_checked().0
    }
    /// Also tells whether the radius had to be enlarged beyond the slack of the certificate (float::SLACK):
    /// the count of such a disc is no longer guaranteed without comparing it with the other discs.
    fn to_root_checked(&self) -> (Root, bool) {
        let z = self.z.to_c();
        let r0 = self.radius.to_f64();
        let (mut radius, mut beyond) = (r0, false);
        if !z.is_finite() || radius.is_nan() {
            radius = f64::INFINITY;
        } else if !self.z.is_exactly(z) {
            // the distance from the centre to its rounding, computed exactly and rounded upwards
            let dist = self.z.sub(&precise::ZP::from_c(z)).to_c().abs();
            radius = (radius + dist * (1.0 + 16.0 * U) + 8.0 * ETA) * (1.0 + 4.0 * U);
            beyond = !(radius <= r0 * (1.0 + float::SLACK / 2.0));
        } else if r0 > ldexp(self.radius.f, self.radius.e) * (1.0 + float::SLACK / 2.0) {
            beyond = true; // the radius itself was rounded up from below the smallest double
        }
        (Root { z, radius, mult: self.mult, count: self.count, real: self.real }, beyond)
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Stats {
    pub sweeps: usize,
    pub certificates: usize,
    pub exact_sweeps: usize,
    /// sweeps at points with more than 53 bits, and the largest number of bits used
    pub precise_sweeps: usize,
    pub bits: u64,
    /// square-free factors, and those whose final count is the fixed-point certificate on every disc
    pub factors: usize,
    pub fixed_point: usize,
    /// seconds spent in the square-free step, in the floating-point sweeps (start included), in the certificate
    pub t_sqfree: f64,
    pub t_sweeps: f64,
    pub t_certify: f64,
    /// every disc holds one root and its radius is within the tolerance asked for (relative to its centre);
    /// `complete` alone only says that the discs account for all the roots
    pub within_tolerance: bool,
}

/// The discs found for one polynomial: plain doubles when nothing else is needed (the usual case, with no
/// big integer involved), centres of any precision otherwise.
enum Out {
    D(Vec<(Root, bool)>),
    P(Vec<PreciseRoot>),
}
/// (discs, degree, counters, shift of the variable), or Err(complete) for an input without roots to find.
type Solved = Result<(Out, usize, Stats, i64), bool>;

/// Roots of a polynomial given by double precision coefficients (highest degree first), taken as exact numbers.
/// Returns the discs, whether they account for all the roots, and counters.
pub fn all_roots(c: &[C], opt: &Options) -> (Vec<Root>, bool, Stats) {
    doubles(solve_float(c, opt, false), opt.tol)
}

/// Roots of a polynomial with Gaussian integer coefficients (highest degree first).
pub fn all_roots_exact(ci: &GPoly, opt: &Options) -> (Vec<Root>, bool, Stats) {
    doubles(solve_exact(ci, opt, false), opt.tol)
}

/// Like `all_roots`, with centres of any precision: set `opt.tol` as small as wanted (down to 1e-280).
pub fn all_roots_precise(c: &[C], opt: &Options) -> (Vec<PreciseRoot>, bool, Stats) {
    precise_out(solve_float(c, opt, true), opt.tol)
}

/// Like `all_roots_exact`, with centres of any precision.
pub fn all_roots_exact_precise(ci: &GPoly, opt: &Options) -> (Vec<PreciseRoot>, bool, Stats) {
    precise_out(solve_exact(ci, opt, true), opt.tol)
}

fn precise_out(r: Solved, tol: f64) -> (Vec<PreciseRoot>, bool, Stats) {
    let (out, complete, mut stats) = precise_all(r);
    stats.within_tolerance = complete
        && out.iter().all(|d| {
            let zbits = d.z.re.bits().max(d.z.im.bits());
            // radius <= tol |z|; a zero centre asks for the radius zero.  When the modulus and the radius are
            // ordinary doubles they are compared as such (the modulus rounded downwards); otherwise |z| is
            // replaced by its lower bound 2^(zbits - 1 + e).  (Up to 0.7.0 only the lower bound was used: a
            // disc within the tolerance by less than a factor of two could be reported as not within it.)
            let (a, r) = (d.z.to_c().abs(), d.radius.to_f64());
            let plain = a.is_finite() && a > 1e-290 && r.is_finite() && r > 1e-290 && r <= tol * a * (1.0 - 1e-12);
            d.count == 1 && (d.radius.f == 0.0 || plain || (zbits > 0 && d.radius.f.log2() + d.radius.e as f64 <= tol.log2() + (zbits as i64 - 1 + d.z.e) as f64))
        });
    (out, complete, stats)
}

fn precise_all(r: Solved) -> (Vec<PreciseRoot>, bool, Stats) {
    match r {
        Err(complete) => (Vec::new(), complete, Stats { within_tolerance: complete, ..Stats::default() }),
        Ok((Out::P(v), n, stats, s)) => finish(v, n, stats, s),
        Ok((Out::D(v), n, stats, s)) => {
            let v = v.into_iter().map(|(d, _)| PreciseRoot { z: ZP::from_c(d.z), radius: Radius { f: d.radius, e: 0 }, mult: d.mult, count: d.count, real: d.real }).collect();
            finish(v, n, stats, s)
        }
    }
}

fn doubles(r: Solved, tol: f64) -> (Vec<Root>, bool, Stats) {
    let (mut v, n, mut stats) = match r {
        Err(complete) => return (Vec::new(), complete, Stats { within_tolerance: complete, ..Stats::default() }),
        Ok((Out::D(v), n, stats, _)) => (v, n, stats),
        Ok((Out::P(v), n, stats, s)) => {
            let (v, _, stats) = finish(v, n, stats, s);
            (v.iter().map(|d| d.to_root_checked()).collect::<Vec<_>>(), n, stats)
        }
    };
    // A disc enlarged beyond the slack of the certificate (its centre does not fit in a double) keeps its
    // count only if it is still disjoint from the other discs of the same multiplicity; otherwise the two
    // discs are merged into one, with the sum of the counts.
    'again: loop {
        if !v.iter().any(|x| x.1) {
            break;
        }
        for i in 0..v.len() {
            for j in 0..v.len() {
                let (a, b) = (v[i].0, v[j].0);
                if i == j || !(v[i].1 || v[j].1) || a.mult != b.mult || !a.radius.is_finite() || !b.radius.is_finite() {
                    continue;
                }
                let d = (a.z - b.z).abs();
                if !(d * (1.0 - 8.0 * U) > (a.radius + b.radius) * (1.0 + float::SLACK)) {
                    let radius = a.radius.max((d + b.radius) * (1.0 + 8.0 * U) + 8.0 * ETA);
                    v[i] = (Root { z: a.z, radius, mult: a.mult, count: a.count + b.count, real: false }, true);
                    v.remove(j);
                    continue 'again;
                }
            }
        }
        break;
    }
    let mut out: Vec<Root> = v.into_iter().map(|x| x.0).collect();
    let complete = out.iter().all(|d| d.radius.is_finite()) && out.iter().map(|d| d.mult * d.count).sum::<usize>() == n;
    out.sort_by(|a, b| a.z.re.total_cmp(&b.z.re).then(a.z.im.total_cmp(&b.z.im)));
    stats.within_tolerance = complete && out.iter().all(|d| d.count == 1 && d.radius <= tol * d.z.abs());
    (out, complete, stats)
}

/// The shift s of the variable z = 2^s u, from the logarithms in base two of the moduli of the coefficients
/// (None for a zero coefficient): the integer s for which the coefficients of the polynomial in u,
/// c_j 2^(s (m - j)), spread over the fewest binary orders of magnitude.  For an ordinary polynomial this is
/// s = 0; it differs from 0 when the roots are far from the unit circle.  (Version 0.2.0 centred an estimate
/// of the root moduli instead: for a large degree a shift of one unit was enough to push most coefficients
/// out of the range of doubles.)
fn variable_shift(l: &[Option<f64>]) -> i64 {
    let m = l.len() - 1;
    let pts: Vec<(f64, f64)> = l.iter().enumerate().filter_map(|(j, x)| x.map(|v| ((m - j) as f64, v))).collect();
    if pts.len() < 2 {
        return 0;
    }
    let spread = |s: i64| {
        let (mut lo, mut hi) = (f64::INFINITY, f64::NEG_INFINITY);
        for &(k, v) in &pts {
            let y = v + s as f64 * k;
            lo = lo.min(y);
            hi = hi.max(y);
        }
        hi - lo
    };
    // the spread is a convex function of s: ternary search on the integers
    let big = pts.iter().map(|p| p.1.abs()).fold(0.0, f64::max).min(1e15) as i64 + 2;
    let (mut a, mut b) = (-big, big);
    while b - a > 2 {
        let (m1, m2) = (a + (b - a) / 3, b - (b - a) / 3);
        if spread(m1) <= spread(m2) { b = m2 } else { a = m1 }
    }
    let mut best = 0i64;
    for s in a..=b {
        if spread(s) < spread(best) - 0.5 {
            best = s;
        }
    }
    best
}

/// The coefficients of the polynomial in u = z / 2^s, divided by a power of two that brings the largest one
/// near 1.  Exact, except for coefficients that fall below the smallest normal number (the rounding bound of
/// the certificate covers them).
fn scaled_floats(c: &[C], s: i64) -> Vec<C> {
    let m = c.len() - 1;
    let parts: Vec<[(f64, i64); 2]> = c
        .iter()
        .enumerate()
        .map(|(j, x)| {
            let k = s * (m - j) as i64;
            let (fr, er) = frexp(x.re);
            let (fi, ei) = frexp(x.im);
            [(fr, er + k), (fi, ei + k)]
        })
        .collect();
    let emax = parts.iter().flatten().filter(|t| t.0 != 0.0).map(|t| t.1).max().unwrap_or(0);
    parts.iter().map(|p| C::new(ldexp(p[0].0, p[0].1 - emax), ldexp(p[1].0, p[1].1 - emax))).collect()
}

/// The root 0 of P = z^k Q, Q(0) != 0, added to the discs found for Q: exact, radius zero, multiplicity k
/// (Lean: `ZeroDeflation.roots_X_pow_mul`, `rootMultiplicity_zero_X_pow_mul`).  Returns None when a disc of Q
/// is not proved to stay away from 0 (its count would then no longer be a count of roots of P): the caller
/// solves P without deflation.
fn with_zero_root(q: Solved, k: usize, real: bool) -> Option<Solved> {
    let (mut out, n, mut stats, s) = match q {
        Ok(x) => x,
        Err(_) => return None,
    };
    let away = match &out {
        // |z| > radius, with the modulus rounded downwards
        Out::D(v) => v.iter().all(|(d, _)| d.radius.is_finite() && d.z.abs() * (1.0 - 4.0 * U) > d.radius),
        // radius < 2^(er + e) <= 2^(zbits - 1 + z.e) <= |z|   (a scaling of the variable keeps 0 in place)
        Out::P(v) => v.iter().all(|d| {
            let zbits = d.z.re.bits().max(d.z.im.bits()) as i64;
            let (rf, er) = frexp(d.radius.f);
            zbits > 0 && d.radius.f.is_finite() && (rf == 0.0 || er + d.radius.e <= zbits - 1 + d.z.e)
        }),
    };
    if !away {
        return None;
    }
    match &mut out {
        Out::D(v) => v.push((Root { z: C::new(0.0, 0.0), radius: 0.0, mult: k, count: 1, real }, false)),
        Out::P(v) => v.push(PreciseRoot { z: ZP::from_c(C::new(0.0, 0.0)), radius: Radius { f: 0.0, e: 0 }, mult: k, count: 1, real }),
    }
    stats.factors += 1;
    stats.fixed_point += 1;
    Some(Ok((out, n + k, stats, s)))
}

fn solve_float(c: &[C], opt: &Options, precise: bool) -> Solved {
    let lead = c.iter().position(|x| x.re != 0.0 || x.im != 0.0).unwrap_or(c.len());
    let c = &c[lead..];
    if c.len() <= 1 {
        return Err(true);
    }
    if c.iter().any(|x| !x.is_finite()) {
        return Err(false); // not a polynomial
    }
    // P = z^k Q with Q(0) != 0: the root 0 is exact and has multiplicity k; only Q is solved
    let k = c.iter().rev().take_while(|x| x.re == 0.0 && x.im == 0.0).count();
    if k > 0 {
        let real = c.iter().all(|x| x.im == 0.0);
        let q = &c[..c.len() - k];
        if q.len() == 1 {
            let out = if precise {
                Out::P(vec![PreciseRoot { z: ZP::from_c(C::new(0.0, 0.0)), radius: Radius { f: 0.0, e: 0 }, mult: k, count: 1, real }])
            } else {
                Out::D(vec![(Root { z: C::new(0.0, 0.0), radius: 0.0, mult: k, count: 1, real }, false)])
            };
            return Ok((out, k, Stats { factors: 1, fixed_point: 1, ..Stats::default() }, 0));
        }
        if let Some(r) = with_zero_root(solve_float_nonzero(q, opt, precise), k, real) {
            return r;
        }
    }
    solve_float_nonzero(c, opt, precise)
}

/// `c` has a nonzero leading coefficient, finite coefficients and degree at least one.
fn solve_float_nonzero(c: &[C], opt: &Options, precise: bool) -> Solved {
    let t0 = std::time::Instant::now();
    if sqfree::squarefree_mod_p_float(c) {
        let logs: Vec<Option<f64>> = c
            .iter()
            .map(|x| {
                let (f, e) = frexp(x.re.abs().max(x.im.abs()));
                if f == 0.0 { None } else { Some(e as f64 + f.log2()) }
            })
            .collect();
        let s = variable_shift(&logs);
        // square-free: the exact coefficients are built only if the certificate asks for exact values
        let cell: std::cell::OnceCell<GPoly> = std::cell::OnceCell::new();
        let lazy = || cell.get_or_init(|| exact::scale_variable(&exact::from_float(c), s));
        let mut stats = Stats { t_sqfree: t0.elapsed().as_secs_f64(), ..Default::default() };
        let mut out = if precise || s != 0 { Out::P(Vec::new()) } else { Out::D(Vec::new()) };
        let real = c.iter().all(|x| x.im == 0.0);
        let floats = scaled_floats(c, s);
        // coefficients that the scaling pushed below the smallest normal number are lost to double precision
        let lost = floats.iter().filter(|x| x.abs() >= f64::MIN_POSITIVE).count() != c.iter().filter(|x| x.re != 0.0 || x.im != 0.0).count();
        factor_roots(1, &lazy, Poly::new(floats), real, opt, &mut out, &mut stats, !precise, lost);
        return Ok((out, c.len() - 1, stats, s));
    }
    solve_exact(&exact::from_float(c), opt, precise)
}

fn solve_exact(ci: &GPoly, opt: &Options, precise: bool) -> Solved {
    let ci = sqfree::strip(ci);
    if ci.len() <= 1 {
        return Err(true);
    }
    // P = z^k Q with Q(0) != 0, as in `solve_float`
    let k = ci.iter().rev().take_while(|x| x.0.bits() == 0 && x.1.bits() == 0).count();
    if k > 0 {
        let real = exact::is_real(&ci);
        let q: GPoly = ci[..ci.len() - k].to_vec();
        if q.len() == 1 {
            let out = if precise {
                Out::P(vec![PreciseRoot { z: ZP::from_c(C::new(0.0, 0.0)), radius: Radius { f: 0.0, e: 0 }, mult: k, count: 1, real }])
            } else {
                Out::D(vec![(Root { z: C::new(0.0, 0.0), radius: 0.0, mult: k, count: 1, real }, false)])
            };
            return Ok((out, k, Stats { factors: 1, fixed_point: 1, ..Stats::default() }, 0));
        }
        if let Some(r) = with_zero_root(solve_exact_nonzero(q, opt, precise), k, real) {
            return r;
        }
    }
    solve_exact_nonzero(ci, opt, precise)
}

/// `ci` has a nonzero leading coefficient and degree at least one.
fn solve_exact_nonzero(ci: GPoly, opt: &Options, precise: bool) -> Solved {
    let mut stats = Stats::default();
    let n = ci.len() - 1;
    let logs: Vec<Option<f64>> = ci
        .iter()
        .map(|(a, b)| {
            let bits = a.bits().max(b.bits());
            if bits == 0 { None } else { Some(bits as f64) }
        })
        .collect();
    let s = variable_shift(&logs);
    let ci = exact::scale_variable(&ci, s);
    let real_coeffs = exact::is_real(&ci);
    let t0 = std::time::Instant::now();
    let factors: Vec<(usize, GPoly)> = if sqfree::squarefree_mod_p(&ci) { vec![(1, ci)] } else { sqfree::yun(&ci) };
    stats.t_sqfree = t0.elapsed().as_secs_f64();
    let mut out = if precise || s != 0 { Out::P(Vec::new()) } else { Out::D(Vec::new()) };
    for (mult, f) in &factors {
        if f.len() >= 2 {
            let floats = exact::to_float(f);
            let lost = floats.iter().filter(|x| x.abs() >= f64::MIN_POSITIVE).count() != f.iter().filter(|x| x.0.bits() != 0 || x.1.bits() != 0).count();
            factor_roots(*mult, &|| f, Poly::new(floats), real_coeffs, opt, &mut out, &mut stats, !precise, lost);
        }
    }
    Ok((out, n, stats, s))
}

/// Back to the variable z = 2^s u (exact), and the final order.
fn finish(mut out: Vec<PreciseRoot>, n: usize, stats: Stats, s: i64) -> (Vec<PreciseRoot>, bool, Stats) {
    for d in out.iter_mut() {
        d.z.e += s;
        d.radius.e += s;
    }
    let complete = out.iter().all(|d| d.radius.is_finite()) && out.iter().map(|d| d.mult * d.count).sum::<usize>() == n;
    // by real part, then imaginary part, compared exactly
    out.sort_by(|a, b| {
        let d = a.z.sub(&b.z);
        d.re.cmp(&num_bigint::BigInt::from(0)).then(d.im.cmp(&num_bigint::BigInt::from(0)))
    });
    (out, complete, stats)
}

/// The roots of one square-free factor S (multiplicity `mult` in P).  `doubles`: the discs will be returned
/// with double precision centres (`all_roots`, `all_roots_exact`).  `lost`: the double precision coefficients
/// `s` miss some of the coefficients.
fn factor_roots<'a>(mult: usize, f: &dyn Fn() -> &'a GPoly, s: Poly, real_coeffs: bool, opt: &Options, out: &mut Out, stats: &mut Stats, doubles: bool, lost: bool) {
    let m = s.degree();
    match out {
        Out::P(v) => v.reserve(m),
        Out::D(v) => v.reserve(m),
    }
    let t0 = std::time::Instant::now();
    // `lost`: some coefficients do not fit in double precision next to the others (roots over more orders of
    // magnitude than a double has).  The double precision sweeps would then run on another polynomial: the
    // points start from the dominant binomials of the exact coefficients and go straight to the sweeps with
    // values beyond double precision.
    let (z0, sw, pre) = match if lost { exact::scaled_start(f()) } else { None } {
        Some(z) => (z, 0, None),
        None => float::simultaneous_bounds(&s, opt, 100 + 10 * m),
    };
    stats.t_sweeps += t0.elapsed().as_secs_f64();
    let t0 = std::time::Instant::now();
    // the other start, for the case where double precision is not enough (`exact::certify_from`)
    // (computed only if the certificate asks for it; it finds by itself that the two starts are the same)
    let other = || simultaneous(&s, &Options { start: float::Start::Edges, ..*opt }, 60 + m).0;
    let alt: Option<&dyn Fn() -> Vec<C>> = if opt.start == float::Start::Binomial && !lost && m >= 16 { Some(&other) } else { None };
    let cert = exact::certify_pre(f, &s, &z0, pre, opt, real_coeffs, alt);
    stats.sweeps += sw;
    stats.certificates += cert.certificates;
    stats.exact_sweeps += cert.exact_sweeps;
    stats.factors += 1;
    let rad = |f: f64| Radius { f, e: 0 };
    let mut push = |d: PreciseRoot| match out {
        Out::P(v) => v.push(d),
        Out::D(v) => v.push(d.to_root_checked()),
    };
    if cert.strict && opt.tol >= 1e-12 {
        // double precision was enough: every disc passes the fixed-point certificate (one root in each, and
        // no other root: Lean, all_roots_of_computed), is within the tolerance and is decided
        stats.fixed_point += 1;
        for i in 0..m {
            let (zz, rr) = (cert.z[i], cert.rho[i]);
            // a real root: the conjugate root lies in the same disc, which is replaced by a real one
            let real = real_coeffs && zz.im.abs() <= rr;
            let (zz, rr) = if real { (C::new(zz.re, 0.0), (rr + zz.im.abs()) * (1.0 + 4.0 * U)) } else { (zz, rr) };
            match out {
                Out::D(v) => v.push((Root { z: zz, radius: rr, mult, count: 1, real }, false)),
                Out::P(v) => v.push(PreciseRoot { z: ZP::from_c(zz), radius: rad(rr), mult, count: 1, real }),
            }
        }
        stats.t_certify += t0.elapsed().as_secs_f64();
        return;
    }
    // more bits: the same sweep and the same certificate at multiprecision points
    let rf = precise::refine_for(f(), &cert, opt, real_coeffs, doubles);
    stats.precise_sweeps += rf.sweeps;
    stats.bits = stats.bits.max(rf.bits);
    let all_one = rf.one.iter().all(|&x| x);
    stats.fixed_point += all_one as usize;
    let cover = if all_one { &rf.rho } else { &rf.r };
    // otherwise (points that could not be separated, or that need not be: `Options::isolate`) the components
    // of the Smith discs are counted by Smith's theorem; a component is reported as one disc around its
    // first point
    let groups: Vec<Vec<usize>> = if all_one { (0..m).map(|k| vec![k]).collect() } else { precise::components(m, &rf.r, &rf.dist) };
    let enclosing = |comp: &[usize]| precise::enclosing(m, comp, &rf.r, &rf.dist);
    for comp in groups.iter() {
        let i = comp[0];
        if comp.len() == 1 {
            let rr = if rf.one[i] { rf.rho[i] } else { rf.r[i] };
            let zc = rf.zc[i];
            if real_coeffs && zc.im.abs() <= rr * (1.0 + 8.0 * U) && precise::mirror(&rf.z, &rf.zc, &rf.isd, cover, i, rr) {
                let z = ZP { re: rf.z[i].re.clone(), im: num_bigint::BigInt::from(0), e: rf.z[i].e };
                push(PreciseRoot { z, radius: rad(precise::real_radius(rr, zc.im)), mult, count: 1, real: true });
            } else {
                push(PreciseRoot { z: rf.z[i].clone(), radius: rad(rr), mult, count: 1, real: false });
            }
        } else {
            // one disc around the first point of the component
            push(PreciseRoot { z: rf.z[i].clone(), radius: rad(enclosing(comp)), mult, count: comp.len(), real: false });
        }
    }
    stats.t_certify += t0.elapsed().as_secs_f64();
}
