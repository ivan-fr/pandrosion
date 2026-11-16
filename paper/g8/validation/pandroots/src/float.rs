//! Floating-point part: the start, the sweeps of the simultaneous rectangle, Smith's radii.
use crate::complex::{C, ONE, ZERO};

pub const U: f64 = 2.220446049250313e-16; // 2^-52
/// The smallest positive double, 2^-1074: the absolute error of an operation whose result underflows.
pub const ETA: f64 = 5e-324;
/// Added to the sum of the moduli in the rounding bound of Horner's rule, so that the bound also covers the
/// operations that underflow (each adds at most a few ETA; marg * TINY = 16 (m+1) ETA) and the coefficients
/// that became subnormal when the polynomial was scaled.
pub const TINY: f64 = 4.0 * f64::MIN_POSITIVE;
/// Below this size a distance is not trusted to have a relative error of a few units in the last place.
pub const SMALL: f64 = 1e-280;
/// The fixed-point test is made with the bounds w_k (1 + SLACK): the discs of radius 2 w_k (1 + SLACK) are
/// then pairwise disjoint with one root each, the root being in the disc of radius 2 w_k that is returned.
/// A returned disc may therefore be enlarged by SLACK (rounding of its centre, printing) and still contain
/// exactly one root.
pub const SLACK: f64 = 1.0 / 1024.0;

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Support {
    /// line AK: q = 1 (with no announcement: the Ehrlich-Aberth iteration)
    AK,
    /// the three means of V29
    Three,
}
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Start {
    /// dominant binomials at every scale, angle section
    Binomial,
    /// one circle around the centroid
    Circle,
    /// dominant binomials, each edge of the Newton polygon for itself: the single-root edges that the
    /// other terms disturb are not merged into one shifted power (version 0.12.0; the second candidate
    /// when double precision is not enough, see `exact::certify_from`)
    Edges,
}
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Announce {
    /// where they are
    None,
    /// after their own step on the line AK (Newton's step of S: no second derivative)
    AK,
    /// after their three-mean step on S
    Three,
}
#[derive(Clone, Copy, Debug)]
pub struct Options {
    /// relative radius aimed at
    pub tol: f64,
    pub outer: Support,
    /// where the neighbours are seen
    pub announce: Announce,
    /// use every point as soon as it has moved
    pub gauss_seidel: bool,
    pub start: Start,
    /// Points with more than 53 bits (tolerances below double precision, or roots that double precision
    /// cannot separate).  `false` (default): each sweep is asked to double the number of correct bits, which
    /// the sums over the other points give when their terms are taken in double precision.  `true`: each
    /// sweep is asked for all its order can give (six times the correct bits with the default support), and
    /// the sums are then m^2 multiprecision divisions.  Same results; `false` is the faster one.
    pub full_order: bool,
    /// What is done with roots closer to one another than the tolerance.  `true` (default): the solver goes
    /// on, with more bits, until each of them has its own disc or 4096 bits are not enough.  `false`: it
    /// stops as soon as every root is in a disc within the tolerance, alone or with the roots it could not
    /// yet be told from; such a disc is returned with their number as `count` (it is the union of
    /// overlapping Smith discs, counted by Smith's theorem, as for the clusters that 4096 bits do not
    /// resolve).  Roots farther apart than the tolerance are separated either way.  This is the goal that
    /// MPSolve calls "approximate", against "isolate".
    pub isolate: bool,
    /// The step of a cluster.  `true` (default): when the points that share a cluster of K roots are much
    /// farther from it than it is wide, they are moved by the step of degree K on the function deflated of
    /// the points outside the cluster (the virtual anchor of the p-th root, `precise::cluster_moves`)
    /// instead of the step of degree m on the function deflated of all the other points, which brings
    /// them to the cluster by a constant factor per sweep only.  `false`: the sweeps of version 0.8.0.
    /// The discs returned are certified after the move, whatever it was.
    pub cluster: bool,
}
impl Default for Options {
    fn default() -> Self {
        Options { tol: 1e-10, outer: Support::Three, announce: Announce::Three, gauss_seidel: true, start: Start::Binomial, full_order: false, isolate: true, cluster: true }
    }
}

/// Coefficients of the three-mean support of degree p.
pub fn coeffs3(p: f64) -> [f64; 4] {
    let p2 = p * p;
    [
        (p - 2.0) * (47.0 * p2 + 21.0 * p + 4.0) / (60.0 * p * (4.0 * p2 - 1.0)),
        16.0 * (p + 1.0) * (4.0 * p2 - 1.0) / (15.0 * p * (5.0 * p2 + 4.0)),
        49.0 * p * (p + 1.0) * (p2 - 4.0) / (10.0 * (4.0 * p2 - 1.0) * (5.0 * p2 + 4.0)),
        (5.0 * p2 + 4.0) / (84.0 * p2),
    ]
}

#[inline(always)]
pub fn three(t: C, cf: &[f64; 4]) -> C {
    let s = t.sqrt();
    let t1 = t - ONE;
    let r = (t + (t1 * t1).scale(cf[3])).sqrt();
    (ONE + t).scale(cf[0]) + s.scale(cf[1]) - r.scale(cf[2])
}

/// What a sweep needs at a point: the logarithmic data of S and whether the residual is at rounding level.
#[derive(Clone, Copy)]
pub struct Ev {
    /// S'/S
    pub a: C,
    /// S''/S
    pub b: C,
    /// |S(z)| <= rounding bound of Horner's rule
    pub done: bool,
}

/// A polynomial with complex coefficients in double precision, highest degree first.
/// Outside the unit disc it is evaluated through the reversed polynomial R(w) = w^m S(1/w), so that no power
/// of z overflows.
pub struct Poly {
    pub c: Vec<C>,
    pub abs: Vec<f64>,
    rev: Vec<C>,
    absrev: Vec<f64>,
    /// few non-zero coefficients: the steps of Horner's rule over the runs of zero coefficients, for the
    /// polynomial and for the reversed one (version 0.13.0)
    sparse: Option<[Vec<Gap>; 2]>,
}
/// One step of Horner's rule over a run of zero coefficients: multiply by x^gap, add the coefficient.
#[derive(Clone, Copy)]
struct Gap {
    gap: usize,
    c: C,
    abs: f64,
}
fn gaps(c: &[C], abs: &[f64]) -> Vec<Gap> {
    let (mut out, mut last) = (Vec::new(), 0);
    for j in 1..c.len() {
        if abs[j] != 0.0 || c[j].re != 0.0 || c[j].im != 0.0 || j + 1 == c.len() {
            out.push(Gap { gap: j - last, c: c[j], abs: abs[j] });
            last = j;
        }
    }
    out
}
/// x^n by repeated squaring (n >= 1).  The computed power is the product of n factors x in some order: its
/// relative error is that of n - 1 products, as for the n - 1 products of Horner's rule.
#[inline(always)]
fn cpow(x: C, mut n: usize) -> C {
    let (mut r, mut b, mut first) = (x, x, true);
    loop {
        if n & 1 == 1 {
            r = if first { b } else { r * b };
            first = false;
        }
        n >>= 1;
        if n == 0 {
            return r;
        }
        b = b * b;
    }
}
#[inline(always)]
fn rpow(x: f64, mut n: usize) -> f64 {
    let (mut r, mut b, mut first) = (x, x, true);
    loop {
        if n & 1 == 1 {
            r = if first { b } else { r * b };
            first = false;
        }
        n >>= 1;
        if n == 0 {
            return r;
        }
        b *= b;
    }
}
/// S, S', S''/2 and sum |c_j| |x|^(m-j) at a point of the unit disc, for a polynomial with few terms.
///
/// A run of g - 1 zero coefficients is g steps of Horner's rule with nothing to add:
///
/// ```text
/// p2 <- p2 x^g + g p1 x^(g-1) + g (g-1)/2 p0 x^(g-2),   p1 <- p1 x^g + g p0 x^(g-1),   p0 <- p0 x^g + c
/// ```
///
/// with x^(g-2) by repeated squaring and two more products.  The value of S goes through g products for the
/// run (g - 1 inside x^g, one by it) and one sum, as in the dense rule: the rounding bound of Horner's rule,
/// `marg` times the sum of the moduli, holds for it unchanged.  (Operations that underflow: see `Poly::tiny`.)
#[inline(always)]
fn sparse_eval(steps: &[Gap], c0: C, a0: f64, x: C, ax: f64, second: bool) -> (C, C, C, f64) {
    let (mut p, mut d1, mut d2, mut sa) = (c0, ZERO, ZERO, a0);
    for st in steps {
        let g = st.gap;
        if g == 1 {
            if second {
                d2 = d2 * x + d1;
            }
            d1 = d1 * x + p;
            p = p * x + st.c;
            sa = sa * ax + st.abs;
            continue;
        }
        // y = x^(g-2), x1 = x^(g-1), x2 = x^g
        let (y, x1) = if g == 2 { (ONE, x) } else { let y = cpow(x, g - 2); (y, y * x) };
        let x2 = x1 * x;
        let gf = g as f64;
        if second {
            d2 = d2 * x2 + (d1 * x1).scale(gf) + (p * y).scale(gf * (gf - 1.0) / 2.0);
        }
        d1 = d1 * x2 + (p * x1).scale(gf);
        p = p * x2 + st.c;
        sa = sa * rpow(ax, g) + st.abs;
    }
    (p, d1, d2, sa)
}
#[inline(always)]
fn horner3(c: &[C], z: C) -> (C, C, C) {
    let (mut p, mut d1, mut d2) = (c[0], ZERO, ZERO);
    for a in &c[1..] {
        d2 = d2 * z + d1;
        d1 = d1 * z + p;
        p = p * z + *a;
    }
    (p, d1, d2.scale(2.0))
}
#[inline(always)]
fn horner_abs(c: &[f64], x: f64) -> f64 {
    let mut s = c[0];
    for a in &c[1..] {
        s = s * x + *a;
    }
    s
}
impl Poly {
    pub fn new(c: Vec<C>) -> Poly {
        let abs: Vec<f64> = c.iter().map(|x| x.abs()).collect();
        let rev: Vec<C> = c.iter().rev().cloned().collect();
        let absrev: Vec<f64> = abs.iter().rev().cloned().collect();
        // twelve zero coefficients or more for each one that is not: the runs of zeros are jumped over
        let nz = abs.iter().filter(|&&a| a != 0.0).count();
        let sparse = if c.len() >= 24 && 12 * nz <= c.len() { Some([gaps(&c, &abs), gaps(&rev, &absrev)]) } else { None };
        Poly { c, abs, rev, absrev, sparse }
    }
    /// What is added to the sum of the moduli in the rounding bound (`TINY` for the dense rule).  With few
    /// terms, a power x^g that underflows is off by a few ETA for each of its products, and that error is
    /// multiplied by the value so far, below sqrt 2 (m + 1): 64 TINY for each run of zeros covers it.
    pub fn tiny(&self) -> f64 {
        match &self.sparse {
            Some(g) => TINY * 64.0 * (g[0].len() as f64 + 1.0),
            None => TINY,
        }
    }
    pub fn degree(&self) -> usize {
        self.c.len() - 1
    }
    /// S and S' at a point (direct Horner; used at the centroid only).
    pub fn eval2(&self, z: C) -> (C, C) {
        let (p, d1, _) = horner3(&self.c, z);
        (p, d1)
    }
    /// S'/S, S''/S and the residual test at a point.
    #[inline]
    pub fn ev(&self, z: C, marg: f64) -> Ev {
        let m = self.degree() as f64;
        if z.norm_sqr() <= 1.0 {
            let (p, d1, d2) = horner3(&self.c, z);
            Ev { a: d1 / p, b: d2 / p, done: p.abs() <= marg * horner_abs(&self.abs, z.abs()) }
        } else {
            let w = z.inv();
            let (r, r1, r2) = horner3(&self.rev, w);
            let u = w * r1 / r;
            let v = w * w * r2 / r;
            let a = w * (C::new(m, 0.0) - u);
            let b = w * w * (C::new(m * (m - 1.0), 0.0) - u.scale(2.0 * (m - 1.0)) + v);
            Ev { a, b, done: r.abs() <= marg * horner_abs(&self.absrev, w.abs()) }
        }
    }
}

/// Scratch arrays for the evaluation of S, S', S'' at all the points at once (structure of arrays: the loop
/// over the points is the inner one, so that it is vectorised).
#[derive(Default)]
pub struct EvalWs {
    idx: Vec<usize>,
    x: [Vec<f64>; 2],
    p: [Vec<f64>; 2],
    a: [Vec<f64>; 2],
    b: [Vec<f64>; 2],
    ax: Vec<f64>,
    sa: Vec<f64>,
    /// how many of the points of `idx` are in the unit disc (they come first)
    nin: usize,
}
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn kernel<const D2: bool>(c: &[C], ca: &[f64], xr: &[f64], xi: &[f64], ax: &[f64], pr: &mut [f64], pi: &mut [f64], ar: &mut [f64], ai: &mut [f64], br: &mut [f64], bi: &mut [f64], sa: &mut [f64]) {
    let n = xr.len();
    let (xi, ax) = (&xi[..n], &ax[..n]);
    let (pr, pi, ar, ai, br, bi, sa) = (&mut pr[..n], &mut pi[..n], &mut ar[..n], &mut ai[..n], &mut br[..n], &mut bi[..n], &mut sa[..n]);
    for k in 0..n {
        pr[k] = c[0].re;
        pi[k] = c[0].im;
        ar[k] = 0.0;
        ai[k] = 0.0;
        br[k] = 0.0;
        bi[k] = 0.0;
        sa[k] = ca[0];
    }
    for (cj, caj) in c[1..].iter().zip(&ca[1..]) {
        let (cr, cim, caj) = (cj.re, cj.im, *caj);
        for k in 0..n {
            let (x, y) = (xr[k], xi[k]);
            if D2 {
                let nbr = br[k] * x - bi[k] * y + ar[k];
                let nbi = br[k] * y + bi[k] * x + ai[k];
                br[k] = nbr;
                bi[k] = nbi;
            }
            let nar = ar[k] * x - ai[k] * y + pr[k];
            let nai = ar[k] * y + ai[k] * x + pi[k];
            let npr = pr[k] * x - pi[k] * y + cr;
            let npi = pr[k] * y + pi[k] * x + cim;
            ar[k] = nar;
            ai[k] = nai;
            pr[k] = npr;
            pi[k] = npi;
            sa[k] = sa[k] * ax[k] + caj;
        }
    }
}
impl Poly {
    /// S'/S, S''/S and the residual test at all the points.
    /// `second`: also S''/S (not needed by the line AK).
    pub fn ev_all(&self, z: &[C], marg: f64, second: bool, ws: &mut EvalWs, out: &mut [Ev]) {
        self.ev_some(z, &[], marg, second, ws, out)
    }
    /// `ev_all` at the points k for which `skip[k]` is false (all of them if `skip` is empty); `out` keeps
    /// what it had for the others.  A point whose residual is at rounding level does not move any more, and
    /// its values need not be computed again (version 0.13.0).
    pub fn ev_some(&self, z: &[C], skip: &[bool], marg: f64, second: bool, ws: &mut EvalWs, out: &mut [Ev]) {
        let m = z.len();
        let deg = self.degree() as f64;
        let live = |k: usize| skip.is_empty() || !skip[k];
        ws.idx.clear();
        ws.idx.extend((0..m).filter(|&k| live(k) && z[k].norm_sqr() <= 1.0));
        let nin = ws.idx.len();
        ws.idx.extend((0..m).filter(|&k| live(k) && !(z[k].norm_sqr() <= 1.0)));
        let cnt = ws.idx.len();
        ws.nin = nin;
        for v in ws.x.iter_mut().chain(ws.p.iter_mut()).chain(ws.a.iter_mut()).chain(ws.b.iter_mut()) {
            v.resize(m, 0.0);
        }
        ws.ax.resize(m, 0.0);
        ws.sa.resize(m, 0.0);
        for (i, &k) in ws.idx.iter().enumerate() {
            let x = if i < nin { z[k] } else { z[k].inv() };
            ws.x[0][i] = x.re;
            ws.x[1][i] = x.im;
            ws.ax[i] = x.norm_sqr().sqrt();
        }
        let [xr, xi] = &ws.x;
        let [pr, pi] = &mut ws.p;
        let [ar, ai] = &mut ws.a;
        let [br, bi] = &mut ws.b;
        if let Some(sp) = &self.sparse {
            for i in 0..cnt {
                let (steps, c0, a0) = if i < nin { (&sp[0], self.c[0], self.abs[0]) } else { (&sp[1], self.rev[0], self.absrev[0]) };
                let (p, d1, d2, sa) = sparse_eval(steps, c0, a0, C::new(xr[i], xi[i]), ws.ax[i], second);
                pr[i] = p.re;
                pi[i] = p.im;
                ar[i] = d1.re;
                ai[i] = d1.im;
                br[i] = d2.re;
                bi[i] = d2.im;
                ws.sa[i] = sa;
            }
        } else if second {
            kernel::<true>(&self.c, &self.abs, &xr[..nin], &xi[..nin], &ws.ax[..nin], &mut pr[..nin], &mut pi[..nin], &mut ar[..nin], &mut ai[..nin], &mut br[..nin], &mut bi[..nin], &mut ws.sa[..nin]);
            kernel::<true>(&self.rev, &self.absrev, &xr[nin..cnt], &xi[nin..cnt], &ws.ax[nin..cnt], &mut pr[nin..cnt], &mut pi[nin..cnt], &mut ar[nin..cnt], &mut ai[nin..cnt], &mut br[nin..cnt], &mut bi[nin..cnt], &mut ws.sa[nin..cnt]);
        } else {
            kernel::<false>(&self.c, &self.abs, &xr[..nin], &xi[..nin], &ws.ax[..nin], &mut pr[..nin], &mut pi[..nin], &mut ar[..nin], &mut ai[..nin], &mut br[..nin], &mut bi[..nin], &mut ws.sa[..nin]);
            kernel::<false>(&self.rev, &self.absrev, &xr[nin..cnt], &xi[nin..cnt], &ws.ax[nin..cnt], &mut pr[nin..cnt], &mut pi[nin..cnt], &mut ar[nin..cnt], &mut ai[nin..cnt], &mut br[nin..cnt], &mut bi[nin..cnt], &mut ws.sa[nin..cnt]);
        }
        for (i, &k) in ws.idx.iter().enumerate() {
            let p = C::new(pr[i], pi[i]);
            let d1 = C::new(ar[i], ai[i]);
            let d2 = C::new(2.0 * br[i], 2.0 * bi[i]);
            let n2 = p.norm_sqr();
            let pa = if n2 > 1e-290 && n2 < 1e290 { n2.sqrt() } else { p.abs() };
            let done = pa <= marg * ws.sa[i];
            let ip = p.inv();
            out[k] = if i < nin {
                Ev { a: d1 * ip, b: d2 * ip, done }
            } else {
                let w = C::new(xr[i], xi[i]);
                let u = w * d1 * ip;
                let v = w * w * d2 * ip;
                Ev { a: w * (C::new(deg, 0.0) - u), b: w * w * (C::new(deg * (deg - 1.0), 0.0) - u.scale(2.0 * (deg - 1.0)) + v), done }
            };
        }
    }
}

impl Poly {
    /// Upper bounds of |S(z_k)| / |c| as (mantissa, exponent of two): computed modulus plus the rounding bound
    /// of Horner's rule.
    pub fn bound_all(&self, z: &[C], ws: &mut EvalWs, out: &mut Vec<(f64, i64)>) {
        let m = self.degree();
        let marg = 4.0 * (m as f64 + 1.0) * U;
        let mut ev = vec![Ev { a: ZERO, b: ZERO, done: false }; z.len()];
        self.ev_all(z, marg, false, ws, &mut ev);
        out.clear();
        out.resize(z.len(), (0.0, 0));
        for (i, &k) in ws.idx.iter().enumerate() {
            out[k] = self.bound_one(ws.p[0][i], ws.p[1][i], ws.sa[i], i < ws.nin, z[k]);
        }
    }
    /// The bound of one point from what Horner's rule computed there: the value (pr, pi) of S, or of the
    /// reversed polynomial at 1/z for a point outside the unit disc, and the sum of the moduli `sa`.
    fn bound_one(&self, pr: f64, pi: f64, sa: f64, inside: bool, z: C) -> (f64, i64) {
        let m = self.degree();
        let marg = 4.0 * (m as f64 + 1.0) * U;
        let pa = pr.hypot(pi);
        // outside the unit disc the point 1/z is itself rounded: twice the margin
        let mg = if inside { marg } else { 2.0 * marg };
        // the leading coefficient may have been rounded to a subnormal number: lower bound of its modulus
        let lead = self.abs[0] - 4.0 * ETA;
        let b = if lead > 0.0 { (pa + mg * (sa + self.tiny())) / lead * (1.0 + 4.0 * U) } else { f64::INFINITY };
        if inside {
            (b, 0)
        } else {
            let (fz, e) = frexp(z.abs());
            (b * fz.powi(m as i32) * (1.0 + 2.0 * m as f64 * U), e * m as i64)
        }
    }
}

/// Fujiwara's bound of the moduli of the roots.
pub fn fujiwara(s: &Poly) -> f64 {
    let mut rf: f64 = 0.0;
    for j in 1..=s.degree() {
        rf = rf.max((s.abs[j] / s.abs[0]).powf(1.0 / j as f64));
    }
    2.0 * rf
}

/// m points on a circle around the centroid of the roots (start of G2/G7); also the Fujiwara bound.
pub fn landing_circle(s: &Poly) -> (Vec<C>, f64) {
    let m = s.degree();
    let c0 = s.c[0];
    let cen = -(s.c[1] / c0).scale(1.0 / m as f64);
    let rf = fujiwara(s);
    let (p0, p1) = s.eval2(cen);
    let mut r = (p0.abs() / s.abs[0]).powf(1.0 / m as f64).max((p1.abs() / (m as f64 * s.abs[0])).powf(1.0 / (m as f64 - 1.0)));
    if !r.is_finite() || r < 1e-8 * rf {
        r = rf / 2.0;
    }
    let z = (0..m).map(|j| cen + C::from_polar(r, 2.0 * std::f64::consts::PI * j as f64 / m as f64 + 0.7)).collect();
    (z, rf)
}

/// Start from the dominant binomials of S at every scale.  Each edge (i, k) of the Newton polygon of the
/// coefficients a_j of z^j is a binomial carrying K = k - i roots; runs of single-root edges that are not
/// dominant are merged; a group is treated as a shifted power (its centroid, then the K-th roots at their true
/// angles).  Real polynomials: groups with K >= 2 are rotated by a tenth of their angular spacing.
pub fn binomial_start(s: &Poly) -> Option<Vec<C>> {
    binomial_start_with(s, true)
}

/// `binomial_start`; with `merge` false every edge of the Newton polygon is a group by itself.
pub fn binomial_start_with(s: &Poly, merge: bool) -> Option<Vec<C>> {
    const THETA: f64 = 2.0;
    const FRAC: f64 = 0.1;
    let m = s.degree();
    let a = |j: usize| s.c[m - j];
    let la: Vec<f64> = (0..=m).map(|j| s.abs[m - j].ln()).collect();
    let j0 = (0..=m).find(|&j| s.abs[m - j] > 0.0)?;
    let mut h: Vec<usize> = Vec::new();
    for j in j0..=m {
        if s.abs[m - j] == 0.0 {
            continue;
        }
        while h.len() >= 2 {
            let (p, q) = (h[h.len() - 1], h[h.len() - 2]);
            if (la[p] - la[q]) * (j - q) as f64 <= (la[j] - la[q]) * (p - q) as f64 {
                h.pop();
            } else {
                break;
            }
        }
        h.push(j);
    }
    let ne = h.len() - 1;
    let mut soft = vec![false; ne];
    for e in 0..ne {
        let (i, k) = (h[e], h[e + 1]);
        if k - i == 1 {
            let lu = la[i] - la[k];
            let base = la[i] + i as f64 * lu;
            let mut others = -2.0;
            for j in j0..=m {
                if la[j].is_finite() {
                    others += (la[j] + j as f64 * lu - base).exp();
                    if others > THETA {
                        break;
                    }
                }
            }
            soft[e] = merge && !(others <= THETA);
        }
    }
    let real = s.c.iter().all(|x| x.im == 0.0);
    let mut z: Vec<C> = vec![ZERO; j0];
    let mut e = 0;
    while e < ne {
        let mut f = e;
        if soft[e] {
            while f + 1 < ne && soft[f + 1] {
                f += 1;
            }
        }
        let (i, k) = (h[e], h[f + 1]);
        let kk = k - i;
        e = f + 1;
        if kk == 1 {
            z.push(-(a(i) / a(k)));
            continue;
        }
        let g = -(a(k - 1) / a(k)).scale(1.0 / kk as f64);
        let mut q = a(k);
        for j in (i..k).rev() {
            q = q * g + a(j);
        }
        let w = -(q / a(k));
        let r = w.abs().powf(1.0 / kk as f64);
        let th0 = w.arg() / kk as f64 + if real { FRAC * 2.0 * std::f64::consts::PI / kk as f64 } else { 0.0 };
        for j in 0..kk {
            z.push(g + C::from_polar(r, th0 + 2.0 * std::f64::consts::PI * j as f64 / kk as f64));
        }
    }
    if z.len() != m || z.iter().any(|x| !x.is_finite()) {
        return None;
    }
    for i in 0..m {
        for j in 0..i {
            if z[i] == z[j] {
                return None;
            }
        }
    }
    Some(z)
}

/// sum over the slices of 1/(z - y_l) and of its square (four independent lanes, so that the loop is vectorised)
#[inline(always)]
fn sums(z: C, yr: &[f64], yi: &[f64], s1: &mut C, s2: &mut C) {
    let n = yr.len();
    let yi = &yi[..n];
    let mut acc = [[0.0f64; 4]; 4];
    let mut cr = yr.chunks_exact(4);
    let mut ci = yi.chunks_exact(4);
    for (r4, i4) in (&mut cr).zip(&mut ci) {
        for j in 0..4 {
            let dr = z.re - r4[j];
            let di = z.im - i4[j];
            let r = 1.0 / (dr * dr + di * di);
            let ir = dr * r;
            let ii = -di * r;
            acc[0][j] += ir;
            acc[1][j] += ii;
            acc[2][j] += ir * ir - ii * ii;
            acc[3][j] += 2.0 * ir * ii;
        }
    }
    for (yr, yi) in cr.remainder().iter().zip(ci.remainder()) {
        let dr = z.re - yr;
        let di = z.im - yi;
        let r = 1.0 / (dr * dr + di * di);
        let ir = dr * r;
        let ii = -di * r;
        acc[0][0] += ir;
        acc[1][0] += ii;
        acc[2][0] += ir * ir - ii * ii;
        acc[3][0] += 2.0 * ir * ii;
    }
    let s = |a: &[f64; 4]| (a[0] + a[1]) + (a[2] + a[3]);
    s1.re += s(&acc[0]);
    s1.im += s(&acc[1]);
    s2.re += s(&acc[2]);
    s2.im += s(&acc[3]);
}
#[inline(always)]
fn sum1(z: C, yr: &[f64], yi: &[f64], s1: &mut C) {
    let n = yr.len();
    let yi = &yi[..n];
    let mut acc = [[0.0f64; 4]; 2];
    let mut cr = yr.chunks_exact(4);
    let mut ci = yi.chunks_exact(4);
    for (r4, i4) in (&mut cr).zip(&mut ci) {
        for j in 0..4 {
            let dr = z.re - r4[j];
            let di = z.im - i4[j];
            let r = 1.0 / (dr * dr + di * di);
            acc[0][j] += dr * r;
            acc[1][j] -= di * r;
        }
    }
    for (yr, yi) in cr.remainder().iter().zip(ci.remainder()) {
        let dr = z.re - yr;
        let di = z.im - yi;
        let r = 1.0 / (dr * dr + di * di);
        acc[0][0] += dr * r;
        acc[1][0] -= di * r;
    }
    let s = |a: &[f64; 4]| (a[0] + a[1]) + (a[2] + a[3]);
    s1.re += s(&acc[0]);
    s1.im += s(&acc[1]);
}

/// Scratch of a sweep: the announced positions, as two arrays.
#[derive(Default)]
pub struct StepWs {
    yr: Vec<f64>,
    yi: Vec<f64>,
}

/// One sweep of the simultaneous rectangle from a = S'/S and b = S''/S at the points.
/// `ev[k].done`: the point k does not move.  Writes the displacements in `dz` (new point = z - dz).
pub fn rectangle_step(z: &[C], ev: &[Ev], cf: &[f64; 4], opt: &Options, ws: &mut StepWs, dz: &mut [C]) {
    let m = z.len();
    let mf = m as f64;
    ws.yr.clear();
    ws.yi.clear();
    for l in 0..m {
        let mut yl = z[l];
        if opt.announce != Announce::None && !ev[l].done {
            let ia = ev[l].a.inv();
            let h = if opt.announce == Announce::AK {
                ia
            } else {
                let t = ONE - (ev[l].b * ia * ia).scale(mf / (mf - 1.0));
                (ia * (ONE + three(t, cf).scale(mf - 1.0)).fast_inv()).scale(mf)
            };
            if h.is_finite() {
                yl = z[l] - h;
            }
        }
        ws.yr.push(yl.re);
        ws.yi.push(yl.im);
    }
    for k in 0..m {
        if ev[k].done {
            dz[k] = ZERO;
            continue;
        }
        let a = ev[k].a;
        let (mut s1, mut s2) = (ZERO, ZERO);
        let step = match opt.outer {
            Support::AK => {
                sum1(z[k], &ws.yr[..k], &ws.yi[..k], &mut s1);
                sum1(z[k], &ws.yr[k + 1..], &ws.yi[k + 1..], &mut s1);
                (a - s1).inv()
            }
            Support::Three => {
                sums(z[k], &ws.yr[..k], &ws.yi[..k], &mut s1, &mut s2);
                sums(z[k], &ws.yr[k + 1..], &ws.yi[k + 1..], &mut s1, &mut s2);
                let ia = (a - s1).inv();
                let b = a * a - ev[k].b - s2;
                let t = ((b * ia * ia).scale(mf) - ONE).scale(1.0 / (mf - 1.0));
                (ia * (ONE + three(t, cf).scale(mf - 1.0)).fast_inv()).scale(mf)
            }
        };
        dz[k] = step;
        if opt.gauss_seidel && step.is_finite() {
            let n = z[k] - step;
            ws.yr[k] = n.re;
            ws.yi[k] = n.im;
        }
    }
}

/// The simultaneous rectangle in double precision.  Returns the points and the number of sweeps.
pub fn simultaneous(s: &Poly, opt: &Options, max_sweeps: usize) -> (Vec<C>, usize) {
    let (z, it, _) = simultaneous_bounds(s, opt, max_sweeps);
    (z, it)
}

/// `simultaneous`, and the bounds of |S(z_k)| / |c| at the points returned (those of `Poly::bound_all`) when
/// the sweeps ended with every residual at rounding level (version 0.13.0).
///
/// The points are rounded to 53 bits of their modulus as they move (`exact::quantize`), which is what the
/// certificate asks of them; the last evaluation of each point by the sweeps is then the evaluation that
/// the certificate would make, and it is not made twice.  A point whose residual is at rounding level does
/// not move, and is not evaluated again.  (Up to 0.13.0 a polynomial of degree 20 was evaluated at its
/// points six times: four sweeps, the evaluation that found them all at rounding level, and the same once
/// more at the rounded points for the certificate.)
pub fn simultaneous_bounds(s: &Poly, opt: &Options, max_sweeps: usize) -> (Vec<C>, usize, Option<Vec<(f64, i64)>>) {
    let m = s.degree();
    if m == 1 {
        return (vec![-(s.c[1] / s.c[0])], 0, None);
    }
    // the circle around the centroid only if the dominant binomials give no start
    let start = if opt.start != Start::Circle { binomial_start_with(s, opt.start == Start::Binomial) } else { None };
    let (z, mut rf) = match start {
        Some(zb) => (zb, None),
        None => {
            let (z, rf) = landing_circle(s);
            (z, Some(rf))
        }
    };
    let mut z: Vec<C> = z.into_iter().map(crate::exact::quantize).collect();
    let cf = coeffs3(m as f64);
    let marg = 4.0 * (m as f64 + 1.0) * U;
    let mut ev = vec![Ev { a: ZERO, b: ZERO, done: false }; m];
    let mut done = vec![false; m];
    // what Horner's rule computed at the last evaluation of each point: value, sum of the moduli, inside
    let mut last = vec![(0.0f64, 0.0f64, 0.0f64, true); m];
    let mut ews = EvalWs::default();
    let mut sws = StepWs::default();
    let mut dz = vec![ZERO; m];
    let mut it = 0;
    let mut settled = false;
    while it < max_sweeps {
        s.ev_some(&z, &done, marg, opt.outer == Support::Three || opt.announce == Announce::Three, &mut ews, &mut ev);
        for (i, &k) in ews.idx.iter().enumerate() {
            last[k] = (ews.p[0][i], ews.p[1][i], ews.sa[i], i < ews.nin);
            done[k] = ev[k].done;
        }
        if done.iter().all(|&d| d) {
            settled = true;
            break;
        }
        rectangle_step(&z, &ev, &cf, opt, &mut sws, &mut dz);
        let mut small = true;
        for k in 0..m {
            if done[k] {
                continue; // dz[k] = 0
            }
            if !dz[k].is_finite() {
                let r = *rf.get_or_insert_with(|| fujiwara(s));
                dz[k] = C::from_polar(1e-3 * r, k as f64); // 0/0: nudge, the same iteration goes on
            }
            let n = crate::exact::quantize(z[k] - dz[k]);
            small &= (z[k] - n).norm_sqr() <= 16.0 * U * U * n.norm_sqr();
            z[k] = n;
        }
        it += 1;
        if small {
            break;
        }
    }
    let bounds = settled.then(|| (0..m).map(|k| s.bound_one(last[k].0, last[k].1, last[k].2, last[k].3, z[k])).collect());
    (z, it, bounds)
}

/// frexp: x = f 2^e with 0.5 <= |f| < 1 (x finite, nonzero).
#[inline]
pub fn frexp(x: f64) -> (f64, i64) {
    if x == 0.0 || !x.is_finite() {
        return (x, 0);
    }
    let bits = x.to_bits();
    let ex = ((bits >> 52) & 0x7ff) as i64;
    if ex == 0 {
        let (f, e) = frexp(x * 18014398509481984.0); // 2^54
        return (f, e - 54);
    }
    (f64::from_bits((bits & !(0x7ffu64 << 52)) | (1022u64 << 52)), ex - 1022)
}
/// x 2^e without spurious overflow or underflow of the scale factor.
#[inline]
pub fn ldexp(mut x: f64, mut e: i64) -> f64 {
    while e > 1000 {
        x *= 1.0715086071862673e301; // 2^1000
        e -= 1000;
        if !x.is_finite() {
            return x;
        }
    }
    while e < -1000 {
        x *= 9.332636185032189e-302; // 2^-1000
        e += 1000;
        if x == 0.0 {
            return x;
        }
    }
    x * (2.0f64).powi(e as i32)
}

/// |dr + i di| as (mantissa, exponent of two), accurate also when the components are subnormal or huge
/// (they are first scaled by an exact power of two).
pub fn abs_scaled(dr: f64, di: f64) -> (f64, i64) {
    let big = dr.abs().max(di.abs());
    if big == 0.0 || !big.is_finite() {
        return (big, 0);
    }
    let (_, e) = frexp(big);
    let (f, e2) = frexp(ldexp(dr, -e).hypot(ldexp(di, -e)));
    (f, e + e2)
}

/// prod_{l != k} |z_k - z_l| as (mantissa, exponent of two); mantissa 0 if two points coincide.
pub fn products(z: &[C]) -> Vec<(f64, i64)> {
    const MANT: u64 = (1u64 << 52) - 1;
    let m = z.len();
    let zr: Vec<f64> = z.iter().map(|x| x.re).collect();
    let zi: Vec<f64> = z.iter().map(|x| x.im).collect();
    let mut out = Vec::with_capacity(m);
    for k in 0..m {
        let (x, y) = (zr[k], zi[k]);
        // fast path: mantissas multiplied, exponents added (squared moduli must be normal numbers)
        let mut f = [1.0f64; 4];
        let mut e = [0i64; 4];
        let mut unsafe_ = false;
        let mut cnt = 0usize;
        let mut ff = 1.0f64;
        let mut ee = 0i64;
        for (r4, i4) in zr.chunks(4).zip(zi.chunks(4)) {
            for j in 0..r4.len() {
                let dr = x - r4[j];
                let di = y - i4[j];
                let n = dr * dr + di * di;
                let n = if cnt + j == k { 1.0 } else { n };
                unsafe_ |= !(n > 1e-290 && n < 1e290);
                let bits = n.to_bits();
                f[j] *= f64::from_bits((bits & MANT) | (1023u64 << 52));
                e[j] += ((bits >> 52) & 0x7ff) as i64 - 1023;
            }
            cnt += r4.len();
            if cnt % 512 == 0 {
                for j in 0..4 {
                    let (g, eg) = frexp(f[j]);
                    f[j] = g;
                    e[j] += eg;
                }
            }
        }
        if !unsafe_ {
            for j in 0..4 {
                let (g, eg) = frexp(f[j]);
                ff *= g;
                ee += e[j] + eg;
            }
        } else {
            for l in 0..m {
                if l == k {
                    continue;
                }
                let (fa, ea) = abs_scaled(z[k].re - z[l].re, z[k].im - z[l].im);
                ff *= fa * fa;
                ee += 2 * ea;
                if ff == 0.0 || !ff.is_finite() {
                    break;
                }
                let (g, eg) = frexp(ff);
                ff = g;
                ee += eg;
            }
        }
        if ff == 0.0 || !ff.is_finite() {
            out.push((0.0, 0));
            continue;
        }
        let (g, eg) = frexp(ff);
        let (g, eg) = if (ee + eg).rem_euclid(2) != 0 { (g * 2.0, ee + eg - 1) } else { (g, ee + eg) };
        out.push((g.sqrt(), eg / 2));
    }
    out
}

/// |a - b| compared with a bound, through squares when they are safe.
#[inline(always)]
pub fn dist_le(dr: f64, di: f64, bound: f64) -> bool {
    let n = dr * dr + di * di;
    let b2 = bound * bound;
    if n > 1e-290 && n < 1e290 && b2 > 1e-290 && b2 < 1e290 {
        n <= b2
    } else {
        // near the underflow threshold the comparison is made after an exact scaling; "true" (the discs may
        // touch) is the safe answer
        let (f, e) = abs_scaled(dr, di);
        let (fb, eb) = frexp(bound);
        if bound.is_nan() || f.is_nan() {
            return true;
        }
        if f == 0.0 || bound.is_infinite() {
            return true;
        }
        if f.is_infinite() || bound == 0.0 {
            return false;
        }
        e < eb || (e == eb && f <= fb * (1.0 + 4.0 * U))
    }
}

/// The smallest of |x + i y - z_l|^2 over the slices (infinite for empty slices).
#[inline(always)]
fn min_sq(x: f64, y: f64, zr: &[f64], zi: &[f64]) -> f64 {
    let n = zr.len();
    let zi = &zi[..n];
    let mut lo = [f64::INFINITY; 4];
    let mut cr = zr.chunks_exact(4);
    let mut ci = zi.chunks_exact(4);
    for (r4, i4) in (&mut cr).zip(&mut ci) {
        for j in 0..4 {
            let (dr, di) = (x - r4[j], y - i4[j]);
            let n = dr * dr + di * di;
            if n < lo[j] {
                lo[j] = n;
            }
        }
    }
    for (a, b) in cr.remainder().iter().zip(ci.remainder()) {
        let (dr, di) = (x - a, y - b);
        let n = dr * dr + di * di;
        if n < lo[0] {
            lo[0] = n;
        }
    }
    lo[0].min(lo[1]).min(lo[2].min(lo[3]))
}

/// The fixed-point certificate (formalised in Lean: FixedPointCertificate.all_roots_of_computed,
/// with w = r / m and g = the lowered gaps below).
/// With w_k = r_k / m >= |W_k| and rho_k = 2 w_k: if every gap g_kl = |z_k - z_l| - rho_k is positive,
/// sigma_k = sum_{l != k} w_l / g_kl < 1/2 and w_k tau_k < 1/4, tau_k = sum_{l != k} w_l / g_kl^2, the map
/// Phi_k is a contraction of D(z_k, rho_k) into itself and the disc contains exactly one root; sigma_k < 1/2
/// also makes it disjoint from every other disc.  Returns the radii rho_k and the flags.
/// One point: D(z_1, |W_1|) contains the root (Smith).
pub fn fixed_point(z: &[C], r: &[f64]) -> (Vec<f64>, Vec<bool>) {
    let m = z.len();
    if m == 1 {
        return (r.to_vec(), vec![r[0].is_finite()]);
    }
    let mf = m as f64;
    let zr: Vec<f64> = z.iter().map(|x| x.re).collect();
    let zi: Vec<f64> = z.iter().map(|x| x.im).collect();
    let w: Vec<f64> = r.iter().map(|&x| x / mf * (1.0 + SLACK)).collect(); // inflated bounds: see SLACK
    let down = 1.0 - 8.0 * U;
    let up = 1.0 + (2.0 * mf + 16.0) * U;
    let mut rho = vec![0.0; m];
    let mut one = vec![false; m];
    // The test from the smallest gap (version 0.13.0).  With g = min_l g_kl > 0 and W = sum_l w_l,
    // sigma_k <= W / g and tau_k <= W / g^2: when these bounds pass the two tests, with `up` three times
    // (once for the rounding of W and of the quotients, twice so that the sums below would pass as well),
    // the disc passes and the sums are not formed.  The smallest gap costs one pass without square root or
    // division; for points that have converged W is tiny against the gaps and the bounds are enough.
    let wsum: f64 = w.iter().sum();
    let up3 = up * up * up;
    let quick = wsum.is_finite() && z.iter().all(|x| x.is_finite());
    for k in 0..m {
        let (x, y, wk) = (zr[k], zi[k], w[k]);
        let rk = 2.0 * wk;
        rho[k] = 2.0 * r[k] / mf;
        if !r[k].is_finite() {
            continue;
        }
        if quick {
            let lo = min_sq(x, y, &zr[..k], &zi[..k]).min(min_sq(x, y, &zr[k + 1..], &zi[k + 1..]));
            let g = lo.sqrt() * down - rk;
            if lo > 1e-290 && g > 0.0 {
                let s = wsum / g;
                if s * up3 + 1e-300 < 0.5 && wk * (s / g) * up3 + 1e-300 < 0.25 {
                    one[k] = true;
                    continue;
                }
            }
        }
        // Four independent lanes (point l in lane l mod 4, the last points in lane 0): the sums do not wait
        // for one another.  The groups of four that do not hold k are straight-line code on arrays of four,
        // which the compiler turns into vector instructions (version 0.13.0; the sums are those of the
        // loop of 0.12.0, term for term).  The smallest gap is the gap of the smallest squared distance
        // (square root, product and difference are monotone), and a squared distance out of range, or one
        // that is not a number, shows in the smallest, in the largest or in the sum.
        let (mut sg, mut ta) = ([0.0f64; 4], [0.0f64; 4]);
        let (mut nmin, mut nmax) = ([f64::INFINITY; 4], [0.0f64; 4]);
        let m4 = m & !3;
        let own = k / 4; // the group of k
        let group = |c: usize, sg: &mut [f64; 4], ta: &mut [f64; 4], nmin: &mut [f64; 4], nmax: &mut [f64; 4]| {
            let (r4, i4, w4) = (&zr[4 * c..4 * c + 4], &zi[4 * c..4 * c + 4], &w[4 * c..4 * c + 4]);
            for j in 0..4 {
                let (dr, di) = (x - r4[j], y - i4[j]);
                let n = dr * dr + di * di;
                if n < nmin[j] {
                    nmin[j] = n;
                }
                if n > nmax[j] {
                    nmax[j] = n;
                }
                let inv = 1.0 / (n.sqrt() * down - rk);
                let t = w4[j] * inv;
                sg[j] += t;
                ta[j] += t * inv;
            }
        };
        let single = |l: usize, j: usize, sg: &mut [f64; 4], ta: &mut [f64; 4], nmin: &mut [f64; 4], nmax: &mut [f64; 4]| {
            if l == k {
                return; // the term of k itself is zero
            }
            let (dr, di) = (x - zr[l], y - zi[l]);
            let n = dr * dr + di * di;
            if n < nmin[j] {
                nmin[j] = n;
            }
            if n > nmax[j] {
                nmax[j] = n;
            }
            let inv = 1.0 / (n.sqrt() * down - rk);
            let t = w[l] * inv;
            sg[j] += t;
            ta[j] += t * inv;
        };
        for c in 0..(m4 / 4).min(own) {
            group(c, &mut sg, &mut ta, &mut nmin, &mut nmax);
        }
        if own < m4 / 4 {
            for j in 0..4 {
                single(4 * own + j, j, &mut sg, &mut ta, &mut nmin, &mut nmax);
            }
            for c in own + 1..m4 / 4 {
                group(c, &mut sg, &mut ta, &mut nmin, &mut nmax);
            }
        }
        for l in m4..m {
            single(l, 0, &mut sg, &mut ta, &mut nmin, &mut nmax);
        }
        let (lo, hi) = (nmin[0].min(nmin[1]).min(nmin[2].min(nmin[3])), nmax[0].max(nmax[1]).max(nmax[2].max(nmax[3])));
        let mut closed = !(lo.sqrt() * down - rk > 0.0);
        let mut sigma = (sg[0] + sg[1]) + (sg[2] + sg[3]);
        let mut tau = (ta[0] + ta[1]) + (ta[2] + ta[3]);
        let unsafe_ = !(lo > 1e-290 && hi < 1e290) || sigma.is_nan() || tau.is_nan();
        if unsafe_ {
            sigma = 0.0;
            tau = 0.0;
            closed = false;
            for l in 0..m {
                if l != k {
                    let d = (x - zr[l]).hypot(y - zi[l]);
                    let g = d * down - rk;
                    closed |= !(g > 0.0) || d < SMALL; // a distance that small is not trusted
                    let t = w[l] / g;
                    sigma += t;
                    tau += t / g;
                }
            }
        }
        one[k] = !closed && sigma * up + 1e-300 < 0.5 && wk * tau * up + 1e-300 < 0.25;
    }
    (rho, one)
}

/// The real-root test: the disc centred at the real point Re z_k with radius rad + |Im z_k|, which contains
/// D(z_k, rad) and its mirror image, meets no disc D(z_l, cover_l), l != k.  Then the root of D(z_k, rad) is
/// real, and that real disc (the one returned) contains no other root.
pub fn mirror(z: &[C], cover: &[f64], k: usize, rad: f64) -> bool {
    let (x, big) = (z[k].re, (rad + z[k].im.abs()) * (1.0 + 4.0 * U));
    (0..z.len()).all(|j| j == k || !dist_le(x - z[j].re, -z[j].im, (big + cover[j]) * (1.0 + SLACK)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn next(state: &mut u64) -> f64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        (*state >> 11) as f64 / (1u64 << 53) as f64
    }

    /// The evaluation over the runs of zero coefficients gives the values of the dense rule, within the
    /// rounding bound of both, at points inside and outside the unit disc.
    #[test]
    fn sparse_evaluation_agrees_with_the_dense_rule() {
        let mut st = 0x9e3779b97f4a7c15u64;
        let mut seen = 0;
        for t in 0..300 {
            let m = 24 + (next(&mut st) * 400.0) as usize;
            let mut c = vec![ZERO; m + 1];
            let terms = 1 + (next(&mut st) * (m / 14) as f64) as usize;
            for _ in 0..terms {
                let j = (next(&mut st) * (m + 1) as f64) as usize;
                c[j.min(m)] = C::new(next(&mut st) - 0.5, if t % 2 == 0 { 0.0 } else { next(&mut st) - 0.5 });
            }
            c[0] = C::new(1.0, 0.0);
            if t % 3 != 0 {
                c[m] = C::new(0.5, 0.25); // otherwise the last coefficient may be zero
            }
            if t % 5 == 0 && m > 30 {
                c[m - 1] = C::new(-0.3, 0.0); // two coefficients in a row
                c[m - 3] = C::new(0.2, 0.1); // and a run of one zero
            }
            let sp = Poly::new(c.clone());
            if sp.sparse.is_none() {
                continue; // too many terms for this degree
            }
            seen += 1;
            let dense = Poly { sparse: None, ..Poly::new(c) };
            let z: Vec<C> = (0..40).map(|k| C::from_polar(if k % 4 == 0 { 1.0 } else { 0.2 + 1.6 * next(&mut st) }, 7.0 * next(&mut st))).collect();
            let marg = 4.0 * (m as f64 + 1.0) * U;
            let blank = vec![Ev { a: ZERO, b: ZERO, done: false }; z.len()];
            let (mut e1, mut e2, mut w1, mut w2) = (blank.clone(), blank, EvalWs::default(), EvalWs::default());
            sp.ev_all(&z, marg, true, &mut w1, &mut e1);
            dense.ev_all(&z, marg, true, &mut w2, &mut e2);
            for i in 0..z.len() {
                let (p1, p2) = (C::new(w1.p[0][i], w1.p[1][i]), C::new(w2.p[0][i], w2.p[1][i]));
                // the two values of S are within the two rounding bounds; the sums of the moduli agree
                assert!((p1 - p2).abs() <= marg * (w1.sa[i] + w2.sa[i]), "case {t}, point {i}: {p1:?} {p2:?}");
                assert!((w1.sa[i] - w2.sa[i]).abs() <= 1e-12 * w2.sa[i]);
                // S' and S'': where the value is well above its rounding bound, the ratios agree
                if p2.abs() > 1e6 * marg * w2.sa[i] {
                    let k = w1.idx[i];
                    assert_eq!(k, w2.idx[i]);
                    assert!((e1[k].a - e2[k].a).abs() <= 1e-6 * e2[k].a.abs() + 1e-9, "case {t}, point {i}: S'/S {:?} {:?}", e1[k].a, e2[k].a);
                    assert!((e1[k].b - e2[k].b).abs() <= 1e-6 * e2[k].b.abs() + 1e-6, "case {t}, point {i}: S''/S {:?} {:?}", e1[k].b, e2[k].b);
                }
            }
        }
        assert!(seen > 200, "{seen}");
    }

    /// The flags of the certificate against the two sums formed one term at a time: a disc that passes
    /// satisfies the two inequalities, and one that satisfies them with a margin passes (whether the test
    /// from the smallest gap or the sums decided).
    #[test]
    fn fixed_point_flags_agree_with_the_plain_sums() {
        let mut st = 0x2545f4914f6cdd1du64;
        let (mut passed, mut failed) = (0, 0);
        for t in 0..400 {
            let m = 2 + (next(&mut st) * 40.0) as usize;
            let z: Vec<C> = (0..m).map(|_| C::new(next(&mut st) - 0.5, next(&mut st) - 0.5)).collect();
            // radii from far below the gaps to their size; sometimes one that is zero or infinite
            let scale = 10f64.powf(-12.0 * next(&mut st));
            let mut r: Vec<f64> = (0..m).map(|_| scale * next(&mut st) * m as f64).collect();
            if t % 7 == 0 {
                r[0] = 0.0;
            }
            if t % 11 == 0 {
                r[m - 1] = f64::INFINITY;
            }
            let (rho, one) = fixed_point(&z, &r);
            for k in 0..m {
                assert_eq!(rho[k], 2.0 * r[k] / m as f64);
                let w = |l: usize| r[l] / m as f64 * (1.0 + SLACK);
                let (mut sigma, mut tau, mut open) = (0.0, 0.0, true);
                for l in (0..m).filter(|&l| l != k) {
                    let g = (z[k] - z[l]).abs() - 2.0 * w(k);
                    open &= g > 0.0;
                    sigma += w(l) / g;
                    tau += w(l) / (g * g);
                }
                let holds = |margin: f64| r[k].is_finite() && open && sigma < 0.5 * margin && w(k) * tau < 0.25 * margin;
                if one[k] {
                    assert!(holds(1.0 + 1e-9), "case {t}, point {k}: passed, sigma = {sigma}, w tau = {}", w(k) * tau);
                    passed += 1;
                } else {
                    assert!(!holds(1.0 - 1e-6), "case {t}, point {k}: refused, sigma = {sigma}, w tau = {}", w(k) * tau);
                    failed += 1;
                }
            }
        }
        assert!(passed > 1000 && failed > 1000, "{passed} {failed}");
    }
}
