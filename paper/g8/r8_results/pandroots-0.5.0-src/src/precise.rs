//! Points with more than 53 bits.
//!
//! The same sweep and the same certificate as in double precision, continued when the tolerance asks for
//! more digits than a double holds, or when double precision could not separate or decide the roots.  The
//! points are dyadic numbers of any size.
//!
//! * The values of S, S', S'' are computed in fixed point with F bits and a rigorous bound of the rounding
//!   of S (`BallPoly`), F being raised until S is known to the relative precision asked for.  S' and S''
//!   are not small near a root: they are computed with fewer bits (version 0.5.0).
//! * The step is N / (1 + w): N = S/S' is the first term of the rectangle step, w what the three-mean
//!   support and the other points add to it; w has the size of the error of the point.  By default N is a
//!   multiprecision quotient and the correction N w / (1 + w), of the size of the square of the error, is
//!   computed in double precision (`step`): the number of correct digits doubles at each sweep.  With
//!   `Options::full_order` the whole step is computed in multiprecision (`step_mp`): the number of correct
//!   digits is multiplied by the order of the sweep, six with the default support, at the price of m^2
//!   multiprecision divisions per sweep.
//! * Only the points whose disc is not yet good enough are evaluated and moved.
use crate::complex::{C, ONE, ZERO};
use crate::exact::{dyadic, exact_horner, exact_val, fl2, Certified, GPoly, Val};
use crate::float::{abs_scaled, coeffs3, frexp, ldexp, three, Announce, Ev, Options, Support, SLACK, SMALL, U};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{Signed, ToPrimitive, Zero};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

/// The dyadic complex number (re + i im) 2^e.
#[derive(Clone, Debug)]
pub struct ZP {
    pub re: BigInt,
    pub im: BigInt,
    pub e: i64,
}

impl ZP {
    /// A double precision point, exactly.
    pub fn from_c(z: C) -> ZP {
        let (nx, dx) = dyadic(z.re);
        let (ny, dy) = dyadic(z.im);
        let s = dx.max(dy);
        ZP { re: nx << (s - dx), im: ny << (s - dy), e: -(s as i64) }
    }
    /// Rounded to double precision (relative error below 2^-50 on each coordinate; infinite if too large).
    pub fn to_c(&self) -> C {
        let one = BigInt::from(1);
        let (fr, er) = fl2(&self.re, &one);
        let (fi, ei) = fl2(&self.im, &one);
        C::new(ldexp(fr, er + self.e), ldexp(fi, ei + self.e))
    }
    /// self - other, exactly.
    pub fn sub(&self, o: &ZP) -> ZP {
        let e = self.e.min(o.e);
        let (a, b) = ((self.e - e) as u64, (o.e - e) as u64);
        ZP { re: (&self.re << a) - (&o.re << b), im: (&self.im << a) - (&o.im << b), e }
    }
    /// self * other, exactly.
    pub fn mul(&self, o: &ZP) -> ZP {
        ZP { re: &self.re * &o.re - &self.im * &o.im, im: &self.re * &o.im + &self.im * &o.re, e: self.e + o.e }
    }
    pub fn conj(&self) -> ZP {
        ZP { re: self.re.clone(), im: -&self.im, e: self.e }
    }
    pub fn is_zero(&self) -> bool {
        self.re.is_zero() && self.im.is_zero()
    }
    /// Is this exactly the double precision point z?
    pub fn is_exactly(&self, z: C) -> bool {
        z.is_finite() && self.sub(&ZP::from_c(z)).is_zero()
    }
    /// Rounded to `bits` bits of its larger coordinate.
    pub fn round(mut self, bits: u64) -> ZP {
        let have = self.re.bits().max(self.im.bits());
        if have > bits {
            let d = have - bits;
            let half = BigInt::from(1) << (d - 1);
            self.re = (&self.re + &half) >> d;
            self.im = (&self.im + &half) >> d;
            self.e += d as i64;
        }
        self
    }
    /// Decimal strings of the two coordinates, with `digits` significant digits.
    pub fn decimal(&self, digits: usize) -> (String, String) {
        (decimal(&self.re, self.e, digits), decimal(&self.im, self.e, digits))
    }
}

/// n 2^e in scientific notation with about `digits` significant digits (rounded to nearest).
pub fn decimal(n: &BigInt, e: i64, digits: usize) -> String {
    decimal_checked(n, e, digits).0
}

/// The same, with a flag telling that the decimal string is exactly the number.
pub fn decimal_checked(n: &BigInt, e: i64, digits: usize) -> (String, bool) {
    if n.is_zero() {
        return ("0".to_string(), true);
    }
    let a = n.abs();
    let l10 = ((a.bits() as i64 + e) as f64 * std::f64::consts::LOG10_2).floor() as i64;
    let k = digits as i64 - 1 - l10;
    let ten = BigInt::from(10);
    let (mut num, mut den) = if k >= 0 { (&a * ten.pow(k as u32), BigInt::from(1)) } else { (a.clone(), ten.pow((-k) as u32)) };
    if e >= 0 {
        num <<= e as u64;
    } else {
        den <<= (-e) as u64;
    }
    let mut q: BigInt = (&num * 2 + &den) / (&den * 2);
    let mut k = k;
    if (q.to_string().len() as i64) < digits as i64 {
        // the estimate of the decimal exponent (from the number of bits) was one too high: one more digit
        num *= &ten;
        k += 1;
        q = (&num * 2 + &den) / (&den * 2);
    }
    let exact = (&num % &den).is_zero();
    let s = q.to_string();
    let exp = s.len() as i64 - 1 - k;
    (format!("{}{}.{}e{}", if n.is_negative() { "-" } else { "" }, &s[..1], &s[1..], exp), exact)
}

/// A radius f 2^e (it may be far below the smallest double).
#[derive(Clone, Copy, Debug)]
pub struct Radius {
    pub f: f64,
    pub e: i64,
}
impl Radius {
    /// As a double, rounded upwards when it is not representable.
    pub fn to_f64(&self) -> f64 {
        let r = ldexp(self.f, self.e);
        if self.f > 0.0 && r < 1e-290 { r + 64.0 * 5e-324 } else { r }
    }
    pub fn is_finite(&self) -> bool {
        self.f.is_finite()
    }
    pub fn decimal(&self) -> String {
        if !self.f.is_finite() {
            return "inf".to_string();
        }
        let (n, d) = dyadic(self.f * (1.0 + SLACK / 4.0)); // printed with eight digits: rounded upwards
        decimal(&n, self.e - d as i64, 8)
    }
}

/// Fixed-point evaluation of S, S', S'' with a rigorous error bound ("ball" evaluation).
///
/// The coefficients are divided by 2^E (E: the largest bit length) and rounded to F fractional bits; the
/// point x (z itself if |z| <= 1, 1/z and the reversed polynomial otherwise) is in the unit disc, so Horner's
/// rule does not amplify the errors: with every product rounded downwards to F bits, the computed value P
/// (in units of 2^-F) satisfies |P - S(x) 2^F / 2^E| <= A, A = (m+1)(2.25 + 1.5 sum |c_j| / 2^E) 1.01 + 1.
pub struct BallPoly<'a> {
    ci: &'a GPoly,
    e: u64,
    sa: f64,
    /// |c_0| / 2^E >= lead.0 2^lead.1
    lead: (f64, i64),
    /// indices of the non-zero coefficients; few of them: the polynomial is evaluated term by term
    nz: Vec<usize>,
    sparse: bool,
    /// beta = S S''/S'^2 is wanted in multiprecision (only `Options::full_order` uses it)
    beta: bool,
    cache: RefCell<HashMap<u64, Rc<Vec<(BigInt, BigInt)>>>>,
}

pub struct Ball {
    pub val: Val,
    /// the value is known to the relative precision asked for (|P| >= 2^rel A)
    pub good: bool,
    /// N = S/S' and beta = S S''/S'^2 as multiprecision numbers: what the step is made of (None if S'
    /// vanishes at this precision)
    pub parts: Option<(ZP, ZP)>,
    /// bits that S' lacks to be known to the relative precision asked for (S' and S'' are computed with
    /// `cut` bits fewer than S: 0 if that was enough)
    pub lack1: u64,
    /// the value cannot be told from zero at this precision (|P| <= A)
    pub tiny: bool,
    /// bits to add to F for the value to be known to that precision (0 if unknown)
    pub more: u64,
    /// bits that F had in excess of that precision
    pub spare: u64,
}

fn mant(re: &BigInt, im: &BigInt) -> (C, i64) {
    let sh = re.bits().max(im.bits()).saturating_sub(62);
    (C::new((re >> sh).to_f64().unwrap_or(0.0), (im >> sh).to_f64().unwrap_or(0.0)), sh as i64)
}

/// (f 2^e)^n as (mantissa, exponent), rounded upwards.
fn pow_fe(f: f64, e: i64, n: usize) -> (f64, i64) {
    let (mut rf, mut re, mut bf, mut be, mut k) = (1.0f64, 0i64, f, e, n);
    while k > 0 {
        if k & 1 == 1 {
            let (g, x) = frexp(rf * bf);
            rf = g;
            re += be + x;
        }
        let (g, x) = frexp(bf * bf);
        bf = g;
        be = 2 * be + x;
        k >>= 1;
    }
    (rf * (1.0 + (n as f64 + 64.0) * 4.0 * U), re)
}

impl<'a> BallPoly<'a> {
    pub fn new(ci: &'a GPoly, beta: bool) -> BallPoly<'a> {
        let e = ci.iter().map(|(a, b)| a.bits().max(b.bits())).max().unwrap_or(1).max(1);
        let one = BigInt::from(1);
        let modulus = |c: &(BigInt, BigInt)| {
            let (fr, er) = fl2(&c.0, &one);
            let (fi, ei) = fl2(&c.1, &one);
            abs_scaled(ldexp(fr, er - e as i64), ldexp(fi, ei - e as i64)) // coefficients / 2^E: moduli below 1.5
        };
        let sa = ci.iter().map(|c| { let (f, x) = modulus(c); ldexp(f, x) }).sum::<f64>() * (1.0 + 1e-9);
        let (f0, e0) = modulus(&ci[0]);
        let nz: Vec<usize> = (0..ci.len()).filter(|&j| !(ci[j].0.is_zero() && ci[j].1.is_zero())).collect();
        let sparse = nz.len() * 48 < ci.len();
        BallPoly { ci, e, sa, lead: (f0 * (1.0 - 1e-9), e0), nz, sparse, beta, cache: RefCell::new(HashMap::new()) }
    }
    fn coeffs(&self, f: u64) -> Rc<Vec<(BigInt, BigInt)>> {
        if let Some(c) = self.cache.borrow().get(&f) {
            return c.clone();
        }
        let sh = |x: &BigInt| -> BigInt {
            if f >= self.e { x << (f - self.e) } else { (x + (BigInt::from(1) << (self.e - f - 1))) >> (self.e - f) }
        };
        let c: Rc<Vec<(BigInt, BigInt)>> = Rc::new(self.ci.iter().map(|(a, b)| (sh(a), sh(b))).collect());
        let mut cache = self.cache.borrow_mut();
        if cache.len() > 6 {
            cache.clear();
        }
        cache.insert(f, c.clone());
        c
    }
    /// Bound of |S(z)| / |c_0| (as `Val::q`, a real mantissa, and `Val::ex`) and S'/S, S''/S, from an
    /// evaluation with `f` fractional bits.
    ///
    /// S is small at a point near a root and must be known to `rel` bits of its own size: that is what F
    /// is for.  S' and S'' are not small, and the same relative precision needs fewer bits: they are
    /// computed with F - `cut` bits (`cut` about the number of correct bits of the point).  The bound of S,
    /// the only number the certificate uses, does not depend on them.
    pub fn eval(&self, z: &ZP, f: u64, rel: u64, cut: u64) -> Ball {
        let m = self.ci.len() - 1;
        let mf = m as f64;
        let zc = z.to_c();
        let inside = !(zc.abs() > 1.0);
        let fi = f as i64;
        // the point in fixed point: z, or 1/z = conj(n) 2^-e / |n|^2 rounded downwards
        let shift = |x: &BigInt, k: i64| -> BigInt { if k >= 0 { x << k as u64 } else { x >> (-k) as u64 } };
        let (xr, xi) = if inside {
            (shift(&z.re, z.e + fi), shift(&z.im, z.e + fi))
        } else {
            let d: BigInt = &z.re * &z.re + &z.im * &z.im;
            (shift(&z.re, fi - z.e).div_floor(&d), shift(&(-&z.im), fi - z.e).div_floor(&d))
        };
        let c = self.coeffs(f);
        let zero = || (BigInt::from(0), BigInt::from(0));
        let (mut p0, mut p1, mut p2) = (zero(), zero(), zero());
        let mul = |p: &(BigInt, BigInt)| -> (BigInt, BigInt) { ((&p.0 * &xr - &p.1 * &xi) >> f, (&p.0 * &xi + &p.1 * &xr) >> f) };
        let mut a_err = (mf + 1.0) * (2.25 + 1.5 * self.sa) * 1.01 + 1.0;
        // S' and S'' in units of 2^-(F - c12)
        let c12 = if self.sparse { 0 } else { cut.min(f.saturating_sub(64)) };
        let f12 = f - c12;
        let (xr12, xi12): (BigInt, BigInt) = (&xr >> c12, &xi >> c12);
        let mul12 = |p: &(BigInt, BigInt)| -> (BigInt, BigInt) { ((&p.0 * &xr12 - &p.1 * &xi12) >> f12, (&p.0 * &xi12 + &p.1 * &xr12) >> f12) };
        if !self.sparse {
            for j in 0..=m {
                let cj = if inside { &c[j] } else { &c[m - j] };
                let (a2, a1, a0) = (mul12(&p2), mul12(&p1), mul(&p0));
                p2 = (a2.0 + &p1.0, a2.1 + &p1.1);
                p1 = if c12 == 0 { (a1.0 + &p0.0, a1.1 + &p0.1) } else { (a1.0 + (&p0.0 >> c12), a1.1 + (&p0.1 >> c12)) };
                p0 = (a0.0 + &cj.0, a0.1 + &cj.1);
            }
        } else {
            // few terms: c x^e for each of them, the powers by repeated squaring.  The computed x^k is within
            // 2.84 k units of the true one (induction on the products), so a term is within 6 (e + 1) + 2.2.
            let unit = (BigInt::from(1) << f, BigInt::from(0));
            let times = |p: &(BigInt, BigInt), q: &(BigInt, BigInt)| -> (BigInt, BigInt) { ((&p.0 * &q.0 - &p.1 * &q.1) >> f, (&p.0 * &q.1 + &p.1 * &q.0) >> f) };
            let x = (xr.clone(), xi.clone());
            let power = |mut e: usize| {
                let (mut r, mut b) = (unit.clone(), x.clone());
                while e > 0 {
                    if e & 1 == 1 {
                        r = times(&r, &b);
                    }
                    e >>= 1;
                    if e > 0 {
                        b = times(&b, &b);
                    }
                }
                r
            };
            a_err = 1.0;
            for &j in &self.nz {
                let e = if inside { m - j } else { j };
                a_err += (6.0 * (e as f64 + 1.0) + 2.2) * 1.01;
                let (w2, w1, w0) = if e >= 2 {
                    let w2 = power(e - 2);
                    let w1 = times(&w2, &x);
                    let w0 = times(&w1, &x);
                    (Some(w2), Some(w1), w0)
                } else if e == 1 {
                    (None, Some(unit.clone()), x.clone())
                } else {
                    (None, None, unit.clone())
                };
                let t = times(&c[j], &w0);
                p0 = (p0.0 + t.0, p0.1 + t.1);
                if let Some(w1) = w1 {
                    let t = times(&c[j], &w1);
                    p1 = (p1.0 + t.0 * e, p1.1 + t.1 * e);
                }
                if let Some(w2) = w2 {
                    let t = times(&c[j], &w2);
                    let k = BigInt::from(e) * (e - 1) / 2;
                    p2 = (p2.0 + t.0 * &k, p2.1 + t.1 * &k);
                }
            }
        }
        // |P| + A as (mantissa, exponent), in units of 2^-F
        let one = BigInt::from(1);
        let (fr, er) = fl2(&p0.0, &one);
        let (fim, eim) = fl2(&p0.1, &one);
        let big = er.max(eim);
        let (hf, he) = if p0.0.is_zero() && p0.1.is_zero() { (0.0, 0) } else { frexp(ldexp(fr, er - big).hypot(ldexp(fim, eim - big)) * (1.0 + 1e-12)) };
        let he = he + if hf == 0.0 { 0 } else { big };
        // good: log2 |P| >= log2 A + rel
        let lack = if hf == 0.0 { f64::INFINITY } else { a_err.log2() + rel as f64 - (hf.log2() + he as f64) };
        let (good, more) = (lack <= 0.0, if lack.is_finite() && lack > 0.0 { lack.ceil() as u64 + 8 } else { 0 });
        let spare = if lack.is_finite() && lack < 0.0 { (-lack).floor() as u64 } else { 0 };
        let (tiny, tf, te) = if hf != 0.0 && he > 200 {
            (false, hf * (1.0 + 1e-12), he)
        } else {
            let pa = ldexp(hf, he);
            let (g, x) = frexp(pa + a_err);
            (pa <= a_err, g * (1.0 + 4.0 * U), x)
        };
        // N = S/S' and beta = S S''/S'^2.  Inside the unit disc N = P0/P1 and beta = 2 P0 P2 / P1^2; outside,
        // with w = 1/z and the reversed polynomial, N = z P0 / D and beta = P0 B / D^2, D = m P0 - w P1,
        // B = m (m-1) P0 - 2 (m-1) w P1 + 2 w^2 P2.  P0 is in units of 2^-F, the others of 2^-(F - c12).
        let (den, num2) = if inside {
            (p1.clone(), (&p2.0 * 2, &p2.1 * 2))
        } else {
            let t1 = mul12(&p1);
            let t2 = mul12(&mul12(&p2));
            let q0: (BigInt, BigInt) = (&p0.0 >> c12, &p0.1 >> c12);
            let mm = BigInt::from(m) * (m - 1);
            ((&q0.0 * m - &t1.0, &q0.1 * m - &t1.1), (&q0.0 * &mm - &t1.0 * (2 * (m - 1)) + &t2.0 * 2, &q0.1 * &mm - &t1.1 * (2 * (m - 1)) + &t2.1 * 2))
        };
        let dn: BigInt = &den.0 * &den.0 + &den.1 * &den.1;
        // S' (or D) known to `rel` bits: its modulus against (m + 1) A units
        let have = den.0.bits().max(den.1.bits()) as f64 - 1.0;
        let need = ((mf + 1.0) * a_err).log2() + rel as f64;
        let lack1 = if c12 > 0 && have < need { ((need - have).ceil() as u64 + 8).min(c12) } else { 0 };
        let parts = if dn.is_zero() {
            None
        } else {
            let quo = |n: &(BigInt, BigInt)| -> (BigInt, BigInt) { (((&n.0 * &den.0 + &n.1 * &den.1) << f12).div_floor(&dn), ((&n.1 * &den.0 - &n.0 * &den.1) << f12).div_floor(&dn)) };
            let (qr, qi) = quo(&p0); // (P0 / den) 2^f12, a number of size N 2^F
            let q = ZP { re: qr.clone(), im: qi.clone(), e: -fi };
            let beta = if self.beta {
                let r = quo(&num2); // (num2 / den) 2^f12
                ZP { re: (&qr * &r.0 - &qi * &r.1) >> f12, im: (&qr * &r.1 + &qi * &r.0) >> f12, e: -fi }
            } else {
                ZP { re: BigInt::zero(), im: BigInt::zero(), e: 0 }
            };
            Some((if inside { q } else { z.mul(&q) }, beta))
        };
        // divided by the leading coefficient, times |z|^m outside the unit disc
        let (mut qf, mut qe) = (tf / self.lead.0 * (1.0 + 4.0 * U), te - fi - self.lead.1);
        let (r1, r2) = {
            let (c0, s0) = mant(&p0.0, &p0.1);
            let (c1, s1) = mant(&p1.0, &p1.1);
            let (c2, s2) = mant(&p2.0, &p2.1);
            let up = |c: C, k: i64| C::new(ldexp(c.re, k), ldexp(c.im, k));
            (up(c1 / c0, s1 - s0 + c12 as i64), up((c2 / c0).scale(2.0), s2 - s0 + c12 as i64))
        };
        let (a, b) = if inside {
            (r1, r2)
        } else {
            let (zf, ze) = abs_scaled(zc.re, zc.im);
            let (pf, pe) = pow_fe(zf * (1.0 + 8.0 * U), ze, m);
            let (g, x) = frexp(qf * pf);
            qf = g * (1.0 + 4.0 * U);
            qe += pe + x;
            // S(z) = z^m R(w), w = 1/z
            let w = zc.inv();
            let w2 = w * w;
            (w * (C::new(mf, 0.0) - w * r1), w2.scale(mf * (mf - 1.0)) - (w2 * w * r1).scale(2.0 * (mf - 1.0)) + w2 * w2 * r2)
        };
        Ball { val: Val { q: C::new(qf, 0.0), ex: qe, a, b, exact: true }, good, tiny, more, spare, parts, lack1 }
    }
}

/// The value at z with enough bits: F is raised from `f0` until the value is known to the relative precision
/// 2^-rel or F reaches `fcap`; S' and S'' are computed with `cut` bits fewer, less if that turns out to be
/// too few.  A value that cannot be told from zero with many more bits than the point has (`pbits`) is
/// computed exactly: an exact root gets the radius zero.  Returns the value, the last F (0: exact) and the
/// parts of the step, N = S/S' and beta = S S''/S'^2, the `cut` that was enough and the F that would have been enough (0: unknown).
pub fn ball_auto(bp: &BallPoly, z: &ZP, f0: u64, fcap: u64, pbits: u64, rel: u64, cut: u64) -> (Val, u64, Option<(ZP, ZP)>, u64, u64) {
    let (mut f, mut cut) = (f0, cut);
    loop {
        let ball = bp.eval(z, f, rel, cut);
        if ball.good {
            if ball.lack1 > 0 {
                cut = cut.min(f.saturating_sub(64)) - ball.lack1;
                continue;
            }
            return (ball.val, f, ball.parts, cut, f - ball.spare.min(f));
        }
        if ball.tiny && f >= 2 * pbits + 128 {
            let (x, y, s) = if z.e <= 0 { (z.re.clone(), z.im.clone(), (-z.e) as u64) } else { (&z.re << z.e as u64, &z.im << z.e as u64, 0) };
            let h = exact_horner(bp.ci, &x, &y, s);
            let mut v = exact_val(bp.ci, &h, s);
            v.exact = true;
            let parts = if v.q.re == 0.0 && v.q.im == 0.0 { None } else { exact_parts(&h, s, rel + 64) };
            return (v, 0, parts, cut, 0);
        }
        if f >= fcap {
            return (ball.val, f, ball.parts, cut, 0);
        }
        // straight to the number of bits that the value just computed calls for
        f = if ball.more > 0 { (f + ball.more).min(fcap) } else { (2 * f).min(fcap) };
    }
}

/// N = S/S' and beta = S S''/S'^2 from the exact values, rounded to `g` bits of their own size.
fn exact_parts(h: &((BigInt, BigInt), (BigInt, BigInt), (BigInt, BigInt), u64), s: u64, g: u64) -> Option<(ZP, ZP)> {
    let (p, a, b) = (&h.0, &h.1, &h.2);
    let dn: BigInt = &a.0 * &a.0 + &a.1 * &a.1;
    if dn.is_zero() {
        return None;
    }
    let a2: (BigInt, BigInt) = (&a.0 * &a.0 - &a.1 * &a.1, &a.0 * &a.1 * 2);
    let d2: BigInt = &a2.0 * &a2.0 + &a2.1 * &a2.1;
    let pb: (BigInt, BigInt) = ((&p.0 * &b.0 - &p.1 * &b.1) * 2, (&p.0 * &b.1 + &p.1 * &b.0) * 2);
    let ratio = |n: &(BigInt, BigInt), d: &(BigInt, BigInt), dd: &BigInt, e: i64| -> ZP {
        let k = g + d.0.bits().max(d.1.bits()).saturating_sub(n.0.bits().max(n.1.bits())) + 2;
        ZP { re: ((&n.0 * &d.0 + &n.1 * &d.1) << k).div_floor(dd), im: ((&n.1 * &d.0 - &n.0 * &d.1) << k).div_floor(dd), e: e - k as i64 }
    };
    // S = p / 2^sh, S' = a / 2^(sh - s), S''/2 = b / 2^(sh - 2s)
    Some((ratio(&p, &a, &dn, -(s as i64)), ratio(&pb, &a2, &d2, 0)))
}

/// The differences between two points of the multiprecision stage are computed from their double precision
/// roundings when |z_k - z_l| >= FAR (|z_k| + |z_l|): their relative error is then below DREL = 2^-28, and the
/// certificate is computed with that margin.  Closer points are subtracted exactly.
const FAR: f64 = 1.0 / 1048576.0;
pub const DREL: f64 = 1.0 / 268435456.0;

pub struct Refined {
    pub z: Vec<ZP>,
    /// the points rounded to doubles, and whether they are exactly these doubles
    pub zc: Vec<C>,
    pub isd: Vec<bool>,
    /// Smith radii m w_k, fixed-point radii 2 w_k and the flags of the fixed-point certificate
    pub r: Vec<f64>,
    pub rho: Vec<f64>,
    pub one: Vec<bool>,
    /// |z_k - z_l| (row k, column l)
    pub dist: Vec<f64>,
    pub sweeps: usize,
    pub bits: u64,
}

/// Radius of the real disc that contains D(z, rad), for a point z whose imaginary part is im (rounded).
pub fn real_radius(rad: f64, im: f64) -> f64 {
    if rad == 0.0 && im == 0.0 {
        return 0.0; // an exact real root
    }
    (rad + im.abs()) * (1.0 + 16.0 * U) + 8.0 * 5e-324
}

/// The real-root test (see float::mirror): the disc centred at Re z_k with radius rad + |Im z_k| meets no
/// disc D(z_j, cover_j), j != k.  Distances between two double precision points are computed in doubles,
/// the others exactly and then rounded.
pub fn mirror(z: &[ZP], zc: &[C], isd: &[bool], cover: &[f64], k: usize, rad: f64) -> bool {
    let big = real_radius(rad, zc[k].im);
    let x = ZP { re: z[k].re.clone(), im: BigInt::from(0), e: z[k].e };
    (0..z.len()).all(|j| {
        if j == k {
            return true;
        }
        let d = if isd[k] && isd[j] { C::new(zc[k].re - zc[j].re, -zc[j].im) } else { x.sub(&z[j]).to_c() };
        let (f, e) = abs_scaled(d.re, d.im);
        let dist = ldexp(f, e);
        dist >= SMALL && dist * (1.0 - 16.0 * U) > (big + cover[j]) * (1.0 + SLACK)
    })
}

/// The certificate from the bounds `vals` and the differences d (row k, column l): Smith radii, fixed-point
/// radii and flags.
fn certificate(m: usize, vals: &[Val], d: &[C], dist: &[f64]) -> (Vec<f64>, Vec<f64>, Vec<bool>) {
    let mf = m as f64;
    let mut r = vec![0.0; m];
    for k in 0..m {
        let v = &vals[k];
        if v.q.re == 0.0 && v.q.im == 0.0 {
            continue;
        }
        let (mut pf, mut pe) = (1.0f64, 0i64);
        for l in 0..m {
            if l != k {
                let (fa, ea) = abs_scaled(d[k * m + l].re, d[k * m + l].im);
                pf *= fa;
                pe += ea;
                if pf == 0.0 || !pf.is_finite() {
                    break;
                }
                if l & 7 == 7 {
                    let (g, eg) = frexp(pf);
                    pf = g;
                    pe += eg;
                }
            }
        }
        if pf == 0.0 || !pf.is_finite() || !v.q.is_finite() {
            r[k] = f64::INFINITY;
            continue;
        }
        let rk = mf * ldexp(v.q.abs() / pf, v.ex - pe) * (1.0 + (mf + 8.0) * 2.0 * DREL);
        let rk = if rk < 1e-290 { rk + 64.0 * 5e-324 } else { rk };
        r[k] = if rk.is_nan() { f64::INFINITY } else { rk };
    }
    if m == 1 {
        return (r.clone(), r.clone(), vec![r[0].is_finite()]);
    }
    let up = 1.0 + (2.0 * mf + 16.0) * U;
    let mut rho = vec![0.0; m];
    let mut one = vec![false; m];
    for k in 0..m {
        // the test is made with inflated bounds (see float::SLACK); the radius returned is 2 w_k
        let wk = r[k] / mf * (1.0 + SLACK);
        rho[k] = 2.0 * r[k] / mf;
        if !r[k].is_finite() {
            continue;
        }
        let rk = 2.0 * wk;
        let (mut sigma, mut tau, mut closed) = (0.0f64, 0.0f64, false);
        for l in 0..m {
            if l != k {
                let dd = dist[k * m + l];
                let g = dd * (1.0 - 2.0 * DREL) - rk;
                closed |= !(g > 0.0) || dd < SMALL;
                let t = r[l] / mf * (1.0 + SLACK) / g;
                sigma += t;
                tau += t / g;
            }
        }
        one[k] = !closed && sigma * up + 1e-300 < 0.5 && wk * tau * up + 1e-300 < 0.25;
    }
    (r, rho, one)
}


/// One sweep (all the points at once) with the correction in double precision; the differences are those of `d`.  For each point the step is
/// N / (1 + w) with N = S/S' (the Newton correction) and w the effect of the neighbours and of the support:
/// with u = s1 N, v = s2 N^2, beta = S S''/S'^2,
///     (1 - u)^2 (t - 1) = m (2u - u^2 - beta - v) / (m - 1),   kappa = (m - 1)(q(t) - 1) / m,
///     w = kappa - u - u kappa,
/// all small numbers computed without cancellation.  Returns (N, w) in double precision; the caller takes N
/// in multiprecision when it has it, so that only the small correction N w / (1 + w) is rounded to doubles.
fn step(d: &[C], ev: &[Ev], cf: &[f64; 4], opt: &Options, out: &mut [(C, C)]) {
    let m = ev.len();
    let mf = m as f64;
    let h: Vec<C> = (0..m)
        .map(|l| {
            if opt.announce == Announce::None || ev[l].done {
                return ZERO;
            }
            let ia = ev[l].a.inv();
            let h = if opt.announce == Announce::AK {
                ia
            } else {
                let t = ONE - (ev[l].b * ia * ia).scale(mf / (mf - 1.0));
                (ia * (ONE + three(t, cf).scale(mf - 1.0)).inv()).scale(mf)
            };
            if h.is_finite() { h } else { ZERO }
        })
        .collect();
    for k in 0..m {
        if ev[k].done {
            out[k] = (ZERO, ZERO);
            continue;
        }
        let (mut s1, mut s2) = (ZERO, ZERO);
        for l in 0..m {
            if l != k {
                let w = (d[k * m + l] + h[l]).inv();
                s1 = s1 + w;
                s2 = s2 + w * w;
            }
        }
        let n = ev[k].a.inv();
        let u = s1 * n;
        let w = match opt.outer {
            Support::AK => ZERO - u,
            Support::Three => {
                let beta = ev[k].b * n * n;
                let v = s2 * n * n;
                let om = ONE - u;
                let tau = ((u.scale(2.0) - u * u - beta - v) * (om * om).inv()).scale(mf / (mf - 1.0));
                // q(1 + tau) - 1: near 1 the series tau/2 + q2 tau^2, q2 = -(m+1)/(12m), elsewhere the support
                let qm1 = if tau.abs() < 1e-6 { tau.scale(0.5) + (tau * tau).scale(-(mf + 1.0) / (12.0 * mf)) } else { three(ONE + tau, cf) - ONE };
                let kappa = qm1.scale((mf - 1.0) / mf);
                kappa - u - u * kappa
            }
        };
        out[k] = (n, w);
    }
}

/// Complex numbers in fixed point: (re, im) in units of 2^-g.
type Fx = (BigInt, BigInt);

fn fx_from(z: &ZP, g: u64) -> Fx {
    let k = z.e + g as i64;
    if k >= 0 { (&z.re << k as u64, &z.im << k as u64) } else { (&z.re >> (-k) as u64, &z.im >> (-k) as u64) }
}
fn fx_mul(a: &Fx, b: &Fx, g: u64) -> Fx {
    ((&a.0 * &b.0 - &a.1 * &b.1) >> g, (&a.0 * &b.1 + &a.1 * &b.0) >> g)
}
fn fx_inv(a: &Fx, g: u64) -> Option<Fx> {
    let n: BigInt = &a.0 * &a.0 + &a.1 * &a.1;
    if n.is_zero() {
        return None;
    }
    Some(((&a.0 << (2 * g)).div_floor(&n), (-(&a.1 << (2 * g))).div_floor(&n)))
}
/// a times the fraction r.0 / r.1.
fn fx_rat(a: &Fx, r: &(BigInt, BigInt)) -> Fx {
    ((&a.0 * &r.0).div_floor(&r.1), (&a.1 * &r.0).div_floor(&r.1))
}
/// The principal square root.
fn fx_sqrt(a: &Fx, g: u64) -> Fx {
    let (x, y): (BigInt, BigInt) = (&a.0 << g, &a.1 << g);
    if x.is_zero() && y.is_zero() {
        return (BigInt::zero(), BigInt::zero());
    }
    let r: BigInt = (&x * &x + &y * &y).sqrt();
    if !x.is_negative() {
        let s: BigInt = ((&r + &x) >> 1u32).sqrt();
        if s.is_zero() {
            return (s, BigInt::zero());
        }
        let t = y.div_floor(&(&s * 2));
        (s, t)
    } else {
        let t: BigInt = ((&r - &x) >> 1u32).sqrt();
        if t.is_zero() {
            return (BigInt::zero(), t);
        }
        let s = y.abs().div_floor(&(&t * 2));
        (s, if y.is_negative() { -t } else { t })
    }
}
/// 1/d in units of 2^-g, within one unit: d is first cut to the bits that this needs.
fn recip(d: &ZP, g: u64) -> Option<Fx> {
    let nb = d.re.bits().max(d.im.bits()) as i64;
    if nb == 0 {
        return None;
    }
    let keep = (g as i64 - (nb + d.e) + 8).max(16);
    let cut = (nb - keep).max(0);
    let (a, b): (BigInt, BigInt) = (&d.re >> cut as u64, &d.im >> cut as u64);
    let n: BigInt = &a * &a + &b * &b;
    let sh = g as i64 - (d.e + cut);
    let (x, y): (BigInt, BigInt) = if sh >= 0 { (a << sh as u64, (-b) << sh as u64) } else { (a >> (-sh) as u64, (-b) >> (-sh) as u64) };
    Some((x.div_floor(&n), y.div_floor(&n)))
}

/// The coefficients of the three-mean support of degree p (`float::coeffs3`), as exact fractions.
fn coeffs3_exact(p: usize) -> [(BigInt, BigInt); 4] {
    let p = BigInt::from(p);
    let p2: BigInt = &p * &p;
    let a: BigInt = &p2 * 4 - 1;
    let b: BigInt = &p2 * 5 + 4;
    [
        ((&p - 2) * (&p2 * 47 + &p * 21 + 4), &p * 60 * &a),
        ((&p + 1) * 16 * &a, &p * 15 * &b),
        (&p * 49 * (&p + 1) * (&p2 - 4), &a * 10 * &b),
        (b.clone(), &p2 * 84),
    ]
}

/// The three-mean support q(t) = c0 (1 + t) + c1 sqrt(t) - c2 sqrt(t + c3 (t - 1)^2) (`float::three`), in
/// fixed point with g bits.
fn three_fx(t: &Fx, g: u64, cf: &[(BigInt, BigInt); 4]) -> Fx {
    let one = BigInt::from(1) << g;
    let s = fx_sqrt(t, g);
    let t1: Fx = (&t.0 - &one, t.1.clone());
    let q = fx_rat(&fx_mul(&t1, &t1, g), &cf[3]);
    let r = fx_sqrt(&(&t.0 + q.0, &t.1 + q.1), g);
    let a = fx_rat(&(&t.0 + &one, t.1.clone()), &cf[0]);
    let b = fx_rat(&s, &cf[1]);
    let c = fx_rat(&r, &cf[2]);
    (a.0 + b.0 - c.0, a.1 + b.1 - c.1)
}

/// q(1 + tau) - 1 in fixed point with g bits.  For a small tau the two terms tau/2 - (m + 1) tau^2 / (12 m) of
/// its series (the third one is below the last bit when |tau|^3 < 2^-(g + 8)), the support itself otherwise.
fn q1_fx(tau: &Fx, g: u64, m: usize, cf: &[(BigInt, BigInt); 4]) -> Fx {
    let small = g.saturating_sub(tau.0.bits().max(tau.1.bits())); // |tau| < 2^-small
    if 3 * small >= g + 8 {
        let t2 = fx_rat(&fx_mul(tau, tau, g), &(BigInt::from(m + 1), BigInt::from(12 * m)));
        return ((&tau.0 >> 1u32) - t2.0, (&tau.1 >> 1u32) - t2.1);
    }
    let one = BigInt::from(1) << g;
    let q = three_fx(&(&one + &tau.0, tau.1.clone()), g, cf);
    (q.0 - one, q.1)
}

/// One sweep (all the points at once), entirely in multiprecision: the same step as in double precision
/// (`float`), the rectangle with the three-mean support used twice.
///
/// First every point announces where it is going by itself: z_l - h_l, h_l = m N_l / (1 + (m - 1) q(t_l)),
/// t_l = 1 - m beta_l / (m - 1), with N = S/S' and beta = S S''/S'^2.  Then, with the sums s1, s2 of the
/// powers of 1 / (z_k - announced position of l), u = s1 N, v = s2 N^2,
///     (1 - u)^2 (t - 1) = m (2u - u^2 - beta - v) / (m - 1),   kappa = (m - 1)(q(t) - 1) / m,
///     w = kappa - u - u kappa,   z_k <- z_k - N / (1 + w).
/// N and beta come from the ball evaluation with `relk` bits of their own size; everything here is computed
/// with g = relk + 24 bits after the point (the sums with as many as their product by N needs), which is
/// what the new point can use.  None: the point does not move (certified already, or no step exists).
fn step_mp(z: &[ZP], parts: &[Option<(ZP, ZP)>], relk: &[u64], done: &[bool], cf: &[(BigInt, BigInt); 4], opt: &Options, bits: u64, d: &[C]) -> Vec<Option<ZP>> {
    let m = z.len();
    let (mb, m1) = (BigInt::from(m), BigInt::from(m - 1));
    let up = (mb.clone(), m1.clone());
    let down = (m1.clone(), mb.clone());
    let ann: Vec<ZP> = (0..m)
        .map(|l| {
            let (n, beta) = match &parts[l] {
                Some(p) if !done[l] && opt.announce != Announce::None => p,
                _ => return z[l].clone(),
            };
            let h = if opt.announce == Announce::AK {
                n.clone()
            } else {
                let g = relk[l] + 24;
                let one = BigInt::from(1) << g;
                let b = fx_rat(&fx_from(beta, g), &up);
                let q = q1_fx(&(-b.0, -b.1), g, m, cf);
                match fx_inv(&(&one + (&one + q.0) * &m1, q.1 * &m1), g) {
                    Some(i) => n.mul(&ZP { re: i.0 * &mb, im: i.1 * &mb, e: -(g as i64) }),
                    None => return z[l].clone(),
                }
            };
            z[l].sub(&h).round(bits + 64)
        })
        .collect();
    // the moves announced, in double precision, for the sums that need no more
    let hd: Vec<C> = (0..m).map(|l| z[l].sub(&ann[l]).to_c()).collect();
    (0..m)
        .map(|k| {
            if done[k] {
                return None;
            }
            let (n, beta) = parts[k].as_ref()?;
            let nb = n.re.bits().max(n.im.bits());
            if nb == 0 {
                return None;
            }
            let g = relk[k] + 24;
            // |N| < 2^-en.  The sums s1, s2 only appear multiplied by N and N^2.  A term r = 1 / (z_k - a_l) is
            // taken from the double precision difference of the certificate (known to 2^-28) when its product
            // by N is then known to the precision of the step, and computed in multiprecision otherwise.
            let en = -(nb as i64 + n.e);
            let gs = (g as i64 - en + 16).clamp(64, g as i64 + 64) as u64;
            let lim = 2.0 * (28.0 - 16.0 - relk[k] as f64 + en as f64);
            let lim = if lim > 1000.0 { f64::INFINITY } else if lim < -1000.0 { 0.0 } else { lim.exp2() };
            let (mut a1, mut a2) = (ZERO, ZERO);
            let (mut s1, mut s2): (Fx, Fx) = ((BigInt::zero(), BigInt::zero()), (BigInt::zero(), BigInt::zero()));
            for l in 0..m {
                if l != k {
                    let r = (d[k * m + l] + hd[l]).inv();
                    let r2 = r.re * r.re + r.im * r.im;
                    if r2.is_finite() && r2 <= lim {
                        a1 = a1 + r;
                        a2 = a2 + r * r;
                    } else {
                        let r = recip(&z[k].sub(&ann[l]), gs)?;
                        let r2 = fx_mul(&r, &r, gs);
                        s1 = (s1.0 + r.0, s1.1 + r.1);
                        s2 = (s2.0 + r2.0, s2.1 + r2.1);
                    }
                }
            }
            let plus = |s: Fx, a: C| -> ZP { ZP { re: s.0, im: s.1, e: -(gs as i64) }.sub(&ZP::from_c(ZERO - a)) };
            let (s1z, s2z) = (plus(s1, a1), plus(s2, a2));
            let one = BigInt::from(1) << g;
            let s1n = s1z.mul(n);
            let u = fx_from(&s1n, g);
            let w: Fx = match opt.outer {
                Support::AK => (-u.0, -u.1),
                Support::Three => {
                    let bf = fx_from(beta, g);
                    let v = fx_from(&s2z.mul(n).mul(n), g);
                    let om: Fx = (&one - &u.0, -&u.1);
                    let uu = fx_mul(&u, &u, g);
                    let num: Fx = (&u.0 * 2 - uu.0 - bf.0 - v.0, &u.1 * 2 - uu.1 - bf.1 - v.1);
                    let iom = fx_inv(&fx_mul(&om, &om, g), g)?;
                    let tau = fx_rat(&fx_mul(&num, &iom, g), &up);
                    let kappa = fx_rat(&q1_fx(&tau, g, m, cf), &down);
                    let uk = fx_mul(&u, &kappa, g);
                    (kappa.0 - &u.0 - uk.0, kappa.1 - &u.1 - uk.1)
                }
            };
            let gi = fx_inv(&(&one + w.0, w.1), g)?;
            let dz = n.mul(&ZP { re: gi.0, im: gi.1, e: -(g as i64) });
            Some(z[k].sub(&dz).round(bits))
        })
        .collect()
}

/// The root -c1/c0 of a polynomial of degree one, rounded to `bits` bits.
fn linear_root(ci: &GPoly, bits: u64) -> ZP {
    let ((a, b), (c, d)) = (&ci[0], &ci[1]);
    let den: BigInt = a * a + b * b;
    let (nr, ni): (BigInt, BigInt) = (-(c * a + d * b), -(d * a - c * b));
    let sh = bits + den.bits().saturating_sub(nr.bits().max(ni.bits())) + 2;
    let half = &den >> 1u32;
    ZP { re: ((nr << sh) + &half).div_floor(&den), im: ((ni << sh) + &half).div_floor(&den), e: -(sh as i64) }
}

/// Continue from the state of the double precision stage until every disc passes the fixed-point
/// certificate, is within the tolerance and (real coefficients) is decided.  Only the points whose disc is
/// not good enough are evaluated again and moved; the precision of the points is doubled when they no longer
/// move.  Returns the last state, whatever it is: its radii are certified.
pub fn refine(ci: &GPoly, cert: &Certified, opt: &Options, real: bool) -> Refined {
    const CAP: u64 = 4096;
    const FCAP: u64 = 32768;
    let m = cert.z.len();
    let tol = opt.tol.max(1e-280) / (1.0 + SLACK); // the radius that may be printed is within the tolerance
    let mut bits = ((-tol.log2()).ceil() as u64 + 40).max(128);
    let bp = BallPoly::new(ci, opt.full_order);
    let mut z: Vec<ZP> = cert.z.iter().map(|&x| ZP::from_c(x)).collect();
    let mut zc: Vec<C> = cert.z.clone();
    let mut isd = vec![true; m];
    let mut vals: Vec<Val> = cert.vals.clone();
    let mut sweeps = 0usize;
    if m == 1 {
        // degree one: the root is a quotient, rounded to as many bits as the tolerance asks for
        loop {
            z[0] = linear_root(ci, bits);
            zc[0] = z[0].to_c();
            isd[0] = z[0].is_exactly(zc[0]);
            vals[0] = ball_auto(&bp, &z[0], bits + 128, FCAP, bits, 40, 0).0;
            let (r, rho, one) = certificate(1, &vals, &[ZERO], &[0.0]);
            if r[0] <= tol * zc[0].abs() || bits >= CAP {
                return Refined { z, zc, isd, r, rho, one, dist: vec![0.0], sweeps, bits };
            }
            bits *= 2;
        }
    }
    let cf = coeffs3(m as f64);
    let cfx = coeffs3_exact(m);
    let mut dparts = vec![(ZERO, ZERO); m];
    // order of the sweep (3 to 6), used only to guess how many bits the next point will have
    let order = 3 + (opt.outer == Support::Three) as u64 + (opt.announce != Announce::None) as u64 + (opt.announce == Announce::Three && opt.outer == Support::Three) as u64;
    // F of the last ball evaluation, and whether the value of a point has been computed here (the others
    // still carry what the double stage left, without the parts of the step)
    let mut fb = vec![0u64; m];
    let mut sharp: Vec<bool> = (0..m).map(|k| cert.parts[k].is_some() || (vals[k].q.re == 0.0 && vals[k].q.im == 0.0)).collect();
    // (the parts that come with the values of the double stage have 40 bits: they give a first step for free)
    let mut d = vec![ZERO; m * m];
    let mut dist = vec![0.0f64; m * m];
    let mut dirty = vec![true; m];
    let mut budget = 30 + bits as usize / 40;
    let pbits = |x: &ZP| x.re.bits().max(x.im.bits());
    // the parts of the step (N, beta) in multiprecision, the relative precision they were asked with, and
    // the number of correct bits of each point (from its radius)
    let mut parts: Vec<Option<(ZP, ZP)>> = cert.parts.clone();
    let mut relk = vec![40u64; m];
    let mut eb = vec![40u64; m];
    // Relative precision asked of S at a point with `e` correct bits: what the next step can turn into
    // correct bits (as many as the point has, or with `full_order` as many as the order of the sweep gives),
    // or what the target still needs.  `pg` is the gain to expect of a point: unknown at first; after a step
    // that gave fewer bits than it was computed with (points still sharing a cluster of roots gain a few
    // bits per sweep), four times that.
    const ANY: u64 = 1 << 40;
    let full = opt.full_order;
    let rel = |e: u64, bits: u64, pg: u64| (if full { (order - 1) * e } else { e }).min(pg).saturating_add(50).min(bits.saturating_sub(e) + 16).max(40);
    let mut pg = vec![ANY; m];
    let mut cap = vec![0u64; m];
    let mut nf = vec![(0u64, 0u64); m];
    let mut last: Vec<Option<(u64, u64)>> = vec![None; m]; // correct bits before the last step, and its precision
    loop {
        for k in 0..m {
            for l in 0..m {
                if k != l && (dirty[k] || dirty[l]) {
                    // from the rounded points when they are far apart (relative error below 2^-28), exactly otherwise
                    let c = zc[k] - zc[l];
                    let far = c.abs() >= FAR * (zc[k].abs() + zc[l].abs());
                    let c = if far || (isd[k] && isd[l]) { c } else { z[k].sub(&z[l]).to_c() };
                    d[k * m + l] = c;
                    dist[k * m + l] = c.abs();
                }
            }
        }
        dirty.iter_mut().for_each(|x| *x = false);
        // two points at the same place would stay together for ever: one of them is moved aside
        let mut nudged = false;
        for k in 0..m {
            if (0..k).any(|l| d[k * m + l].re == 0.0 && d[k * m + l].im == 0.0) {
                let a = zc[k].abs();
                let h = ldexp(if a > 0.0 { a } else { 1.0 }, -(bits as i64) / 2);
                let off = C::new(h * (k as f64 + 1.0).cos(), h * (k as f64 + 1.0).sin());
                z[k] = z[k].sub(&ZP::from_c(off)).round(bits);
                zc[k] = z[k].to_c();
                isd[k] = false;
                let (v, f, p, _, _) = ball_auto(&bp, &z[k], fb[k].max(128), FCAP, pbits(&z[k]), 40, 0);
                nf[k] = (0, 0);
                vals[k] = v;
                fb[k] = f;
                parts[k] = p;
                relk[k] = 40;
                sharp[k] = true;
                dirty[k] = true;
                nudged = true;
            }
        }
        if nudged && sweeps < 400 {
            sweeps += 1;
            continue;
        }
        let (r, rho, one) = certificate(m, &vals, &d, &dist);
        let strict: Vec<bool> = (0..m)
            .map(|k| {
                let a = zc[k].abs();
                // a root proved real is returned in a real disc of radius rho + |Im z|: that is the radius
                // compared with the tolerance
                one[k] && rho[k] <= tol * a
                    && (!real || zc[k].im.abs() > rho[k] * (1.0 + 8.0 * U) || (real_radius(rho[k], zc[k].im) <= tol * a && mirror(&z, &zc, &isd, &rho, k, rho[k])))
            })
            .collect();
        if strict.iter().all(|&f| f) || sweeps >= 400 {
            return Refined { z, zc, isd, r, rho, one, dist, sweeps, bits };
        }
        for k in 0..m {
            let a = zc[k].abs();
            eb[k] = if rho[k] > 0.0 && a > 0.0 && rho[k].is_finite() { (-(rho[k] / a).log2()).clamp(0.0, bits as f64) as u64 } else if rho[k] == 0.0 { bits } else { 0 };
            if let Some((before, with)) = last[k].take() {
                let got = eb[k].saturating_sub(before);
                pg[k] = if got + 16 < with { (4 * got).max(8) } else { ANY };
            }
        }
        // the value and the parts of the step where the point still carries what the double stage left
        let mut changed = false;
        for k in 0..m {
            if !strict[k] && !sharp[k] {
                let e = eb[k].max(40);
                let rl = rel(e, bits, pg[k]);
                let (v, f, p, c, need) = ball_auto(&bp, &z[k], e + rl + 96, FCAP, pbits(&z[k]), rl, e.saturating_sub(16));
                cap[k] = c;
                nf[k] = (need, 0);
                vals[k] = v;
                fb[k] = f;
                parts[k] = p;
                relk[k] = rl;
                sharp[k] = true;
                changed = true;
            }
        }
        if changed {
            continue;
        }
        if sweeps >= budget {
            if bits >= CAP {
                return Refined { z, zc, isd, r, rho, one, dist, sweeps, bits };
            }
            bits *= 2;
            budget = sweeps + 30 + bits as usize / 40;
        }
        let done: Vec<bool> = (0..m).map(|k| strict[k] || (vals[k].q.re == 0.0 && vals[k].q.im == 0.0)).collect();
        // The step is N / (1 + w), N = S/S' and w what the rectangle and the other points add (see `step`).
        // The new point and the bits that the step can add to the correct ones:
        //  - by default N is the multiprecision quotient of the ball evaluation and the correction
        //    N w / (1 + w), of the size of the square of the error, is computed in double precision: the
        //    correct bits are doubled, and 40 more;
        //  - with `full_order` everything is computed in multiprecision (`step_mp`): as many bits as N has.
        let new: Vec<Option<(ZP, u64)>> = if opt.full_order {
            step_mp(&z, &parts, &relk, &done, &cfx, opt, bits, &d).into_iter().enumerate().map(|(k, n)| n.map(|n| (n, relk[k].saturating_sub(8)))).collect()
        } else {
            let ev: Vec<Ev> = (0..m).map(|k| Ev { a: vals[k].a, b: vals[k].b, done: done[k] }).collect();
            step(&d, &ev, &cf, opt, &mut dparts);
            (0..m)
                .map(|k| {
                    let (nd, w) = dparts[k];
                    let iw = (ONE + w).inv();
                    if done[k] || !(nd.is_finite() && w.is_finite() && iw.is_finite() && (nd * iw).is_finite() && (nd * w * iw).is_finite()) {
                        return None;
                    }
                    Some(match &parts[k] {
                        Some((big, _)) => (z[k].sub(big).sub(&ZP::from_c(ZERO - nd * w * iw)).round(bits), eb[k] + 40),
                        None => (z[k].sub(&ZP::from_c(nd * iw)).round(bits), 40),
                    })
                })
                .collect()
        };
        let mut moved = false;
        for (k, n) in new.into_iter().enumerate() {
            let (n, acc) = match n {
                Some(x) => x,
                None => continue,
            };
            if !n.sub(&z[k]).is_zero() {
                moved = true;
                // correct bits expected of the new point: what the precision of the step gives, at most the
                // order of the sweep; the value is asked for with that many bits
                let e = (eb[k] + acc.min(pg[k])).min(order * eb[k]).max(40).min(bits);
                let rl = rel(e, bits, pg[k]);
                last[k] = Some((eb[k], acc));
                // S' is small too near a cluster of roots: while the gain is slow, no more bits are cut than last time
                let cut = if pg[k] == ANY { e.saturating_sub(16) } else { e.saturating_sub(16).min(cap[k]) };
                // and S itself shrinks faster than the distance to the cluster: F follows what the last two
                // evaluations of the point needed
                let f0 = if pg[k] != ANY && nf[k].0 > 0 && nf[k].1 > 0 { (2 * nf[k].0).saturating_sub(nf[k].1).max(nf[k].0) + rl.saturating_sub(relk[k]) + 12 } else { e + rl + 96 };
                let (v, f, p, c, need) = ball_auto(&bp, &n, f0.max(128), FCAP, pbits(&n), rl, cut.min(f0.saturating_sub(64)));
                cap[k] = c;
                nf[k] = (if need > 0 { need + relk[k].saturating_sub(rl) } else { 0 }, nf[k].0);
                vals[k] = v;
                fb[k] = f;
                parts[k] = p;
                relk[k] = rl;
                zc[k] = n.to_c();
                isd[k] = false;
                dirty[k] = true;
                z[k] = n;
            }
        }
        sweeps += 1;
        if !moved {
            if bits >= CAP {
                return Refined { z, zc, isd, r, rho, one, dist, sweeps, bits };
            }
            bits *= 2;
            budget = sweeps + 30 + bits as usize / 40;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn series_of_the_support_near_one() {
        // q(1 + tau) - 1 by its two-term series and by the support itself, for several degrees
        for m in [2usize, 3, 7, 40, 1000] {
            let cf = coeffs3_exact(m);
            let g = 120u64;
            let tau: Fx = (BigInt::from(3) << (g - 42), BigInt::from(-5) << (g - 43));
            let a = q1_fx(&tau, g, m, &cf); // |tau| < 2^-40: the series
            let one = BigInt::from(1) << g;
            let q = three_fx(&(&one + &tau.0, tau.1.clone()), g, &cf);
            let b: Fx = (q.0 - &one, q.1);
            let d = (&a.0 - &b.0).abs().max((&a.1 - &b.1).abs());
            assert!(d.bits() <= 12, "degree {}: difference of {} bits", m, d.bits());
            // and the double precision support agrees with the multiprecision one
            let t = C::new(1.25, -0.5);
            let tf: Fx = (BigInt::from(5) << (g - 2), -(BigInt::from(1) << (g - 1)));
            let qd = three(t, &coeffs3(m as f64));
            let qm = ZP { re: three_fx(&tf, g, &cf).0, im: three_fx(&tf, g, &cf).1, e: -(g as i64) }.to_c();
            assert!((qd - qm).abs() < 1e-13, "degree {}: {:?} {:?}", m, qd, qm);
        }
    }
}
