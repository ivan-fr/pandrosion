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
    ci: std::borrow::Cow<'a, GPoly>,
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
    /// the polynomials T_e(t) = S(2^e t), for the points outside the unit disc that have few bits
    scaled: RefCell<HashMap<i64, Rc<BallPoly<'static>>>>,
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
    /// bits of F that the scaled variable used up, `m log2(1/|t|)` (0 for the other evaluations)
    pub lost: u64,
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
        BallPoly::make(std::borrow::Cow::Borrowed(ci), beta)
    }
    fn make(ci: std::borrow::Cow<'a, GPoly>, beta: bool) -> BallPoly<'a> {
        let e = ci.iter().map(|(a, b)| a.bits().max(b.bits())).max().unwrap_or(1).max(1);
        let one = BigInt::from(1);
        let modulus = |c: &(BigInt, BigInt)| {
            let (fr, er) = fl2(&c.0, &one);
            let (fi, ei) = fl2(&c.1, &one);
            abs_scaled(ldexp(fr, er - e as i64), ldexp(fi, ei - e as i64)) // coefficients / 2^E: moduli below 1.5
        };
        let sa = ci.iter().map(|c| { let (f, x) = modulus(c); ldexp(f, x) }).sum::<f64>() * (1.0 + 1e-9);
        // the leading coefficient with its own exponent: next to coefficients 2^1100 times larger (roots over
        // hundreds of orders of magnitude) its modulus divided by 2^E is not a double
        let (f0, e0) = {
            let (fr, er) = fl2(&ci[0].0, &one);
            let (fi, ei) = fl2(&ci[0].1, &one);
            let big = if fr == 0.0 { ei } else if fi == 0.0 { er } else { er.max(ei) };
            let (f, x) = abs_scaled(ldexp(fr, er - big), ldexp(fi, ei - big));
            (f, x + big - e as i64)
        };
        let nz: Vec<usize> = (0..ci.len()).filter(|&j| !(ci[j].0.is_zero() && ci[j].1.is_zero())).collect();
        let sparse = nz.len() * 48 < ci.len();
        BallPoly { ci, e, sa, lead: (f0 * (1.0 - 1e-9), e0), nz, sparse, beta, cache: RefCell::new(HashMap::new()), scaled: RefCell::new(HashMap::new()) }
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
    /// The evaluation at a point outside the unit disc (or, since 0.11.0, far inside it) that has few bits (a double, in the stage that follows
    /// the double precision one), through the polynomial T(t) = S(2^e t) at t = z / 2^e, |t| <= 1.
    ///
    /// The other way, 1/z and the reversed polynomial, multiplies by a number with as many bits as F at
    /// every step; t has the bits of z, one or two limbs, and each product costs a pass or two over the
    /// accumulator.  T has the exact coefficients c_j 2^(e (m - j)) and T(t) = S(z) exactly, so this is the
    /// evaluation inside the unit disc of another polynomial, with the same error bound, and
    ///
    ///   S(z) / c_0 = 2^(e m) T(t) / lead(T),   S'/S (z) = 2^-e T'/T (t),   S''/S (z) = 4^-e T''/T (t),
    ///   N = S/S' (z) = 2^e T/T' (t),           beta = S S''/S'^2 is the same
    ///
    /// (Lean: `ScaledVariable`).  None if this does not apply: the point has many bits, the coefficients
    /// of T would be too long, or Horner's rule at t would lose more bits than the short multiplier saves.
    fn eval_scaled(&self, z: &ZP, zc: C, f: u64, rel: u64, cut: u64) -> Option<Ball> {
        let m = self.ci.len() - 1;
        if z.re.bits().max(z.im.bits()) > 64 || m < 2 {
            return None;
        }
        let a = zc.abs();
        if !a.is_finite() {
            return None;
        }
        // |z| = g 2^e with g in [1/2, 1): t = z / 2^e, or z / 2^(e+1) if the rounding of |z| hid |t| > 1
        let (_, mut e) = frexp(a);
        let mut t = ZP { re: z.re.clone(), im: z.im.clone(), e: z.e - e };
        if t.to_c().abs() > 1.0 {
            e += 1;
            t.e -= 1;
        }
        if e == 0 || e.unsigned_abs() * m as u64 > 16384 || t.to_c().abs() > 1.0 {
            return None;
        }
        // Horner's rule at t loses m log2(1 / |t|) bits that the reversed polynomial at 1/z does not lose
        // (|t| is between 1/2 and 1: up to m bits, for a point just outside the unit circle).  The short
        // multiplier pays for them only while they are few against F: up to version 0.10.0 this path was
        // taken for every such point, and a dense polynomial of degree 320 took six times longer at 30
        // digits than with version 0.7.0.
        // Version 0.13.0: the limit is F itself (it was a quarter of F from 0.10.1 to 0.12.0).  Most of that
        // slowdown was not the wider numbers but the exact evaluation that `ball_auto` fell back on when
        // F - lost bits could not tell the value from zero; it now waits for F to pass the bits lost.  With
        // that, and with the product by a short multiplier in one pass (`limbs::combine_short`), the limit F
        // takes 15 % off the time of the polynomials of the corpus that reach this stage and leaves the
        // dense polynomials of degree 320 and 640 at 30 digits where they were.
        // (A point far inside the unit disc is the other way round: Horner's rule at z itself loses m log2(1/|z|)
        // bits when the low coefficients dominate there, and the scaled variable at most m of them.)
        let lost = m as f64 * -t.to_c().abs().log2();
        if e > 0 && lost > f as f64 + 32.0 {
            return None;
        }
        let inner = {
            let mut map = self.scaled.borrow_mut();
            if map.len() > 64 {
                map.clear();
            }
            map.entry(e).or_insert_with(|| Rc::new(BallPoly::make(std::borrow::Cow::Owned(crate::exact::scale_variable(&self.ci, e)), self.beta))).clone()
        };
        if inner.sparse {
            return None;
        }
        let mut ball = inner.eval(&t, f, rel, cut);
        ball.lost = lost.max(0.0).ceil() as u64;
        let up = |c: C, k: i64| C::new(ldexp(c.re, k), ldexp(c.im, k));
        ball.val.ex += e * m as i64;
        ball.val.a = up(ball.val.a, -e);
        ball.val.b = up(ball.val.b, -2 * e);
        if let Some((n, _)) = ball.parts.as_mut() {
            n.e += e;
        }
        Some(ball)
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
        // outside the unit disc, or far inside it (|z| < 1/16): through the variable scaled to the point
        if (!inside || zc.abs() < 0.0625) && !self.sparse {
            if let Some(ball) = self.eval_scaled(z, zc, f, rel, cut) {
                return ball;
            }
        }
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
        let mut a_err = (mf + 1.0) * (2.25 + 1.5 * self.sa) * 1.01 + 1.0;
        // S' and S'' in units of 2^-(F - c12)
        let c12 = if self.sparse { 0 } else { cut.min(f.saturating_sub(64)) };
        let f12 = f - c12;
        let (xr12, xi12): (BigInt, BigInt) = (&xr >> c12, &xi >> c12);
        let mul12 = |p: &(BigInt, BigInt)| -> (BigInt, BigInt) { ((&p.0 * &xr12 - &p.1 * &xi12) >> f12, (&p.0 * &xi12 + &p.1 * &xr12) >> f12) };
        if !self.sparse {
            // the same integers from numbers of a fixed width (module `limbs`), or from `BigInt` when they
            // do not fit or F is large
            let rev = !inside;
            let [q0, q1, q2] = match crate::limbs::horner3(&c, rev, &xr, &xi, f, c12, &xr12, &xi12) {
                Some(r) => r,
                None => crate::limbs::horner3_big(&c, rev, &xr, &xi, f, c12, &xr12, &xi12),
            };
            p0 = q0;
            p1 = q1;
            p2 = q2;
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
        Ball { val: Val { q: C::new(qf, 0.0), ex: qe, a, b, exact: true }, good, tiny, more, spare, parts, lack1, lost: 0 }
    }
}

/// The value at z with enough bits: F is raised from `f0` until the value is known to the relative precision
/// 2^-rel or F reaches `fcap`; S' and S'' are computed with `cut` bits fewer, less if that turns out to be
/// too few.  A value that cannot be told from zero with many more bits than the point has (`pbits`) is
/// computed exactly: an exact root gets the radius zero.  Returns the value, the last F (0: exact) and the
/// parts of the step, N = S/S' and beta = S S''/S'^2, the `cut` that was enough and the F that would have been enough (0: unknown).
pub fn ball_auto(bp: &BallPoly, z: &ZP, f0: u64, fcap: u64, pbits: u64, rel: u64, cut: u64) -> (Val, u64, Option<(ZP, ZP)>, u64, u64) {
    // F is rounded up to a multiple of 64: the evaluation works on whole limbs, the bits up to the next
    // limb are free
    let whole = |f: u64| f.div_ceil(64) * 64;
    let fcap = whole(fcap);
    let (mut f, mut cut) = (whole(f0).min(fcap), cut);
    loop {
        let ball = bp.eval(z, f, rel, cut);
        if ball.good {
            if ball.lack1 > 0 {
                cut = cut.min(f.saturating_sub(64)) - ball.lack1;
                continue;
            }
            return (ball.val, f, ball.parts, cut, f - ball.spare.min(f));
        }
        // (Version 0.13.0: the bits that the scaled variable used up do not count.  Before, a value that
        // F - lost bits could not tell from zero was computed exactly, with integers of 53 m bits, when a
        // few more bits of F would have shown it.  On the Mandelbrot polynomial of degree 255, evaluated
        // through the scaled variable up to `lost` = F / 2, half of the time went to those exact values.)
        if ball.tiny && f >= 2 * pbits + 128 + ball.lost {
            let (x, y, s) = if z.e <= 0 { (z.re.clone(), z.im.clone(), (-z.e) as u64) } else { (&z.re << z.e as u64, &z.im << z.e as u64, 0) };
            let h = exact_horner(&bp.ci, &x, &y, s);
            let mut v = exact_val(&bp.ci, &h, s);
            v.exact = true;
            let parts = if v.q.re == 0.0 && v.q.im == 0.0 { None } else { exact_parts(&h, s, rel + 64) };
            return (v, 0, parts, cut, 0);
        }
        if f >= fcap {
            return (ball.val, f, ball.parts, cut, 0);
        }
        // straight to the number of bits that the value just computed calls for
        f = if ball.more > 0 { whole(f + ball.more).min(fcap) } else { (2 * f).min(fcap) };
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

/// The connected components of the Smith discs D(z_k, r_k): two discs that are not proved disjoint are in
/// the same component, and a component whose enclosing disc (centred at its first point) reaches the disc
/// of a point outside it is joined with that point's component, until nothing changes.  By Smith's theorem
/// a component of q discs contains exactly q roots.  `dist` holds the distances between the points, with a
/// relative error below `DREL`.
pub fn components(m: usize, r: &[f64], dist: &[f64]) -> Vec<Vec<usize>> {
    let mut parent: Vec<usize> = (0..m).collect();
    fn find(p: &mut Vec<usize>, mut i: usize) -> usize {
        while p[i] != i {
            p[i] = p[p[i]];
            i = p[i];
        }
        i
    }
    for k in 0..m {
        for l in 0..k {
            if !(dist[k * m + l] * (1.0 - 2.0 * DREL) > (r[k] + r[l]) * (1.0 + SLACK)) || dist[k * m + l] < SMALL {
                let (a, b) = (find(&mut parent, k), find(&mut parent, l));
                parent[a] = b;
            }
        }
    }
    loop {
        let mut groups: std::collections::BTreeMap<usize, Vec<usize>> = Default::default();
        for k in 0..m {
            let g = find(&mut parent, k);
            groups.entry(g).or_default().push(k);
        }
        let mut joined = false;
        for comp in groups.values().filter(|c| c.len() > 1) {
            let (i, big) = (comp[0], enclosing(m, comp, r, dist));
            for l in 0..m {
                if !comp.contains(&l) && !(dist[i * m + l] * (1.0 - 2.0 * DREL) > (big + r[l]) * (1.0 + SLACK)) {
                    let (a, b) = (find(&mut parent, i), find(&mut parent, l));
                    if a != b {
                        parent[a] = b;
                        joined = true;
                    }
                }
            }
        }
        if !joined {
            return groups.into_values().collect();
        }
    }
}

/// The radius of a disc centred at the first point of a component that contains all its Smith discs.
pub fn enclosing(m: usize, comp: &[usize], r: &[f64], dist: &[f64]) -> f64 {
    comp.iter().map(|&l| dist[comp[0] * m + l] * (1.0 + 2.0 * DREL) + r[l]).fold(0.0, f64::max)
}

/// Every root is in a disc within the tolerance, alone or with others (`Options::isolate` = false): each
/// point that is not `strict` has a Smith disc within the tolerance and disjoint from the others, or belongs
/// to a component whose enclosing disc is within the tolerance.  `za` holds the moduli of the points.
pub fn covered(m: usize, strict: &[bool], r: &[f64], dist: &[f64], za: &[f64], tol: f64) -> bool {
    covered_with(m, strict, r, dist, za, tol, false)
}

/// The same; with `alone_strict` a point that is alone in its component must be `strict` (only the roots
/// that share a component are excused from having a disc of their own).
pub fn covered_with(m: usize, strict: &[bool], r: &[f64], dist: &[f64], za: &[f64], tol: f64, alone_strict: bool) -> bool {
    if (0..m).any(|k| !strict[k] && !(r[k] <= tol * za[k])) {
        return false; // a Smith disc alone is already too large
    }
    components(m, r, dist).iter().all(|comp| {
        if comp.len() == 1 {
            let k = comp[0];
            strict[k] || (!alone_strict && r[k] <= tol * za[k])
        } else {
            enclosing(m, comp, r, dist) <= tol * za[comp[0]]
        }
    })
}

/// Relative radius below which a cluster cannot be resolved by double precision centres: a quarter of the
/// distance between two doubles.  The doubles interface merges the discs of such roots into one whatever
/// the precision they were separated with (`doubles` in lib.rs), so it no longer separates them first.
pub const GRID: f64 = 1.0 / 18014398509481984.0; // 2^-54

/// The step of a cluster of roots (version 0.9.0).
///
/// K points that approach a cluster of K roots from a distance much larger than its width see it as one
/// root of multiplicity K, and the sweep (each point deflated of all the others, K - 1 of which are as far
/// from the cluster as it is) brings them closer by a constant factor only: 1/4 for a pair, 4/7 for five
/// roots.  Seen from outside, the cluster is a shifted power (w - g)^K - a, the function for which the
/// rectangle of the p-th root is exact: with F the polynomial deflated of the points *outside* the cluster,
/// A = F'/F and B = -(F'/F)' at one point z of the cluster, the step of degree p = K has the cursor
///
///   t = (K B - A^2) / ((K - 1) A^2),   and   u = K / (A (1 - t))
///
/// is z - g, g being the virtual anchor; the K roots of the model are g + u t^(1/K) w^j, w^K = 1 (the exact
/// support returns t^(1/p) in one step).  For (w - g)^K - a itself this is exact (Lean: `ClusterStep`);
/// for K = 2 every quadratic is such a function.
///
/// For each component of K >= 2 overlapping Smith discs that is tight (its enclosing disc is at least 16
/// times smaller than its distance to the discs of the other points) and seen from far enough (the model
/// radius is at most a quarter of |u|), returns its members and their new positions as offsets from the
/// point `from`: the roots of the model, on a circle of radius at least `floor` |u| (the cursor of a
/// cluster seen from very far is lost in the rounding of S'/S and S''/S).  `diff(k, l)` is z_k - z_l.
/// The moves are proposals: the certificate is computed afterwards at the points reached.
pub fn cluster_moves(m: usize, r: &[f64], dist: &[f64], vals: &[Val], diff: &dyn Fn(usize, usize) -> C, floor: f64) -> Vec<(usize, Vec<(usize, C)>)> {
    cluster_moves_in(m, &components(m, r, dist), r, dist, vals, diff, floor)
}

/// `cluster_moves` with the components already computed.
pub fn cluster_moves_in(m: usize, comps: &[Vec<usize>], r: &[f64], dist: &[f64], vals: &[Val], diff: &dyn Fn(usize, usize) -> C, floor: f64) -> Vec<(usize, Vec<(usize, C)>)> {
    tight_clusters(m, comps, r, dist, vals).iter().filter_map(|cl| double_cursor(m, cl, vals, diff).and_then(|(u, rho, arg)| place(cl, u, rho.max(floor), arg, diff)).map(|mv| (cl.from, mv))).collect()
}

/// Below this the cursor computed from double precision ratios is not trusted.
pub const CURSOR_NOISE: f64 = 1.0 / 16777216.0; // 2^-24

/// A tight component of Smith discs, and the point of it where the model of the cluster is read.
pub struct Tight {
    pub members: Vec<usize>,
    pub from: usize,
    /// radius of the disc centred at the first member that contains the Smith discs of the component
    pub big: f64,
}

/// The components of K >= 2 overlapping Smith discs (K < m) that are tight: the enclosing disc is at least
/// 16 times smaller than its distance to the discs of the other points.  `from` is a member whose value
/// comes from an evaluation and is not zero.
pub fn tight_clusters(m: usize, comps: &[Vec<usize>], r: &[f64], dist: &[f64], vals: &[Val]) -> Vec<Tight> {
    let mut out = Vec::new();
    if m < 3 {
        return out;
    }
    for comp in comps {
        let k = comp.len();
        if k < 2 || k == m {
            continue;
        }
        let big = enclosing(m, comp, r, dist);
        let room = (0..m).filter(|l| !comp.contains(l)).flat_map(|l| comp.iter().map(move |&i| (i, l))).map(|(i, l)| dist[i * m + l] - r[l]).fold(f64::INFINITY, f64::min);
        if !(big.is_finite() && room > 0.0 && 16.0 * big <= room) {
            continue;
        }
        if let Some(from) = comp.iter().copied().find(|&i| vals[i].exact && vals[i].a.is_finite() && vals[i].b.is_finite() && !(vals[i].q.re == 0.0 && vals[i].q.im == 0.0)) {
            out.push(Tight { members: comp.clone(), from, big });
        }
    }
    out
}

/// The cursor of a cluster from the double precision ratios S'/S and S''/S: (u, |t|^(1/K), arg(t)/K), or
/// None if the point is not far from the cluster (|t|^(1/K) > 1/4).  A cursor below about 2^-34 is lost in
/// the rounding of the ratios (`CURSOR_NOISE` leaves a margin): `cluster_model` then computes it in
/// multiprecision.
pub fn double_cursor(m: usize, cl: &Tight, vals: &[Val], diff: &dyn Fn(usize, usize) -> C) -> Option<(C, f64, f64)> {
    let (from, kf) = (cl.from, cl.members.len() as f64);
    let (mut a, mut b) = (vals[from].a, vals[from].a * vals[from].a - vals[from].b);
    for l in (0..m).filter(|l| !cl.members.contains(l)) {
        let inv = diff(from, l).inv();
        a = a - inv;
        b = b - inv * inv;
    }
    let a2 = a * a;
    let t = (b.scale(kf) - a2) / a2.scale(kf - 1.0);
    let u = (a * (ONE - t)).inv().scale(kf);
    let rho = t.abs().powf(1.0 / kf);
    if !(t.is_finite() && u.is_finite() && u.abs() > 0.0 && rho <= 0.25) {
        return None; // not a cluster seen from far: the sweep does better
    }
    Some((u, rho, if t.re == 0.0 && t.im == 0.0 { 0.0 } else { t.im.atan2(t.re) / kf }))
}

/// The new positions of the members, as offsets from the point `from`: the K points g + u s e^(i (arg +
/// 2 pi j / K)), g = z - u, each member going to the one nearest in angle.
pub fn place(cl: &Tight, u: C, scale: f64, arg: f64, diff: &dyn Fn(usize, usize) -> C) -> Option<Vec<(usize, C)>> {
    let kf = cl.members.len() as f64;
    let g_off = ZERO - u; // the anchor, from the point `from`
    let mut order: Vec<(f64, usize)> = cl.members.iter().map(|&i| { let c = diff(i, cl.from) - g_off; (c.im.atan2(c.re), i) }).collect();
    order.sort_by(|x, y| x.0.total_cmp(&y.0));
    let j0 = ((order[0].0 - (u.im.atan2(u.re) + arg)) / (2.0 * std::f64::consts::PI / kf)).round();
    let moves: Vec<(usize, C)> = order
        .iter()
        .enumerate()
        .map(|(j, &(_, i))| {
            let ang = arg + 2.0 * std::f64::consts::PI * (j as f64 + j0) / kf;
            (i, g_off + u * C::new(scale * ang.cos(), scale * ang.sin()))
        })
        .collect();
    moves.iter().all(|x| x.1.is_finite()).then_some(moves)
}

/// The model of a cluster with its cursor in multiprecision (version 0.10.0).
pub struct ClusterModel {
    /// z - g, to the precision of the evaluation: the anchor g = z - u is the centre of the cluster
    pub u: ZP,
    /// log2 |t| and arg t, t the cursor (a / u^K for the shifted power (w - g)^K - a)
    pub lt: f64,
    pub arg: f64,
    /// the cursor stands above the rounding of the evaluation: |t|^(1/K) |u| is the radius of the cluster.
    /// Otherwise the cluster is smaller than 2^(noise / K) |u|.
    pub significant: bool,
    pub noise: f64,
}
impl ClusterModel {
    /// The radius of the model, or its upper bound, relative to |u|; and the angle of its first root.
    pub fn radius(&self, k: usize) -> (f64, f64) {
        let l = if self.significant { self.lt } else { self.noise };
        ((l / k as f64).exp2(), if self.significant { self.arg / k as f64 } else { 0.0 })
    }
}

/// The cursor t and the anchor of a cluster of K roots, from one evaluation of S, S', S'' at the point z
/// of the cluster with `rel` bits of relative precision, the other points being those of `outside`.
///
/// With N = S/S' and beta = S S''/S'^2 in multiprecision (the parts of the ball evaluation), and the sums
/// s1 = sum 1/(z - z_l), s2 = sum 1/(z - z_l)^2 over the points outside,
///
///   A = 1/N - s1,   B = (1 - beta)/N^2 - s2,   t = (K B / A^2 - 1)/(K - 1),   u = K / (A (1 - t)).
///
/// K B / A^2 is 1 + (K - 1) t: a cursor of size 2^-tau needs A and B to tau bits and more, which double
/// precision ratios do not have (their cursor stops near 2^-34, and a cluster seen from far is then closed
/// on by nine digits a step).  Here the cursor is known down to 2^-(rel - 24): one evaluation gives the
/// radius of the cluster, or the proof that it is below the one aimed at.  Everything is scaled by a power
/// of two near |N| so that the numbers are of size one.  None if S' vanishes at the precision used.
pub fn cluster_model(bp: &BallPoly, z: &ZP, outside: &[&ZP], k: usize, rel: u64, fcap: u64) -> Option<ClusterModel> {
    let pb = z.re.bits().max(z.im.bits());
    let (_, _, parts, _, _) = ball_auto(bp, z, rel + 64, fcap, pb, rel, 0);
    let (n, beta) = parts?;
    let nb = n.re.bits().max(n.im.bits()) as i64;
    if nb == 0 {
        return None;
    }
    let es = nb + n.e; // |N| is between 2^(es - 1) and 2^(es + 1/2)
    let g = rel + 96;
    let one: Fx = (BigInt::from(1) << g, BigInt::zero());
    let sub = |x: &Fx, y: &Fx| -> Fx { (&x.0 - &y.0, &x.1 - &y.1) };
    let inv = fx_inv(&fx_from(&ZP { re: n.re.clone(), im: n.im.clone(), e: n.e - es }, g), g)?; // 2^es / N
    let mut a = inv.clone(); // A 2^es
    let mut b = fx_mul(&sub(&one, &fx_from(&beta, g)), &fx_mul(&inv, &inv, g), g); // B 4^es
    for o in outside {
        // 2^es / (z - z_l) in units of 2^-g
        let gg = (g as i64 + es).max(16) as u64;
        let x = recip(&z.sub(o), gg)?;
        let sh = es + g as i64 - gg as i64;
        let sx: Fx = if sh >= 0 { (&x.0 << sh as u64, &x.1 << sh as u64) } else { (&x.0 >> (-sh) as u64, &x.1 >> (-sh) as u64) };
        b = sub(&b, &fx_mul(&sx, &sx, g));
        a = sub(&a, &sx);
    }
    let ia = fx_inv(&a, g)?;
    let ratio = fx_mul(&b, &fx_mul(&ia, &ia, g), g); // B / A^2
    let kb = BigInt::from(k);
    let kt: Fx = sub(&(&ratio.0 * &kb, &ratio.1 * &kb), &one); // (K - 1) t
    let t = fx_rat(&kt, &(BigInt::from(1), BigInt::from(k - 1)));
    let den = fx_mul(&a, &sub(&one, &t), g);
    let uq = fx_inv(&den, g)?; // u / (K 2^es)
    let u = ZP { re: &uq.0 * &kb, im: &uq.1 * &kb, e: es - g as i64 };
    if u.is_zero() {
        return None;
    }
    let noise = 24.0 + (k as f64).log2() - rel as f64;
    if t.0.is_zero() && t.1.is_zero() {
        return Some(ClusterModel { u, lt: f64::NEG_INFINITY, arg: 0.0, significant: false, noise });
    }
    let (c, sh) = mant(&t.0, &t.1);
    let lt = c.abs().log2() + sh as f64 - g as f64;
    Some(ClusterModel { u, lt, arg: c.im.atan2(c.re), significant: lt > noise, noise })
}

/// The moves of the points of a tight cluster from its multiprecision model: `Ok` with the offsets from
/// the anchor g = z_from - u (double precision is enough for them: g carries the bits), or `Err(radius)`
/// when the cluster is not worth a move here: it is not far (the model radius is above a quarter of |u|,
/// `Err` of that radius).  `scale_floor` keeps the points apart when the radius is only bounded.
pub fn model_moves(cl: &Tight, model: &ClusterModel, diff: &dyn Fn(usize, usize) -> C) -> Option<(f64, Vec<(usize, C)>)> {
    let k = cl.members.len();
    let (scale, arg) = model.radius(k);
    let u = model.u.to_c();
    if !(scale <= 0.25 && scale > 0.0 && u.is_finite() && u.abs() > 0.0) {
        return None;
    }
    // offsets from the point `from` in `place`: turned into offsets from the anchor
    let mv = place(cl, u, scale, arg, diff)?;
    Some((scale * u.abs(), mv.into_iter().map(|(i, off)| (i, off + u)).collect()))
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
    refine_for(ci, cert, opt, real, false)
}

/// `refine` for one of the two kinds of output.  `doubles`: the centres will be rounded to doubles; roots
/// that share a disc of relative radius below `GRID` are then left together, with their number (they would
/// be merged after the rounding: the discs of two roots that doubles cannot tell apart overlap).
pub fn refine_for(ci: &GPoly, cert: &Certified, opt: &Options, real: bool, doubles: bool) -> Refined {
    const CAP: u64 = 4096;
    const FCAP: u64 = 32768;
    let m = cert.z.len();
    let tol = opt.tol.max(1e-280) / (1.0 + SLACK); // the radius that may be printed is within the tolerance
    let mut bits = ((-tol.log2()).ceil() as u64 + 40).max(128);
    let bp = BallPoly::new(ci, opt.full_order);
    // the polynomial of the cluster models: its evaluations return S S''/S'^2 in multiprecision too
    let bpc: std::cell::OnceCell<BallPoly> = std::cell::OnceCell::new();
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
        if !opt.isolate || doubles {
            let za: Vec<f64> = zc.iter().map(|x| x.abs()).collect();
            let done = if !opt.isolate { covered(m, &strict, &r, &dist, &za, if doubles { tol.max(GRID) } else { tol }) } else { covered_with(m, &strict, &r, &dist, &za, GRID, true) };
            if done {
                return Refined { z, zc, isd, r, rho, one, dist, sweeps, bits };
            }
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
        let mut new = new;
        let mut hint = vec![0u64; m];
        if opt.cluster {
            let diff = |k: usize, l: usize| d[k * m + l];
            let comps = components(m, &r, &dist);
            for cl in tight_clusters(m, &comps, &r, &dist, &vals) {
                if cl.members.iter().any(|&i| done[i]) {
                    continue;
                }
                let (from, k) = (cl.from, cl.members.len());
                let a = zc[from].abs();
                // bits to add to the next evaluation of a point brought closer by `scale`: S shrinks like the
                // K-th power of the distance to the cluster
                let more = |scale: f64| (k as f64 * -scale.log2()).clamp(0.0, FCAP as f64).ceil() as u64;
                // the cursor from the double precision ratios: enough when it stands above their rounding
                let (u, rho, arg) = match double_cursor(m, &cl, &vals, &diff) {
                    Some(x) => x,
                    None => continue, // the points are not far from the cluster: the sweep
                };
                if rho.powi(k as i32) >= CURSOR_NOISE {
                    if let Some(moves) = place(&cl, u, rho, arg, &diff) {
                        let grid = ldexp(a, 12 - bits as i64);
                        if !moves.windows(2).any(|w| (w[0].1 - w[1].1).abs() < grid) {
                            for (i, off) in moves {
                                new[i] = Some((z[from].sub(&ZP::from_c(ZERO - off)).round(bits), 28));
                                hint[i] = more(rho);
                            }
                        }
                    }
                    continue;
                }
                // The cursor in multiprecision.  The radius aimed at: the one below which the roots are left
                // together (doubles, or a goal that does not isolate), an eighth of it; none when they are
                // to be separated at any cost, and the cursor is then asked for as many bits as the points
                // have.
                let goal = if !opt.isolate { (if doubles { tol.max(GRID) } else { tol }) * a / 8.0 } else if doubles { GRID * a / 8.0 } else { 0.0 };
                let far = u.abs();
                let rel = if goal > 0.0 && far > goal { (k as f64 * (far / goal).log2()).ceil() as u64 + 48 } else if goal > 0.0 { 64 } else { bits };
                let outside: Vec<&ZP> = (0..m).filter(|l| !cl.members.contains(l)).map(|l| &z[l]).collect();
                let mp = cluster_model(bpc.get_or_init(|| BallPoly::new(ci, true)), &z[from], &outside, k, rel.min(8192), FCAP).and_then(|md| model_moves(&cl, &md, &diff).map(|x| (md, x)));
                if let Some((md, (radius, moves))) = mp {
                    // the points need the bits of the circle they are put on
                    let need = if radius > 0.0 && a > 0.0 { ((a / radius).log2().max(0.0) as u64 + 40).div_ceil(64) * 64 } else { bits };
                    if need > CAP {
                        continue;
                    }
                    if need > bits {
                        bits = need;
                        budget = sweeps + 30 + bits as usize / 40;
                    }
                    let anchor = z[from].sub(&md.u);
                    for (i, off) in moves {
                        new[i] = Some((anchor.sub(&ZP::from_c(ZERO - off)).round(bits), 28));
                        hint[i] = more(md.radius(k).0);
                    }
                } else if let Some(moves) = place(&cl, u, rho.max(ldexp(1.0, -30)), arg, &diff) {
                    // no model (S' vanishes at this precision): the double precision cursor with its floor
                    let grid = ldexp(a, 12 - bits as i64);
                    if !moves.windows(2).any(|w| (w[0].1 - w[1].1).abs() < grid) {
                        for (i, off) in moves {
                            new[i] = Some((z[from].sub(&ZP::from_c(ZERO - off)).round(bits), 28));
                            hint[i] = more(rho.max(ldexp(1.0, -30)));
                        }
                    }
                }
            }
        }
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
                let f0 = if hint[k] > 0 { f0.max(fb[k] + hint[k]) } else { f0 };
                hint[k] = 0;
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
    fn scaled_evaluation_agrees_with_exact_values() {
        // points with 53 bits outside the unit disc: the evaluation goes through T(t) = S(2^e t)
        let mut st = 0x9e3779b97f4a7c15u64;
        let mut next = || {
            st ^= st << 13;
            st ^= st >> 7;
            st ^= st << 17;
            st
        };
        for case in 0..200 {
            let m = 3 + (next() % 30) as usize;
            let ci: GPoly = (0..=m).map(|j| (BigInt::from((next() % 2001) as i64 - 1000 + if j == 0 { 2000 } else { 0 }), BigInt::from(if case % 2 == 0 { 0 } else { (next() % 2001) as i64 - 1000 }))).collect();
            let unit = |x: u64| (x >> 11) as f64 / (1u64 << 53) as f64;
            let radius = 1.0 + 30.0 * unit(next()) * unit(next());
            let angle = 6.283185307179586 * unit(next());
            let zc = C::new(radius * angle.cos(), radius * angle.sin());
            if !(zc.abs() > 1.0) {
                continue;
            }
            let (bp, z) = (BallPoly::new(&ci, false), ZP::from_c(zc));
            let scaled = bp.eval_scaled(&z, zc, 512, 40, 0).expect("the scaled evaluation applies");
            let exact = crate::exact::exact_values(&ci, zc);
            assert!(scaled.good, "case {case}");
            // |S(z)| / |c_0|: an upper bound (it carries a margin of 10^-9 for the rounding of the leading coefficient)
            let ratio = scaled.val.q.re / exact.q.abs() * 2f64.powi((scaled.val.ex - exact.ex) as i32);
            assert!(ratio >= 1.0 - 1e-12 && ratio <= 1.0 + 1e-8, "case {case}: bound / value = {ratio}");
            let close = |a: C, b: C| (a - b).abs() <= 1e-9 * b.abs();
            assert!(close(scaled.val.a, exact.a) && close(scaled.val.b, exact.b), "case {case}: S'/S or S''/S");
            // N = S/S' against 1 / (S'/S)
            let n = scaled.parts.unwrap().0.to_c();
            assert!(close(n, exact.a.inv()), "case {case}: N");
        }
    }

    #[test]
    fn cluster_step_finds_the_roots_of_a_shifted_power() {
        // S = ((w - g)^K - a) (w - o1) (w - o2): K points at distance d from g, two points on the other roots
        let pw = |x: C, n: usize| (0..n).fold(ONE, |acc, _| acc * x);
        for &(k, rho) in &[(2usize, 1e-2f64), (3, 1e-2), (2, 1e-5), (4, 3e-2)] {
            let (g, o1, o2) = (C::new(0.7, -0.2), C::new(-1.5, 0.4), C::new(2.0, 1.0));
            let d = 1e-2;
            let a = C::new(0.3, 0.8).scale((d * rho).powi(k as i32) / C::new(0.3, 0.8).abs());
            let m = k + 2;
            let mut z: Vec<C> = (0..k).map(|j| g + C::new((1.0 + 2.1 * j as f64).cos(), (1.0 + 2.1 * j as f64).sin()).scale(d * (1.0 + 0.1 * j as f64))).collect();
            z.push(o1);
            z.push(o2);
            let kf = k as f64;
            let vals: Vec<Val> = (0..m)
                .map(|i| {
                    if i >= k {
                        return Val { q: ZERO, ex: 0, a: ZERO, b: ZERO, exact: true };
                    }
                    let u = z[i] - g;
                    let (f, f1, f2) = (pw(u, k) - a, pw(u, k - 1).scale(kf), pw(u, k - 2).scale(kf * (kf - 1.0)));
                    let (i1, i2) = ((z[i] - o1).inv(), (z[i] - o2).inv());
                    // S'/S, and S''/S = (S'/S)^2 - sum of 1 / (z - root)^2
                    let la = f1 / f + i1 + i2;
                    let lb = (f1 * f1 - f * f2) / (f * f) + i1 * i1 + i2 * i2;
                    Val { q: ONE, ex: 0, a: la, b: la * la - lb, exact: true }
                })
                .collect();
            let dist: Vec<f64> = (0..m * m).map(|i| (z[i / m] - z[i % m]).abs()).collect();
            let r: Vec<f64> = (0..m).map(|i| if i < k { 1.5 * d } else { 0.0 }).collect();
            let diff = |x: usize, y: usize| z[x] - z[y];
            let moves = cluster_moves(m, &r, &dist, &vals, &diff, ldexp(1.0, -30));
            assert_eq!(moves.len(), 1, "K = {k}");
            let (from, new) = &moves[0];
            assert_eq!(new.len(), k);
            // the K-th roots of a
            let radius = a.abs().powf(1.0 / kf);
            let base = a.im.atan2(a.re) / kf;
            let roots: Vec<C> = (0..k).map(|j| { let t = base + 2.0 * std::f64::consts::PI * j as f64 / kf; g + C::new(radius * t.cos(), radius * t.sin()) }).collect();
            let mut hit = vec![false; k];
            for (_, off) in new {
                let w = z[*from] + *off;
                let (j, e) = (0..k).map(|j| (j, (w - roots[j]).abs())).fold((0, f64::INFINITY), |x, y| if y.1 < x.1 { y } else { x });
                assert!(e <= 1e-5 * radius, "K = {k}, rho = {rho}: {e:e} from the nearest root of radius {radius:e}");
                hit[j] = true;
            }
            assert!(hit.iter().all(|&h| h), "K = {k}: every root of the model is reached once");
            // a component with too little room around it is left to the sweep
            let wide: Vec<f64> = (0..m).map(|i| if i < k { 0.2 } else { 0.0 }).collect();
            assert!(cluster_moves(m, &wide, &dist, &vals, &diff, ldexp(1.0, -30)).is_empty());
        }
    }

    #[test]
    fn multiprecision_cursor_gives_the_radius_of_a_distant_cluster() {
        // S = ((c w - p)^K - 1) (w - 2) (w + 3): K roots on a circle of radius 1/c around g = p/c = 0.7
        let pmul = |a: &GPoly, b: &GPoly| -> GPoly {
            let mut r = vec![(BigInt::zero(), BigInt::zero()); a.len() + b.len() - 1];
            for (i, x) in a.iter().enumerate() {
                for (j, y) in b.iter().enumerate() {
                    r[i + j].0 += &x.0 * &y.0 - &x.1 * &y.1;
                    r[i + j].1 += &x.0 * &y.1 + &x.1 * &y.0;
                }
            }
            r
        };
        let int = |v: i128| (BigInt::from(v), BigInt::zero());
        for &(k, digits) in &[(2usize, 12u32), (3, 12), (5, 30), (5, 9)] {
            let c = BigInt::from(10).pow(digits);
            let p7: BigInt = &c * 7 / 10;
            let lin: GPoly = vec![(c.clone(), BigInt::zero()), (-p7, BigInt::zero())];
            let mut pw: GPoly = vec![int(1)];
            for _ in 0..k {
                pw = pmul(&pw, &lin);
            }
            let last = pw.len() - 1;
            pw[last].0 -= 1;
            let ci = pmul(&pmul(&pw, &vec![int(1), int(-2)]), &vec![int(1), int(3)]);
            let bp = BallPoly::new(&ci, true);
            let z = ZP::from_c(C::new(0.701, 0.0005));
            let (o1, o2) = (ZP::from_c(C::new(2.0, 0.0)), ZP::from_c(C::new(-3.0, 0.0)));
            // the cursor is (1/(c u))^K: enough bits for it, then too few
            let tau = k as f64 * (digits as f64 * 10f64.log2() + (0.701f64 - 0.7).hypot(0.0005).log2());
            let md = cluster_model(&bp, &z, &[&o1, &o2], k, tau as u64 + 80, 16384).expect("a model");
            assert!(md.significant, "K = {k}: log2 |t| = {}, noise {}", md.lt, md.noise);
            assert!((md.lt + tau).abs() < 1e-6 * tau.max(1.0) + 1e-6, "K = {k}: log2 |t| = {} against {}", md.lt, -tau);
            // the anchor is the centre: |z - u - 0.7| is far below the radius 1/c
            let g = z.sub(&md.u).to_c();
            let radius = 10f64.powi(-(digits as i32));
            assert!((g - C::new(0.7, 0.0)).abs() < 1e-3 * radius.max(1e-16) + 4e-16, "K = {k}: anchor {g:?}");
            let (scale, _) = md.radius(k);
            assert!((scale * md.u.to_c().abs() / radius - 1.0).abs() < 1e-6, "K = {k}: radius {:e}", scale * md.u.to_c().abs());
            // with too few bits the cursor is not trusted, and the bound of the radius is above the radius
            let few = cluster_model(&bp, &z, &[&o1, &o2], k, 40, 16384).expect("a model");
            assert!(!few.significant && few.radius(k).0 * few.u.to_c().abs() > radius, "K = {k}");
        }
    }

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
