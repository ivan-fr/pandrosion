//! Fixed-width integers on preallocated limbs, for the inner loop of the ball evaluation.
//!
//! The dense Horner scheme of `precise::BallPoly::eval` makes about twelve big multiplications per
//! coefficient, on numbers of a few hundred bits.  With `num-bigint` each of them allocates its result, and
//! below a thousand bits the allocation and the bookkeeping cost more than the multiplication.  Here the
//! numbers live in buffers allocated once per evaluation.
//!
//! Numbers are in sign-magnitude form: a flag and a slice of 64-bit limbs, least significant first, of a
//! width fixed for the whole evaluation.  Every operation computes exactly the integer that the `BigInt`
//! code computes (products are exact, shifts round towards minus infinity like `BigInt >> k`), or reports
//! that the result does not fit the width, in which case the caller falls back to `BigInt`.  The results
//! are therefore identical to those of the `BigInt` loop, bit for bit, and the error bound of the ball
//! evaluation is unchanged.
use num_bigint::{BigInt, BigUint, Sign};

/// Above this number of fractional bits the `BigInt` loop is used (its multiplication is subquadratic).
pub(crate) const MAX_BITS: u64 = 2048;

#[inline]
fn is_zero(a: &[u64]) -> bool {
    a.iter().all(|&x| x == 0)
}
#[inline]
fn len(a: &[u64]) -> usize {
    let mut n = a.len();
    while n > 0 && a[n - 1] == 0 {
        n -= 1;
    }
    n
}

/// out = a * b (out.len() == a.len() + b.len()), schoolbook.
fn mul_mag(a: &[u64], b: &[u64], out: &mut [u64]) {
    out.fill(0);
    let (la, lb) = (len(a), len(b));
    // the low limbs of b that are zero are skipped: a point with 53 bits has one or two non-zero limbs,
    // and the product then costs a few passes over a instead of len(b) of them
    let lo = b[..lb].iter().position(|&x| x != 0).unwrap_or(lb);
    for i in 0..la {
        let x = a[i] as u128;
        if x == 0 {
            continue;
        }
        let mut carry = 0u128;
        for j in lo..lb {
            let t = x * b[j] as u128 + out[i + j] as u128 + carry;
            out[i + j] = t as u64;
            carry = t >> 64;
        }
        out[i + lb] = carry as u64;
    }
}

/// a >= b, as magnitudes of the same width.
fn ge_mag(a: &[u64], b: &[u64]) -> bool {
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return a[i] > b[i];
        }
    }
    true
}
/// acc += b; returns the carry out.
fn add_mag(acc: &mut [u64], b: &[u64]) -> bool {
    let mut carry = false;
    for i in 0..acc.len() {
        let (s, c1) = acc[i].overflowing_add(b[i]);
        let (s, c2) = s.overflowing_add(carry as u64);
        acc[i] = s;
        carry = c1 | c2;
    }
    carry
}
/// acc = acc - b (acc >= b).
fn sub_mag(acc: &mut [u64], b: &[u64]) {
    let mut borrow = false;
    for i in 0..acc.len() {
        let (s, b1) = acc[i].overflowing_sub(b[i]);
        let (s, b2) = s.overflowing_sub(borrow as u64);
        acc[i] = s;
        borrow = b1 | b2;
    }
}
/// acc = b - acc (b >= acc).
fn rsub_mag(acc: &mut [u64], b: &[u64]) {
    let mut borrow = false;
    for i in 0..acc.len() {
        let (s, b1) = b[i].overflowing_sub(acc[i]);
        let (s, b2) = s.overflowing_sub(borrow as u64);
        acc[i] = s;
        borrow = b1 | b2;
    }
}

/// (neg, acc) += (bn, b), numbers of the same width.  Returns false if the sum does not fit.
fn add_signed(neg: &mut bool, acc: &mut [u64], bn: bool, b: &[u64]) -> bool {
    if *neg == bn {
        if add_mag(acc, b) {
            return false;
        }
    } else if ge_mag(acc, b) {
        sub_mag(acc, b);
    } else {
        rsub_mag(acc, b);
        *neg = bn;
    }
    if is_zero(acc) {
        *neg = false;
    }
    true
}

/// dst = floor((neg, src) / 2^k): the quotient towards minus infinity, as `BigInt >> k`.  Returns the sign
/// of the result, or None if it does not fit `dst`.
fn shr_floor(neg: bool, src: &[u64], k: u64, dst: &mut [u64]) -> Option<bool> {
    let (w, s) = ((k / 64) as usize, (k % 64) as u32);
    for i in 0..dst.len() {
        let lo = src.get(i + w).copied().unwrap_or(0);
        let hi = src.get(i + w + 1).copied().unwrap_or(0);
        dst[i] = if s == 0 { lo } else { (lo >> s) | (hi << (64 - s)) };
    }
    // what is left above the width of dst must be zero
    let top = dst.len() + w;
    if top < src.len() {
        if s != 0 && src[top] >> s != 0 {
            return None;
        }
        if s == 0 && src[top] != 0 {
            return None;
        }
        if src[top + 1..].iter().any(|&x| x != 0) {
            return None;
        }
    }
    if neg {
        // floor(-a / 2^k) = -ceil(a / 2^k): one more if a bit was dropped
        let dropped = src[..w.min(src.len())].iter().any(|&x| x != 0) || (s != 0 && w < src.len() && src[w] & ((1u64 << s) - 1) != 0);
        if dropped {
            let mut carry = true;
            for x in dst.iter_mut() {
                let (v, c) = x.overflowing_add(carry as u64);
                *x = v;
                carry = c;
                if !carry {
                    break;
                }
            }
            if carry {
                return None;
            }
        }
    }
    Some(neg && !is_zero(dst))
}

/// A number of a fixed width.
struct Num {
    neg: bool,
    mag: Vec<u64>,
}
impl Num {
    fn zero(n: usize) -> Num {
        Num { neg: false, mag: vec![0; n] }
    }
    /// None if the integer does not fit n limbs.
    fn load(x: &BigInt, n: usize) -> Option<Num> {
        let mut r = Num::zero(n);
        r.set(x).then_some(r)
    }
    fn set(&mut self, x: &BigInt) -> bool {
        self.mag.fill(0);
        for (i, d) in x.iter_u64_digits().enumerate() {
            if i >= self.mag.len() {
                return false;
            }
            self.mag[i] = d;
        }
        self.neg = x.sign() == Sign::Minus;
        true
    }
    fn to_bigint(&self) -> BigInt {
        let digits: Vec<u32> = self.mag[..len(&self.mag)].iter().flat_map(|&d| [d as u32, (d >> 32) as u32]).collect();
        let m = BigUint::new(digits);
        BigInt::from_biguint(if self.neg { Sign::Minus } else { Sign::Plus }, m)
    }
}

/// Scratch space for the products (twice the width of the widest factor, plus the widest of the two).
struct Work {
    p: Vec<u64>,
    q: Vec<u64>,
}

/// out += a * b (out.len() == a.len() + b.len()); returns the carry out.
fn mul_acc(a: &[u64], b: &[u64], out: &mut [u64]) -> bool {
    let (la, lb) = (len(a), len(b));
    let lo = b[..lb].iter().position(|&x| x != 0).unwrap_or(lb);
    let mut over = false;
    for i in 0..la {
        let x = a[i] as u128;
        if x == 0 {
            continue;
        }
        let mut carry = 0u128;
        for j in lo..lb {
            let t = x * b[j] as u128 + out[i + j] as u128 + carry;
            out[i + j] = t as u64;
            carry = t >> 64;
        }
        // the carry goes up as far as it has to
        let mut k = i + lb;
        let mut c = carry as u64;
        while c != 0 {
            if k == out.len() {
                over = true;
                break;
            }
            let (s, o) = out[k].overflowing_add(c);
            out[k] = s;
            c = o as u64;
            k += 1;
        }
    }
    over
}

/// dst = floor((a b + sgn c d) / 2^k), sgn = -1 if `minus`.  False if the result does not fit dst.
#[inline]
fn combine(a: &Num, b: &Num, c: &Num, d: &Num, minus: bool, k: u64, w: &mut Work, dst: &mut Num) -> bool {
    let n = a.mag.len() + b.mag.len();
    let (p, q) = (&mut w.p[..n], &mut w.q[..n]);
    mul_mag(&a.mag, &b.mag, p);
    let mut neg = a.neg != b.neg;
    let qn = (c.neg != d.neg) != minus;
    if neg == qn {
        // same sign: the second product is accumulated on the first (a carry out is an overflow)
        if mul_acc(&c.mag, &d.mag, p) {
            return false;
        }
    } else {
        // opposite signs: p - q modulo 2^(64 n); a borrow out means q > p, and the difference is negated
        mul_mag(&c.mag, &d.mag, q);
        let mut borrow = false;
        for i in 0..n {
            let (s, b1) = p[i].overflowing_sub(q[i]);
            let (s, b2) = s.overflowing_sub(borrow as u64);
            p[i] = s;
            borrow = b1 | b2;
        }
        if borrow {
            let mut carry = true;
            for x in p.iter_mut() {
                let (v, c1) = (!*x).overflowing_add(carry as u64);
                *x = v;
                carry = c1;
            }
            neg = qn;
        }
    }
    match shr_floor(neg, p, k, &mut dst.mag) {
        Some(s) => {
            dst.neg = s;
            true
        }
        None => false,
    }
}

/// The dense Horner scheme of the ball evaluation, on fixed-width numbers.
///
/// With x = (xr, xi) in units of 2^-f and x12 = (xr12, xi12) in units of 2^-(f - c12), runs, for the
/// coefficients c_j in the order given by `rev`:
///
/// ```text
/// p2 <- floor(p2 x12 / 2^(f - c12)) + p1
/// p1 <- floor(p1 x12 / 2^(f - c12)) + floor(p0 / 2^c12)
/// p0 <- floor(p0 x / 2^f) + c_j
/// ```
///
/// (each floor taken on the real and on the imaginary part) and returns (p0, p1, p2): exactly the integers
/// of the `BigInt` loop.  None if a number does not fit the width chosen for it; the caller then runs the
/// `BigInt` loop.
#[allow(clippy::too_many_arguments)]
pub(crate) fn horner3(
    c: &[(BigInt, BigInt)],
    rev: bool,
    xr: &BigInt,
    xi: &BigInt,
    f: u64,
    c12: u64,
    xr12: &BigInt,
    xi12: &BigInt,
) -> Option<[(BigInt, BigInt); 3]> {
    if f > MAX_BITS || c.is_empty() {
        return None;
    }
    let f12 = f - c12;
    // room for the fractional bits and for an integer part of 64 bits (the values of S, S', S'' on the unit
    // disc are below (m + 1)^3 times the largest coefficient; a larger value is reported as an overflow)
    let n = (f as usize + 64).div_ceil(64);
    let n12 = (f12 as usize + 64).div_ceil(64);
    let (xr, xi) = (Num::load(xr, n)?, Num::load(xi, n)?);
    let (xr12, xi12) = (Num::load(xr12, n12)?, Num::load(xi12, n12)?);
    let mut w = Work { p: vec![0; 2 * n], q: vec![0; 2 * n] };
    let (mut p0r, mut p0i) = (Num::zero(n), Num::zero(n));
    let (mut p1r, mut p1i, mut p2r, mut p2i) = (Num::zero(n12), Num::zero(n12), Num::zero(n12), Num::zero(n12));
    let (mut tr, mut ti) = (Num::zero(n), Num::zero(n));
    let (mut ur, mut ui) = (Num::zero(n12), Num::zero(n12));
    let (mut cr, mut cim) = (Num::zero(n), Num::zero(n));
    let m = c.len() - 1;
    for j in 0..=m {
        let cj = if rev { &c[m - j] } else { &c[j] };
        // p2 <- p2 x12 + p1
        if !combine(&p2r, &xr12, &p2i, &xi12, true, f12, &mut w, &mut ur) || !combine(&p2r, &xi12, &p2i, &xr12, false, f12, &mut w, &mut ui) {
            return None;
        }
        std::mem::swap(&mut p2r, &mut ur);
        std::mem::swap(&mut p2i, &mut ui);
        if !add_signed(&mut p2r.neg, &mut p2r.mag, p1r.neg, &p1r.mag) || !add_signed(&mut p2i.neg, &mut p2i.mag, p1i.neg, &p1i.mag) {
            return None;
        }
        // p1 <- p1 x12 + (p0 >> c12)
        if !combine(&p1r, &xr12, &p1i, &xi12, true, f12, &mut w, &mut ur) || !combine(&p1r, &xi12, &p1i, &xr12, false, f12, &mut w, &mut ui) {
            return None;
        }
        std::mem::swap(&mut p1r, &mut ur);
        std::mem::swap(&mut p1i, &mut ui);
        ur.neg = shr_floor(p0r.neg, &p0r.mag, c12, &mut ur.mag)?;
        ui.neg = shr_floor(p0i.neg, &p0i.mag, c12, &mut ui.mag)?;
        if !add_signed(&mut p1r.neg, &mut p1r.mag, ur.neg, &ur.mag) || !add_signed(&mut p1i.neg, &mut p1i.mag, ui.neg, &ui.mag) {
            return None;
        }
        // p0 <- p0 x + c_j
        if !combine(&p0r, &xr, &p0i, &xi, true, f, &mut w, &mut tr) || !combine(&p0r, &xi, &p0i, &xr, false, f, &mut w, &mut ti) {
            return None;
        }
        std::mem::swap(&mut p0r, &mut tr);
        std::mem::swap(&mut p0i, &mut ti);
        if !cr.set(&cj.0) || !cim.set(&cj.1) {
            return None;
        }
        if !add_signed(&mut p0r.neg, &mut p0r.mag, cr.neg, &cr.mag) || !add_signed(&mut p0i.neg, &mut p0i.mag, cim.neg, &cim.mag) {
            return None;
        }
    }
    Some([(p0r.to_bigint(), p0i.to_bigint()), (p1r.to_bigint(), p1i.to_bigint()), (p2r.to_bigint(), p2i.to_bigint())])
}

/// The same scheme with `BigInt` (the loop of versions up to 0.6.0): the reference, and the fallback.
#[allow(clippy::too_many_arguments)]
pub(crate) fn horner3_big(
    c: &[(BigInt, BigInt)],
    rev: bool,
    xr: &BigInt,
    xi: &BigInt,
    f: u64,
    c12: u64,
    xr12: &BigInt,
    xi12: &BigInt,
) -> [(BigInt, BigInt); 3] {
    let f12 = f - c12;
    let zero = || (BigInt::from(0), BigInt::from(0));
    let (mut p0, mut p1, mut p2) = (zero(), zero(), zero());
    let mul = |p: &(BigInt, BigInt)| -> (BigInt, BigInt) { ((&p.0 * xr - &p.1 * xi) >> f, (&p.0 * xi + &p.1 * xr) >> f) };
    let mul12 = |p: &(BigInt, BigInt)| -> (BigInt, BigInt) { ((&p.0 * xr12 - &p.1 * xi12) >> f12, (&p.0 * xi12 + &p.1 * xr12) >> f12) };
    let m = c.len() - 1;
    for j in 0..=m {
        let cj = if rev { &c[m - j] } else { &c[j] };
        let (a2, a1, a0) = (mul12(&p2), mul12(&p1), mul(&p0));
        p2 = (a2.0 + &p1.0, a2.1 + &p1.1);
        p1 = if c12 == 0 { (a1.0 + &p0.0, a1.1 + &p0.1) } else { (a1.0 + (&p0.0 >> c12), a1.1 + (&p0.1 >> c12)) };
        p0 = (a0.0 + &cj.0, a0.1 + &cj.1);
    }
    [p0, p1, p2]
}

#[cfg(test)]
mod tests {
    use super::*;

    fn next(state: &mut u64) -> u64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        *state
    }
    /// A random integer of at most `bits` bits, of either sign, sometimes zero or with long runs of bits.
    fn random(state: &mut u64, bits: u64) -> BigInt {
        let kind = next(state) % 16;
        if kind == 0 {
            return BigInt::from(0);
        }
        let mut x = BigInt::from(0);
        for _ in 0..(bits / 64 + 1) {
            let d = match kind {
                1 => u64::MAX,
                2 => 0,
                _ => next(state),
            };
            x = (x << 64u32) + BigInt::from(d);
        }
        if kind == 2 {
            x += BigInt::from(1);
        }
        x >>= (x.bits().saturating_sub(bits.max(1) - next(state) % bits.max(1))) as u64;
        if next(state) & 1 == 1 { -x } else { x }
    }

    #[test]
    fn floor_shift_and_signed_sum_match_bigint() {
        let mut st = 0x9e3779b97f4a7c15u64;
        for t in 0..20000u64 {
            let (a, b) = (random(&mut st, 1 + t % 300), random(&mut st, 1 + (t * 7) % 300));
            let k = next(&mut st) % 200;
            let n = 6;
            let (x, y) = (Num::load(&a, n).unwrap(), Num::load(&b, n).unwrap());
            let mut d = Num::zero(n);
            d.neg = shr_floor(x.neg, &x.mag, k, &mut d.mag).unwrap();
            assert_eq!(d.to_bigint(), &a >> k, "shift {a} by {k}");
            let mut s = Num::load(&a, n).unwrap();
            assert!(add_signed(&mut s.neg, &mut s.mag, y.neg, &y.mag));
            assert_eq!(s.to_bigint(), &a + &b);
            let mut w = Work { p: vec![0; 2 * n], q: vec![0; 2 * n] };
            let mut r = Num::zero(2 * n);
            for minus in [false, true] {
                assert!(combine(&x, &y, &y, &x, minus, k, &mut w, &mut r));
                let exact: BigInt = if minus { BigInt::from(0) } else { (&a * &b * 2) >> k };
                assert_eq!(r.to_bigint(), exact);
            }
        }
    }

    #[test]
    fn overflow_is_reported() {
        let big = BigInt::from(1) << 200u32;
        assert!(Num::load(&big, 3).is_none() && Num::load(&big, 4).is_some());
        let x = Num::load(&((BigInt::from(1) << 128u32) - 1), 2).unwrap();
        let mut s = Num::load(&BigInt::from(1), 2).unwrap();
        assert!(!add_signed(&mut s.neg, &mut s.mag, x.neg, &x.mag));
        let mut d = Num::zero(1);
        assert!(shr_floor(false, &x.mag, 10, &mut d.mag).is_none());
        assert!(shr_floor(false, &x.mag, 64, &mut d.mag).is_some());
        // -(2^64 - 1) - 1/2 rounds to -2^64, which does not fit one limb
        let v: BigInt = (BigInt::from(1) << 65u32) - 1;
        let y = Num::load(&-v, 2).unwrap();
        assert!(shr_floor(true, &y.mag, 1, &mut d.mag).is_none());
    }

    #[test]
    fn horner_matches_the_bigint_loop() {
        let mut st = 0x2545f4914f6cdd1du64;
        let mut fast = 0;
        for t in 0..1500u64 {
            let f = 64 + next(&mut st) % 700;
            let c12 = if t % 3 == 0 { 0 } else { next(&mut st) % (f - 63) };
            let m = 1 + (next(&mut st) % 40) as usize;
            // coefficients below 1.5 in modulus, a point of the unit disc (sometimes on its boundary)
            let c: Vec<(BigInt, BigInt)> = (0..=m).map(|_| (random(&mut st, f), if t % 4 == 0 { BigInt::from(0) } else { random(&mut st, f) })).collect();
            let one = BigInt::from(1) << f;
            let (xr, xi): (BigInt, BigInt) = match t % 6 {
                0 => (one.clone(), BigInt::from(0)),
                1 => (-one.clone(), BigInt::from(0)),
                2 => (BigInt::from(0), one.clone()),
                3 => ((random(&mut st, 53) << (f - 60)), (random(&mut st, 53) << (f - 60))),
                _ => (random(&mut st, f - 1), random(&mut st, f - 1)),
            };
            let (xr12, xi12): (BigInt, BigInt) = (&xr >> c12, &xi >> c12);
            let slow = horner3_big(&c, t % 2 == 0, &xr, &xi, f, c12, &xr12, &xi12);
            if let Some(got) = horner3(&c, t % 2 == 0, &xr, &xi, f, c12, &xr12, &xi12) {
                assert_eq!(got, slow, "case {t}: f = {f}, c12 = {c12}, m = {m}");
                fast += 1;
            }
        }
        assert!(fast > 1400, "the fixed-width loop gave up too often: {fast}");
    }
}
