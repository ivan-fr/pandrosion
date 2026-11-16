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
    // the limbs of src from w on, as many as dst takes; the rest of dst is zero
    let live = &src[w.min(src.len())..];
    let cnt = live.len().min(dst.len());
    if s == 0 {
        dst[..cnt].copy_from_slice(&live[..cnt]);
    } else {
        for i in 0..cnt {
            let hi = if i + 1 < live.len() { live[i + 1] } else { 0 };
            dst[i] = (live[i] >> s) | (hi << (64 - s));
        }
    }
    dst[cnt..].fill(0);
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

/// A complex multiplier with few bits: (re + i im) 2^sh, |re| and |im| below 2^62 (version 0.13.0).
///
/// The points of the stage that follows the double precision one are doubles rounded to 53 bits of their
/// modulus (`exact::quantize`): in units of 2^-F their two coordinates are integers of 53 bits at most
/// times one power of two.  The product of an accumulator by such a point is then one pass over its limbs
/// with two multiplications each, instead of two full products, a subtraction and a shift over twice the
/// width (`combine`).
#[derive(Clone, Copy)]
struct Short {
    re: u64,
    im: u64,
    re_neg: bool,
    im_neg: bool,
    sh: u64,
}
impl Short {
    /// None if the two coordinates do not fit 62 bits once their common power of two is taken out.
    fn new(xr: &BigInt, xi: &BigInt) -> Option<Short> {
        let sh = match (xr.trailing_zeros(), xi.trailing_zeros()) {
            (Some(a), Some(b)) => a.min(b),
            (Some(a), None) | (None, Some(a)) => a,
            (None, None) => 0,
        };
        let part = |x: &BigInt| -> Option<u64> {
            let m = x.magnitude() >> sh;
            if m.bits() > 62 { None } else { Some(m.iter_u64_digits().next().unwrap_or(0)) }
        };
        Some(Short { re: part(xr)?, im: part(xi)?, re_neg: xr.sign() == Sign::Minus, im_neg: xi.sign() == Sign::Minus, sh })
    }
}

/// dst = floor((a xa + sgn b xb) 2^sh / 2^k) with sgn = -1 if `minus`, for multipliers xa, xb below 2^62 with
/// the signs `xa_neg`, `xb_neg`: the same integer as `combine` on the full numbers xa 2^sh and xb 2^sh
/// (the sum a xa + sgn b xb is exact on one limb more than a, and floor(T 2^sh / 2^k) = floor(T / 2^(k - sh))).
/// False if the result does not fit dst, or if sh > k.
#[inline]
#[allow(clippy::too_many_arguments)]
fn combine_short(a: &Num, xa: u64, xa_neg: bool, b: &Num, xb: u64, xb_neg: bool, minus: bool, sh: u64, k: u64, w: &mut Work, dst: &mut Num) -> bool {
    if sh > k {
        return false;
    }
    let n = a.mag.len();
    let (am, bm) = (&a.mag[..n], &b.mag[..n]);
    let p = &mut w.p[..n + 1];
    let (sa, sb) = (a.neg != xa_neg, (b.neg != xb_neg) != minus);
    let neg;
    if sa == sb {
        // each term is below 2^126 and the carry below 2^63: the sum fits 128 bits
        let (xa, xb) = (xa as u128, xb as u128);
        let mut carry = 0u128;
        for i in 0..n {
            let t = am[i] as u128 * xa + bm[i] as u128 * xb + carry;
            p[i] = t as u64;
            carry = t >> 64;
        }
        p[n] = carry as u64;
        neg = sa;
    } else {
        // the difference in two's complement on n + 1 limbs; a negative one is negated
        let (xa, xb) = (xa as i128, xb as i128);
        let mut carry = 0i128;
        for i in 0..n {
            let t = am[i] as i128 * xa - bm[i] as i128 * xb + carry;
            p[i] = t as u64;
            carry = t >> 64;
        }
        p[n] = carry as u64;
        if carry < 0 {
            let mut c = true;
            for x in p.iter_mut() {
                let (v, c1) = (!*x).overflowing_add(c as u64);
                *x = v;
                c = c1;
            }
            neg = sb;
        } else {
            neg = sa;
        }
    }
    match shr_floor(neg, p, k - sh, &mut dst.mag) {
        Some(s) => {
            dst.neg = s;
            true
        }
        None => false,
    }
}

// ---- The same scheme in two's complement, for short multipliers (version 0.14.0) -----------------------
//
// With a short multiplier every step is "multiply two numbers by two small signed integers, add, shift
// right, add a third number".  In sign and magnitude each of these looks at the signs, compares
// magnitudes and may negate; in two's complement none does: the products are accumulated with a signed
// carry, and the shift that fills with the sign bit is the quotient towards minus infinity, which is the
// rounding of `BigInt >> k`.  The integers are the same; a number that does not fit its width (one bit
// less than in sign and magnitude) is reported, and the caller falls back on the loop above.

/// x as n limbs in two's complement; false if it does not fit (|x| must be below 2^(64 n - 1)).
fn tc_load(x: &BigInt, dst: &mut [u64]) -> bool {
    let n = dst.len();
    if x.bits() > 64 * n as u64 - 1 {
        return false;
    }
    dst.fill(0);
    for (i, d) in x.iter_u64_digits().enumerate() {
        dst[i] = d;
    }
    if x.sign() == Sign::Minus {
        let mut carry = true;
        for v in dst.iter_mut() {
            let (w, c) = (!*v).overflowing_add(carry as u64);
            *v = w;
            carry = c;
        }
    }
    true
}
fn tc_to_bigint(a: &[u64]) -> BigInt {
    let neg = (a[a.len() - 1] as i64) < 0;
    let mut mag: Vec<u64> = a.to_vec();
    if neg {
        let mut carry = true;
        for v in mag.iter_mut() {
            let (w, c) = (!*v).overflowing_add(carry as u64);
            *v = w;
            carry = c;
        }
    }
    let digits: Vec<u32> = mag[..len(&mag)].iter().flat_map(|&d| [d as u32, (d >> 32) as u32]).collect();
    BigInt::from_biguint(if neg { Sign::Minus } else { Sign::Plus }, BigUint::new(digits))
}
/// dst = floor(src / 2^k), src and dst in two's complement (dst.len() <= src.len() + 1).  False if the
/// quotient does not fit dst.
#[inline(always)]
fn tc_shr(src: &[u64], k: u64, dst: &mut [u64]) -> bool {
    let (w, s) = ((k / 64) as usize, (k % 64) as u32);
    let ext = if (src[src.len() - 1] as i64) < 0 { u64::MAX } else { 0 };
    let n = dst.len();
    let at = |i: usize| if i < src.len() { src[i] } else { ext };
    if s == 0 {
        for i in 0..n {
            dst[i] = at(i + w);
        }
    } else {
        for i in 0..n {
            dst[i] = (at(i + w) >> s) | (at(i + w + 1) << (64 - s));
        }
    }
    // what is above dst must be the sign of dst, limb after limb
    if ((dst[n - 1] as i64) < 0) != (ext != 0) {
        return false;
    }
    for i in n + w..src.len() {
        let v = if s == 0 { at(i) } else { (at(i) >> s) | (at(i + 1) << (64 - s)) };
        if v != ext {
            return false;
        }
    }
    true
}
/// acc += b in two's complement (same width); false on overflow.
#[inline(always)]
fn tc_add(acc: &mut [u64], b: &[u64]) -> bool {
    let n = acc.len();
    let (sa, sb) = ((acc[n - 1] as i64) < 0, (b[n - 1] as i64) < 0);
    let mut carry = false;
    for i in 0..n {
        let (v, c1) = acc[i].overflowing_add(b[i]);
        let (v, c2) = v.overflowing_add(carry as u64);
        acc[i] = v;
        carry = c1 | c2;
    }
    sa != sb || ((acc[n - 1] as i64) < 0) == sa
}
/// dst = floor((a xa + b xb) / 2^k) for a, b in two's complement of the same width and |xa|, |xb| < 2^62;
/// `tmp` has one limb more than a.  False if the result does not fit dst.
#[inline(always)]
fn tc_mul2_shr(a: &[u64], xa: i64, b: &[u64], xb: i64, k: u64, tmp: &mut [u64], dst: &mut [u64]) -> bool {
    let n = a.len();
    let (b, tmp) = (&b[..n], &mut tmp[..n + 1]);
    let (xa, xb) = (xa as i128, xb as i128);
    let mut carry = 0i128;
    // the low limbs are unsigned, the top one carries the sign; each term is below 2^126 in modulus and
    // the carry below 2^63
    for i in 0..n - 1 {
        let t = a[i] as i128 * xa + b[i] as i128 * xb + carry;
        tmp[i] = t as u64;
        carry = t >> 64;
    }
    let t = (a[n - 1] as i64) as i128 * xa + (b[n - 1] as i64) as i128 * xb + carry;
    tmp[n - 1] = t as u64;
    tmp[n] = (t >> 64) as u64;
    tc_shr(tmp, k, dst)
}

/// dst = floor((a xa + b xb) / 2^k) + add, the three operations of a step in one pass when the shift is
/// below one limb (the usual case: the bits of a double precision point of the unit disc are at the top of
/// its F bits).  The limbs of the product come out from the lowest; each one completes a limb of the
/// quotient, to which the limb of `add` is added at once.  False if the result does not fit dst.
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn tc_step(a: &[u64], xa: i64, b: &[u64], xb: i64, k: u64, add: &[u64], tmp: &mut [u64], dst: &mut [u64]) -> bool {
    let n = a.len();
    if k == 0 || k >= 64 || n < 2 {
        return tc_mul2_shr(a, xa, b, xb, k, tmp, dst) && tc_add(dst, add);
    }
    let (b, add, dst) = (&b[..n], &add[..n], &mut dst[..n]);
    let s = k as u32;
    let (xa, xb) = (xa as i128, xb as i128);
    let t = a[0] as i128 * xa + b[0] as i128 * xb;
    let (mut prev, mut carry, mut cadd) = (t as u64, t >> 64, false);
    for i in 1..n - 1 {
        let t = a[i] as i128 * xa + b[i] as i128 * xb + carry;
        carry = t >> 64;
        let v = (prev >> s) | ((t as u64) << (64 - s));
        prev = t as u64;
        let (v, c1) = v.overflowing_add(add[i - 1]);
        let (v, c2) = v.overflowing_add(cadd as u64);
        dst[i - 1] = v;
        cadd = c1 | c2;
    }
    // the top limbs carry the sign
    let t = (a[n - 1] as i64) as i128 * xa + (b[n - 1] as i64) as i128 * xb + carry;
    let top = (t >> 64) as i64; // limb n of the product
    let v = (prev >> s) | ((t as u64) << (64 - s));
    let (v, c1) = v.overflowing_add(add[n - 2]);
    let (v, c2) = v.overflowing_add(cadd as u64);
    dst[n - 2] = v;
    cadd = c1 | c2;
    let q = ((t as u64) >> s) | ((top as u64) << (64 - s)); // limb n - 1 of the quotient
    // the quotient fits n limbs if what is above is its sign
    if (top >> s) != ((q as i64) >> 63) {
        return false;
    }
    let (v, c1) = q.overflowing_add(add[n - 1]);
    let (v, _) = v.overflowing_add(cadd as u64);
    let _ = c1;
    dst[n - 1] = v;
    let (sq, sa) = ((q as i64) < 0, (add[n - 1] as i64) < 0);
    sq != sa || ((v as i64) < 0) == sq
}

/// The coefficients of a polynomial as limbs in two's complement: for each one its real part and its
/// imaginary part, `n` limbs each, n the width of the evaluation with F fractional bits.  Built once for
/// each F (the coefficients were loaded from `BigInt` at every step of every evaluation).
pub(crate) struct Table {
    n: usize,
    limbs: Vec<u64>,
}
impl Table {
    /// None if a coefficient does not fit the width.
    pub(crate) fn new(c: &[(BigInt, BigInt)], f: u64) -> Option<Table> {
        let n = (f as usize + 64).div_ceil(64);
        let mut limbs = vec![0u64; 2 * n * c.len()];
        for (j, co) in c.iter().enumerate() {
            let (re, im) = limbs[2 * n * j..2 * n * (j + 1)].split_at_mut(n);
            if !tc_load(&co.0, re) || !tc_load(&co.1, im) {
                return None;
            }
        }
        Some(Table { n, limbs })
    }
}

/// `horner3` for multipliers with few bits, in two's complement.  None if a number does not fit.
fn horner3_tc(c: &[(BigInt, BigInt)], table: Option<&Table>, rev: bool, x: Short, x12: Short, f: u64, c12: u64) -> Option<[(BigInt, BigInt); 3]> {
    let f12 = f - c12;
    if x.sh > f || x12.sh > f12 {
        return None;
    }
    let n = (f as usize + 64).div_ceil(64);
    let n12 = (f12 as usize + 64).div_ceil(64);
    let sg = |v: u64, neg: bool| if neg { -(v as i64) } else { v as i64 };
    let (xr, xi) = (sg(x.re, x.re_neg), sg(x.im, x.im_neg));
    let (yr, yi) = (sg(x12.re, x12.re_neg), sg(x12.im, x12.im_neg));
    let (k, k12) = (f - x.sh, f12 - x12.sh);
    let table = table.filter(|t| t.n == n && t.limbs.len() == 2 * n * c.len());
    // one buffer: p0 (2 n), the next p0 (2 n), the coefficient (2 n), p1, p2 and their next values (8 n12),
    // p0 shifted (2 n12), the product (n + 1)
    let mut buf = vec![0u64; 6 * n + 10 * n12 + n + 1];
    let (p0, rest) = buf.split_at_mut(2 * n);
    let (q0, rest) = rest.split_at_mut(2 * n);
    let (cj, rest) = rest.split_at_mut(2 * n);
    let (p1, rest) = rest.split_at_mut(2 * n12);
    let (q1, rest) = rest.split_at_mut(2 * n12);
    let (p2, rest) = rest.split_at_mut(2 * n12);
    let (q2, rest) = rest.split_at_mut(2 * n12);
    let (s0, tmp) = rest.split_at_mut(2 * n12);
    let (mut p0, mut q0, mut p1, mut q1, mut p2, mut q2) = (p0, q0, p1, q1, p2, q2);
    let m = c.len() - 1;
    for j in 0..=m {
        let co = if rev { &c[m - j] } else { &c[j] };
        {
            // p2 <- p2 x12 + p1
            let (ar, ai) = p2.split_at(n12);
            let (dr, di) = q2.split_at_mut(n12);
            if !tc_step(ar, yr, ai, -yi, k12, &p1[..n12], tmp, dr) || !tc_step(ar, yi, ai, yr, k12, &p1[n12..], tmp, di) {
                return None;
            }
        }
        std::mem::swap(&mut p2, &mut q2);
        {
            // p1 <- p1 x12 + (p0 >> c12)
            let (ar, ai) = p1.split_at(n12);
            let (dr, di) = q1.split_at_mut(n12);
            if c12 == 0 {
                // p0 has the width of p1 and is added as it is
                if !tc_step(ar, yr, ai, -yi, k12, &p0[..n], tmp, dr) || !tc_step(ar, yi, ai, yr, k12, &p0[n..], tmp, di) {
                    return None;
                }
            } else {
                let (sr, si) = s0.split_at_mut(n12);
                if !tc_shr(&p0[..n], c12, sr) || !tc_shr(&p0[n..], c12, si) {
                    return None;
                }
                if !tc_step(ar, yr, ai, -yi, k12, sr, tmp, dr) || !tc_step(ar, yi, ai, yr, k12, si, tmp, di) {
                    return None;
                }
            }
        }
        std::mem::swap(&mut p1, &mut q1);
        {
            // p0 <- p0 x + c_j
            let (ar, ai) = p0.split_at(n);
            let (dr, di) = q0.split_at_mut(n);
            let (cr, ci): (&[u64], &[u64]) = match table {
                Some(t) => {
                    let at = 2 * n * if rev { m - j } else { j };
                    t.limbs[at..at + 2 * n].split_at(n)
                }
                None => {
                    let (cr, ci) = cj.split_at_mut(n);
                    if !tc_load(&co.0, cr) || !tc_load(&co.1, ci) {
                        return None;
                    }
                    (cr, ci)
                }
            };
            if !tc_step(ar, xr, ai, -xi, k, cr, tmp, dr) || !tc_step(ar, xi, ai, xr, k, ci, tmp, di) {
                return None;
            }
        }
        std::mem::swap(&mut p0, &mut q0);
    }
    let pair = |p: &[u64], w: usize| (tc_to_bigint(&p[..w]), tc_to_bigint(&p[w..]));
    Some([pair(p0, n), pair(p1, n12), pair(p2, n12)])
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
pub(crate) fn horner3_table(
    c: &[(BigInt, BigInt)],
    table: Option<&Table>,
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
    // points with few bits (the doubles of the stage of exact values): one fused pass per product
    let (short, short12) = (Short::new(xr, xi), Short::new(xr12, xi12));
    if let (Some(a), Some(b)) = (short, short12) {
        if let Some(r) = horner3_tc(c, table, rev, a, b, f, c12) {
            return Some(r);
        }
    }
    let (xr, xi) = (Num::load(xr, n)?, Num::load(xi, n)?);
    let (xr12, xi12) = (Num::load(xr12, n12)?, Num::load(xi12, n12)?);
    let mut w = Work { p: vec![0; 2 * n + 1], q: vec![0; 2 * n] };
    let (mut p0r, mut p0i) = (Num::zero(n), Num::zero(n));
    let (mut p1r, mut p1i, mut p2r, mut p2i) = (Num::zero(n12), Num::zero(n12), Num::zero(n12), Num::zero(n12));
    let (mut tr, mut ti) = (Num::zero(n), Num::zero(n));
    let (mut ur, mut ui) = (Num::zero(n12), Num::zero(n12));
    let (mut cr, mut cim) = (Num::zero(n), Num::zero(n));
    let m = c.len() - 1;
    for j in 0..=m {
        let cj = if rev { &c[m - j] } else { &c[j] };
        // p2 <- p2 x12 + p1
        let ok = match short12 {
            Some(x) => combine_short(&p2r, x.re, x.re_neg, &p2i, x.im, x.im_neg, true, x.sh, f12, &mut w, &mut ur) && combine_short(&p2r, x.im, x.im_neg, &p2i, x.re, x.re_neg, false, x.sh, f12, &mut w, &mut ui),
            None => combine(&p2r, &xr12, &p2i, &xi12, true, f12, &mut w, &mut ur) && combine(&p2r, &xi12, &p2i, &xr12, false, f12, &mut w, &mut ui),
        };
        if !ok {
            return None;
        }
        std::mem::swap(&mut p2r, &mut ur);
        std::mem::swap(&mut p2i, &mut ui);
        if !add_signed(&mut p2r.neg, &mut p2r.mag, p1r.neg, &p1r.mag) || !add_signed(&mut p2i.neg, &mut p2i.mag, p1i.neg, &p1i.mag) {
            return None;
        }
        // p1 <- p1 x12 + (p0 >> c12)
        let ok = match short12 {
            Some(x) => combine_short(&p1r, x.re, x.re_neg, &p1i, x.im, x.im_neg, true, x.sh, f12, &mut w, &mut ur) && combine_short(&p1r, x.im, x.im_neg, &p1i, x.re, x.re_neg, false, x.sh, f12, &mut w, &mut ui),
            None => combine(&p1r, &xr12, &p1i, &xi12, true, f12, &mut w, &mut ur) && combine(&p1r, &xi12, &p1i, &xr12, false, f12, &mut w, &mut ui),
        };
        if !ok {
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
        let ok = match short {
            Some(x) => combine_short(&p0r, x.re, x.re_neg, &p0i, x.im, x.im_neg, true, x.sh, f, &mut w, &mut tr) && combine_short(&p0r, x.im, x.im_neg, &p0i, x.re, x.re_neg, false, x.sh, f, &mut w, &mut ti),
            None => combine(&p0r, &xr, &p0i, &xi, true, f, &mut w, &mut tr) && combine(&p0r, &xi, &p0i, &xr, false, f, &mut w, &mut ti),
        };
        if !ok {
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

/// `horner3_table` without a table (the tests).
#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn horner3(c: &[(BigInt, BigInt)], rev: bool, xr: &BigInt, xi: &BigInt, f: u64, c12: u64, xr12: &BigInt, xi12: &BigInt) -> Option<[(BigInt, BigInt); 3]> {
    horner3_table(c, None, rev, xr, xi, f, c12, xr12, xi12)
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
    fn short_multipliers_match_bigint() {
        let mut st = 0x1234567887654321u64;
        let mut used = 0;
        for t in 0..40000u64 {
            let n = 1 + (t % 6) as usize;
            let (a, b) = (random(&mut st, 64 * n as u64), random(&mut st, 64 * n as u64));
            // multipliers of 62 bits at most, sometimes zero, of either sign, times a common power of two
            let (ba, bb) = (1 + next(&mut st) % 62, 1 + next(&mut st) % 62);
            let (xa, xb) = (random(&mut st, ba), random(&mut st, bb));
            let sh = next(&mut st) % 130;
            let (x, y) = (Num::load(&a, n).unwrap(), Num::load(&b, n).unwrap());
            let short = Short::new(&(&xa << sh), &(&xb << sh)).unwrap();
            // the parts times the power of two taken out are the multipliers
            assert_eq!(BigInt::from(short.re) << short.sh, BigInt::from(xa.magnitude().clone()) << sh);
            assert_eq!(BigInt::from(short.im) << short.sh, BigInt::from(xb.magnitude().clone()) << sh);
            let k = short.sh + next(&mut st) % 200;
            let mut w = Work { p: vec![0; 2 * n + 1], q: vec![0; 2 * n] };
            let mut d = Num::zero(n + 1);
            for minus in [false, true] {
                let exact: BigInt = if minus { (&a * &xa - &b * &xb) << sh } else { (&a * &xa + &b * &xb) << sh };
                let exact: BigInt = exact >> k;
                let fits = exact.magnitude().bits() <= 64 * (n as u64 + 1);
                let ok = combine_short(&x, short.re, short.re_neg, &y, short.im, short.im_neg, minus, short.sh, k, &mut w, &mut d);
                assert_eq!(ok, fits, "case {t}");
                if ok {
                    assert_eq!(d.to_bigint(), exact, "case {t}: a = {a}, b = {b}, xa = {xa}, xb = {xb}, sh = {sh}, k = {k}, minus = {minus}");
                    used += 1;
                }
            }
        }
        assert!(used > 70000, "{used}");
        // too many bits: no short form
        assert!(Short::new(&((BigInt::from(1) << 70u32) + 1), &BigInt::from(1)).is_none());
        assert!(Short::new(&BigInt::from(0), &BigInt::from(0)).is_some());
    }

    #[test]
    fn two_complement_horner_matches_the_bigint_loop() {
        let mut st = 0x7f4a7c159e3779b9u64;
        let mut done = 0;
        for t in 0..3000u64 {
            let f = 64 + next(&mut st) % 700;
            let c12 = if t % 3 == 0 { 0 } else { next(&mut st) % (f - 63) };
            let m = 1 + (next(&mut st) % 40) as usize;
            let c: Vec<(BigInt, BigInt)> = (0..=m).map(|_| (random(&mut st, f), if t % 4 == 0 { BigInt::from(0) } else { random(&mut st, f) })).collect();
            // a point of the unit disc with few bits: two integers of 53 bits at most times a power of two,
            // of either sign, sometimes zero, sometimes 1 or i
            let sh = f - 54 - next(&mut st) % (f - 53).min(40);
            let one = BigInt::from(1) << f;
            let (xr, xi): (BigInt, BigInt) = match t % 7 {
                0 => (one.clone(), BigInt::from(0)),
                1 => (BigInt::from(0), -one.clone()),
                2 => (random(&mut st, 53) << sh, BigInt::from(0)),
                _ => {
                    let bits = 1 + next(&mut st) % 53;
                    (random(&mut st, 53) << sh, random(&mut st, bits) << sh)
                }
            };
            let (xr12, xi12): (BigInt, BigInt) = (&xr >> c12, &xi >> c12);
            let slow = horner3_big(&c, t % 2 == 0, &xr, &xi, f, c12, &xr12, &xi12);
            if let (Some(a), Some(b)) = (Short::new(&xr, &xi), Short::new(&xr12, &xi12)) {
                let table = if t % 5 < 3 { Table::new(&c, f) } else { None };
                if let Some(got) = horner3_tc(&c, table.as_ref(), t % 2 == 0, a, b, f, c12) {
                    assert_eq!(got, slow, "case {t}: f = {f}, c12 = {c12}, m = {m}");
                    done += 1;
                }
            }
            // and through the entry point, whatever path it takes
            if let Some(got) = horner3(&c, t % 2 == 0, &xr, &xi, f, c12, &xr12, &xi12) {
                assert_eq!(got, slow, "case {t} (entry point)");
            }
        }
        assert!(done > 2500, "the two's complement loop gave up too often: {done}");
        // the shift, the sum and the load at their limits
        let mut d = [0u64; 2];
        assert!(tc_load(&-(BigInt::from(1) << 126u32), &mut d) && !tc_load(&(BigInt::from(1) << 127u32), &mut d));
        let mut q = [0u64; 1];
        assert!(tc_load(&BigInt::from(-5), &mut d) && tc_shr(&d, 1, &mut q) && tc_to_bigint(&q) == BigInt::from(-3));
        assert!(tc_load(&(BigInt::from(1) << 70u32), &mut d) && !tc_shr(&d, 3, &mut q) && tc_shr(&d, 8, &mut q));
        let big = (BigInt::from(1) << 126u32) + 5;
        let (mut a, mut b) = ([0u64; 2], [0u64; 2]);
        assert!(tc_load(&big, &mut a) && tc_load(&big, &mut b) && !tc_add(&mut a, &b));
        assert!(tc_load(&big, &mut a) && tc_load(&-&big, &mut b) && tc_add(&mut a, &b) && tc_to_bigint(&a) == BigInt::from(0));
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
