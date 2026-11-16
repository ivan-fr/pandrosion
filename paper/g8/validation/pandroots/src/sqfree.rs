//! Square-free decomposition: a test modulo a prime (exact, cheap), and Yun's algorithm over the Gaussian
//! rationals when the test does not conclude.
use crate::complex::C;
use crate::exact::GPoly;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Zero};

const PRIMES: [(u64, u64); 3] = [(998244353, 3), (1004535809, 3), (469762049, 3)]; // p = 1 mod 4, primitive root

fn powmod(mut b: u64, mut e: u64, p: u64) -> u64 {
    let mut r = 1u64;
    b %= p;
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % p;
        }
        b = b * b % p;
        e >>= 1;
    }
    r
}
fn red(x: &BigInt, p: u64) -> u64 {
    // p < 2^31: the digits of 32 bits from the top, without a big integer for the remainder
    let mut r = 0u64;
    for d in x.iter_u32_digits().rev() {
        r = ((r << 32) | d as u64) % p;
    }
    if x.sign() == num_bigint::Sign::Minus && r != 0 { p - r } else { r }
}

/// True if S is certainly square-free: gcd(S, S') = 1 modulo a prime that does not divide the leading
/// coefficient.  False: not decided here.  (The primes are below 2^30: products fit in 64 bits.)
pub fn squarefree_mod_p(ci: &GPoly) -> bool {
    PRIMES.iter().any(|&(p, g)| {
        let r = powmod(g, (p - 1) / 4, p); // r^2 = -1
        euclid(ci.iter().map(|(x, y)| (red(x, p) + r * red(y, p)) % p).collect(), p)
    })
}

/// The same test for double precision coefficients taken as exact numbers (no big integers: a common power
/// of two is dropped, which changes nothing modulo an odd prime).
pub fn squarefree_mod_p_float(c: &[C]) -> bool {
    let dec = |v: f64| -> (u64, i64, bool) {
        let bits = v.to_bits();
        let ex = ((bits >> 52) & 0x7ff) as i64;
        let frac = bits & ((1u64 << 52) - 1);
        if ex == 0 { (frac, -1074, bits >> 63 != 0) } else { (frac | (1u64 << 52), ex - 1075, bits >> 63 != 0) }
    };
    let parts: Vec<[(u64, i64, bool); 2]> = c.iter().map(|x| [dec(x.re), dec(x.im)]).collect();
    let emin = parts.iter().flatten().filter(|t| t.0 != 0).map(|t| t.1).min().unwrap_or(0);
    let emax = parts.iter().flatten().filter(|t| t.0 != 0).map(|t| t.1).max().unwrap_or(0);
    let mut pow2: Vec<u64> = Vec::with_capacity((emax - emin + 1).max(1) as usize);
    PRIMES.iter().any(|&(p, g)| {
        let r = powmod(g, (p - 1) / 4, p);
        // the powers of two that the coefficients need, by doublings (one power per coefficient by
        // repeated squaring was most of this test for a polynomial of degree 20)
        pow2.clear();
        let mut v = 1u64;
        for _ in emin..=emax {
            pow2.push(v);
            v = if 2 * v >= p { 2 * v - p } else { 2 * v };
        }
        let one = |t: &(u64, i64, bool)| {
            if t.0 == 0 {
                return 0;
            }
            let v = (t.0 % p) * pow2[(t.1 - emin) as usize] % p;
            if t.2 { (p - v) % p } else { v }
        };
        euclid(parts.iter().map(|t| (one(&t[0]) + r * one(&t[1])) % p).collect(), p)
    })
}

/// gcd(a, a') = 1 modulo p, for a polynomial a (highest degree first) with a nonzero leading coefficient.
fn euclid(a: Vec<u64>, p: u64) -> bool {
    // one copy of the loop for each prime of the table: the compiler then knows the modulus and replaces
    // the divisions by multiplications (version 0.13.0; a tenth of the time of a dense polynomial of
    // degree 2000 was spent in these divisions)
    match p {
        998244353 => euclid_p::<998244353>(a),
        1004535809 => euclid_p::<1004535809>(a),
        469762049 => euclid_p::<469762049>(a),
        _ => unreachable!(),
    }
}
fn euclid_p<const P: u64>(mut a: Vec<u64>) -> bool {
    let p = P;
    let n = a.len() - 1;
    if a[0] == 0 || (n as u64) % p == 0 {
        return false;
    }
    let mut b: Vec<u64> = (0..n).map(|i| a[i] * ((n - i) as u64 % p) % p).collect();
    let (mut a0, mut b0) = (0usize, 0usize); // first live index of each vector
    loop {
        while b0 < b.len() && b[b0] == 0 {
            b0 += 1;
        }
        if b0 == b.len() {
            break;
        }
        // a <- lead(b) a - lead(a) x^k b: the remainder up to a constant that is not zero modulo p, without
        // the inverse of lead(b) (thirty squarings for each remainder: most of this test at degree 20)
        let lead = b[b0];
        let lb = b.len() - b0;
        let pp = p * p;
        while a.len() - a0 >= lb {
            let f = a[a0];
            for i in 1..lb {
                a[a0 + i] = (a[a0 + i] * lead + pp - f * b[b0 + i]) % p;
            }
            for x in a[a0 + lb..].iter_mut() {
                *x = *x * lead % p;
            }
            a0 += 1;
        }
        std::mem::swap(&mut a, &mut b);
        std::mem::swap(&mut a0, &mut b0);
        while a0 < a.len() && a[a0] == 0 {
            a0 += 1;
        }
    }
    a.len() - a0 == 1
}

// ---- Yun's algorithm with Gaussian integers ------------------------------------------------------------
//
// Polynomials are vectors of Gaussian integers, highest degree first, without leading zeros (the zero
// polynomial is the empty vector).  Divisions are pseudo-divisions (the dividend is multiplied by a power
// of the leading coefficient of the divisor), and the integer content is removed after each step: no
// fraction is ever formed.  Everything Yun's algorithm computes is defined up to a nonzero constant, with
// one constraint, kept below: c and d carry the same constant.

type G = (BigInt, BigInt);
type Q = Vec<G>;

fn gzero(a: &G) -> bool {
    a.0.is_zero() && a.1.is_zero()
}
fn gmul(a: &G, b: &G) -> G {
    if a.1.is_zero() && b.1.is_zero() {
        return (&a.0 * &b.0, BigInt::zero());
    }
    (&a.0 * &b.0 - &a.1 * &b.1, &a.0 * &b.1 + &a.1 * &b.0)
}
fn qtrim(mut p: Q) -> Q {
    let lead = p.iter().position(|x| !gzero(x)).unwrap_or(p.len());
    p.drain(..lead);
    p
}
fn qderiv(p: &Q) -> Q {
    if p.len() <= 1 {
        return Vec::new();
    }
    let n = p.len() - 1;
    (0..n).map(|i| (&p[i].0 * BigInt::from(n - i), &p[i].1 * BigInt::from(n - i))).collect()
}
/// p - q.
fn qsub(p: &Q, q: &Q) -> Q {
    let n = p.len().max(q.len());
    let get = |v: &Q, i: usize| if i + v.len() >= n { v[i + v.len() - n].clone() } else { (BigInt::zero(), BigInt::zero()) };
    qtrim((0..n).map(|i| { let (a, b) = (get(p, i), get(q, i)); (a.0 - b.0, a.1 - b.1) }).collect())
}
fn qscale(p: &mut Q, f: &G) {
    for x in p.iter_mut() {
        *x = gmul(x, f);
    }
}
/// A gcd of two Gaussian integers (Euclid's algorithm with the quotient rounded to the nearest Gaussian
/// integer: the norm of the remainder is at most half that of the divisor).
fn ggcd(a: &G, b: &G) -> G {
    let (mut a, mut b) = (a.clone(), b.clone());
    while !gzero(&b) {
        if a.1.is_zero() && b.1.is_zero() {
            return (a.0.gcd(&b.0), BigInt::zero());
        }
        let n: BigInt = &b.0 * &b.0 + &b.1 * &b.1;
        let n2: BigInt = &n * 2;
        let round = |x: BigInt| -> BigInt { let y: BigInt = x * 2 + &n; y.div_floor(&n2) };
        // a / b = a conj(b) / |b|^2
        let q = (round(&a.0 * &b.0 + &a.1 * &b.1), round(&a.1 * &b.0 - &a.0 * &b.1));
        let qb = gmul(&q, &b);
        let r = (&a.0 - qb.0, &a.1 - qb.1);
        a = b;
        b = r;
    }
    a
}
/// A gcd in Z[i] of all the coefficients of the polynomials (0 if they are all zero).
fn content(ps: &[&Q]) -> G {
    let mut g = (BigInt::zero(), BigInt::zero());
    for p in ps {
        for x in p.iter() {
            g = ggcd(&g, x);
            if (g.1.is_zero() && g.0.magnitude().is_one()) || (g.0.is_zero() && g.1.magnitude().is_one()) {
                return g;
            }
        }
    }
    g
}
/// Exact division of the coefficients by a common divisor g (nothing is done for g = 0 or a unit).
fn qdiv_int(p: &mut Q, g: &G) {
    let n: BigInt = &g.0 * &g.0 + &g.1 * &g.1;
    if n.is_zero() || n.is_one() {
        return;
    }
    for x in p.iter_mut() {
        if g.1.is_zero() {
            *x = (&x.0 / &g.0, &x.1 / &g.0);
        } else {
            // x / g = x conj(g) / |g|^2
            *x = ((&x.0 * &g.0 + &x.1 * &g.1) / &n, (&x.1 * &g.0 - &x.0 * &g.1) / &n);
        }
    }
}
/// Pseudo-division: lc(b)^steps a = quo b + rem, with steps = deg a - deg b + 1 (0 if deg a < deg b) and
/// deg rem < deg b.  `b` is not zero.
fn pdivmod(a: &Q, b: &Q) -> (Q, Q, usize) {
    if a.len() < b.len() {
        return (Vec::new(), a.clone(), 0);
    }
    let steps = a.len() - b.len() + 1;
    let lb = &b[0];
    let mut r: Vec<G> = a.clone();
    let mut quo: Q = Vec::with_capacity(steps);
    for i in 0..steps {
        // r[i..] is the current remainder; its leading coefficient is the next coefficient of the quotient
        let f = r[i].clone();
        for x in quo.iter_mut() {
            *x = gmul(x, lb);
        }
        for j in i + 1..r.len() {
            let t = gmul(&r[j], lb);
            r[j] = if j - i < b.len() { let u = gmul(&f, &b[j - i]); (t.0 - u.0, t.1 - u.1) } else { t };
        }
        quo.push(f);
    }
    (quo, qtrim(r[steps..].to_vec()), steps)
}
/// A gcd of two polynomials, not both zero (defined up to a constant; the integer content is removed).
fn qgcd(p: &Q, q: &Q) -> Q {
    let (mut p, mut q) = (p.clone(), q.clone());
    while !q.is_empty() {
        let mut r = pdivmod(&p, &q).1;
        let g = content(&[&r]);
        qdiv_int(&mut r, &g);
        p = q;
        q = r;
    }
    let g = content(&[&p]);
    qdiv_int(&mut p, &g);
    p
}
/// (a / s, b / s) multiplied by one common nonzero constant, for a divisor s of a and of b (b may be zero).
fn qquo2(a: &Q, b: &Q, s: &Q) -> (Q, Q) {
    let (mut qa, ra, ka) = pdivmod(a, s);
    let (mut qb, rb, kb) = pdivmod(b, s);
    debug_assert!(ra.is_empty() && rb.is_empty());
    // lc^ka a = qa s and lc^kb b = qb s: bring both to the power max(ka, kb)
    for _ in ka..kb {
        qscale(&mut qa, &s[0]);
    }
    for _ in kb..ka {
        qscale(&mut qb, &s[0]);
    }
    (qa, qb)
}

// ---- gcd by images modulo primes (version 0.11.0) ---------------------------------------------------------
//
// The remainder sequences above keep the gcd right but not small: on a polynomial of degree 50 with 30-digit
// coefficients and multiple roots the pseudo-divisions produced numbers of tens of thousands of bits, and the
// square-free decomposition took seconds where the rest of the solver takes a fraction of a millisecond.  A
// gcd is now computed from its images modulo primes p = 1 mod 4 (where -1 has a square root r, so that a
// Gaussian integer a + i b has the two images a + r b and a - r b), put together by the Chinese remainder
// theorem, and accepted only when it divides both polynomials exactly: the result is checked, whatever
// the primes were.  Every number met is an image below 2^31 or a coefficient of a divisor of the input.

fn mulmod(a: u64, b: u64, p: u64) -> u64 {
    a * b % p
}
fn is_prime(n: u64) -> bool {
    // Miller-Rabin with the bases 2, 7, 61: exact below 2^32
    if n < 2 || n % 2 == 0 {
        return n == 2;
    }
    let (mut d, mut s) = (n - 1, 0);
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }
    'bases: for a in [2u64, 7, 61] {
        if a % n == 0 {
            continue;
        }
        let mut x = powmod(a, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        for _ in 1..s {
            x = mulmod(x, x, n);
            if x == n - 1 {
                continue 'bases;
            }
        }
        return false;
    }
    true
}
/// Primes p = 1 mod 4 just below 2^31, each with a square root of -1.
fn primes() -> &'static Vec<(u64, u64)> {
    static TABLE: std::sync::OnceLock<Vec<(u64, u64)>> = std::sync::OnceLock::new();
    TABLE.get_or_init(|| {
        let mut out = Vec::new();
        let mut p = (1u64 << 31) - 3; // 1 mod 4
        while out.len() < 96 {
            if is_prime(p) {
                // a non-residue a gives r = a^((p-1)/4) with r^2 = -1
                let r = (2..).map(|a| powmod(a, (p - 1) / 4, p)).find(|&r| mulmod(r, r, p) == p - 1).unwrap();
                out.push((p, r));
            }
            p -= 4;
        }
        out
    })
}
/// The image of a polynomial: a + r b for each coefficient (`r` or `p - r`).
fn image(a: &Q, p: u64, r: u64) -> Vec<u64> {
    a.iter().map(|(x, y)| (red(x, p) + mulmod(r, red(y, p), p)) % p).collect()
}
/// The monic gcd of two polynomials modulo p (highest degree first, leading coefficients not zero).
fn gcd_modp(mut a: Vec<u64>, mut b: Vec<u64>, p: u64) -> Vec<u64> {
    let pp = p * p;
    loop {
        let lead = b.iter().position(|&x| x != 0).unwrap_or(b.len());
        b.drain(..lead);
        if b.is_empty() {
            let inv = powmod(a[0], p - 2, p);
            return a.iter().map(|&x| mulmod(x, inv, p)).collect();
        }
        let inv = powmod(b[0], p - 2, p);
        let mut a0 = 0;
        while a.len() - a0 >= b.len() {
            let f = mulmod(a[a0], inv, p);
            if f != 0 {
                for i in 1..b.len() {
                    a[a0 + i] = (a[a0 + i] + pp - f * b[i]) % p;
                }
            }
            a0 += 1;
        }
        a.drain(..a0);
        std::mem::swap(&mut a, &mut b);
    }
}
fn gdiv_exact(a: &G, b: &G) -> Option<G> {
    // a / b = a conj(b) / |b|^2, if it is a Gaussian integer
    let n: BigInt = &b.0 * &b.0 + &b.1 * &b.1;
    let (x, y): (BigInt, BigInt) = (&a.0 * &b.0 + &a.1 * &b.1, &a.1 * &b.0 - &a.0 * &b.1);
    let (qx, rx) = x.div_mod_floor(&n);
    let (qy, ry) = y.div_mod_floor(&n);
    (rx.is_zero() && ry.is_zero()).then_some((qx, qy))
}
/// a / b when b divides a in Z[i][x] (quotient with Gaussian integer coefficients), None otherwise.
fn qdiv_exact(a: &Q, b: &Q) -> Option<Q> {
    if a.is_empty() {
        return Some(Vec::new());
    }
    if b.is_empty() || a.len() < b.len() {
        return None;
    }
    let mut r = a.clone();
    let steps = a.len() - b.len() + 1;
    let mut quo = Vec::with_capacity(steps);
    for i in 0..steps {
        if gzero(&r[i]) {
            quo.push((BigInt::zero(), BigInt::zero()));
            continue;
        }
        let f = gdiv_exact(&r[i], &b[0])?;
        for j in 1..b.len() {
            if !gzero(&b[j]) {
                let u = gmul(&f, &b[j]);
                r[i + j].0 -= u.0;
                r[i + j].1 -= u.1;
            }
        }
        quo.push(f);
    }
    r[steps..].iter().all(gzero).then_some(quo)
}
fn primitive(mut p: Q) -> Q {
    let g = content(&[&p]);
    qdiv_int(&mut p, &g);
    p
}
/// A gcd of two polynomials of Z[i][x], not both zero, primitive.  From its images modulo primes; verified
/// by exact division.  Falls back on the remainder sequence if 96 primes (coefficients of the gcd up to about 2900 bits) are not enough.
fn gcd_modular(a: &Q, b: &Q) -> Q {
    if b.is_empty() {
        return primitive(a.clone());
    }
    if a.is_empty() {
        return primitive(b.clone());
    }
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let real = a.iter().chain(b.iter()).all(|x| x.1.is_zero());
    // the leading coefficient of the gcd divides l
    let l = ggcd(&a[0], &b[0]);
    let half = |m: &BigInt, x: BigInt| -> BigInt { let h: BigInt = m >> 1u32; if x > h { x - m } else { x } };
    let mut modulus = BigInt::one();
    let mut acc: Vec<(BigInt, BigInt)> = Vec::new(); // residues in [0, modulus)
    let mut last: Option<Q> = None;
    for &(p, r) in primes().iter() {
        let signs: &[u64] = if real { &[r] } else { &[r, p - r] };
        let mut imgs: Vec<Vec<u64>> = Vec::new();
        let mut lead_ok = true;
        for &s in signs {
            let (ia, ib) = (image(a, p, s), image(b, p, s));
            if ia[0] == 0 || ib[0] == 0 {
                lead_ok = false;
                break;
            }
            let lv = (red(&l.0, p) + mulmod(s, red(&l.1, p), p)) % p;
            let g = gcd_modp(ia, ib, p);
            imgs.push(g.iter().map(|&x| mulmod(x, lv, p)).collect());
        }
        if !lead_ok || (imgs.len() == 2 && imgs[0].len() != imgs[1].len()) {
            continue;
        }
        let d = imgs[0].len();
        if d == 1 {
            return vec![(BigInt::one(), BigInt::zero())]; // a gcd modulo p has at least the degree of the gcd
        }
        if !acc.is_empty() && d > acc.len() {
            continue; // an unlucky prime
        }
        if d < acc.len() {
            acc.clear(); // the primes so far were unlucky
        }
        // the Gaussian coefficients modulo p: re = (g+ + g-)/2, im = (g+ - g-)/(2 r)
        let inv2 = (p + 1) / 2;
        let inv2r = powmod(2 * r % p, p - 2, p);
        let vals: Vec<(u64, u64)> = (0..d).map(|j| if real { (imgs[0][j], 0) } else { (mulmod((imgs[0][j] + imgs[1][j]) % p, inv2, p), mulmod((imgs[0][j] + p - imgs[1][j]) % p, inv2r, p)) }).collect();
        if acc.is_empty() {
            modulus = BigInt::from(p);
            acc = vals.iter().map(|&(x, y)| (BigInt::from(x), BigInt::from(y))).collect();
        } else {
            let minv = powmod(red(&modulus, p), p - 2, p);
            for (c, &(x, y)) in acc.iter_mut().zip(&vals) {
                let fix = |c: &BigInt, v: u64| -> BigInt { let t = mulmod((v + p - red(c, p)) % p, minv, p); c + &modulus * BigInt::from(t) };
                *c = (fix(&c.0, x), fix(&c.1, y));
            }
            modulus *= BigInt::from(p);
        }
        let lift: Q = acc.iter().map(|(x, y)| (half(&modulus, x.clone()), half(&modulus, y.clone()))).collect();
        if last.as_ref() == Some(&lift) {
            // unchanged by one more prime: the candidate, accepted if it divides both
            let g = primitive(lift.clone());
            if qdiv_exact(a, &g).is_some() && qdiv_exact(b, &g).is_some() {
                return g;
            }
        }
        last = Some(lift);
    }
    qgcd(a, b)
}

/// P = c prod_k S_k^k with S_k square-free and pairwise coprime; returns the pairs (k, S_k), deg S_k >= 1.
/// (Yun's algorithm over the Gaussian integers.  Every polynomial met is a divisor of P or of P' with
/// Gaussian integer coefficients: the gcds are primitive, so the quotients are exact, by Gauss's lemma.)
pub fn yun(ci: &GPoly) -> Vec<(usize, GPoly)> {
    let p: Q = primitive(qtrim(ci.clone()));
    let dp = qderiv(&p);
    if dp.is_empty() {
        return Vec::new();
    }
    let g = gcd_modular(&p, &dp);
    let (c, e) = match (qdiv_exact(&p, &g), qdiv_exact(&dp, &g)) {
        (Some(c), Some(e)) => (c, e),
        _ => return yun_prs(ci),
    };
    let mut c = c;
    let mut d = qsub(&e, &qderiv(&c));
    let mut out = Vec::new();
    let mut k = 0;
    while c.len() >= 2 {
        k += 1;
        let s = if d.is_empty() { primitive(c.clone()) } else { gcd_modular(&c, &d) };
        let (c2, e2) = match (qdiv_exact(&c, &s), qdiv_exact(&d, &s)) {
            (Some(x), Some(y)) => (x, y),
            _ => return yun_prs(ci),
        };
        d = qsub(&e2, &qderiv(&c2));
        c = c2;
        if s.len() >= 2 {
            out.push((k, s));
        }
    }
    out
}

/// Yun's algorithm with pseudo-divisions (versions 0.6.0 to 0.10.1): the fallback, and a reference in the tests.
pub fn yun_prs(ci: &GPoly) -> Vec<(usize, GPoly)> {
    let mut p: Q = qtrim(ci.clone());
    let g0 = content(&[&p]);
    qdiv_int(&mut p, &g0);
    let dp = qderiv(&p);
    if dp.is_empty() {
        return Vec::new();
    }
    let g = qgcd(&p, &dp);
    // c = P / g and d = P' / g - c', with one common constant
    let (mut c, e) = qquo2(&p, &dp, &g);
    let mut d = qsub(&e, &qderiv(&c));
    let mut out = Vec::new();
    let mut k = 0;
    while c.len() >= 2 {
        k += 1;
        let h = content(&[&c, &d]);
        qdiv_int(&mut c, &h);
        qdiv_int(&mut d, &h);
        let s = if d.is_empty() { let mut s = c.clone(); let g = content(&[&s]); qdiv_int(&mut s, &g); s } else { qgcd(&c, &d) };
        let (c2, e2) = qquo2(&c, &d, &s);
        d = qsub(&e2, &qderiv(&c2));
        c = c2;
        if s.len() >= 2 {
            out.push((k, s));
        }
    }
    out
}

/// Remove leading zero coefficients.
pub fn strip(ci: &GPoly) -> GPoly {
    let lead = ci.iter().position(|x| !(x.0.is_zero() && x.1.is_zero())).unwrap_or(ci.len());
    ci[lead..].to_vec()
}

#[cfg(test)]
mod reference {
    use super::*;
    use num_rational::BigRational;
    #[derive(Clone, PartialEq)]
    struct Gq {
        re: BigRational,
        im: BigRational,
    }
    impl Gq {
        fn zero() -> Gq {
            Gq { re: BigRational::zero(), im: BigRational::zero() }
        }
        fn is_zero(&self) -> bool {
            self.re.is_zero() && self.im.is_zero()
        }
        fn sub(&self, o: &Gq) -> Gq {
            Gq { re: &self.re - &o.re, im: &self.im - &o.im }
        }
        fn mul(&self, o: &Gq) -> Gq {
            Gq { re: &self.re * &o.re - &self.im * &o.im, im: &self.re * &o.im + &self.im * &o.re }
        }
        fn div(&self, o: &Gq) -> Gq {
            let d = &o.re * &o.re + &o.im * &o.im;
            Gq { re: (&self.re * &o.re + &self.im * &o.im) / &d, im: (&self.im * &o.re - &self.re * &o.im) / &d }
        }
        fn scale(&self, k: usize) -> Gq {
            let k = BigRational::from_integer(BigInt::from(k));
            Gq { re: &self.re * &k, im: &self.im * &k }
        }
    }
    type P = Vec<Gq>;

    fn trim(mut p: P) -> P {
        let lead = p.iter().position(|x| !x.is_zero()).unwrap_or(p.len() - 1).min(p.len() - 1);
        p.drain(..lead);
        p
    }
    fn deg(p: &P) -> usize {
        p.len() - 1
    }
    fn pzero(p: &P) -> bool {
        p.len() == 1 && p[0].is_zero()
    }
    fn deriv(p: &P) -> P {
        let n = deg(p);
        if n == 0 {
            return vec![Gq::zero()];
        }
        (0..n).map(|i| p[i].scale(n - i)).collect()
    }
    fn psub(p: &P, q: &P) -> P {
        let n = p.len().max(q.len());
        let get = |v: &P, i: usize| if i + v.len() >= n { v[i + v.len() - n].clone() } else { Gq::zero() };
        trim((0..n).map(|i| get(p, i).sub(&get(q, i))).collect())
    }
    fn divmod(p: &P, q: &P) -> (P, P) {
        let mut p = p.clone();
        let mut out = Vec::new();
        if p.len() >= q.len() {
            for _ in 0..(p.len() - q.len() + 1) {
                let f = p[0].div(&q[0]);
                for i in 0..q.len() {
                    p[i] = p[i].sub(&f.mul(&q[i]));
                }
                p.remove(0);
                out.push(f);
            }
        }
        if out.is_empty() {
            out.push(Gq::zero());
        }
        if p.is_empty() {
            p.push(Gq::zero());
        }
        (out, trim(p))
    }
    fn monic(p: &P) -> P {
        p.iter().map(|x| x.div(&p[0])).collect()
    }
    fn gcd(p: &P, q: &P) -> P {
        let (mut p, mut q) = (p.clone(), q.clone());
        while !pzero(&q) {
            let r = divmod(&p, &q).1;
            p = q;
            q = r;
        }
        monic(&p)
    }

    /// Yun's algorithm over the Gaussian rationals (the implementation up to 0.5.0), kept as a reference.
        pub fn yun(ci: &GPoly) -> Vec<(usize, GPoly)> {
        let p: P = trim(ci.iter().map(|(a, b)| Gq { re: BigRational::from_integer(a.clone()), im: BigRational::from_integer(b.clone()) }).collect());
        let dp = deriv(&p);
        let g = gcd(&p, &dp);
        let mut c = divmod(&p, &g).0;
        let mut d = psub(&divmod(&dp, &g).0, &deriv(&c));
        let mut out = Vec::new();
        let mut k = 0;
        while deg(&c) >= 1 {
            k += 1;
            let s = if !pzero(&d) { gcd(&c, &d) } else { monic(&c) };
            c = divmod(&c, &s).0;
            d = psub(&divmod(&d, &s).0, &deriv(&c));
            if deg(&s) >= 1 {
                let mut den = BigInt::one();
                for x in &s {
                    den = den.lcm(x.re.denom()).lcm(x.im.denom());
                }
                let dr = BigRational::from_integer(den);
                out.push((k, s.iter().map(|x| ((&x.re * &dr).to_integer(), (&x.im * &dr).to_integer())).collect()));
            }
        }
        out
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    fn mul(a: &Q, b: &Q) -> Q {
        if a.is_empty() || b.is_empty() {
            return Vec::new();
        }
        let mut r = vec![(BigInt::zero(), BigInt::zero()); a.len() + b.len() - 1];
        for (i, x) in a.iter().enumerate() {
            for (j, y) in b.iter().enumerate() {
                let t = gmul(x, y);
                r[i + j].0 += t.0;
                r[i + j].1 += t.1;
            }
        }
        r
    }
    /// a and b are proportional.
    fn same(a: &Q, b: &Q) -> bool {
        a.len() == b.len() && { let (mut x, mut y) = (a.clone(), b.clone()); qscale(&mut x, &b[0]); qscale(&mut y, &a[0]); x == y }
    }
    fn rng(state: &mut u64) -> i64 {
        *state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        ((*state >> 33) % 13) as i64 - 6
    }
    fn random_poly(state: &mut u64, deg: usize, complex: bool) -> Q {
        let mut p: Q = (0..=deg).map(|_| (BigInt::from(rng(state)), BigInt::from(if complex { rng(state) } else { 0 }))).collect();
        if gzero(&p[0]) {
            p[0].0 = BigInt::from(1);
        }
        p
    }

    #[test]
    fn pseudo_division_identity() {
        let mut st = 7u64;
        for t in 0..300 {
            let a = random_poly(&mut st, 1 + t % 9, t % 2 == 0);
            let b = random_poly(&mut st, 1 + t % 4, t % 3 == 0);
            let (q, r, k) = pdivmod(&a, &b);
            let mut lhs = a.clone();
            for _ in 0..k {
                qscale(&mut lhs, &b[0]);
            }
            assert!(r.len() < b.len());
            assert_eq!(qsub(&lhs, &mul(&q, &b)), r);
        }
    }

    #[test]
    fn yun_agrees_with_the_rational_version_and_rebuilds_the_polynomial() {
        let mut st = 11u64;
        for t in 0..400 {
            // a product of powers of random factors, with multiplicities up to 4
            let complex = t % 2 == 1;
            let mut p: Q = vec![(BigInt::from(1 + t as i64 % 5), BigInt::zero())];
            for m in 1..=(1 + t % 4) {
                let f = random_poly(&mut st, 1 + (t + m) % 3, complex);
                for _ in 0..m {
                    p = mul(&p, &f);
                }
            }
            let new = yun(&p);
            let prs = yun_prs(&p);
            assert_eq!(new.len(), prs.len(), "case {t}");
            assert!(new.iter().zip(&prs).all(|(x, y)| x.0 == y.0 && same(&x.1, &y.1)), "case {t}: modular and remainder-sequence factors differ");
            let old = reference::yun(&p);
            assert_eq!(new.len(), old.len(), "case {t}");
            let mut prod: Q = vec![(BigInt::from(1), BigInt::zero())];
            for ((k1, s1), (k2, s2)) in new.iter().zip(&old) {
                assert_eq!(k1, k2);
                assert!(same(s1, s2), "case {t}, multiplicity {k1}");
                for _ in 0..*k1 {
                    prod = mul(&prod, s1);
                }
            }
            assert!(same(&prod, &p), "case {t}: the factors do not rebuild the polynomial");
            // each factor is square-free: its gcd with its derivative is a constant
            for (_, s) in &new {
                assert_eq!(qgcd(s, &qderiv(s)).len(), 1);
            }
        }
    }
}
