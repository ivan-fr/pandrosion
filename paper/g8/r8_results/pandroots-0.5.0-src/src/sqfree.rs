//! Square-free decomposition: a test modulo a prime (exact, cheap), and Yun's algorithm over the Gaussian
//! rationals when the test does not conclude.
use crate::complex::C;
use crate::exact::GPoly;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};

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
    x.mod_floor(&BigInt::from(p)).to_u64().unwrap()
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
    PRIMES.iter().any(|&(p, g)| {
        let r = powmod(g, (p - 1) / 4, p);
        let one = |t: &(u64, i64, bool)| {
            if t.0 == 0 {
                return 0;
            }
            let v = (t.0 % p) * powmod(2, (t.1 - emin) as u64, p) % p;
            if t.2 { (p - v) % p } else { v }
        };
        euclid(parts.iter().map(|t| (one(&t[0]) + r * one(&t[1])) % p).collect(), p)
    })
}

/// gcd(a, a') = 1 modulo p, for a polynomial a (highest degree first) with a nonzero leading coefficient.
fn euclid(mut a: Vec<u64>, p: u64) -> bool {
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
        let inv = powmod(b[b0], p - 2, p);
        let lb = b.len() - b0;
        let pp = p * p;
        while a.len() - a0 >= lb {
            let f = a[a0] * inv % p;
            for i in 1..lb {
                a[a0 + i] = (a[a0 + i] + pp - f * b[b0 + i]) % p;
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

/// P = c prod_k S_k^k with S_k square-free and pairwise coprime; returns the pairs (k, S_k), deg S_k >= 1.
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

/// Remove leading zero coefficients.
pub fn strip(ci: &GPoly) -> GPoly {
    let lead = ci.iter().position(|x| !(x.0.is_zero() && x.1.is_zero())).unwrap_or(ci.len());
    ci[lead..].to_vec()
}
