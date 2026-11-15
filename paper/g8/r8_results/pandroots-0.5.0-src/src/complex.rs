//! Minimal complex arithmetic in double precision.
use std::ops::{Add, Div, Mul, Neg, Sub};

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct C {
    pub re: f64,
    pub im: f64,
}

pub const ZERO: C = C { re: 0.0, im: 0.0 };
pub const ONE: C = C { re: 1.0, im: 0.0 };

impl C {
    #[inline(always)]
    pub fn new(re: f64, im: f64) -> C {
        C { re, im }
    }
    #[inline(always)]
    pub fn norm_sqr(self) -> f64 {
        self.re * self.re + self.im * self.im
    }
    #[inline(always)]
    pub fn abs(self) -> f64 {
        self.re.hypot(self.im)
    }
    #[inline(always)]
    pub fn conj(self) -> C {
        C::new(self.re, -self.im)
    }
    #[inline(always)]
    pub fn scale(self, k: f64) -> C {
        C::new(self.re * k, self.im * k)
    }
    /// 1/z without overflow of the squared modulus (Smith's formula).
    #[inline]
    pub fn inv(self) -> C {
        if self.re.abs() >= self.im.abs() {
            let r = self.im / self.re;
            let d = 1.0 / (self.re + self.im * r);
            C::new(d, -r * d)
        } else {
            let r = self.re / self.im;
            let d = 1.0 / (self.re * r + self.im);
            C::new(r * d, -d)
        }
    }
    /// 1/z for a number of ordinary size (one division).
    #[inline(always)]
    pub fn fast_inv(self) -> C {
        let r = 1.0 / self.norm_sqr();
        C::new(self.re * r, -self.im * r)
    }
    #[inline(always)]
    pub fn is_finite(self) -> bool {
        self.re.is_finite() && self.im.is_finite()
    }
    pub fn arg(self) -> f64 {
        self.im.atan2(self.re)
    }
    pub fn from_polar(r: f64, th: f64) -> C {
        C::new(r * th.cos(), r * th.sin())
    }
    /// Principal square root (real part >= 0; on the cut the sign of the imaginary zero decides).
    #[inline]
    pub fn sqrt(self) -> C {
        if self.re == 0.0 && self.im == 0.0 {
            return C::new(0.0, self.im);
        }
        let n = self.norm_sqr();
        let r = if n > 1e-290 && n < 1e290 { n.sqrt() } else { self.abs() };
        if self.re >= 0.0 {
            let w = ((r + self.re) * 0.5).sqrt();
            C::new(w, self.im / (2.0 * w))
        } else {
            let w = ((r - self.re) * 0.5).sqrt();
            C::new(self.im.abs() / (2.0 * w), w.copysign(self.im))
        }
    }
}

impl Add for C {
    type Output = C;
    #[inline(always)]
    fn add(self, o: C) -> C {
        C::new(self.re + o.re, self.im + o.im)
    }
}
impl Sub for C {
    type Output = C;
    #[inline(always)]
    fn sub(self, o: C) -> C {
        C::new(self.re - o.re, self.im - o.im)
    }
}
impl Mul for C {
    type Output = C;
    #[inline(always)]
    fn mul(self, o: C) -> C {
        C::new(self.re * o.re - self.im * o.im, self.re * o.im + self.im * o.re)
    }
}
impl Div for C {
    type Output = C;
    #[inline(always)]
    fn div(self, o: C) -> C {
        if o.re.abs() >= o.im.abs() {
            let r = o.im / o.re;
            let d = o.re + o.im * r;
            C::new((self.re + self.im * r) / d, (self.im - self.re * r) / d)
        } else {
            let r = o.re / o.im;
            let d = o.re * r + o.im;
            C::new((self.re * r + self.im) / d, (self.im * r - self.re) / d)
        }
    }
}
impl Neg for C {
    type Output = C;
    #[inline(always)]
    fn neg(self) -> C {
        C::new(-self.re, -self.im)
    }
}
