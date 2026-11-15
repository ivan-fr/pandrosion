use num_bigint::BigInt;
use pandroots::{all_roots, all_roots_exact, Options, C};

fn from_roots(roots: &[i64]) -> Vec<(BigInt, BigInt)> {
    let mut p = vec![BigInt::from(1)];
    for &r in roots {
        let mut q = vec![BigInt::from(0); p.len() + 1];
        for (i, a) in p.iter().enumerate() {
            q[i] += a;
            q[i + 1] -= a * r;
        }
        p = q;
    }
    p.into_iter().map(|a| (a, BigInt::from(0))).collect()
}

#[test]
fn wilkinson_20() {
    let roots: Vec<i64> = (1..=20).collect();
    let (out, complete, _) = all_roots_exact(&from_roots(&roots), &Options::default());
    assert!(complete && out.len() == 20);
    for (i, d) in out.iter().enumerate() {
        assert!(d.real && d.count == 1 && d.mult == 1);
        assert!((d.z.re - (i as f64 + 1.0)).abs() <= d.radius && d.radius < 1e-9);
    }
}

#[test]
fn multiplicities() {
    // (z-1)^3 (z+2)^2 (z-5)
    let (out, complete, _) = all_roots_exact(&from_roots(&[1, 1, 1, -2, -2, 5]), &Options::default());
    assert!(complete && out.len() == 3);
    let got: Vec<(i64, usize)> = out.iter().map(|d| (d.z.re.round() as i64, d.mult)).collect();
    assert_eq!(got, vec![(-2, 2), (1, 3), (5, 1)]);
    assert!(out.iter().all(|d| d.real && (d.z.re - d.z.re.round()).abs() <= d.radius));
}

#[test]
fn unit_roots_and_scales() {
    // z^12 - 1
    let mut c = vec![C::new(0.0, 0.0); 13];
    c[0] = C::new(1.0, 0.0);
    c[12] = C::new(-1.0, 0.0);
    let (out, complete, _) = all_roots(&c, &Options::default());
    assert!(complete && out.len() == 12 && out.iter().filter(|d| d.real).count() == 2);
    for d in &out {
        assert!((d.z.abs() - 1.0).abs() <= d.radius + 1e-15 && d.radius < 1e-12);
    }
    // roots 1, 10, ..., 10^9
    let roots: Vec<i64> = (0..10).map(|k| 10i64.pow(k)).collect();
    let (out, complete, st) = all_roots_exact(&from_roots(&roots), &Options::default());
    assert!(complete && out.len() == 10 && st.sweeps <= 4);
    for (d, r) in out.iter().zip(&roots) {
        assert!(d.real && (d.z.re - *r as f64).abs() <= d.radius && d.radius <= 1e-10 * *r as f64);
    }
}

#[test]
fn degenerate_inputs() {
    let o = Options::default();
    assert!(all_roots(&[C::new(5.0, 0.0)], &o).0.is_empty());
    let (out, complete, _) = all_roots(&[C::new(0.0, 0.0), C::new(2.0, 0.0), C::new(-4.0, 0.0)], &o);
    assert!(complete && out.len() == 1 && (out[0].z.re - 2.0).abs() <= out[0].radius);
    // z^3 (z - 1): root 0 of multiplicity 3
    let (out, complete, _) = all_roots(&[1.0, -1.0, 0.0, 0.0, 0.0].map(|x| C::new(x, 0.0)), &o);
    assert!(complete && out.len() == 2 && out[0].mult == 3 && out[0].z.abs() <= out[0].radius && out[1].mult == 1);
}

#[test]
fn mignotte_fixed_point_certificate() {
    // z^12 - 2 (100 z - 1)^2: two real roots 1.4e-14 apart, near 0.01
    let mut c = vec![(BigInt::from(0), BigInt::from(0)); 13];
    c[0].0 = BigInt::from(1);
    c[10].0 = BigInt::from(-20000);
    c[11].0 = BigInt::from(400);
    c[12].0 = BigInt::from(-2);
    let (out, complete, stats) = all_roots_exact(&c, &Options::default());
    assert!(complete && out.len() == 12 && out.iter().all(|d| d.count == 1 && d.mult == 1));
    // the count is the fixed-point certificate on every disc (the statement proved in Lean)
    assert!(stats.factors == 1 && stats.fixed_point == 1);
    assert_eq!(out.iter().filter(|d| d.real).count(), 4);
    // the close pair: two disjoint discs, one on each side of 0.01 +- 7.07e-15
    let pair: Vec<_> = out.iter().filter(|d| (d.z.re - 0.01).abs() < 1e-6).collect();
    assert!(pair.len() == 2 && pair.iter().all(|d| d.real));
    assert!((pair[0].z.re - pair[1].z.re).abs() > pair[0].radius + pair[1].radius);
    let b = 7.0710678e-15;
    assert!((pair[0].z.re - (0.01 - b)).abs() <= pair[0].radius && (pair[1].z.re - (0.01 + b)).abs() <= pair[1].radius);
}

// ---- version 0.2.0: the edges of double precision, and more digits than a double holds ----
use pandroots::{all_roots_exact_precise, all_roots_precise};

fn contains(d: &pandroots::Root, x: f64, y: f64) -> bool {
    (d.z.re - x).hypot(d.z.im - y) <= d.radius
}

#[test]
fn subnormal_coefficients() {
    // 2^-1070 (z-1)(z-2)(z-3): version 0.1.0 returned a wrong root with radius zero and complete = true
    let s = 2f64.powi(-1070);
    let c = [1.0, -6.0, 11.0, -6.0].map(|x| C::new(x * s, 0.0));
    let (out, complete, _) = all_roots(&c, &Options::default());
    assert!(complete && out.len() == 3);
    for (i, d) in out.iter().enumerate() {
        assert!(d.count == 1 && d.real && d.radius < 1e-9 && contains(d, i as f64 + 1.0, 0.0), "{:?}", d);
    }
}

#[test]
fn values_that_underflow() {
    // z^3 - 1e-250 z: normal coefficients, but every term underflows near the roots 0, +-1e-125
    let c = [1.0, 0.0, -1e-250, 0.0].map(|x| C::new(x, 0.0));
    let (out, complete, _) = all_roots(&c, &Options::default());
    assert!(complete && out.len() == 3, "{:?}", out);
    let r = 1e-250f64.sqrt();
    for (d, x) in out.iter().zip([-r, 0.0, r]) {
        assert!(d.count == 1 && d.radius <= 1e-9 * r && (d.z.re - x).abs() <= d.radius + 1e-15 * r, "{:?}", d);
    }
    // subnormal constant term, roots +-1e-160
    let c = [1.0, 0.0, -1e-320].map(|x| C::new(x, 0.0));
    let (out, complete, _) = all_roots(&c, &Options::default());
    assert!(complete && out.len() == 2 && out.iter().all(|d| d.count == 1 && d.real && d.radius < 1e-170 && d.z.re.abs() > 9e-161), "{:?}", out);
}

#[test]
fn sixty_digits_of_sqrt_two() {
    let c = vec![(BigInt::from(1), BigInt::from(0)), (BigInt::from(0), BigInt::from(0)), (BigInt::from(-2), BigInt::from(0))];
    let opt = Options { tol: 1e-60, ..Options::default() };
    let (out, complete, stats) = all_roots_exact_precise(&c, &opt);
    assert!(complete && out.len() == 2 && stats.precise_sweeps > 0);
    let (re, im, radius) = out[1].decimal(60);
    assert!(re.starts_with("1.41421356237309504880168872420969807856967187537694807317667"), "{}", re);
    assert!(im == "0" && out[1].real && radius.parse::<f64>().unwrap() < 1e-59, "{} {}", im, radius);
    // the same from double precision coefficients
    let (out, complete, _) = all_roots_precise(&[1.0, 0.0, -2.0].map(|x| C::new(x, 0.0)), &opt);
    assert!(complete && out[0].decimal(60).0.starts_with("-1.41421356237309504880168872420969807856967187537694807317667"));
}

#[test]
fn roots_closer_than_double_precision() {
    // 10^20 (z - 1)(z - 1 - 10^-20)(z - 2): version 0.1.0 could only report the first two roots together
    let t = BigInt::from(10).pow(20);
    let a: BigInt = &t + 1; // 10^20 (1 + 10^-20)
    // (z - 1)(t z - a)(z - 2) = t z^3 - (3t + a) z^2 + (2t + 3a) z - 2a
    let c2: BigInt = -(&t * 3u32 + &a);
    let c1: BigInt = &t * 2u32 + &a * 3u32;
    let c0: BigInt = -(&a * 2u32);
    let c: Vec<(BigInt, BigInt)> = [t.clone(), c2, c1, c0].into_iter().map(|x| (x, BigInt::from(0))).collect();
    let (out, complete, _) = all_roots_exact_precise(&c, &Options::default());
    assert!(complete && out.len() == 3 && out.iter().all(|d| d.count == 1 && d.real), "{:?}", out.iter().map(|d| d.decimal(30)).collect::<Vec<_>>());
    // two disjoint discs around 1 and 1 + 10^-20, much smaller than what a double can resolve
    let (lo, hi) = (out[0].decimal(25), out[1].decimal(25));
    assert!(lo.0.starts_with("9.999999999999999999") || lo.0.starts_with("1.00000000000000000000"), "{:?}", lo);
    assert!(hi.0.starts_with("1.0000000000000000000"), "{:?}", hi);
    assert!(lo.2.parse::<f64>().unwrap() < 1e-18 && hi.2.parse::<f64>().unwrap() < 1e-18, "{:?} {:?}", lo, hi);
    // in doubles the two discs cannot be told apart: they are returned as one disc with two roots
    let (out, complete, _) = all_roots_exact(&c, &Options::default());
    assert!(complete && out.len() == 2 && out[0].count == 2 && out[1].count == 1, "{:?}", out);
}

// ---- version 0.3.0: the failures found by the comparison with MPSolve on version 0.2.0 ----

fn ints(c: &[i64]) -> Vec<(BigInt, BigInt)> {
    c.iter().map(|&x| (BigInt::from(x), BigInt::from(0))).collect()
}

#[test]
fn mignotte_with_a_pair_far_below_double_precision() {
    // z^12 - 2 (10^8 z - 1)^2: version 0.2.0 returned one disc of infinite radius and complete = false
    let mut c = vec![0i64; 13];
    c[0] = 1;
    c[10] = -20_000_000_000_000_000;
    c[11] = 400_000_000;
    c[12] = -2;
    let c = ints(&c);
    let (out, complete, _) = all_roots_exact(&c, &Options::default());
    assert!(complete && out.iter().all(|d| d.radius.is_finite()) && out.iter().map(|d| d.count).sum::<usize>() == 12, "{:?}", out);
    // with centres of any precision the two close roots are separated
    let (out, complete, stats) = all_roots_exact_precise(&c, &Options::default());
    assert!(complete && stats.within_tolerance && out.len() == 12 && out.iter().all(|d| d.count == 1), "{}", out.len());
    assert_eq!(out.iter().filter(|d| d.real).count(), 4);
}

#[test]
fn degree_one_to_eighty_digits() {
    // 3 z - 1: version 0.2.0 kept the 53-bit centre whatever the tolerance
    let opt = Options { tol: 1e-80, ..Options::default() };
    let (out, complete, stats) = all_roots_exact_precise(&ints(&[3, -1]), &opt);
    assert!(complete && stats.within_tolerance && out.len() == 1);
    let (re, im, radius) = out[0].decimal(80);
    assert!(re.starts_with(&format!("3.{}", "3".repeat(78))) && im == "0", "{} {}", re, im);
    assert!(radius.parse::<f64>().unwrap() < 1e-80, "{}", radius);
    // a complex one: (2 + i) z - (1 - 3 i), root (1 - 3i)/(2 + i) = -1/5 - 7/5 i
    let c = vec![(BigInt::from(2), BigInt::from(1)), (BigInt::from(-1), BigInt::from(3))];
    let (out, complete, _) = all_roots_exact_precise(&c, &opt);
    let (re, im, _) = out[0].decimal(40);
    assert!(complete && re.starts_with("-2.0000000000000000000000000000000000000") || re.starts_with("-1.9999999999999999999999999999999999999"), "{}", re);
    assert!(im.starts_with("-1.4000000000000000000000000000000000000") || im.starts_with("-1.3999999999999999999999999999999999999"), "{}", im);
}

#[test]
fn large_dense_real_polynomial() {
    // degree 800 with pseudo-random coefficients: version 0.2.0 shifted the variable by a power of two for
    // such inputs, which pushed most coefficients out of the range of doubles (10 000 sweeps and a time-out)
    let mut x: u64 = 20261115;
    let mut next = || {
        x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        ((x >> 11) as f64 / (1u64 << 53) as f64) * 2.0 - 1.0
    };
    let c: Vec<C> = (0..=800).map(|_| C::new(next() + next() + next(), 0.0)).collect();
    let (out, complete, stats) = all_roots(&c, &Options::default());
    assert!(complete && stats.within_tolerance && out.len() == 800 && stats.sweeps < 40, "{} {:?}", out.len(), stats);
}

#[test]
fn exact_roots_print_with_radius_zero() {
    // (z - 1)(z + 2): the roots are exact, the decimal centre is exact, the printed radius is zero
    let opt = Options { tol: 1e-80, ..Options::default() };
    let (out, complete, stats) = all_roots_exact_precise(&ints(&[1, 1, -2]), &opt);
    assert!(complete && stats.within_tolerance && out.len() == 2);
    assert_eq!(out[0].decimal(80), ("-2.0000000000000000000000000000000000000000000000000000000000000000000000000000000e0".to_string(), "0".to_string(), "0".to_string()));
    assert_eq!(out[1].decimal(10).2, "0");
}

#[test]
fn eighty_digits_in_few_sweeps() {
    // dense integer polynomial of degree 24; the Newton part of the step is in multiprecision since 0.4.0
    let c: Vec<i64> = (0..25).map(|j: i64| ((j * j * 37 + j * 11 + 5) % 19) - 9 + if j == 0 { 20 } else { 0 }).collect();
    let opt = Options { tol: 1e-80, ..Options::default() };
    let (out, complete, stats) = all_roots_exact_precise(&ints(&c), &opt);
    let n: usize = out.iter().map(|d| d.mult * d.count).sum();
    assert!(complete && stats.within_tolerance && n == 24, "{:?}", stats.precise_sweeps);
    assert!(stats.precise_sweeps <= 4, "precise sweeps {}", stats.precise_sweeps);
    assert!(out.iter().all(|d| d.radius.to_f64() <= 1e-80));
}

#[test]
fn small_exact_roots_in_decimal() {
    // (2^20 z - 1)(3 z - 1): the root 2^-20 = 9.5367431640625e-7 has 14 significant digits
    let c = ints(&[3 << 20, -(3 + (1 << 20)), 1]);
    for digits in [10usize, 13, 14, 30] {
        let opt = Options { tol: 10f64.powi(-(digits as i32)), ..Options::default() };
        let (out, complete, stats) = all_roots_exact_precise(&c, &opt);
        assert!(complete && stats.within_tolerance && out.len() == 2);
        let (re, _, radius) = out[0].decimal(digits);
        let (x, r): (f64, f64) = (re.parse().unwrap(), radius.parse().unwrap());
        assert!((x - 2f64.powi(-20)).abs() <= r + 1e-21 && r <= x * 10f64.powi(-(digits as i32)), "{} {} {}", digits, re, radius);
        if digits >= 14 {
            assert!(re.starts_with("9.5367431640625") && re.ends_with("e-7") && radius == "0", "{} {}", re, radius);
        }
    }
}

#[test]
fn full_order_in_multiprecision() {
    // the same polynomial at 280 digits, with every sweep of the multiprecision stage at its full order:
    // fewer sweeps than by doubling the digits, and the same roots
    let c: Vec<i64> = (0..25).map(|j: i64| ((j * j * 37 + j * 11 + 5) % 19) - 9 + if j == 0 { 20 } else { 0 }).collect();
    let (out, complete, stats) = all_roots_exact_precise(&ints(&c), &Options { tol: 1e-280, full_order: true, ..Options::default() });
    let n: usize = out.iter().map(|d| d.mult * d.count).sum();
    assert!(complete && stats.within_tolerance && n == 24);
    let (def, complete, st) = all_roots_exact_precise(&ints(&c), &Options { tol: 1e-280, ..Options::default() });
    assert!(complete && st.within_tolerance && def.len() == out.len());
    assert!(stats.precise_sweeps <= 3 && st.precise_sweeps > stats.precise_sweeps, "{} {}", st.precise_sweeps, stats.precise_sweeps);
    for (a, b) in out.iter().zip(def.iter()) {
        let (x, _, _) = a.decimal(270);
        let (y, _, _) = b.decimal(270);
        assert_eq!(x[..260], y[..260]);
    }
    // a pair of roots far below double precision is separated as well
    let mut m = vec![0i64; 13];
    m[0] = 1;
    m[10] = -20_000_000_000_000_000;
    m[11] = 400_000_000;
    m[12] = -2;
    let (out, complete, stats) = all_roots_exact_precise(&ints(&m), &Options { full_order: true, ..Options::default() });
    assert!(complete && stats.within_tolerance && out.len() == 12);
}

#[test]
fn zero_roots_are_exact_and_cost_nothing() {
    let o = Options::default();
    // z^5 (z - 1)(z + 2) = z^7 + z^6 - 2 z^5, in the four interfaces
    let cf = [1.0, 1.0, -2.0, 0.0, 0.0, 0.0, 0.0, 0.0].map(|x| C::new(x, 0.0));
    let ci = ints(&[1, 1, -2, 0, 0, 0, 0, 0]);
    for (out, complete, stats) in [all_roots(&cf, &o), all_roots_exact(&ci, &o)] {
        assert!(complete && stats.within_tolerance && out.len() == 3);
        assert!(out[1].z.re == 0.0 && out[1].z.im == 0.0 && out[1].radius == 0.0 && out[1].mult == 5 && out[1].count == 1 && out[1].real);
        assert!(contains(&out[0], -2.0, 0.0) && contains(&out[2], 1.0, 0.0) && out[0].mult == 1 && out[2].mult == 1);
        // no disc of the other factor reaches the root 0
        assert!(out[0].z.abs() > out[0].radius && out[2].z.abs() > out[2].radius);
    }
    let p = Options { tol: 1e-40, ..Options::default() };
    for (out, complete, stats) in [all_roots_precise(&cf, &p), all_roots_exact_precise(&ci, &p)] {
        assert!(complete && stats.within_tolerance && out.len() == 3);
        assert_eq!(out[1].decimal(40), ("0".to_string(), "0".to_string(), "0".to_string()));
        assert!(out[1].mult == 5 && out[1].real);
    }
    // a monomial, with a complex leading coefficient
    let (out, complete, _) = all_roots(&[C::new(0.0, 3.0), C::new(0.0, 0.0), C::new(0.0, 0.0)], &o);
    assert!(complete && out.len() == 1 && out[0].mult == 2 && out[0].radius == 0.0 && !out[0].real);
    let (out, complete, _) = all_roots_exact(&ints(&[7, 0, 0, 0]), &o);
    assert!(complete && out.len() == 1 && out[0].mult == 3 && out[0].radius == 0.0 && out[0].real);
    // the root 0 next to multiple roots: z^2 (z - 1)^2 (z + 3)
    let (out, complete, _) = all_roots_exact(&ints(&[1, 1, -5, 3, 0, 0]), &o);
    assert!(complete && out.len() == 3);
    let got: Vec<(i64, usize)> = out.iter().map(|d| (d.z.re.round() as i64, d.mult)).collect();
    assert_eq!(got, vec![(-3, 1), (0, 2), (1, 2)]);
    // roots far below the unit circle next to the root 0: z^3 - 10^-300 z
    let (out, complete, _) = all_roots(&[1.0, 0.0, -1e-300, 0.0].map(|x| C::new(x, 0.0)), &o);
    assert!(complete && out.len() == 3 && out[1].radius == 0.0 && out[1].mult == 1);
    assert!(contains(&out[0], -1e-150, 0.0) && contains(&out[2], 1e-150, 0.0));
    assert!(out[0].radius < 1e-160 && out[2].radius < 1e-160);
}

#[test]
fn square_free_factors_of_a_complex_polynomial() {
    // (z - i)^3 (z + 1 + 2i)^2 (z - 4), expanded with Gaussian integers
    let mul = |a: &[(i64, i64)], b: &[(i64, i64)]| {
        let mut r = vec![(0i64, 0i64); a.len() + b.len() - 1];
        for (i, x) in a.iter().enumerate() {
            for (j, y) in b.iter().enumerate() {
                r[i + j].0 += x.0 * y.0 - x.1 * y.1;
                r[i + j].1 += x.0 * y.1 + x.1 * y.0;
            }
        }
        r
    };
    let mut p = vec![(1i64, 0i64)];
    for f in [[(1, 0), (0, -1)], [(1, 0), (0, -1)], [(1, 0), (0, -1)], [(1, 0), (1, 2)], [(1, 0), (1, 2)], [(1, 0), (-4, 0)]] {
        p = mul(&p, &f);
    }
    let ci: Vec<(BigInt, BigInt)> = p.iter().map(|&(a, b)| (BigInt::from(a), BigInt::from(b))).collect();
    let (out, complete, stats) = all_roots_exact(&ci, &Options::default());
    assert!(complete && stats.within_tolerance && out.len() == 3);
    assert!(contains(&out[0], -1.0, -2.0) && out[0].mult == 2);
    assert!(contains(&out[1], 0.0, 1.0) && out[1].mult == 3);
    assert!(contains(&out[2], 4.0, 0.0) && out[2].mult == 1);
}

#[test]
fn roots_closer_than_the_tolerance_need_not_be_isolated() {
    // z^12 - 2 (10^8 z - 1)^2: two roots near 10^-8, about 10^-48 apart relative to their size
    let mut c = vec![0i64; 13];
    c[0] = 1;
    let ci: Vec<(BigInt, BigInt)> = {
        let mut v = ints(&c);
        v[10].0 = BigInt::from(-20_000_000_000_000_000i64);
        v[11].0 = BigInt::from(400_000_000i64);
        v[12].0 = BigInt::from(-2);
        v
    };
    let approx = Options { isolate: false, ..Options::default() };
    let (out, complete, stats) = all_roots_exact(&ci, &approx);
    assert!(complete && !stats.within_tolerance && out.len() == 11);
    assert_eq!(out.iter().map(|d| d.mult * d.count).sum::<usize>(), 12);
    let pair: Vec<_> = out.iter().filter(|d| d.count == 2).collect();
    assert!(pair.len() == 1 && (pair[0].z.re - 1e-8).abs() < 1e-15 && pair[0].radius <= 1e-10 * pair[0].z.abs());
    assert!(out.iter().all(|d| d.radius <= 1e-10 * d.z.abs()));
    // the default goal gives the same discs in double precision: two roots that doubles cannot tell apart
    // are no longer separated before being put back in one disc (0.9.0; version 0.8.0 took 43 sweeps with
    // more bits here), and the step of a cluster brings the two points to the pair at once
    let (iso, _, iso_stats) = all_roots_exact(&ci, &Options::default());
    assert!(iso.len() == 11 && iso.iter().filter(|d| d.count == 2).count() == 1, "{:?}", iso_stats);
    assert!(iso_stats.precise_sweeps <= 6, "precise sweeps {}", iso_stats.precise_sweeps);
    // with centres of any precision the default goal separates them, at any tolerance
    let (sep, complete, sep_stats) = all_roots_exact_precise(&ci, &Options::default());
    assert!(complete && sep_stats.within_tolerance && sep.len() == 12 && sep.iter().all(|d| d.count == 1));
    // without the step of a cluster: the same discs, more sweeps
    let plain = Options { cluster: false, ..Options::default() };
    let (old, complete, old_stats) = all_roots_exact_precise(&ci, &plain);
    assert!(complete && old.len() == 12 && old_stats.precise_sweeps >= sep_stats.precise_sweeps, "{} against {}", old_stats.precise_sweeps, sep_stats.precise_sweeps);
    // a tolerance below the distance between the two roots: they are separated with either goal
    let fine = Options { tol: 1e-60, isolate: false, ..Options::default() };
    let (out, complete, stats) = all_roots_exact_precise(&ci, &fine);
    assert!(complete && stats.within_tolerance && out.len() == 12 && out.iter().all(|d| d.count == 1));
    // roots farther apart than the tolerance: the goal changes nothing
    let w = from_roots(&(1..=20).collect::<Vec<i64>>());
    let (a, ca, _) = all_roots_exact(&w, &Options::default());
    let (b, cb, sb) = all_roots_exact(&w, &approx);
    assert!(ca && cb && sb.within_tolerance && a.len() == 20 && b.len() == 20);
    assert!(a.iter().zip(&b).all(|(x, y)| x.z.re == y.z.re && x.z.im == y.z.im && x.radius == y.radius && x.count == 1 && y.count == 1));
}
