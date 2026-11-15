//! pandroots-bench FILE [REPS] [MODE] [TOL] [precise]
//! FILE: one polynomial per line, "re im re im ..." (highest degree first), or "int: c0 c1 ..." with big
//! integer coefficients.  MODE: g8 (default) | full (multiprecision sweeps at their full order) | jacobi | circle | aberth.
//! TOL: relative radius aimed at (default 1e-10).  Below 1e-12 the centres are written in decimal with as
//! many digits as needed (functions all_roots_precise, all_roots_exact_precise); the word `precise` asks for
//! that output at any tolerance.
//! Prints the best time per polynomial over REPS runs and writes the roots to FILE.out, one line per disc:
//! re im radius multiplicity count real.
use num_bigint::BigInt;
use pandroots::{all_roots, all_roots_exact, all_roots_exact_precise, all_roots_precise, Announce, Options, Start, Support, C};
use std::io::Write;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let text = std::fs::read_to_string(&args[1]).expect("file");
    let reps: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(5);
    let mode = args.get(3).map(|s| s.as_str()).unwrap_or("g8");
    let mut opt = Options::default();
    if let Some(t) = args.get(4).and_then(|s| s.parse::<f64>().ok()) {
        opt.tol = t;
    }
    let precise = opt.tol < 1e-12 || args.get(5).map(|s| s == "precise").unwrap_or(false);
    match mode {
        "jacobi" => opt.gauss_seidel = false,
        "full" => opt.full_order = true,
        "circle" => opt.start = Start::Circle,
        "aberth" => {
            opt.outer = Support::AK;
            opt.announce = Announce::None;
        }
        "ak-ak" => {
            opt.outer = Support::AK;
            opt.announce = Announce::AK;
        }
        "ak-ak-jacobi" => {
            opt.outer = Support::AK;
            opt.announce = Announce::AK;
            opt.gauss_seidel = false;
        }
        "ak-three" => {
            opt.outer = Support::AK;
        }
        "three-ak" => opt.announce = Announce::AK,
        "three-none" => opt.announce = Announce::None,
        "aberth-jacobi" => {
            opt.outer = Support::AK;
            opt.announce = Announce::None;
            opt.gauss_seidel = false;
        }
        _ => {}
    }
    enum In {
        F(Vec<C>),
        I(Vec<(BigInt, BigInt)>),
    }
    let polys: Vec<In> = text
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            if let Some(rest) = l.strip_prefix("int:") {
                In::I(rest.split_whitespace().map(|t| (t.parse::<BigInt>().unwrap(), BigInt::from(0))).collect())
            } else {
                let v: Vec<f64> = l.split_whitespace().map(|t| t.parse().unwrap()).collect();
                In::F(v.chunks(2).map(|p| C::new(p[0], p[1])).collect())
            }
        })
        .collect();
    let run = |p: &In| match p {
        In::F(c) => all_roots(c, &opt),
        In::I(c) => all_roots_exact(c, &opt),
    };
    let mut best = f64::INFINITY;
    let mut results = Vec::new();
    for rep in 0..reps {
        let t0 = Instant::now();
        let res: Vec<_> = polys.iter().map(run).collect();
        best = best.min(t0.elapsed().as_secs_f64());
        if rep == 0 {
            results = res;
        }
    }
    let n = polys.len() as f64;
    let sweeps: usize = results.iter().map(|r| r.2.sweeps).sum();
    let certs: usize = results.iter().map(|r| r.2.certificates).sum();
    let exact: usize = results.iter().map(|r| r.2.exact_sweeps).sum();
    let fp = results.iter().filter(|r| r.2.factors == r.2.fixed_point).count();
    let complete = results.iter().filter(|r| r.1 && r.0.iter().all(|d| d.count == 1)).count();
    let ts = |f: &dyn Fn(&pandroots::Stats) -> f64| 1e6 * results.iter().map(|r| f(&r.2)).sum::<f64>() / n;
    println!(
        "mode {} polys {} time_us {:.3} t_sqfree {:.3} t_sweeps {:.3} t_certify {:.3} sweeps {:.3} certificates {:.3} exact_sweeps {:.3} isolated_complete {} fixed_point {}",
        mode,
        polys.len(),
        1e6 * best / n,
        ts(&|s| s.t_sqfree),
        ts(&|s| s.t_sweeps),
        ts(&|s| s.t_certify),
        sweeps as f64 / n,
        certs as f64 / n,
        exact as f64 / n,
        complete,
        fp
    );
    let mut f = std::io::BufWriter::new(std::fs::File::create(format!("{}.out", args[1])).unwrap());
    if precise {
        let digits = (-opt.tol.max(1e-280).log10()).ceil() as usize + 10;
        for p in &polys {
            let (roots, comp, st) = match p {
                In::F(c) => all_roots_precise(c, &opt),
                In::I(c) => all_roots_exact_precise(c, &opt),
            };
            writeln!(f, "poly {} {} {} {} {} {} {}", roots.len(), comp as u8, st.sweeps, st.certificates, st.exact_sweeps, st.precise_sweeps, st.bits).unwrap();
            for d in &roots {
                // enough digits for the decimal rounding of the centre to be far below the radius, which
                // is printed enlarged by that rounding
                let (re, im, radius) = d.decimal(digits);
                writeln!(f, "{} {} {} {} {} {}", re, im, radius, d.mult, d.count, d.real as u8).unwrap();
            }
        }
        return;
    }
    for (roots, comp, st) in &results {
        writeln!(f, "poly {} {} {} {} {}", roots.len(), *comp as u8, st.sweeps, st.certificates, st.exact_sweeps).unwrap();
        for d in roots {
            writeln!(f, "{:e} {:e} {:e} {} {} {}", d.z.re, d.z.im, d.radius, d.mult, d.count, d.real as u8).unwrap();
        }
    }
}
