//! hp_bench FILE TOL MODE REPS
//! FILE: one polynomial per line, "int: c_m ... c_0" (highest degree first, integers).
//! MODE: default | full (Options::full_order).  Calls all_roots_exact_precise, the public function of the
//! crate for points of any precision, and prints one line per polynomial:
//!   ms <best of REPS> discs <n> complete <0|1> within_tol <0|1> sweeps <s> certs <c> exact <e> precise <p> bits <b>
//! The discs of the first run are written to FILE.MODE.out in decimal: re im radius mult count real.
use num_bigint::BigInt;
use pandroots::{all_roots_exact_precise, Options};
use std::io::Write;
use std::time::Instant;

fn main() {
    let a: Vec<String> = std::env::args().collect();
    let text = std::fs::read_to_string(&a[1]).unwrap();
    let tol: f64 = a[2].parse().unwrap();
    let mode = a[3].as_str();
    let reps: usize = a[4].parse().unwrap();
    let opt = Options { tol, full_order: mode == "full", ..Options::default() };
    let digits = (-tol.max(1e-280).log10()).ceil() as usize + 10;
    let mut f = std::io::BufWriter::new(std::fs::File::create(format!("{}.{}.out", a[1], mode)).unwrap());
    for l in text.lines().filter(|l| !l.trim().is_empty()) {
        let c: Vec<(BigInt, BigInt)> = l.strip_prefix("int:").unwrap().split_whitespace().map(|t| (t.parse::<BigInt>().unwrap(), BigInt::from(0))).collect();
        let mut best = f64::INFINITY;
        let mut first = None;
        for _ in 0..reps {
            let t0 = Instant::now();
            let r = all_roots_exact_precise(&c, &opt);
            best = best.min(t0.elapsed().as_secs_f64());
            if first.is_none() {
                first = Some(r);
            }
        }
        let (roots, comp, st) = first.unwrap();
        println!("ms {:.3} discs {} complete {} within_tol {} sweeps {} certs {} exact {} precise {} bits {}", 1e3 * best, roots.len(), comp as u8, st.within_tolerance as u8, st.sweeps, st.certificates, st.exact_sweeps, st.precise_sweeps, st.bits);
        writeln!(f, "poly {} {}", roots.len(), comp as u8).unwrap();
        for d in &roots {
            let (re, im, rad) = d.decimal(digits);
            writeln!(f, "{} {} {} {} {} {}", re, im, rad, d.mult, d.count, d.real as u8).unwrap();
        }
    }
}
