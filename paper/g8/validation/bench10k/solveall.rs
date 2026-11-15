// solveall LIST OUT : solves every polynomial of the list once (doubles interface, default options) and
// writes, for each, a line "poly <file> <degree> <seconds> <complete> <within_tolerance> <discs> <sweeps>
// <exact_sweeps> <precise_sweeps> <bits>" followed by one line per disc: re im radius mult count real.
use num_bigint::BigInt;
use pandroots::{all_roots, all_roots_exact, Options, C};
use std::io::Write;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let list = std::fs::read_to_string(&a[1]).unwrap();
    let mut out = std::io::BufWriter::new(std::fs::File::create(&a[2]).unwrap());
    let opt = Options::default();
    let t = std::time::Instant::now();
    let (mut n_poly, mut complete) = (0usize, 0usize);
    for f in list.lines() {
        let text = std::fs::read_to_string(f).unwrap();
        let mut it = text.split_whitespace();
        let kind = it.next().unwrap();
        let n: usize = it.next().unwrap().parse().unwrap();
        let t1;
        let (r, c, s) = if kind == "F" {
            let p: Vec<C> = (0..=n).map(|_| C::new(it.next().unwrap().parse().unwrap(), it.next().unwrap().parse().unwrap())).collect();
            t1 = std::time::Instant::now();
            all_roots(&p, &opt)
        } else {
            let p: Vec<(BigInt, BigInt)> = (0..=n).map(|_| (it.next().unwrap().parse().unwrap(), it.next().unwrap().parse().unwrap())).collect();
            t1 = std::time::Instant::now();
            all_roots_exact(&p, &opt)
        };
        let e = t1.elapsed().as_secs_f64();
        n_poly += 1;
        complete += c as usize;
        writeln!(out, "poly {} {} {:.6e} {} {} {} {} {} {} {}", f, n, e, c as u8, s.within_tolerance as u8, r.len(), s.sweeps, s.exact_sweeps, s.precise_sweeps, s.bits).unwrap();
        for d in &r {
            writeln!(out, "{:e} {:e} {:e} {} {} {}", d.z.re, d.z.im, d.radius, d.mult, d.count, d.real as u8).unwrap();
        }
    }
    println!("{} polynomials, {} complete, {:.2} s in all", n_poly, complete, t.elapsed().as_secs_f64());
}
