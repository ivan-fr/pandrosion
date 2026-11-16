use pandroots::{all_roots, Options, C};
use std::io::{BufRead, BufWriter, Write};
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let f = std::io::BufReader::new(std::fs::File::open(&a[1]).unwrap());
    let mut o = BufWriter::new(std::fs::File::create(&a[2]).unwrap());
    let opt = Options::default();
    for (i, line) in f.lines().enumerate() {
        let v: Vec<f64> = line.unwrap().split_whitespace().map(|x| x.parse().unwrap()).collect();
        let c: Vec<C> = v.chunks(2).map(|p| C::new(p[0], p[1])).collect();
        let t = std::time::Instant::now();
        let (roots, complete, st) = all_roots(&c, &opt);
        let ns = t.elapsed().as_nanos();
        write!(o, "{} {} {} {} {} {}", complete as u8, st.within_tolerance as u8, ns, st.sweeps, st.exact_sweeps + st.precise_sweeps, roots.len()).unwrap();
        for r in &roots { write!(o, " {:e} {:e} {:e} {} {}", r.z.re, r.z.im, r.radius, r.mult, r.count).unwrap(); }
        writeln!(o).unwrap();
        if i % 1000 == 999 { o.flush().unwrap(); eprintln!("{} {}", a[1], i + 1); }
    }
}
