G8, revision 8 - The simultaneous rectangle (Rust crate pandroots 0.5.0)
=======================================================================
Built on revision 7 (G8_source.zip, 14 November 2026); sections 1 to 8, the figures and the Lean files are
unchanged except where the multiprecision values of the crate are mentioned.

New in revision 8
  * Section 9 describes pandroots 0.5.0: the fixed-point ball evaluation of S, S', S'' (0.3.0), the step
    written as N/(1+w) with N = S/S' a multiprecision quotient (0.4.0: digits doubled per sweep), the
    option full_order (0.5.0: the whole step in multiprecision, order six, not faster), S', S'' with fewer
    bits; the repairs of 0.3.0 (shift of the variable, Mignotte pairs, degree one).
  * Comparison with MPSolve 3.2.3 (Table 7): figures as reported in the crate's README (external harness,
    not rerun here).
  * All the Rust measurements rerun with 0.5.0 on an Apple M5 (load average about 5):
      validation/rust_check.py    results_rust.txt (2608/2608 certified, 17/17 families, 60/60 multiplicities)
                                  results_rust_run1.txt: an earlier, noisier run of the same script
      validation/simple.py        results_simple.txt (Table 9)
      validation/underflow_check.py  results_edge.txt (195 edges: 189 sharp, 6 weak, 0 wrong;
                                  31 polynomials at 1e-30 and 1e-80: all certified)
      validation/precise_check.py results_precise.txt (new: all_roots_exact_precise, default and
                                  full_order, against mpmath; Table 6) - needs hp_bench (below)
      validation/hp_bench/        small harness calling all_roots_exact_precise (the crate's bench binary
                                  times the doubles interface only)
      cargo test --release in validation/pandroots: 19 tests pass.
  * Observed: Stats::within_tolerance is conservative (says no on Chebyshev 30 at 1e-80 with radii at
    0.88 of the tolerance); z^40 - 2(10^8 z - 1)^2 keeps its pair (1.4e-168 apart) in one disc by default,
    full_order separates it (checked at 1e-10, 1e-30, 1e-80).

Run (from validation/):  (cd pandroots && RUSTFLAGS="-C target-cpu=native" cargo build --release --bin bench)
                         (cd hp_bench && RUSTFLAGS="-C target-cpu=native" cargo build --release)
                         python3 rust_check.py; python3 simple.py > results_simple.txt
                         python3 underflow_check.py; python3 precise_check.py
paper/main.tex           source of the note (pdflatex or tectonic, two passes), with its figures fig_*
