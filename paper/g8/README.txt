Later than revision 9: pandroots 0.13.0 and 0.14.0 (16 November 2026)
=====================================================================
validation/pandroots now holds the crate 0.14.0, which is later than the note and than the archive of
revision 9 on Zenodo (crate 0.12.0; its sources are in the history of this repository).  The note, its
tables and every log and result file listed below are those of 0.12.0 and are unchanged.  What 0.13.0 and
0.14.0 add is in validation/pandroots/CHANGELOG.md and README.md: the same method, with the same step and
the same certificate, at a lower cost (0.13.0: the product by a double precision point in one pass,
Horner's rule over runs of zero coefficients, the certificate computed once, no evaluation made twice;
0.14.0: Horner's rule on long integers in two's complement, the bits of a value asked in advance).
  validation/bench20k/   the crate alone on 20 000 polynomials (the 10 000 of bench10k and 10 000 more):
                         0.12.0 54.0 s, 0.13.0 29.1 s, 0.14.0 18.4 s on an Intel Xeon at 2.1 GHz; the discs
                         of 0.14.0 are those of 0.13.0, and those of 0.12.0 on 19 989 polynomials (the 11
                         others are clusters at the limit of double precision centres); the discs of the
                         7 249 polynomials with prescribed rational roots checked in exact arithmetic
                         (none wrong).  See validation/bench20k/README.txt.
  validation/bench50k/   50 000 polynomials of degree 2 to 60 in eight families, with their check against
                         known roots, numpy and mpmath: 0.12.0 3.03 s, 0.13.0 2.10 s, 0.14.0 1.90 s in one
                         run, the same discs.
  validation/v0_13_0/, validation/v0_14_0/   rust_check.py, underflow_check.py and precise_check.py run
                         again with each version on that machine (their logs; the verdicts are those of
                         0.12.0), and cargo test (35 and 36 tests).
Lean: three more files (fifteen theorems) for what 0.13.0 and 0.14.0 added, in
validation/pandroots/verification/lean, checked by the workflow .github/workflows/pandroots-lean.yml.
Not done for 0.13.0 and 0.14.0: the comparison with MPSolve, and a revision of the note.

G8, revision 9 - The simultaneous rectangle (Rust crate pandroots 0.12.0)
=======================================================================
Built on revision 8 (G8_source_r8.zip, 15 November 2026, crate 0.5.0); Sections 1 to 8 (the step, its order,
the certificate, the start, the algorithm, the trap, the measurements of the Python prototype), the figures
and the 38 theorems of G8 in Lean are unchanged.

New in revision 9
  * Section 10, "The step of a cluster" (crate 0.9.0 and 0.10.0): why the sweep is linear near a cluster
    (measured factors 1/4, 0.40, 4/7), Proposition 10.1 (the step of degree K is exact for a shifted power),
    the tight cluster, the cursor in multiprecision, roots that doubles cannot tell apart, the option isolate.
  * Section 9 describes pandroots 0.12.0: the root zero (0.6.0), the square-free decomposition over the
    Gaussian integers (0.6.0) and by gcds modulo primes (0.11.0), numbers of a fixed width (0.7.0), the bits
    of each point and the scaled variable (0.8.0, corrected in 0.10.1), coefficients beyond the range of
    doubles (0.11.0), the choice between two starts (0.12.0).
  * Comparison with MPSolve 3.2.3 (Tables 7 and 8): the harness was run again for each version from 0.5.0
    to 0.10.1 on the same corpus (462 polynomials, 100 at 14, 30 and 80 digits); the tables give 0.5.0 and
    0.10.1.  Version 0.12.0 was not run against MPSolve.  The harness and its results are not in this
    archive (they are with the author, one folder per version).
  * The crate alone on 10 000 polynomials of sixteen families (Table 9): the solver's own flags and times,
    without an independent check of the discs.  Corpus generator and scripts: validation/bench10k/.
  * Section 11: 31 more theorems in Lean (five files, checked with Lean 4.35.0 / Mathlib v4.35.0, shipped in
    validation/pandroots/verification/lean with their logs); what is not formalised; the limits as they are
    with 0.12.0.
  * All the Rust measurements run again with 0.12.0 on an Apple M5 in use by other programs:
      validation/rust_check.py    results_rust.txt (2608/2608 certified, 17/17 families, 60/60 multiplicities)
      validation/simple.py        results_simple.txt (Table 11)
      validation/underflow_check.py  results_edge.txt, underflow_check.log
      validation/precise_check.py results_precise.txt (124/124, Table 6) - needs hp_bench
      validation/cluster_step.py  the multiprecision model of the sweep and of the step near a cluster
      cargo test --release in validation/pandroots: 30 tests pass (cargo_test.log).
    The results of revision 8 (crate 0.5.0) are kept in r8_results/.
  * A correction of validation/underflow_check.py.  The crate prints the centre of a disc as the shortest
    decimal that reads back as the same double; the script read that decimal as an exact number, which
    differs from the double by up to 1e-16 of the centre.  Up to revision 8 every radius was far above that
    difference.  With 0.11.0 and later some radii are below it (3e-17 of the centre), and the uncorrected
    script reported 6 discs of 0.12.0 as wrong; read as the doubles they are, the 6 discs contain their
    roots.  The script now reads double precision output through float().  No disc of the crate is wrong
    in these runs.
  * Found while preparing this revision, and corrected in the crate: a slowdown of versions 0.8.0 to 0.10.0
    at large degree and high precision (0.10.1), the slow square-free decomposition of 0.6.0 to 0.10.1 on
    polynomials with multiple roots and large coefficients (0.11.0), incomplete answers for roots over more
    than 200 orders of magnitude (0.11.0).  None gave a wrong disc.

Run (from validation/):  (cd pandroots && RUSTFLAGS="-C target-cpu=native" cargo build --release --bin bench)
                         (cd hp_bench && RUSTFLAGS="-C target-cpu=native" cargo build --release)
                         python3 rust_check.py; python3 simple.py > results_simple.txt
                         python3 underflow_check.py; python3 precise_check.py; python3 cluster_step.py
paper/main.tex           source of the note (tectonic or pdflatex, two passes), with its figures fig_*;
                         paper/main_r8.tex is the source of revision 8.
