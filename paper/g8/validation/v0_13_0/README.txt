The validation scripts of the directory above, run again with pandroots 0.13.0 (16 November 2026)
==================================================================================================
Intel Xeon at 2.1 GHz (4 cores of a shared virtual machine), Linux, rustc 1.97.0, Python 3 with numpy and
mpmath; RUSTFLAGS="-C target-cpu=native".  The files of the directory above are those of 0.12.0 on an Apple
M5 and are unchanged; the times here are those of another machine and are not comparable with them.

  rust_check.log, results_rust.txt         python3 rust_check.py: 2608/2608 certified and equal to numpy,
                                           17/17 hard families, 60/60 multiplicities
  underflow_check.log, results_edge.txt    python3 underflow_check.py: edges of double precision, 189 sharp
                                           and right, 6 true but weak, 0 wrong; at 1e-20, 1e-30 and 1e-80
                                           190 + 31 + 31 certified within the tolerance, 0 wrong
  precise_check.log, results_precise.txt   python3 precise_check.py (with hp_bench): 31/31 at 1e-30 and at
                                           1e-80, default and full order; the 13 named polynomials pass
  cargo_test.log                           cargo test --release in pandroots: 35 tests pass (also in a debug
                                           build)
The verdicts are those of the logs of 0.12.0, count for count.  In precise_check the largest radius against
the tolerance is 0.24 at 1e-30 and 0.43 at 1e-80 with full order (0.26 and 0.27 with 0.12.0; below 1 is a pass):
the points of the double precision stage are not the same to the last bit.
