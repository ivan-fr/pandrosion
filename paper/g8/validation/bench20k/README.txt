bench20k - pandroots alone on 20 000 polynomials (crates 0.13.0 and 0.14.0)
===========================================================================
The 10 000 polynomials of bench10k (122 named cases and 9 878 generated, seed 20261116) and 10 000 more of
the same sixteen families from another seed (20261117, names m_*): 1 043 482 roots, degrees 1 to 2 000,
7 249 polynomials built from prescribed rational roots.

  make_corpus.sh DIR   writes DIR/cases/*.poly (88 MB), DIR/corpus.json and DIR/list.txt.  It copies
                       ../bench10k/add_extended_cases.py, ../bench10k/gen10k.py and gen20k.py to DIR and
                       runs them there in that order (python3 with numpy).  Deterministic; the first 10 000
                       files are those of bench10k.
  gen20k.py            the second 10 000.  The families that gen10k.py builds without random numbers are
                       taken elsewhere: orthogonal polynomials at fifty other degrees between 21 and 149,
                       truncated exponentials at the odd degrees, Kameny polynomials with c = 3 10^e,
                       iterated maps with other constants instead of the Mandelbrot polynomials.
  ../bench10k/solveall.rs   solveall LIST OUT: one call per polynomial (doubles interface, default
                       options), its time, the solver's flags and its discs.  Build it as a binary that
                       depends on the crate (Cargo.toml: pandroots = { path = "../pandroots" },
                       num-bigint = "0.4"; release profile of the crate; RUSTFLAGS="-C target-cpu=native").
  analyse.py DIR OUT[,OUT2] [BEFORE[,BEFORE2]]   the solver's own account by group; against the runs of
                       another version: discs that differ (multiplicities and counts), times.  Several
                       runs of one version: the smaller time of each polynomial.
  check_oracle.py DIR OUT   the discs against the prescribed roots, in exact rational arithmetic, for the
                       7 249 polynomials that have them: every root in one disc and only one, with its
                       multiplicity; every disc with as many roots as its count.  Independent of the solver.
  results_0.13.0.txt   0.13.0 against 0.12.0, two runs each, and the check of the discs.
  results_0.14.0.txt   0.14.0 against 0.13.0 and 0.12.0, the same way.

Results (results_0.13.0.txt, results_0.14.0.txt; Intel Xeon at 2.1 GHz, one thread)
  0.12.0   54.0 s   20 000 complete, 18 395 with every root in its own disc within 10^-10
  0.13.0   29.1 s   20 000 complete, 18 395 with every root in its own disc within 10^-10
  0.14.0   18.4 s   the same, and the same discs as 0.13.0 on every polynomial
  between 0.12.0 and 0.13.0 the discs (multiplicities and counts) are the same on 19 989 polynomials; the
  11 others are clusters with roots 10^-14 to 10^-16 of their size apart, at the limit of what double
  precision centres separate
  exact check of the discs on 7 249 polynomials, 70 364 distinct roots: none wrong (the three versions)
The 1 605 polynomials not "within 10^-10" are clusters and Mignotte pairs that double precision centres
cannot separate (one disc with their number) and Kameny polynomials.

What is not checked here: the discs of the 12 751 polynomials without prescribed roots (the figures are the
solver's own flags), and the comparison with MPSolve, which was not run for 0.13.0 or 0.14.0.  The scripts
of the directory above (rust_check.py, underflow_check.py, precise_check.py: numpy and mpmath as references)
were run again with each version (../v0_13_0, ../v0_14_0) and give the counts they gave with 0.12.0.
