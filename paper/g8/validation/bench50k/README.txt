bench50k - 50 000 polynomials of degree 2 to 60, with an independent check of the discs
======================================================================================
The benchmark of the author for pandroots 0.12.0 (gen.py, runner/, verify.py, rest.py and results_0.12.0/
are the author's files, unchanged), run again for 0.13.0.  Eight families, coefficients written as exact doubles,
seed 20261116:

  real_gauss 12 000, complex_gauss 9 000 (degree 2 to 40), small_int 6 000 (coefficients -9..9, degree 2 to
  30), kac_pm1 5 000 (coefficients +-1, degree 5 to 60), wide_scale 5 000 (coefficients over forty orders of
  magnitude), integer_roots_mult 6 000 and gaussian_roots_mult 4 000 (prescribed roots, often repeated),
  real_cluster 3 000 (3 to 8 real roots 10^-4 to 10^-1 apart, coefficients rounded).

  gen.py        writes fam_<family>.txt (one polynomial per line) and truth_<family>.txt (the prescribed
                roots, or "-").
  runner/       runner FAM OUT: one call of all_roots per polynomial; for each, the flags, the time in
                nanoseconds, the sweeps and the discs.  Its Cargo.toml asks for pandroots = "=0.12.0" from
                crates.io; for 0.13.0 the dependency was pointed at ../../pandroots (path = "...").
  verify.py     every polynomial: complete, within tolerance, multiplicities adding up to the degree, discs
                pairwise disjoint; the prescribed roots where there are some (each in one disc, with its
                multiplicity); numpy.roots elsewhere (as many of its roots in each disc as the disc says);
                and mpmath.polyroots at 60 digits on a sample of 350 polynomials per family and on those
                where numpy disagrees (up to 400 per family).  Writes summary.json.
  rest.py       mpmath on every polynomial where numpy disagrees, for the three families that have some.
  compare.py    two versions: times and discs (see its first lines).
  results_0.12.0/   the author's run of 0.12.0 (another machine).
  results_0.13.0/   0.13.0 on an Intel Xeon at 2.1 GHz: verify.log, summary.json, rest.log, and compare.txt
                    (0.12.0 against 0.13.0 on that machine, two runs each).
  results_0.14.0/   the same for 0.14.0.

Results for 0.13.0
  verify.py   50 000 complete and within tolerance; no multiplicity sum off, no two discs that meet, no
              prescribed root missed (10 000 polynomials); numpy disagrees on 2 753 polynomials (wide_scale
              1 137, real_cluster 1 613, kac_pm1 3), as with 0.12.0: these are numpy's roots, not the discs.
              mpmath: 2 830 polynomials checked, 2 830 right.
  rest.py     the 2 753 polynomials where numpy disagrees, each against mpmath: 2 753 right.
  compare.py  0.12.0 2.84 s, 0.13.0 1.97 s for the 50 000; the discs (multiplicities and counts) are the
              same on every polynomial.  Median of a dense real polynomial 56 us -> 36 us.
Results for 0.14.0 (results_0.14.0/)
  verify.py and rest.py: the same counts as for 0.13.0, without a failure.
  compare.py  0.12.0 3.03 s, 0.13.0 2.10 s, 0.14.0 1.90 s, the three versions in one run (the machine is
              shared: the same 0.12.0 took 2.84 s in the run of results_0.13.0/); the same discs.  Only the
              real clusters change with 0.14.0 (0.45 s -> 0.25 s): the other families do not go beyond
              double precision.
The times of results_0.12.0/ and of the summary.json of the two other directories come from two machines
and are not to be compared with one another; the files compare.txt are comparisons on one machine.
