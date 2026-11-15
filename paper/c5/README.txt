Complex Geometric Root Calculators, version C5 - sources

main.tex, *.png          manuscript (pdflatex main.tex, three passes)
LeanMath/Papers          ComplexRoots, ComplexHalfPlane, ArcHalfPlane, NestedHalfPlane,
                         ComplexSlitPlane, ThreeMeanSlitPlane, Audit
                         They go in LeanMath/Papers of the repository ivan-fr/pandrosion (Lean 4.33.1,
                         Mathlib v4.33.1). They import ArcOrderFive and NestedOrderNine from it, and
                         ThreeMeanSlitPlane imports ThreeMeanGlobal and ThreeMeanOrderNine of V29.
                         validation/complex_c5/Audit.lean prints the axioms of the 198 theorems.
                         New in C5: ComplexSlitPlane (4 theorems), ThreeMeanSlitPlane (66 theorems).
                         Changed in C5: NestedHalfPlane (real_residual_bound_gen and
                         order_of_real_limit now hold for every positive degree).
certify_halfplane.py     interval certificate of the half-plane boundary inequality (mpmath.iv)
certify_halfplane_arb.py the same with Arb ball arithmetic (pip install python-flint)
certify_threemean.py     half-plane boundary inequality of the three-mean support, p >= 4 (Arb)
certify_sector.py        certificate of the sector theorem, beta = 5 pi/6 (Arb)
sector_test.py           high-precision test of the sector theorem
verify_complex.py        numerical checks of the statements (mpmath, sympy)
verify_threemean.py      three-mean support: numerical checks and exact recomputation of the
                         polynomial certificates of the slit-plane theorem
realdeg.py               real degrees in the logarithmic chart; rows of the table for p = pi and 5/2
geometry.py              ruler-and-compass protocols, executed and counted
basins.py, logplane.py, geofig.py, tables.py, maps.py   figures and tables
