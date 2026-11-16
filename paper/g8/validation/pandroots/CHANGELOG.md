# Changelog

## 0.14.0 - 2026-11-16

The stage of exact values (double precision points, values of S beyond double precision) cost two thirds
of the time of 0.13.0 on the 20 000 polynomials, and three quarters of that was Horner's rule on fixed
width integers.  This version is about that loop.  The method is unchanged, and the integers computed are
those of 0.13.0: the discs are the same on every one of the 20 000 and of the 50 000 polynomials.

- Horner's rule for a point with few bits in two's complement (`limbs::horner3_tc`).  Every step of it is
  "multiply two numbers by two small signed integers, add, shift right, add a third number".  In sign and
  magnitude (0.7.0, and the pass of 0.13.0) each of these looks at the signs, compares magnitudes and may
  negate.  In two's complement none does: the products are accumulated with a signed carry, and the shift
  that fills with the sign bit is the quotient towards minus infinity, the rounding of `BigInt >> k`.
  When the shift is below one limb, which is the case of a double precision point of the unit disc, the
  three operations are one pass over the limbs (`tc_step`): each limb of the product completes a limb of
  the quotient, to which the limb of the addend is added at once.  A number that does not fit its width,
  one bit less than before, sends the evaluation to the loop of 0.13.0.  Tested against the `BigInt` loop
  on 3 000 polynomials and points, with the limits of the shift, of the sum and of the width.
- The coefficients rounded to F bits are kept as limbs, one table for each F (`limbs::Table`): they were
  converted from `BigInt` at every step of every evaluation.
- The bits of the next value of a point.  A point that moves by 2^-b of its modulus has about b correct
  bits and, if the step keeps its order, at least 3 b after it, 53 at most; S is that many bits smaller
  there, and F is raised by min(2 b, 53 - b) before the evaluation.  One evaluation in five of this stage
  was an attempt with too few bits, made again; one in ten now.
- The test "square-free modulo a prime" of 0.13.0 took its remainders without the inverse of the leading
  coefficient, which multiplies what is left of the dividend at every step: quadratic when the degree
  drops by much, as for a polynomial with few terms (3 ms for `z^2000 + z + 1`, against 0.1 ms with
  0.12.0).  The inverse is used again when the degree drops by more than eight.
- The points of the start are checked to be distinct by sorting them above degree 64 (the pairs took a
  millisecond at degree 2000).

Measurements (one call per polynomial, one thread, Intel Xeon at 2.1 GHz, the smaller of two runs for each
polynomial; 0.12.0, 0.13.0, 0.14.0):

- The 20 000 polynomials: 54.0 s, 29.1 s, 18.4 s (the first 10 000: 22.3 s, 12.0 s, 8.0 s).  The 2 966
  that reach the stage of exact values: 34.4 s, 21.0 s, 10.4 s.  By degree: up to 20, 2.0 s, 1.8 s, 1.7 s;
  21 to 100, 16.0 s, 10.8 s, 6.3 s; 101 to 400, 21.2 s, 11.7 s, 5.8 s; 401 to 2000, 14.9 s, 4.7 s, 4.6 s.
- One call, in ms: Laguerre 150, 287, 81, 41; Chebyshev T 150, 182, 108, 47; Wilkinson 100, 128, 60, 33;
  Mandelbrot 255, 701, 367, 182; truncated exponential 120, 50, 38, 15; `(z - a)^60 - b`, 24, 15, 7.5.
- The 50 000 polynomials of degree 2 to 60, the three versions run one after the other: 3.03 s, 2.10 s,
  1.90 s.  Only the real clusters, three quarters of which reach the stage of exact values, change with
  0.14.0 (median 137 us -> 76 us in that run); for the others double precision is enough.
- The discs (multiplicities and counts) are those of 0.13.0 on the 20 000 and on the 50 000.  Against
  0.12.0 the 11 clusters of the entry below differ, as they did.
- The 7 249 polynomials with prescribed rational roots, checked in exact rational arithmetic: none wrong.

Tests: the two's complement loop against `BigInt`.  36 tests, in release and debug builds.

Lean (added after the measurements, for 0.13.0 and 0.14.0): `CertificateGap.lean` (the test of the
certificate from the smallest gap implies the two inequalities of the theorem), `SparseHorner.lean` (the
closed form of a run of zero coefficients, the value of S alone, and the rounding of a power computed with
k products in any order) and `TwoComplement.lean` (the arithmetic shift as the floor, the power of two of
the multipliers, the limb of the quotient), and `FloatModel.lean` (from a definition of the format and of
the rounding to nearest: a relative error of at most 2^-p in the normal range, 2^-53 for doubles, and the
error of the complex product as the program computes it).  Twenty-four theorems, checked by the workflow
`Pandroots Lean files` of the repository (Lean 4.33.1 / Mathlib v4.33.1), standard axioms only.  Not
formalised: that the machine rounds this way (IEEE 754), the chain from one rounded operation to the
bound of Horner's rule with its term for underflows, and the Rust code.

## 0.13.0 - 2026-11-16

Found by profiling 0.12.0 on the 10 000 polynomials, then measured on 20 000 (the same and 10 000 more
from another seed) and on 50 000 polynomials of degree 2 to 60.  The method is unchanged: same step, same
certificate with the same bounds.  What changed is what they cost.

Values beyond double precision:

- The product of an accumulator by a double precision point in one pass.  Such a point, in units of 2^-F,
  is two integers of 53 bits at most times one power of two; `floor((a x_r - b x_i) / 2^F)` was two full
  products, a subtraction and a shift over twice the width, and is now one pass over the limbs of `a` and
  `b` with two multiplications each (`limbs::combine_short`).  Same integers, tested against `BigInt` on
  40 000 random pairs, sum and difference.  The points evaluated through 1/z, which has as many bits as F,
  keep the full products.
- The scaled variable `T(t) = S(2^e t)` is used while the bits it loses are at most F plus 32 (a quarter of
  F plus 32 from 0.10.1 to 0.12.0), and a value that cannot be told from zero is computed exactly only once
  F has passed 2 x 53 + 128 bits beyond the bits lost.  The slowdown that 0.10.1 corrected came mostly from
  that exact evaluation, with integers of 53 m bits, started when F minus the bits lost was too few to see
  the value; a few more bits of F show it.  Laguerre 150: 287 ms -> 81 ms; Mandelbrot 255: 701 ms -> 367 ms;
  Wilkinson 100: 128 ms -> 60 ms; Chebyshev T 150: 182 ms -> 108 ms.  Dense polynomials of degree 320 and
  640 at 30 digits (`precise` functions): unchanged within the noise.

Double precision:

- The points are rounded to 53 bits of their modulus as they move, which is what the certificate asks of
  them, so the last evaluation of each point by the sweeps is the one the certificate would make: it is not
  made twice (`float::simultaneous_bounds`).  A point whose residual is at rounding level does not move
  and is not evaluated again (`Poly::ev_some`).  A polynomial of degree 20 was evaluated at its points six
  times, four of them for its sweeps; a dense polynomial of degree 2000, whose points settle one after the
  other: 153 ms -> 59 ms.
- Polynomials with few terms (at most one coefficient in twelve is not zero, degree 23 or more): Horner's
  rule jumps over the runs of zero coefficients, `p <- p x^g + c` with `x^g` by repeated squaring, and S',
  S'' by the closed form of g steps with nothing to add.  The value of S goes through as many products and
  sums as in the dense rule or fewer, so the rounding bound of the certificate holds unchanged; what is
  added for the operations that underflow is larger (`Poly::tiny`).  `z^2000 + z + 1`: 72 ms -> 21 ms; the
  1 005 sparse polynomials of the corpus (3 to 9 terms, degree up to 1 500): 11.5 s -> 3.3 s.
- The fixed-point certificate was computed twice on the same points when double precision was enough (16
  of the 72 ms of `z^2000 + z + 1`): its radii and flags are now kept with the state they belong to, and
  that state is returned as it is, not copied.  A disc passes at once when the bounds `sigma_k <= W / g` and
  `tau_k <= W / g^2` (W the sum of the w_l, g the smallest gap of the point) pass the two tests, which
  costs one pass without square root or division; the sums are formed only for the points where this is
  not enough.  The loop of the sums is written on groups of four points so that the compiler turns it into
  vector instructions; its terms and their order are those of 0.12.0.
- Fixed costs of a small polynomial.  The test "square-free modulo a prime": the powers of two of the
  coefficients by doublings instead of one repeated squaring per coefficient, the remainders without the
  inverse of the leading coefficient (thirty squarings each), one copy of the loop per prime so that the
  modulus is a constant, and the residue of a big integer without another big integer.  The circle around
  the centroid, with its powers and cosines, is computed only when the dominant binomials give no start.
  `exact::quantize` without a call in the usual case.

Measurements (one call per polynomial, one thread, Intel Xeon at 2.1 GHz, the smaller of two runs for each
polynomial):

- The 20 000 polynomials (1 043 482 roots): 54.0 s -> 29.1 s (the first 10 000: 22.3 s -> 12.0 s).  All
  complete; 18 395 with every root in its own disc within 10^-10, as with 0.12.0.  By degree: up to 20,
  2.0 s -> 1.8 s; 21 to 100, 16.0 s -> 10.8 s; 101 to 400, 21.2 s -> 11.7 s; 401 to 2000, 14.9 s -> 4.7 s.
  Of the 7 346 polynomials that take more than 0.2 ms, 2 604 are more than 1.5 times faster and 3
  (clusters, 0.2 to 1.7 ms) more than 1.5 times slower in these runs.
- 50 000 polynomials of degree 2 to 60 in eight families (`bench50k`): 2.84 s -> 1.97 s; median of a dense
  real polynomial 56 us -> 36 us, of a polynomial with coefficients +-1 88 us -> 57 us.
- The discs (multiplicities and counts) are those of 0.12.0 on the 50 000, and on 19 989 of the 20 000.
  The 11 others are clusters whose roots are 10^-14 to 10^-16 of their size apart, at the limit of what
  double precision centres separate: the points reach the cluster by another path (they are rounded as
  they move), and 5 of the 11 come out with more roots in their own disc, 6 with fewer.  The 11 are among
  the polynomials checked below, and are right with either version.
- For the 7 249 polynomials of the 20 000 built from prescribed rational roots, the discs were checked in
  exact rational arithmetic against those roots (`bench20k/check_oracle.py`): 70 364 distinct roots, each
  in one disc and only one, with its multiplicity and the right count.  No disc wrong, for 0.12.0 either.

Tests: the product by a short multiplier against `BigInt`; the evaluation over runs of zeros against the
dense rule; the flags of the certificate against the two sums formed one term at a time; `quantize`;
`z^600 - 2` and a trinomial of degree 400 with its reversed polynomial.  35 tests.  The test of subnormal
coefficients builds 2^-1070 from its bits: `2f64.powi(-1070)` is zero without optimisation, and that test
failed in debug builds (the solver was given the zero polynomial); the 35 pass in both builds.

## 0.12.0 - 2026-11-15

- When double precision is not enough for a quarter of the points or more, the sweeps with values beyond
  double precision start from the better of two sets of points.  Their number depends on the start far
  more than on the double precision sweeps before them (which, on Laguerre 150, leave 141 points of 150
  nowhere near a root): 37 sweeps of hundreds of bits from the start of G8, 20 from a start where each
  edge of the Newton polygon keeps its own binomial (new `Start::Edges`), and the reverse on a Mandelbrot
  polynomial.  The points of the stage are evaluated on a sample of 24 at most; if they are far from the
  roots, the other start is computed, sampled the same way, and taken if its median Smith radius is 2^16
  times smaller.  Nothing is done when double precision sufficed.  Laguerre 150: 600 ms -> 243 ms,
  Laguerre 100: 56 ms -> 28 ms; the 260 orthogonal polynomials of the test corpus: 3.9 s -> 3.3 s.
  Other families: unchanged within the noise.
- Tested on 10 000 polynomials of sixteen families (513 018 roots): the same discs as 0.11.0 on every one.

## 0.11.0 - 2026-11-15

Not published separately; these changes are part of 0.12.0.  Found by running the solver alone on 10 000 polynomials of sixteen families.

- Square-free decomposition: the gcds of Yun's algorithm are computed from their images modulo primes
  (p = 1 mod 4, two images per prime for Gaussian coefficients), put together by the Chinese remainder
  theorem and accepted only when they divide both polynomials exactly.  The pseudo-remainder sequences of
  0.6.0 kept the result right but not small: on a polynomial of degree 52 with 30-digit coefficients and
  multiple roots they met numbers of tens of thousands of bits and took up to 9 seconds, where the rest
  of the solver takes less than a millisecond.  250 such products: 87 s -> 0.05 s.  The remainder
  sequences stay as a fallback and as a reference in the tests.
- Polynomials whose coefficients do not fit in double precision next to one another (roots over more
  orders of magnitude than a double has: 14 of the 10 000, returned as one disc of infinite radius with
  `complete = false`) are now solved: the points start from the dominant binomials read on the exact
  coefficients (`exact::scaled_start`) and go straight to the sweeps with values beyond double precision,
  and the evaluation through a scaled variable serves the points far inside the unit disc as well.  A
  leading coefficient 2^1100 times smaller than the largest one no longer underflows in the bound.
- The 10 000 polynomials: 111 s -> 17.5 s in all, 9 986 -> 10 000 complete; on the other 9 986 the discs
  (multiplicities and counts) are those of 0.10.1.

## 0.10.1 - 2026-11-15

Not published separately; this correction is part of 0.12.0.

- Fix a slowdown of versions 0.9.0 and 0.10.0 (it came with 0.8.0) on polynomials of large degree when
  values beyond double precision are needed, in particular with the `precise` functions: a dense
  polynomial of degree 320 at 30 digits took 376 ms against 56 ms with 0.7.0 (degree 160: 20 ms against
  13 ms).  The evaluation of a double precision point outside the unit disc through `T(t) = S(2^e t)`
  loses `m log2(1/|t|)` bits that the reversed polynomial does not lose, up to `m` bits for a point just
  outside the unit circle; it was used for every such point.  It is now used only when those bits are few
  against the bits of the evaluation (at most a quarter of them, plus 32); otherwise the reversed
  polynomial is used, as up to 0.7.0.  Degree 320 at 30 digits: 68 ms; Wilkinson 80 and Chebyshev 120 keep
  their times.  No result was wrong: both evaluations carry their error bound.
- Found while rerunning the validation scripts of the note G8 with 0.10.0.  The comparison with MPSolve
  had not shown it: it has five polynomials of degree above 160 among the hundred run at high precision.

## 0.10.0 - 2026-11-15

- The cursor of a cluster in multiprecision.  The step of a cluster (0.9.0) read the cursor from the
  double precision ratios S'/S and S''/S: for a cluster seen from far the cursor, `(width / distance)^K`,
  is below their rounding (about 2^-34), the radius of the cluster was unknown and the points closed on
  it by nine digits a step.  It is now computed from the two numbers that the ball evaluation returns in
  multiprecision, `N = S/S'` and `beta = S S''/S'^2`, with as many bits as the radius aimed at asks for
  (`precise::cluster_model`): one evaluation gives the radius of the cluster, or shows that it is below
  the one aimed at (the spacing of doubles, or the tolerance with `isolate: false`).  Used only when the
  double precision cursor is below 2^-24; above, that cursor is good and costs nothing.
- After a step of a cluster that brings the points `q` times closer, their next evaluation is asked
  `K log2(1/q)` more bits at once (S shrinks like the K-th power of the distance): on five roots 10^-30
  apart, 69 evaluations for four sweeps without it.
- Mignotte polynomials at 10 digits, same run as 0.9.0: degree 40 with 10^8 0.52 ms -> 0.32 ms (MPSolve
  0.48 ms), degree 24 0.49 ms -> 0.18 ms (0.27 ms), degree 40 with 100 0.36 ms -> 0.30 ms (0.67 ms); no
  sweep at double precision points is left, and one with more bits.  Clusters of five roots: unchanged
  within the noise of the run (the cluster is closed in one step instead of five, but the evaluations at
  its five points, where S is the fifth power of a small number, are what costs).  `z^12 - 2 (100 z - 1)^2`,
  a pair that 0.9.0 already separated in one step, pays the model: 29 us -> 35 us (MPSolve 81 us).
- Lean: `ClusterCursor.lean` (five lemmas: S'/S and its derivative from N and beta, the two forms of the
  cursor, its invariance under the scaling used, the K-th power law behind the bits asked).
- Comparison with MPSolve 3.2.3 rerun: 462/462 at 10 digits with either goal, 100/100 at 14, 30 and 80
  digits; no disc missed a reference root.  Geometric mean of MPSolve's time over pandroots' time at 10
  digits: 3.9, as for 0.9.0 in the same run; pandroots faster on 443 of the 462 (0.9.0: 439); Mignotte
  1.03 -> 1.39, clusters 0.25 -> 0.25.
- Tests: the multiprecision cursor on clusters of 2, 3 and 5 roots down to a radius of 10^-30 (radius to
  10^-6, centre, and no conclusion with too few bits).

## 0.9.0 - 2026-11-15

- The step of a cluster.  Points that approach a cluster of K roots from farther than its width see one
  root of multiplicity K, and the sweep brings them closer by a constant factor only (1/4 for a pair, 4/7
  for five roots).  Seen from outside the cluster is a shifted power `(w - g)^K - a`, the function for
  which the rectangle of the K-th root is exact: on the polynomial deflated of the points outside the
  cluster, the step of degree p = K gives the anchor `g = z - K N / (1 - t)` and the K roots
  `g + u t^(1/K) w^j`.  It is used for a tight component of overlapping Smith discs seen from at least four
  times its width, in the stage of exact values and in the multiprecision stage; everywhere else the sweep
  is that of G8.  New `Options::cluster` (default `true`; `false` gives the sweeps of 0.8.0).  The discs
  are certified after the move, as before.
- The doubles interface (`all_roots`, `all_roots_exact`) no longer separates roots that doubles cannot
  tell apart.  Up to 0.8.0 a pair closer than the spacing of doubles was separated with as many bits as it
  took (4096 bits for `mignotte_40` with 10^8), and the two discs were then merged into one when their
  centres were rounded.  The multiprecision stage now stops when the roots still together are in a disc
  of relative radius below 2^-54, and the stage at double precision points when they are within 4096 units
  of the last place.  Same discs, same counts.  The `precise` functions separate as before.
- Mignotte polynomials at 10 digits, same run: `z^40 - 2 (10^8 z - 1)^2` 13.0 ms -> 0.65 ms (MPSolve
  0.61 ms), degree 24 4.7 ms -> 0.37 ms (0.37 ms), degree 12 0.94 ms -> 0.20 ms (0.11 ms).  Five roots
  10^-30 apart 3.7 ms -> 0.38 ms (0.08 ms), 10^-12 apart 0.65 ms -> 0.31 ms (0.07 ms).
- Lean: `ClusterStep.lean` (six theorems: for `(w - g)^K - a` the cursor is `a / u^K`, the anchor is `g`,
  and every K-th root of the cursor gives a root: the K roots in one step).
- Comparison with MPSolve 3.2.3 rerun: 462/462 at 10 digits with either goal, 100/100 at 14, 30 and 80
  digits; no disc missed a reference root.  Geometric mean of MPSolve's time over pandroots' time at 10
  digits: 3.9 (0.8.0 in the same run: 3.8), pandroots faster on 439 of the 462; Mignotte 0.21 -> 1.05,
  clusters 0.11 -> 0.28.  With `isolate: false`: 4.0, Mignotte 1.47, clusters 0.50.
- Tests: the step of a cluster on shifted powers of degree 2, 3 and 4; the Mignotte pair in the three
  ways (doubles, `precise`, without the step of a cluster).

## 0.8.0 - 2026-11-15

Not published separately; these changes are part of 0.9.0.

- Stage of exact values (double precision points, values of S beyond double precision): each point
  remembers the number of bits its last evaluation needed, instead of starting again at 128 bits (on
  Wilkinson 80, 68 % of the evaluations of 0.7.0 were attempts with too few bits); the number of bits is
  rounded up to whole limbs.
- A multiplier with few bits (a double: one or two limbs) costs a pass or two over the accumulator: the
  low zero limbs are skipped.  Same integers.
- A double precision point outside the unit disc is evaluated through `T(t) = S(2^e t)`, `|t| <= 1`,
  which keeps the 53 bits of the point, instead of `1/z` and the reversed polynomial (a multiplier with as
  many bits as the evaluation).  Lean: `ScaledVariable.lean` (the values and derivatives of `T`, the
  Newton term, the invariance of `S S''/S'^2`, the leading coefficient).
- New `Options::isolate` (default `true`: unchanged).  `false`: the solver stops as soon as every root is
  in a disc within the tolerance, alone or with the roots it has not yet been told from, returned with
  their number; roots farther apart than the tolerance are separated either way.  MPSolve's goal
  "approximate".
- Fix `Stats::within_tolerance` in the `precise` functions: the modulus of the centre was replaced by a
  power of two below it, and a disc within the tolerance by less than a factor of two could be reported
  as not within it.
- Wilkinson 80 at 10 digits 118 ms -> 34 ms, Chebyshev 120 105 ms -> 48 ms (one call, idle machine;
  MPSolve in the comparison runs: 21 to 34 ms and 37 ms).  Comparison with MPSolve rerun: 462/462, 100/100; Chebyshev 1.04 -> 1.62,
  Wilkinson 0.53 -> 0.87 (geometric means of MPSolve's time over pandroots' time, same run).

## 0.7.0 - 2026-11-15

Not published separately; these changes are part of 0.9.0.

No change to the iteration, to the certificate or to any number the solver computes: on the 466
polynomials of the comparison corpus tried, the four interfaces return the same output as 0.6.0, digit for
digit.

- Multiprecision evaluation of S, S', S'' (dense polynomials): the Horner loop works on numbers of a fixed
  width in buffers allocated once per evaluation (new private module `limbs`), instead of `num-bigint`
  integers that allocate at every operation. It computes exactly the integers of the `BigInt` loop
  (exact products, shifts rounded towards minus infinity), so the error bound of the ball evaluation is
  unchanged; when a number does not fit its width, or above 2048 fractional bits, the `BigInt` loop is
  used. A profile of 0.6.0 on Wilkinson 80 showed 19 % of the time in the multiplication itself and 75 %
  in allocation and bookkeeping.
- Ill-conditioned dense polynomials at 10 digits, same run: Wilkinson 80 267 ms -> 154 ms, Wilkinson 50
  36 ms -> 16 ms, Chebyshev 120 227 ms -> 119 ms, Chebyshev 80 53 ms -> 21 ms, `(z - 3)^40 - 5` 14 ms ->
  8 ms. Clusters and Mignotte polynomials gain 15 to 35 %.
- High precision (`precise` functions), dense polynomial of degree 320: 30 digits 170 ms -> 85 ms,
  80 digits 255 ms -> 168 ms (the 0.6.0 figures are from the previous run of the comparison).
- Comparison with MPSolve 3.2.3 rerun: 462/462 at 10 digits, 100/100 at 14, 30 and 80 digits. Geometric
  mean of MPSolve's time over pandroots' time: 3.8 at 10 digits (0.6.0 in the same run: 3.7); with the
  `precise` functions 1.6 at 14 and 30 digits and 2.5 at 80 digits, pandroots faster on 61, 60 and 74 of
  the 100.
- Lean: `verification/lean/FixedWidth.lean`, four lemmas behind the fixed-width arithmetic (floor of a
  negative quotient, wrapped difference with and without a borrow), checked with Lean 4.35.0 / Mathlib
  v4.35.0, as is `ZeroDeflation.lean` again. The Rust code is not formalised.
- Tests: the fixed-width shift, signed sum and product against `BigInt` on 20000 random operands, the
  Horner loop against the `BigInt` loop on 1500 random evaluations, the reporting of overflows.

## 0.6.0 - 2026-11-15

Not published separately; these changes are part of 0.9.0.

No change to the iteration or to the certificate (`float.rs`, `exact.rs`, `precise.rs` are those of 0.5.0).

- The root zero is removed exactly before anything else: `P = z^k Q` with `Q(0) != 0` (the `k` trailing zero
  coefficients are dropped), the root 0 is returned with radius zero and multiplicity `k`, and only `Q` is
  solved. The discs of `Q` are kept only if each is proved to stay away from 0; otherwise `P` is solved
  as before. A monomial costs nothing (`z^20`: 330 us -> 0.5 us); up to 0.5.0 a zero constant term sent
  the polynomial to Yun's algorithm.
- Yun's square-free decomposition runs over the Gaussian integers with pseudo-divisions and content
  removal (a gcd in Z[i]), instead of the Gaussian rationals: no fraction is formed. Same factors up to
  constants. The 25 polynomials with multiple roots of the comparison corpus take 9 to 32 times less time
  (geometric mean 18).
- `num-rational` is no longer a dependency (it remains a dev-dependency: the rational version is the
  reference of a test).
- Lean: `verification/lean/ZeroDeflation.lean`, seven theorems on the deflation of the root zero (the
  factorisation, the roots and multiplicities of `X^k Q`, the count of a disc away from 0), checked with
  Lean 4.33.1 / Mathlib; axioms `propext`, `Classical.choice`, `Quot.sound`.
- Comparison with MPSolve 3.2.3 rerun (same corpus, criteria and scripts): 462/462 at 10 digits, 100/100
  at 14, 30 and 80 digits with the `precise` functions; no disc missed a reference root. Geometric mean
  of MPSolve's time over pandroots' time at 10 digits: 3.7 (0.5.0 in the same run: 2.9); pandroots faster
  on 434 of the 462 (0.5.0: 410).
- Tests: zero roots in the four interfaces, square-free factors of a complex polynomial, the new Yun
  against the rational one on 400 random products, the pseudo-division identity.

## 0.5.0 - 2026-11-15

- Multiprecision stage: S' and S'' are computed with fewer bits than S (they are not small near a root).
  Dense polynomials at 80 and 280 digits take about 30 % less time (degree 320, 80 digits: 560 ms -> 361 ms).
- New `Options::full_order` (default `false`): the whole step of the multiprecision stage, with the
  three-mean support and the sums over the other points, computed in multiprecision, each sweep at its
  full order (six). Same roots; measured slower than the default (m^2 multiprecision divisions per sweep),
  much slower on sparse polynomials of large degree. Adding a field to `Options` breaks code that builds
  it without `..Options::default()`.
- Points sharing a cluster of roots: the bits asked of each evaluation follow what the previous ones needed.
- Doubles interface: a centre rounded to a double is enlarged by the exact rounding distance.
- `bench`: mode `full`.
- Comparison with MPSolve 3.2.3 rerun: 462/462 at 10 digits, 100/100 at 14, 30 and 80 digits.
- Tests: `full_order` against the default to 260 digits, the multiprecision support against its series
  and against the double precision one.

## 0.4.0 - 2026-11-15

- High precision: the Newton part `S / S'` of the step is a multiprecision quotient taken from the ball
  evaluation; only the correction that the rectangle and the other points add to it is computed in double
  precision. The error of a point is roughly squared at each sweep (0.3.0 gained twelve to fifteen digits
  per sweep). Dense degree 160, one call: 80 digits 181 ms -> 144 ms, 200 digits 881 ms -> 287 ms,
  280 digits 1463 ms -> 372 ms.
- Fix `decimal(digits)`: it could print one significant digit fewer than asked, and the radius printed for
  an exact root whose decimal centre is not exact was ten times the tolerance (`2^-20` at 14 digits). Found
  by rerunning the MPSolve comparison.
- Comparison with MPSolve 3.2.3 rerun with this version (same corpus and criteria): 462/462 at 10 digits,
  100/100 at 14, 30 and 80 digits with the `precise` functions, decimal output included.
- README: corrects a sentence of 0.3.0 that quoted MPSolve's time at 10 digits as its time at 80 digits.
- Regression tests: 80 digits in at most four multiprecision sweeps, decimal output of a small exact root.

## 0.3.0 - 2026-11-15

Repairs the failures of 0.2.0 found by an independent comparison with MPSolve 3.2.3.

- Fix the shift of the variable: 0.2.0 could push the coefficients of a large-degree polynomial out of the
  binary64 range (time-out on a dense real polynomial of degree 1024). The shift now minimises the spread of
  the scaled coefficients and is 0 for ordinary inputs.
- Fix Mignotte-type inputs returning one disc of infinite radius with `complete = false`: coincident points
  are separated in the multiprecision stage.
- Degree one: the root is computed as a quotient to the requested precision (0.2.0 kept a 53-bit centre).
- Multiprecision stage: fixed-point ball evaluation of S, S', S'' in place of exact rational evaluation,
  term-by-term evaluation of sparse polynomials, incremental refinement of the points that need it,
  distances of far points from their binary64 roundings.
- Decimal output: radius 0 for exact roots with an exact decimal centre; the tolerance is compared with
  the radius as printed.
- New `Stats::within_tolerance`; `bench` accepts a fifth argument `precise`.
- Exact roots keep the radius zero in the binary64 interface.
- Lean evidence updated to the 38-theorem set of G8 revision 7 (adds `real_disc_of_computed`).
- Regression tests: Mignotte 10^8, `3 z - 1` at 80 digits, dense degree 800, exact-root decimal output.

## 0.2.0 - 2026-11-14

- Repair underflow-related false inclusion discs, including subnormal coefficient inputs.
- Scale variables and coefficients by exact powers of two and include absolute underflow bounds.
- Add arbitrary-precision dyadic centres through `all_roots_precise` and `all_roots_exact_precise`.
- Add decimal output with enlarged, upward-rounded radii and refinement up to 4096 bits.
- Refine the real-root flag and support roots separated below binary64 resolution.
- Add regression tests for underflow, 60-digit sqrt(2), and very close roots.
- Retain the existing MIT license and publication metadata; include source provenance and mathematical evidence.

## 0.1.0 - 2026-11-14

Initial crates.io release from G8, revision 5.

- Simultaneous rectangle iteration with binomial starts and Gauss-Seidel sweeps.
- Exact square-free decomposition over Gaussian rationals and exact multiplicities.
- Floating-point and Gaussian-integer coefficient interfaces.
- A posteriori inclusion discs, fixed-point root-count tests, and exact-evaluation refinement.
- Included Lean theorem sources and archive provenance.
- Publication metadata, MIT license, and usage documentation; the numerical algorithms are unchanged.
