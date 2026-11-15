# Changelog

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
