# pandroots (Rust) - the simultaneous rectangle of note G8

All the roots of a polynomial, with their multiplicities, each in a certified disc.

```rust
use pandroots::{all_roots, Options, C};
// z^3 - 6 z^2 + 11 z - 6, highest degree first
let c = [1.0, -6.0, 11.0, -6.0].map(|x| C::new(x, 0.0));
let (roots, complete, stats) = all_roots(&c, &Options::default());
for r in &roots {
    // the disc D(r.z, r.radius) contains exactly r.count roots, each of multiplicity r.mult
    println!("{:?} radius {:e} mult {} real {}", r.z, r.radius, r.mult, r.real);
}
```

`all_roots` takes double precision coefficients as exact numbers; `all_roots_exact` takes Gaussian
integers of any size (`num_bigint::BigInt`). Both return centres in double precision.

More digits than a double holds: set `tol` (relative radius, down to 1e-280) and call `all_roots_precise` or
`all_roots_exact_precise`; the centres are dyadic numbers of any size and print in decimal:

```rust
use pandroots::{all_roots_precise, Options, C};
let c = [1.0, 0.0, -2.0].map(|x| C::new(x, 0.0)); // z^2 - 2
let (roots, complete, _) = all_roots_precise(&c, &Options { tol: 1e-60, ..Options::default() });
let (re, im, radius) = roots[1].decimal(60); // "1.41421356237309504880168872420969807856967187537694807317667...e0"
```

A returned disc may be enlarged by 1/1024 of its radius and still contain exactly `count` roots; `decimal`
prints enough digits and a radius rounded upwards within that slack.

## Version 0.5.0

**How the step is computed at high precision.** The step of a point is `N / (1 + w)`: `N = S / S'` is
the first term of the rectangle step, and `w` is what the three-mean support and the other points add to
it. `w` has the size of the error of the point, so the correction `N w / (1 + w)` has the size of its
square. Two ways of computing it are now in the crate:

* by default, `N` is a multiprecision quotient and the correction is computed in double precision (as in
  0.4.0): the number of correct digits doubles at each sweep;
* with `Options { full_order: true, .. }`, the whole step is computed in multiprecision (the sums over
  the other points, the support with its two square roots, the announced positions): the number of
  correct digits is multiplied by the order of the sweep, six with the default support. The order shows:
  280 digits in three multiprecision sweeps instead of four.

The second way is not the default because it is not faster. It needs m^2 multiprecision divisions per
sweep, which cost as much as one evaluation of the polynomial at all the points or more, and it saves at
most one such evaluation. Both give the same roots (the tests compare them to 260 digits).

**S' and S'' with fewer bits.** `S` is small at a point near a root and must be known to many bits of its
own size; `S'` and `S''` are not small, and the same relative precision needs fewer bits. They are now
computed with fewer bits than `S` (the bound of `S`, the only number the certificate uses, does not depend
on them). This is where the time of 0.5.0 is gained.

One call, this machine, best of several runs (ms):

| polynomial | digits | 0.4.0 | 0.5.0 | 0.5.0 `full_order` |
|---|---:|---:|---:|---:|
| dense, degree 60 | 30 | 9.0 | 9.1 | 9.6 |
| dense, degree 60 | 80 | 20.7 | 14.7 | 20.8 |
| dense, degree 160 | 80 | 138 | 95 | 132 |
| dense, degree 160 | 280 | 356 | 256 | 287 |
| dense, degree 320 | 30 | 226 | 217 | 221 |
| dense, degree 320 | 80 | 560 | 361 | 497 |
| dense, degree 320 | 280 | 1370 | 986 | 1107 |
| `z^1000 - 1` | 80 | 303 | 235 | 1572 |
| `z^1000 - 1` | 280 | 413 | 426 | 2576 |
| Wilkinson 30 | 80 | 8.2 | 8.7 | 9.2 |
| Mignotte `z^12 - 2 (10^8 z - 1)^2`, separated | 30 | 2.5 | 2.3 | 4.0 |

**Points that share a cluster of roots** gain a few bits per sweep until the cluster is resolved. The
number of bits asked of each evaluation now follows what the last two evaluations of the point needed
(`S` shrinks faster than the distance to the cluster), which avoids evaluating twice.

**Doubles interface.** When a centre of more than 53 bits is rounded to a double, the radius is enlarged
by the exact distance between the two (0.4.0 added eight units of the last place). A root that is a
double, or within its own precision of one, keeps a small radius.

**Comparison with MPSolve 3.2.3, run again with this version** (same corpus, criteria and machine as for
0.4.0; MPSolve's times are those of the first run): 462 of 462 polynomials at 10 digits, 100 of 100 at
14, 30 and 80 digits with the `precise` functions, decimal output included; no disc missed a reference
root. Median of MPSolve's time over pandroots' time: 3.5 at 10 digits (0.4.0 measured in the same
run: 3.3), 0.9 at 30 digits, 1.3 at 80 digits (pandroots faster on 64 of the 100; 0.4.0: 1.2 and 53). On
the five polynomials of degree above 160, 3.9 at 30 digits and 5.9 at 80 digits. MPSolve remains ahead
on clusters, Mignotte, Wilkinson and Chebyshev polynomials and on monomials.

Not done: a faster multiprecision arithmetic (the numbers are `num-bigint` integers, and below a thousand
bits their time is mostly allocation), parallelism. `mignotte_40` with `10^8` (a pair of roots less than 10^-150
apart) is returned as one disc with two roots by default and separated with `full_order`. The ball
evaluation, the multiprecision step and the guards of the code are tested, not formalised; there is no
proof of global convergence.

## Version 0.4.0

**The step at high precision.** Up to 0.3.0 the whole step was computed in double precision from values of
S, S', S'' known to twelve digits: a point of the multiprecision stage gained twelve to fifteen digits per
sweep. The step is `N / (1 + w)`, with `N = S / S'` the Newton correction and `w` what the rectangle (the
three-mean support) and the other points add to it. `N` is now a multiprecision quotient taken from the
ball evaluation, and only the correction `N w / (1 + w)` is computed in double precision; a point with
error `e` goes to about `e^2 2^-50` in one sweep (16, 46, 107 digits) instead of `e 2^-50`. The polynomial
is asked for the relative precision that this needs and no more.

One call, this machine, dense polynomial with integer coefficients:

| degree | digits | 0.3.0 | 0.4.0 |
|---:|---:|---:|---:|
| 160 | 30 | 57 ms | 59 ms |
| 160 | 80 | 181 ms | 144 ms |
| 160 | 200 | 881 ms | 287 ms |
| 160 | 280 | 1463 ms | 372 ms |
| 60 | 280 | 215 ms | 50 ms |

**Decimal output of small exact roots.** `decimal(digits)` could print one digit fewer than asked (the
decimal exponent was estimated from the number of bits), and the radius printed for an exact root whose
decimal centre is not exact was 10^(1-digits) times the modulus, ten times the tolerance: `2^-20` at 14
digits came out as `9.536743164063e-7` with radius `2.2e-19`. The number of digits is now exact, and such
a centre is printed with two more digits and a radius below 10^-digits times the modulus.

**Comparison with MPSolve 3.2.3, run again with this version** (same corpus and same criteria as the
independent comparison of 0.2.0; a different, slower machine, one thread; the scripts are not in this
crate). A case passes when the discs account for every root with its multiplicity, contain the reference
roots, and both the error and the radius are within the tolerance.

| | pandroots 0.4.0 | pandroots 0.2.0 | MPSolve secular | MPSolve standard |
|---|---:|---:|---:|---:|
| 462 polynomials, 10 digits | 462 | 455 | 461 | 460 |
| 100 polynomials, 14 digits (`precise`) | 100 | | 99 | 97 |
| 100 polynomials, 30 digits (`precise`) | 100 | | 99 | 96 |
| 100 polynomials, 80 digits (`precise`) | 100 | | 99 | 81 |

The figures of 0.2.0 and of MPSolve are those of the independent comparison, reproduced. MPSolve's misses
are the ones it lists: radii above the tolerance on multiple roots, clusters and Mignotte pairs, one
time-out, and a cover that does not match the reference roots with their multiplicities on Chebyshev 80
and 120 (standard) and on `(z-1)^10 (z+2)^10 (z-i)^10` (secular). No disc of pandroots missed a
reference root. The doubles interface cannot meet a tolerance below about
10^-15 (28 and 35 of the 100 at 30 and 80 digits, the roots that are exactly doubles): that is what the
`precise` functions are for, and `Stats::within_tolerance` says it.

Time (median of the ratio MPSolve / pandroots over the cases both solve; above 1, pandroots is faster):
at 10 digits 3.7 over the 462 polynomials (geometric mean 3.0; pandroots faster on 409), from 3 at degree
up to 10 to 14 above degree 160. At 30 and 80 digits the two are on a par on dense polynomials (degree
320 at 80 digits: 0.60 s against 0.49 s; degree 160: 0.13 s against 0.12 s; at 30 digits 0.22 s against
0.25 s and 0.056 s against 0.065 s), pandroots is five times faster on `z^1000 - 1` (0.33 s against
1.7 s), and MPSolve is two to five times faster on Wilkinson and Chebyshev polynomials (0.32 s against
0.18 s, 0.50 s against 0.14 s at 80 digits) and much faster on clusters and Mignotte polynomials and on
monomials. Timings on that machine vary by 20 % or more from one run to the next.

Not done in 0.4.0: the correction `N w / (1 + w)` in multiprecision (done in 0.5.0 as
`Options::full_order`, and measured: it gives the full order of the sweep and is not faster), a faster
polynomial evaluation than Horner on big integers, parallelism. The ball evaluation and the guards of the code are tested, not formalised;
there is no proof of global convergence.

## Version 0.3.0

Repairs what an independent comparison with MPSolve 3.2.3 found in version 0.2.0 (462 polynomials up to
degree 1024, and 100 of them at 14, 30 and 80 digits); `python3 ../probe_030.py` replays the cases.

* **Large degrees: the shift of the variable was wrong.** Version 0.2.0 centred an estimate of the root
  moduli; one unit of shift at degree 1024 multiplies the coefficients by powers of two up to 2^1024 and
  pushed most of them out of the range of doubles (10 000 sweeps, a time-out on a dense real polynomial
  of degree 1024). The shift is now the one for which the coefficients spread over the fewest binary orders
  of magnitude: 0 for an ordinary polynomial. That polynomial takes 9 sweeps and 0.04 s again.
* **Mignotte polynomials** (`z^12 - 2 (10^8 z - 1)^2` and five others): 0.2.0 returned one disc of
  infinite radius and `complete = false`. Two points that had fallen on the same place stayed together
  for ever; one of them is now moved aside. The doubles interface returns the close pair as one disc with
  two roots, the precise interface separates it (12 discs at 256 bits).
* **Degree one** (`3 z - 1` at 80 digits): 0.2.0 kept the 53-bit centre. The root is now the quotient,
  rounded to as many bits as the tolerance asks for.
* **Time at high precision.** The values of S, S', S'' at multiprecision points were computed exactly,
  with numbers of m times the bits of the point. They are now computed in fixed point with F bits and a
  rigorous bound of the rounding (`BallPoly`), F being raised until the value is known to twelve digits;
  polynomials with few terms are evaluated term by term; only the points whose disc is not good enough
  are evaluated and moved; distances between far points come from their double roundings. One call,
  this machine: `z^1000 - 1` at 80 digits 1.0 s (0.2.0: more than 40 s), `z^250 - 1` at 80 digits 0.08 s
  (6 s), a dense polynomial of degree 320 at 80 digits 1.5 to 1.9 s (13 s). (This paragraph said that MPSolve
  remained much faster on dense polynomials at high precision, quoting 0.015 s for that degree 320: that
  figure was MPSolve's time at 10 digits. Measured at 80 digits, MPSolve takes about 0.5 s; see 0.4.0.)
* **Decimal output.** An exact root whose decimal centre is exact prints the radius 0 (0.2.0 printed
  about 10^-79 at 80 digits); the tolerance is compared with the radius as it may be printed.
* `Stats::within_tolerance`: every disc holds one root and is within the tolerance. `complete` alone
  only says that the discs account for all the roots.

Unchanged and still true: no wrong disc was found by that comparison in 0.2.0, and none by the tests
here in 0.3.0 (195 polynomials at the edges of double precision, 31 at 30 and 80 digits, 2608 random
ones against LAPACK). Not done in 0.3.0: a multiprecision step (the step was computed in double
precision, twelve to fifteen digits per sweep; see 0.4.0), parallelism.

## Version 0.2.0

* **Defect repaired.** Version 0.1.0 could return a wrong disc with `complete = true` when values underflow,
  for instance on `2^-1070 (z-1)(z-2)(z-3)` (subnormal coefficients) or `z^3 - 1e-250 z` (normal ones): the
  rounding bound of Horner's rule is relative and says nothing of an operation that underflows. Found by an
  external comparison with MPSolve. Now: the variable and the coefficients are scaled by exact powers of
  two; the bound has an absolute term for underflow; distances near the underflow threshold are computed
  after an exact scaling; no panic on non-finite numbers. `python3 ../underflow_check.py` runs 195
  polynomials at the edges of double precision against mpmath: 0.1.0 gave 14 wrong answers, 0.2.0 none
  (186 sharp, 9 true but weak: roots that no double can hold).
* **Centres of any precision** (`precise` module): the same sweep and the same certificate, continued at
  dyadic points when the tolerance is below 1e-12 or when double precision could not separate or decide the
  roots. Fifteen digits per sweep; up to 4096 bits. Roots closer than double precision are separated.
* The real-root flag now tests the real disc that is returned (it contains the disc and its mirror image),
  which also proves that this disc holds one root only.
* `bench FILE [REPS] [MODE] [TOL]`: with TOL below 1e-12 the output has decimal centres.

One path, no rescue method:

1. square-free decomposition (a test modulo a prime; Yun's algorithm over the Gaussian rationals if needed);
2. start from the dominant binomials of the polynomial at every scale (Newton polygon, K-th roots at
   their true angles);
3. sweeps of the simultaneous rectangle in double precision: the three-mean support of the Geometric
   Root Calculators, used once on S to announce where each neighbour is heading and once on S deflated of
   the neighbours; points are used as soon as they have moved (Gauss-Seidel);
4. the certificate, with the rounding bound of Horner's rule (underflow included): Smith's discs contain the
   roots, and the fixed-point certificate of the note (Theorem 4.2: a contraction of the disc D(z_k, 2|W_k|))
   shows that each disc contains exactly one of them; that theorem, down to the inequalities tested here,
   is proved in Lean (lean/FixedPointCertificate.lean). If a disc fails or is not small enough, the same
   sweep goes on with exact values of S, S', S'' (big integers), first at double precision points, then at
   points with more bits. Points that cannot be separated within 4096 bits are reported together, counted
   by Smith's theorem (classical, not formalised).

Differences with the Python prototype of the note: Gauss-Seidel order, and evaluation through the
reversed polynomial outside the unit disc (no overflow at high degree).

Build and test: `RUSTFLAGS="-C target-cpu=native" cargo test --release`.
Benchmark against numpy: `cd .. && python3 rust_check.py`, then `python3 simple.py` (need numpy, mpmath).

Limits: no proof of global convergence; the rounding bounds, the underflow term and the guards near the
underflow threshold are tested, not formally verified (Lean proves the theorem the certificate applies, not
the program); the multiprecision step is computed in double precision (fifteen digits per sweep), so a
specialised multiprecision solver such as MPSolve is expected to be faster at high precision;
timings depend on the machine.
