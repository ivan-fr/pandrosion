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

## Version 0.13.0

Version 0.13.0 comes from profiling 0.12.0, first on the 10 000 polynomials below, then on 50 000 small
ones, and was measured on two corpora (generators and scripts in `bench20k/` and `bench50k/` of the
validation archive):

- 20 000 polynomials of sixteen families, the 10 000 below and as many again from another seed: 1 043 482
  roots, degrees up to 2 000, with the hard cases (clusters, Mignotte, orthogonal polynomials, sparse and
  dense polynomials of large degree);
- 50 000 polynomials of degree 2 to 60 in eight families (dense real and complex, small integers,
  coefficients +-1, coefficients over forty orders of magnitude, integer and Gaussian integer roots with
  multiplicities, real clusters): the ordinary use.

The method is that of 0.12.0, with the same step and the same certificate; what changed is what each of
them costs.  One call per polynomial, one thread, the solver's own flags; Intel Xeon at 2.1 GHz, the smaller
of two runs for each polynomial (on this machine 0.12.0 takes 22 s for the first 10 000, against about 15 s
on the machine of the table of 0.12.0).

| the 20 000 polynomials | 0.12.0 | 0.13.0 |
|---|---:|---:|
| time in all | 54.0 s | 29.1 s |
| ... those for which double precision is enough (15 078) | 18.0 s | 6.6 s |
| ... those that need values beyond double precision (2 966) | 34.4 s | 21.0 s |
| ... those that need points beyond double precision (1 956) | 1.7 s | 1.5 s |
| complete | 20 000 | 20 000 |
| every root in its own disc within 10^-10 | 18 395 | 18 395 |

| the 50 000 polynomials of degree 2 to 60 | 0.12.0 | 0.13.0 |
|---|---:|---:|
| time in all | 2.84 s | 1.97 s |
| median, dense real (degree 2 to 40) | 56 us | 36 us |
| median, coefficients +-1 (degree 5 to 60) | 88 us | 57 us |
| median, integer roots with multiplicities | 22 us | 17 us |
| median, real clusters | 122 us | 108 us |

| one call (ms) | degree | 0.12.0 | 0.13.0 |
|---|---:|---:|---:|
| Laguerre | 150 | 287 | 81 |
| Chebyshev T | 150 | 182 | 108 |
| Wilkinson | 100 | 128 | 60 |
| Mandelbrot | 255 | 701 | 367 |
| truncated exponential | 120 | 50 | 38 |
| `(z - a)^60 - b` | 60 | 24 | 15 |
| `z^2000 + z + 1` | 2000 | 72 | 21 |
| sparse, 6 terms | 1500 | 48 | 13 |
| dense, Gaussian coefficients | 2000 | 153 | 59 |
| dense, Gaussian coefficients | 640 | 12.8 | 5.8 |

**Values beyond double precision.**  In that stage the points are doubles and the values of S are
computed in fixed point with as many bits F as each value asks for.  A point is then, in units of 2^-F,
two integers of 53 bits times one power of two, and the product of an accumulator by it is one pass over
its limbs (`limbs::combine_short`) instead of two full products, a subtraction and a shift over twice the
width: the same integers, tested against `BigInt`.  A point outside the unit disc is evaluated either
through `1/z`, which has F bits, or through `T(t) = S(2^e t)`, whose multiplier is short but which loses
`m log2(1/|t|)` bits; 0.10.1 had limited the second way to a loss of a quarter of F.  Most of what it
cost was elsewhere: when F minus the bits lost could not tell a value from zero, the value was computed
exactly, with integers of 53 m bits, as if the point might be an exact root.  That exact evaluation now
waits until F has passed the bits lost, and the limit of the scaled variable is F itself.

**Evaluations that were made twice.**  A polynomial of degree 20 takes four sweeps in double precision,
and was evaluated at its points six times: after the last sweep once more to find every residual at
rounding level, and then again, at the same points rounded to 53 bits of their modulus, for the bounds of
the certificate.  The points are now rounded as they move, the last evaluation of the sweeps gives the
bounds, and a point whose residual is at rounding level, which no longer moves, is not evaluated again.
At large degree, where the points settle one after the other, this is the larger part of the gain.

**Polynomials with few terms.**  In double precision Horner's rule went through every coefficient, zero
or not: 2 000 steps per point for `z^2000 + z + 1`.  When at most one coefficient in twelve is not zero,
a run of zeros is now one step, `p <- p x^g + c`, with `x^g` by repeated squaring and the two derivatives
by the closed form of g steps with nothing to add.  The value of S goes through no more products than in
the dense rule, so the rounding bound that the certificate uses is the same.

**The certificate.**  Its fixed-point test was run twice on the same points when double precision was
enough, which is the case of three polynomials in four.  It is run once.  And a disc passes without the
two sums over the other points when the bounds `W / g` and `W / g^2` (W the sum of all the w_l, g the
smallest gap of the point) already pass the two tests: one pass without square root or division, enough
for points that have converged.

**Fixed costs.**  For a polynomial of degree 20 the test "square-free modulo a prime" took a seventh of
the time, most of it in modular powers: one per coefficient for its power of two, one per remainder for
the inverse of a leading coefficient.  The powers of two now come by doublings and the remainders are
taken up to a constant.

**Are the discs the same?**  On the 50 000, yes: same multiplicities and counts on every polynomial.  On
the 20 000, on 19 989.  The 11 others are clusters whose roots are 10^-14 to 10^-16 of their size apart,
which is where double precision centres stop being able to tell them apart; the points now reach such a
cluster by another path, since they are rounded as they move, and 5 of the 11 come out with more roots in
their own disc, 6 with fewer.  Both answers are right (next paragraph); which roots of such a cluster get
their own disc was not, and is not, something the doubles interface promises.  The `precise` functions
separate them all.

**Independent checks.**  7 249 of the 20 000 are built from prescribed rational roots.  For these the
discs of 0.13.0 (and of 0.12.0) were compared with the roots in exact rational arithmetic, the printed
doubles read as the binary numbers they are: each of the 70 364 distinct roots lies in one disc and only
one, the disc has its multiplicity and holds as many roots as its count.  None is wrong.  For the other
12 751 polynomials the figures are the solver's own.  On the 50 000, the discs were compared with the
known roots (10 000 polynomials), with `numpy.roots`, and, where numpy disagrees and on a sample of each
family, with `mpmath.polyroots` at 60 digits: see `bench50k/`.

What still costs, of the 29 seconds: the orthogonal polynomials (12.2 s for 510 of them), the powers,
the Wilkinson polynomials and the Mandelbrot polynomials and truncated exponentials (8.4 s with their
groups), 15 to 40 sweeps of hundreds of bits each, a number that 0.13.0 does not change; then the sparse
polynomials (3.3 s) and the dense ones of degree 320 to 2 000 (2.0 s), where what is left is the m^2 pairs
of points of each sweep.  For a polynomial of degree 20, 36 microseconds: two thirds in the four sweeps
(the pairs of points, with a division and two complex square roots per point), the rest in the
certificate and the square-free test.

## Version 0.12.0

Versions 0.10.1 to 0.12.0 come from running the solver alone on 10 000 polynomials of sixteen families
(dense with several laws of coefficients, sparse, prescribed roots, multiple roots, 1 242 clusters, Mignotte,
roots in arithmetic progression, orthogonal polynomials, powers, products, roots over many scales, the
edges of double precision, degrees up to 2 000; 513 018 roots).  The figures below are the solver's own:
its flags `complete` and `within_tolerance`, and its time, one call per polynomial, one thread.

| | 0.10.1 | 0.12.0 |
|---|---:|---:|
| time for the 10 000 | 111 s | about 15 s |
| complete | 9 986 | 10 000 |
| every root in its own disc within 10^-10 | 9 175 | 9 189 |

(The 811 others are clusters and Mignotte pairs that double precision centres cannot separate: one disc
with their number.)

**The square-free decomposition (0.11.0).**  Four fifths of the 111 seconds went to 250 polynomials of
degree about 50 with multiple roots and 30-digit coefficients: Yun's algorithm with pseudo-remainder
sequences (0.6.0) met numbers of tens of thousands of bits, up to 9 seconds for one polynomial.  Each gcd
is now computed from its images modulo primes and accepted only when it divides both polynomials exactly.
Every number met is an image below 2^31 or a coefficient of a divisor of the input.  87 s -> 0.05 s.

**Roots over more orders of magnitude than a double has (0.11.0).**  With roots from 10^-108 to 10^102
the coefficients do not fit in double precision next to one another; the double precision sweeps ran on
another polynomial and the answer was one disc of infinite radius.  The points now start from the dominant
binomials read on the exact coefficients and go straight to the sweeps with values beyond double
precision; one such sweep is enough when the scales are that far apart.

**Where the sweeps beyond double precision start (0.12.0).**  On an ill-conditioned polynomial the double
precision sweeps leave most points far from the roots (141 of 150 on Laguerre 150), and the same sweep
goes on with values of hundreds of bits.  The number of those sweeps depends on the start: 37 from the
start of G8 on Laguerre 150, 20 when each edge of the Newton polygon keeps its own binomial instead of
being merged with its neighbours into one shifted power; on a Mandelbrot polynomial the first start is
the better one.  So, when a quarter of the points or more are left uncertified, both sets of points are
sampled (24 points at most, a few bits of relative precision) and the sweeps go on from the one whose
median Smith radius is smaller, the second being taken only if it is 2^16 times smaller.  Laguerre 150:
600 ms -> 243 ms.  Other families are unchanged within the noise of the machine: the gain is confined to
polynomials of that kind.

What still costs, of the 15 seconds: sparse polynomials of degree up to 1 500 and dense ones up to 2 000
(double precision sweeps, m^2 operations each), and the ill-conditioned families (orthogonal polynomials,
powers, Wilkinson), 15 to 40 sweeps of hundreds of bits each.

## Version 0.10.1

A correction of 0.9.0 and 0.10.0 for large degrees at high precision.  Version 0.8.0 introduced the
evaluation of a double precision point outside the unit disc through `T(t) = S(2^e t)`, whose multiplier
has the 53 bits of the point.  Horner's rule at `t` loses `m log2(1/|t|)` bits that the reversed polynomial
at `1/z` does not lose: up to `m` bits when the point is just outside the unit circle, which is where the
roots of a dense polynomial are.  The short multiplier does not pay for 320 more bits: with the `precise`
functions a dense polynomial of degree 320 took 376 ms at 30 digits, against 56 ms with 0.7.0.  The scaled
variable is now used only when the bits it loses are at most a quarter of the bits of the evaluation, plus
32, and the reversed polynomial otherwise.

| dense polynomial, `precise` functions, one call (ms) | 0.7.0 | 0.10.0 | 0.10.1 |
|---|---:|---:|---:|
| degree 160, 30 digits | 13 | 20 | 18 |
| degree 320, 30 digits | 56 | 376 | 68 |

Wilkinson and Chebyshev polynomials, where the scaled variable helps, keep their times.  No result of
0.8.0 to 0.10.0 was wrong.  The figures of the sections below at 14, 30 and 80 digits were measured with
the versions they describe; those of the polynomials of degree above 160 are too slow by this defect.

## Version 0.10.0

**The cursor of a cluster in multiprecision.**  The step of a cluster of 0.9.0 gives the centre of a
distant cluster at once, but not its radius: the cursor is `t = (width / distance)^K`, and it was read from
S'/S and S''/S in double precision, where anything below about 2^-34 is rounding.  The points were then put
on a circle of 2^-30 of their distance and the step repeated: nine digits a step.

The ball evaluation already returns two numbers in multiprecision, `N = S/S'` and `beta = S S''/S'^2`.
With the sums `s1`, `s2` of `1/(z - z_l)` and `1/(z - z_l)^2` over the points outside the cluster,

```text
A = 1/N - s1,    B = (1 - beta)/N^2 - s2,    t = (K B/A^2 - 1)/(K - 1),    u = K / (A (1 - t)),
```

and `K B/A^2` is `1 + (K - 1) t`: a cursor of 2^-tau is what is left of a number close to one known to
tau bits and more.  So the evaluation is asked for the bits that the radius aimed at needs,
`K log2(distance / radius) + 48`: the radius is the spacing of doubles in the doubles interface, the
tolerance with `isolate: false`, the grid of doubles in the stage at double precision points.  One
evaluation then gives the radius of the cluster, or shows that the cluster is below the radius aimed at,
and the points go to the roots of the model or to a circle of that radius.  Everything is scaled by a
power of two near `|N|`, which the cursor does not see (Lean, `ClusterCursor.lean`).  When the double
precision cursor is above 2^-24 it is used as in 0.9.0: it is good there, and free.

**Bits after the step.**  A point brought `q` times closer to a cluster sees S multiplied by `q^K`; its
next evaluation is now asked `K log2(1/q)` more bits at once instead of failing first with the bits of
the previous one.

Same run, same machine (median of 7 measures, us), 10 digits, doubles interface; the machine was busy, as
for 0.9.0:

| polynomial | 0.9.0 | 0.10.0 | 0.10.0 `isolate: false` | MPSolve 3.2.3 |
|---|---:|---:|---:|---:|
| Mignotte 40, 10^8 | 522 | 324 | 345 | 484 |
| Mignotte 24, 10^8 | 489 | 179 | 182 | 266 |
| Mignotte 12, 10^8 | 127 | 103 | 86 | 89 |
| Mignotte 40, 100 | 360 | 295 | 228 | 671 |
| Mignotte 12, 100 | 39 | 43 | 48 | 81 |
| five roots 10^-30 apart | 308 | 230 | 294 | 54 |
| five roots 10^-20 apart | 419 | 278 | 128 | 48 |
| five roots 10^-8 apart | 276 | 200 | 196 | 144 |

On a Mignotte polynomial no sweep at double precision points is left (8 in 0.9.0), and one sweep with
more bits: the pair is known to be below the spacing of doubles after one evaluation.  On the clusters of
five roots the step count falls as well (5 sweeps at double precision points to 2), but the time does not
follow: measured side by side, best of five runs, the four clusters of five roots 10^-12 apart or closer take
between 13 % less and 6 % more than with 0.9.0.  What costs there is no longer the approach but the evaluations at the
five points, where S is the fifth power of a small number and needs five times its bits.  One case pays the
model without gaining a step: `z^12 - 2 (100 z - 1)^2`, 29 us -> 35 us.

**Comparison with MPSolve 3.2.3, run again with this version**: 462 of 462 polynomials at 10 digits with
either goal, 100 of 100 at 14, 30 and 80 digits with the `precise` functions; no disc missed a reference
root.  Geometric mean of MPSolve's time over pandroots' time at 10 digits: 3.9, as for 0.9.0 in the same
run; pandroots faster on 443 of the 462 (0.9.0: 439).  Mignotte 1.03 -> 1.39; clusters 0.25 -> 0.25.
With the `precise` functions: 1.9 at 14 digits, 1.8 at 30 digits, 2.9 at 80 digits.

MPSolve remains four to twelve times faster on clusters of five roots 10^-12 apart or closer.

## Version 0.9.0

What 0.8.0 and 0.9.0 change is where the points go when the sweep of G8 is slow, and how the values of S
are computed beyond double precision.  The sweep itself (the simultaneous rectangle with the three-mean
support) and the certificate are unchanged, and every disc returned is certified after the points have
moved, whatever moved them.

**The step of a cluster (0.9.0).**  Near simple roots the function deflated of the other points is almost
a straight line, which is why the sweep has order six.  Near a cluster it is not: K points that approach
a cluster of K roots from farther than its width see one root of multiplicity K, each is deflated of
K - 1 points that are as far from the cluster as it is, and the distance to the cluster is multiplied by
a constant at each sweep (measured: 1/4 for a pair, 0.40 for three roots, 4/7 for five).

Seen from outside, a cluster is a shifted power `(w - g)^K - a`: the function of the K-th root, for which
the rectangle with its exact support returns the root in one step.  So, for a tight cluster, the
polynomial is deflated of the points *outside* the cluster only, and the step of degree p = K is applied
to it at one point z of the cluster: with `A = F'/F`, `B = -(F'/F)'`,

```text
t = (K B - A^2) / ((K - 1) A^2),    u = K / (A (1 - t)),    g = z - u,
```

`g` is the virtual anchor, the centre of the cluster, and the K points go to `g + u t^(1/K) w^j`.  For the
shifted power itself this is exact (Lean, `ClusterStep.lean`); for K = 2 every quadratic is one.  In a
multiprecision model of the two steps, from points at 10^-3 of five roots 10^-30 apart, one step of the
cluster gives its centre to 10^-16, where six sweeps bring the points to 3.5 10^-5 of it.  The radius is less well known than the centre (the cursor of a cluster seen from very far is
lost in the rounding of S'/S and S''/S), so the points are put on a circle of at least 2^-30 of their
distance and the step is repeated; it is not used once the points are within four times the width of the
cluster, where the sweep takes over.  `Options { cluster: false, .. }` gives the sweeps of 0.8.0.

The K-th root of the cursor is taken directly, as in the start of G8 (Section 5), not through the three
means: they follow the exact support near t = 1, and here t is near 0.

**Roots that doubles cannot tell apart (0.9.0).**  With double precision centres, two roots closer than
the spacing of doubles end in one disc with `count = 2`: their discs overlap once the centres are
rounded.  Up to 0.8.0 they were first separated, with as many bits as it took (4096 for
`z^40 - 2 (10^8 z - 1)^2`), and merged afterwards.  `all_roots` and `all_roots_exact` now stop when the
roots still together are in a disc of relative radius below 2^-54.  The discs and counts returned are the
same; `all_roots_precise` and `all_roots_exact_precise` separate as before.

**Values beyond double precision (0.8.0).**  Three changes in the stage that follows the double
precision one, where the points are doubles and S, S', S'' are evaluated in fixed point:

* each point starts from the number of bits its last evaluation needed (0.7.0 started again at 128 bits:
  on Wilkinson 80, 68 % of the evaluations were attempts with too few bits);
* a product by a point of 53 bits costs a pass or two over the accumulator instead of one per limb;
* a point outside the unit disc is evaluated through `T(t) = S(2^e t)` at `t = z / 2^e`, which has the
  53 bits of z, instead of through `1/z`, which has as many bits as the evaluation (Lean,
  `ScaledVariable.lean`: `T(t) = S(z)`, `T' = 2^e S'`, `T'' = 4^e S''`, the Newton term and
  `S S''/S'^2`).

**`Options::isolate` (0.8.0).**  `true` by default: nothing changes.  With `false` the solver stops as
soon as every root is in a disc within the tolerance, alone or with the roots it has not yet been told
from; such a disc is returned with their number, as for the clusters that 4096 bits do not resolve.
Either way the discs account for every root (`complete`), and roots farther apart than the tolerance are
separated.  It is the goal that MPSolve calls "approximate", the one it runs with in the comparison
below.  What `false` gives up: roots closer than the tolerance that could be separated share one disc,
without the flag `real`, and `within_tolerance` is `false`.

Same run, same machine (median of 7 measures, ms), 10 digits, doubles interface.  The machine was busy
during that run (other processes used about three cores): the times are longer and less steady than on an
idle machine, where Wilkinson 80 takes 32 ms and Chebyshev 120 45 ms.

| polynomial | 0.8.0 | 0.9.0 | 0.9.0 `isolate: false` | MPSolve 3.2.3 |
|---|---:|---:|---:|---:|
| Mignotte 40, 10^8 | 13.0 | 0.65 | 0.49 | 0.61 |
| Mignotte 24, 10^8 | 4.7 | 0.37 | 0.25 | 0.37 |
| Mignotte 12, 10^8 | 0.94 | 0.20 | 0.13 | 0.11 |
| Mignotte 40, 100 | 2.6 | 0.41 | 0.40 | 0.68 |
| five roots 10^-30 apart | 3.7 | 0.38 | 0.21 | 0.08 |
| five roots 10^-12 apart | 0.65 | 0.31 | 0.21 | 0.07 |
| Wilkinson 80 | 38.4 | 39.0 | 43.9 | 34.3 |
| Chebyshev 120 | 52.4 | 49.4 | 63.7 | 36.6 |

(0.7.0: Wilkinson 80 154 ms, Chebyshev 120 119 ms in its own run.)

**Comparison with MPSolve 3.2.3, run again with this version** (same corpus, criteria and scripts; one
thread): 462 of 462 polynomials at 10 digits with either goal, 100 of 100 at 14, 30 and 80 digits with
the `precise` functions, decimal output included; no disc missed a reference root.  Geometric mean of
MPSolve's time over pandroots' time at 10 digits: 3.9, pandroots faster on 439 of the 462 (0.8.0 in the
same run: 3.8 and 437; with `isolate: false`: 4.0 and 443).  By family, 0.7.0 (its own run), then 0.8.0
and 0.9.0 in this one:

| family | 0.7.0 | 0.8.0 | 0.9.0 | 0.9.0 `isolate: false` |
|---|---:|---:|---:|---:|
| Mignotte | 0.17 | 0.21 | 1.05 | 1.47 |
| clusters | 0.05 | 0.11 | 0.28 | 0.50 |
| Wilkinson | 0.55 | 0.91 | 0.89 | 0.95 |
| Chebyshev | 1.11 | 1.37 | 1.71 | 1.48 |
| rounded Wilkinson | 0.83 | 1.24 | 0.97 | 1.09 |
| shifted powers | 0.92 | 1.31 | 1.06 | 1.28 |

The families of three to nine polynomials move by 30 % from one run to the next on this machine (shifted
powers and rounded Wilkinson take the same time in 0.8.0 and 0.9.0 when measured side by side).  With the
`precise` functions on the 100 polynomials: 1.9 at 14 digits, 1.9 at 30 digits, 3.0 at 80 digits,
pandroots faster on 61, 69 and 77 of them.

MPSolve remains ahead on clusters (four to twelve times faster on the clusters of five roots 10^-12
apart or closer: the step of a cluster finds the centre at once, but closing on five roots, or separating
them, still takes several evaluations with many bits), on monomials and zero roots (it removes them before its timed computation),
and by up to 30 % on Wilkinson polynomials.

Not done in 0.9.0: the cursor of a cluster in multiprecision (done in 0.10.0: it gives the radius of a
distant cluster, and closes on it in one step), clusters that contain all the points, parallelism.  The
step of a cluster is proved for the shifted power only; how well a real cluster is one is measured, not
proved.  As before, the certificate is formalised, the programs are not.

## Version 0.7.0

One change, in the arithmetic of the multiprecision evaluation. The iteration (the simultaneous rectangle
with the three-mean support), the certificate and every number the solver computes are unchanged: on the
466 polynomials of the comparison corpus tried, the four interfaces return the same output as 0.6.0, digit
for digit.

**Where the time went.** When double precision is not enough (ill-conditioned polynomials, or a tolerance
below 10^-12), S, S' and S'' are evaluated in fixed point by Horner's rule with `num-bigint` integers.
A profile of 0.6.0 on Wilkinson 80 gave 19 % of the time in the multiplication itself, 35 % in the memory
allocator and 40 % in the rest of `num-bigint` (additions, shifts, normalisation): every operation
allocates its result, and on numbers of a few hundred bits that costs more than the operation.

**Numbers of a fixed width.** The Horner loop of a dense polynomial now runs on sign-magnitude numbers in
buffers allocated once per evaluation (private module `limbs`). It is written to return exactly the
integers of the `BigInt` loop: products are exact and shifts round towards minus infinity, as `BigInt >> k`
does. The error bound of the ball evaluation therefore needs no new analysis. A number that does not fit
its width is detected and the evaluation is redone with `BigInt`, which also serves above 2048 fractional
bits. Sparse polynomials, the divisions and the exact evaluation still use `num-bigint`.

Same run, same machine (median of 7 measures, ms), 10 digits:

| polynomial | 0.6.0 | 0.7.0 | MPSolve 3.2.3 |
|---|---:|---:|---:|
| Wilkinson 80 | 267 | 154 | 21.5 |
| Wilkinson 50 | 36.5 | 15.6 | 8.3 |
| Wilkinson 30 | 4.9 | 3.3 | 2.4 |
| Chebyshev 120 | 227 | 119 | 36.9 |
| Chebyshev 80 | 52.6 | 20.8 | 9.0 |
| `(z - 3)^40 - 5` | 14.3 | 8.2 | 4.6 |
| five roots 10^-30 apart | 6.4 | 4.7 | 0.08 |
| Mignotte 40, 10^8 | 20.3 | 14.3 | 0.57 |

With the `precise` functions (the 0.6.0 column is from the previous run of the comparison, on the same
machine):

| polynomial | digits | 0.6.0 | 0.7.0 | MPSolve 3.2.3 |
|---|---:|---:|---:|---:|
| dense, degree 320 | 30 | 170 | 85 | 208 |
| dense, degree 320 | 80 | 255 | 168 | 389 |
| dense, degree 160 | 30 | 42.6 | 19.6 | 41.6 |
| dense, degree 160 | 80 | 79.0 | 40.6 | 76.0 |
| Chebyshev 80 | 80 | 94.0 | 45.6 | 26.6 |
| `z^1000 - 1` (sparse: unchanged) | 80 | 112 | 113 | 626 |

**Comparison with MPSolve 3.2.3, run again with this version** (same corpus, criteria and scripts; one
thread): 462 of 462 polynomials at 10 digits, 100 of 100 at 14, 30 and 80 digits with the `precise`
functions, decimal output included; no disc missed a reference root. Geometric mean of MPSolve's time
over pandroots' time at 10 digits: 3.8 (0.6.0 in the same run: 3.7; the polynomials that need
multiprecision are few), pandroots faster on 433 of the 462. By family, against 0.6.0 in the same run:
Chebyshev 0.71 -> 1.11, Wilkinson 0.36 -> 0.55, rounded Wilkinson 0.59 -> 0.83, shifted powers
0.76 -> 0.92, Mignotte 0.145 -> 0.168, clusters 0.039 -> 0.046. With the `precise` functions on the 100
polynomials: 1.6 at 14 digits, 1.6 at 30 digits, 2.5 at 80 digits (0.5.0: 0.61, 0.63, 1.03), pandroots
faster on 61, 60 and 74 of them.

MPSolve remains ahead on clusters and Mignotte pairs (twenty and six times faster) and on Wilkinson
polynomials (twice): there the number of evaluations and of bits is what costs, not the arithmetic.

Not done: products truncated to the bits that matter (the lower half of each product is computed only to
round exactly as `BigInt` does; dropping it would need a new error bound), the sparse evaluation and the
divisions on fixed-width numbers, parallelism. The fixed-width arithmetic is tested against `BigInt`
(20000 random operands, 1500 random evaluations, the whole corpus). `verification/lean/FixedWidth.lean`
proves the two identities it relies on (the floor of a negative quotient from the division of the
magnitude; the difference of two magnitudes computed modulo 2^(64 n), with and without a borrow); the
Rust code itself is not formalised.

## Version 0.6.0

Two changes around the solver; the iteration (the simultaneous rectangle with the three-mean support) and
the certificate are those of 0.5.0, unchanged.

**The root zero.** `P = z^k Q` with `Q(0) != 0`: the `k` trailing zero coefficients are dropped, the root 0
is returned exactly (radius zero, multiplicity `k`) and only `Q` is solved. A disc found for `Q` counts
roots of `Q`; it counts the same roots of `P` if it does not contain 0, which is tested (`|z| > r`); if a
disc is not proved to stay away from 0 the polynomial is solved without deflation, as in 0.5.0. Up to
0.5.0 a zero constant term made the polynomial fail the square-free test and sent it to Yun's algorithm:
`z^20` took 330 us, it now takes 0.5 us.

**Square-free decomposition.** Yun's algorithm ran over the Gaussian rationals (`num-rational`: a gcd of
big integers at every operation). It now runs over the Gaussian integers: pseudo-divisions, and the
content (a gcd in Z[i] of the coefficients) removed after each step. The factors are the same up to
constants; the test suite compares the two versions on 400 random products and rebuilds each polynomial
from its factors.

Same run, same machine, 10 digits (median of 7 measures, us):

| polynomial | 0.5.0 | 0.6.0 | MPSolve 3.2.3 |
|---|---:|---:|---:|
| `z^20` | 329 | 0.5 | 0.0 |
| `z^20 (z - 1)(z + 2)` | 531 | 5.5 | 5.8 |
| `(z-1)^10 (z+2)^10 (z-i)^10` | 3545 | 144 | 13431 |
| random, degree 9, multiple roots | 644 | 26 | 174 |
| random, degree 18, multiple roots | 1727 | 92 | 1841 |

Over the 25 polynomials with multiple roots of the corpus, 0.6.0 takes 9 to 32 times less time than 0.5.0
(geometric mean 18); over the 429 polynomials that have neither multiple roots nor a root zero the two
versions take the same time (ratio 1.03, within the noise of that run).

**Comparison with MPSolve 3.2.3, run again with this version** (same corpus, criteria and scripts as for
0.5.0; one thread): 462 of 462 polynomials at 10 digits, 100 of 100 at 14, 30 and 80 digits with the
`precise` functions, decimal output included; no disc missed a reference root. Geometric mean of
MPSolve's time over pandroots' time at 10 digits: 3.7, against 2.9 for 0.5.0 measured in the same run;
pandroots is faster on 434 of the 462 (0.5.0: 410). By family, polynomials with multiple roots go from
0.8 to 14, zero roots and monomials from 0.005 to 0.4 (MPSolve removes zero roots before its timed
computation). MPSolve remains ahead on clusters (0.06), Mignotte (0.16), Wilkinson (0.45), Chebyshev
(0.67) and shifted powers: there the time is in the multiprecision evaluation of the polynomial, which
this version does not touch. The machine was not idle during that run; the ratios between solvers
measured in the same run are more reliable than the absolute times.

**Lean.** `verification/lean/ZeroDeflation.lean` proves the mathematics of the deflation (seven theorems:
`P = X^k Q` from the zero coefficients, the roots and multiplicities of `X^k Q`, the count of a disc away
from zero, invariance under a constant factor). It does not verify the Rust code, nor Yun's algorithm.

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
