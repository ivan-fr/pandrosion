# Mathematical evidence and source provenance

The Rust solver in this release is version 0.14.0: the sources of 0.5.0 with the changes listed in
`CHANGELOG.md` (0.6.0: deflation of the root zero, Yun's algorithm over the Gaussian integers; 0.7.0:
fixed-width arithmetic in the multiprecision evaluation, which computes the same integers; 0.8.0 to
0.10.0: the evaluation of double precision points, the goal `isolate`, the step of a cluster and its
cursor in multiprecision; 0.11.0 and 0.12.0: gcds by images modulo primes in Yun's algorithm, the start from
the exact coefficients, the choice between two starts; 0.13.0: the product by a short multiplier in one
pass, which computes the same integers, Horner's rule over runs of zero coefficients, the test of the
certificate from the smallest gap, the bounds of the certificate taken from the last evaluation of the sweeps; 0.14.0: the same Horner's rule
in two's complement, which computes the same integers again; no Lean file was added for these, which are checked by exact division,
by the certificate and by the tests).
Its source hashes are recorded in `provenance.json`.

The files `SimultaneousRectangle.lean`, `SmithDiscs.lean` and `FixedPointCertificate.lean` under `lean/`
are those of G8, revision 7 (38 theorems: the simultaneous rectangle, Smith discs, the fixed-point
certificate down to the inequalities the program tests, and the real-disc test), with the build and
axiom-audit log produced on 14 November 2026 in the author's Lean 4 / Mathlib container
(`build_log.txt`). They were not rebuilt for this release.

`ZeroDeflation.lean` is new in 0.6.0 (seven theorems, checked on 15 November 2026 in the same container,
Lean 4.33.1 / Mathlib v4.33.1; log and axiom audit in `build_log_zero_deflation.txt`; axioms: `propext`,
`Classical.choice`, `Quot.sound`). It covers the mathematics of the deflation of the root zero: dropping
`k` zero trailing coefficients is the factorisation `P = X^k Q`; the roots of `P` are `0`, `k` times, and
the roots of `Q`; the multiplicity of `0` is exactly `k` when `Q(0) != 0`; a disc with `|z| > r` holds
the same roots of `P` as of `Q`, so its count is unchanged; a nonzero constant factor changes no root.

`FixedWidth.lean` is new in 0.7.0 (four lemmas, checked on 15 November 2026 with Lean 4.35.0 / Mathlib
v4.35.0 in a new container; `ZeroDeflation.lean` was checked again there; log and axiom audit in
`build_log_fixed_width.txt`). It covers the two identities behind the sign-magnitude arithmetic of the
module `limbs`: `floor(-a / k) = -(a / k)`, minus one when the division is not exact, and the difference
of two magnitudes computed modulo `M`, with and without a borrow.

`ScaledVariable.lean` (0.8.0, nine theorems) and `ClusterStep.lean` (0.9.0, six theorems) were checked on
15 November 2026 with Lean 4.35.0 / Mathlib v4.35.0 (log and axiom audit in `build_log_0_9_0.txt`, which
also rechecks `FixedWidth.lean` and `ZeroDeflation.lean`).  The first covers the evaluation of a point
outside the unit disc through `T(t) = S(2^e t)`: the values of `T`, `T'`, `T''`, its leading coefficient,
the Newton term and the invariance of `S S''/S'^2`, and the inclusion of a Smith disc in the disc that
encloses its component.  The second covers the step of a cluster on the function it is exact for,
`(w - g)^K - a`: the cursor is `a / u^K`, the anchor is `g`, and every `K`-th root of the cursor gives a
root.  It says nothing of how close a cluster of an arbitrary polynomial is to a shifted power: there the
step is a proposal, and the certificate decides.

`ClusterCursor.lean` (0.10.0, five lemmas, checked on 15 November 2026 with Lean 4.35.0 / Mathlib
v4.35.0; log and axiom audit in `build_log_0_10_0.txt`) covers the algebra of the cursor of a cluster
computed from `N = S/S'` and `beta = S S''/S'^2`: the logarithmic derivative and its derivative from these
two numbers, the two forms of the cursor, its invariance under the scaling by a power of two, and the
K-th power law behind the bits asked after a step.  The rounding of that computation is not formalised:
the cursor is used only above an estimate of its rounding, and an error there would cost time, not
correctness.

`CertificateGap.lean`, `SparseHorner.lean`, `TwoComplement.lean` and `FloatModel.lean` (0.13.0 and 0.14.0, twenty-four theorems,
checked on 16 November 2026 by the workflow `Pandroots Lean files` of the repository with its own toolchain,
Lean 4.33.1 / Mathlib v4.33.1; log and axiom audit in `build_log_0_14_0.txt`, script `check_0_14_0.sh`):

* `CertificateGap.lean` (four theorems): the test of the certificate from the smallest gap.  With `g` a
  lower bound of the gaps of the point `k` and `W` the sum of all the bounds `w_l`, `W / g < 1/2` and
  `w_k W / g² < 1/4` give the two inequalities `σ_k < 1/2`, `w_k τ_k < 1/4` that `FixedPointCertificate.lean`
  starts from.
* `SparseHorner.lean` (six theorems): a run of zero coefficients in Horner's rule for `(S, S', S''/2)` is
  the closed form that the program uses (`zero_steps`, `gap_step`, with `q1_succ` and `two_q2` for the two
  factors `g x^(g-1)` and `g (g-1)/2 x^(g-2)`); the value of `S` is that of the rule for `S` alone
  (`value_alone`); and a power `x^(k+1)` computed with `k` products in any order, each within a relative
  error `u`, is within `((1 + u)^k - 1) |x|^(k+1)` of the true one (`comp_bound`), the bound of `k`
  successive products: repeated squaring does not cost the rounding bound anything.
* `TwoComplement.lean` (five theorems): the shift that fills with the sign bit is the floor of the
  quotient, the common power of two of the multipliers comes off the shift, and the limb of the quotient
  is `floor(lo / 2^s) + (hi mod 2^s) 2^(64 - s)` from two consecutive limbs of the product.

* `FloatModel.lean` (nine theorems): the floating-point model.  The format is defined as the numbers
  `m 2^e` with `|m| ≤ 2^p` and `e ≥ emin` (binary64: `p = 53`, `emin = -1074`; no overflow), and `y` is a
  rounding of `x` to nearest when no number of the format is closer.  Then `|x - y| ≤ 2^-p |x|` for every
  `x` of the normal range, `|x| ≥ 2^(emin + p - 1)` (`nearest_normal`, `binary64`), and `|x - y| ≤ 2^emin / 2`
  below it (`nearest_small`): the relative error `u = 2^-53` that the other bounds assume of each product
  and each sum is a consequence of the definition of the rounding.  And the product of two complex numbers
  as the program computes it, four real products, a difference and a sum, is within `√2 (2 u + u²) |z| |w|`
  of the exact one (`cmul_error`, stated with squares).

What these four files do not cover.  They are statements about real, complex and integer numbers.  That the
arithmetic of the machine is the rounding to nearest of `FloatModel.lean` (IEEE 754, which Rust's `f64`
follows), overflow, the chain from one rounded operation to the bound of Horner's rule that the program
uses (`4 (m + 1) 2^-52` times the sum of the moduli, with its term for the operations that underflow), the
rounding of `W / g` in double precision, and the Rust code that implements the formulas (signed carries,
the detection of a number that does not fit) are not formalised; they are covered by the margins of the
code and by its tests against `BigInt`.  That the sweeps and the certificate evaluate the
polynomial at the same points (0.13.0) is a property of the program, not a theorem: `value_alone` is its
mathematical part.  The number of bits asked in advance (0.14.0) is a heuristic and needs no proof: a
value with too few bits is computed again, as before.

These files provide evidence for the mathematical statements, not a formal verification of
version 0.14.0. They are not compiled by Cargo.

The formal certificate assumes valid numerical upper and lower bounds. The Rust
floating-point bounds, underflow handling, guards, fixed-point ball evaluation, multiprecision implementation,
fallback count of unresolved clusters, the fixed-width arithmetic of 0.7.0, 0.13.0 and 0.14.0 (tested against `BigInt`), the rounding bound of Horner's rule over runs of zero coefficients, the test of the certificate from the smallest gap (it implies the two inequalities of the theorem; tested against the plain sums), the test that keeps the discs away from zero, and Yun's algorithm
(tested against the rational version of 0.5.0 and by rebuilding the polynomial from its factors) are not
formally verified by these files. There is no theorem of global convergence of the solver.
