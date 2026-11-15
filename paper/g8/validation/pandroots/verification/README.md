# Mathematical evidence and source provenance

The Rust solver in this release is version 0.12.0: the sources of 0.5.0 with the changes listed in
`CHANGELOG.md` (0.6.0: deflation of the root zero, Yun's algorithm over the Gaussian integers; 0.7.0:
fixed-width arithmetic in the multiprecision evaluation, which computes the same integers; 0.8.0 to
0.10.0: the evaluation of double precision points, the goal `isolate`, the step of a cluster and its
cursor in multiprecision; 0.11.0 and 0.12.0: gcds by images modulo primes in Yun's algorithm, the start from
the exact coefficients, the choice between two starts; no Lean file was added for these, which are
checked by exact division, by the certificate and by the tests).
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

These files provide evidence for the mathematical statements, not a formal verification of
version 0.12.0. They are not compiled by Cargo.

The formal certificate assumes valid numerical upper and lower bounds. The Rust
floating-point bounds, underflow handling, guards, fixed-point ball evaluation, multiprecision implementation,
fallback count of unresolved clusters, the fixed-width arithmetic of 0.7.0 (tested against `BigInt`), the test that keeps the discs away from zero, and Yun's algorithm
(tested against the rational version of 0.5.0 and by rebuilding the polynomial from its factors) are not
formally verified by these files. There is no theorem of global convergence of the solver.
