# Theorem 4.3 — complete scalar Lean coverage

The V25 fixed-circle theorem is formalized for **every real `p > 2`**. The degree is not restricted to natural numbers. The three modules introduced in V23 compile with the repository's pinned Lean/mathlib toolchain; the audit covers all **69 declarations**, including definitions of the inverse and the iteration.

| Manuscript claim | Lean declaration |
|---|---|
| Convex scaling in the logarithmic Cayley coordinate | [`cayleyLog_scaled`](../../LeanMath/Papers/RectangleFixedCircleUniform.lean) |
| Uniform upper-error inequality, including scalar tangent endpoints | `RectangleFixedCircleUniform.uniform_upper` |
| Alternation and strict reduction of absolute logarithmic error | `RectangleFixedCircleUniform.real_branch_alternation_contraction` |
| Exact correction interval and descending sign | `RectangleFixedCircleDynamics.parameters_iff`, `Q_neg_interior`, `input_strictAnti` |
| Existence, uniqueness and continuity of the selected inverse | [`inputHomeomorph`, `correction_input`, `correction_continuous`](../../LeanMath/Papers/RectangleFixedCircleDynamics.lean) |
| Invariance and convergence of every orbit | `RectangleFixedCircleDynamics.orbit_invariant`, `orbit_converges` |
| Exact fifth-order limit in the actual input-error variable | `RectangleFixedCircleDynamics.inverse_order_five`, `order_five_coefficient_neg` |
| Explicit manuscript endpoints and residual domain | [`endpoint_residual`, `tau_reciprocal`, `error_band_iff`, `open_error_band_iff`](../../LeanMath/Papers/RectangleFixedCircleTheorem43.lean) |
| Inversion of the actual rational residual `N(v)/D(v)=t` | `RectangleFixedCircleTheorem43.unique_correction`, `correction_residual` |
| Assembled open-band signs, invariance and convergence | `RectangleFixedCircleTheorem43.theorem_4_3` |
| Initialization at a prescribed positive estimate, multiplicative update, true residual and limit `X^(-1/p)` | `RectangleFixedCircleTheorem43.root_estimate_initial`, `root_estimate_update`, `root_estimate_residual`, `root_estimate_converges` |

The formalization uses `input p v = log(N(v)/D(v))/p` and `output p v = input p v + log v`. The correction parameter lies in the compact interval `[1/v₊, v₊]`. The input map is proved continuous and strictly decreasing, then inverted as a homeomorphism onto the symmetric error interval. Thus the inverse's existence and continuity are conclusions, not assumptions supplied by the caller.

Compactness and strict error reduction prove convergence. The existing parameterized fifth-order limit is composed with the continuous inverse, with punctured neighborhoods explicitly checked. The resulting coefficient is `−(p²−1)(p²−4)/720`, proved strictly negative. The error interval contains a neighborhood of zero because its radius is proved positive.

The formal endpoints use `r = sqrt(12(p²−1))` and `τ± = (7p²−4 ± 2pr)/(p²−4)`; `r_eq_two_sqrt` identifies these with the displayed manuscript formulas. The scalar proof includes tangent endpoints. Regular geometric constructions still require the transverse interior and their stated finite-chart hypotheses.

## Reproduce

From the repository root:

```sh
lake build LeanMath.Papers.RectangleFixedCircleTheorem43
python3 scripts/audit_circle_v23.py
```

[`Audit.lean`](../../validation/rectangle_fixed_circle_v23/Audit.lean) prints each declaration's transitive axioms. The audit script verifies that this manifest covers all three modules, rejects `sorryAx`, and permits only `propext`, `Classical.choice` and `Quot.sound`. The default `LeanMath` import and GitHub Actions include the new development.

The earlier 33-declaration integer-degree proof remains unchanged. The separate 41-declaration residual-gate controller is also retained. The written global decentered-arc theorem, branch-driven AD switching assembly and geometric cost inventory have their distinct evidence scopes; they are not subsumed by this scalar theorem audit.

V24 adds a written equivalence comparison with symbolic checks. It does not extend this Lean coverage; the three source modules and 69-declaration audit are unchanged from V23. The recorded target build and original audit remain in [the V23 archive](../reciprocal_geometry_v23/verification/).

V25 is an editorial reorganization: Theorem 4.3 and the Lean declaration names are preserved. The equivalence discussion is now Appendix F; the branch-driven switching proposition is now 8.1. No Lean source or audit declaration changed.
