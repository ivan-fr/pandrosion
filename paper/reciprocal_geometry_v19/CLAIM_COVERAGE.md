# Claim-level coverage — V19

| Paper statement | Source / evidence | Boundary |
|---|---|---|
| Rail products, telescope, Halley readout | `RectanglePencils.lean` | Explicit finite-chart hypotheses; modular incidence proofs |
| Rational fifth order and global positive convergence | `RectanglePencilsPade.lean` | Exact-real rational map; not every finite chart |
| Projective order-four support | `RectangleProjective.lean`, `RectangleProjectiveVerification.lean` | Full finite report theorem plus numerical map |
| Inverse quadratic / stable radical charts | `RectangleFixedCircle.lean`: `discriminant`, `sqrt_branch_left`, `sqrt_branch_right` | Branch equations with nonzero-denominator and nonnegative-discriminant assumptions |
| Fixed-circle order five | `logarithmic_order_five` | Formally parameterized by v=1+u; inverse-function passage and iterate convergence are written arguments |
| Circle and projector for arbitrary p | `circle_incidence`, `general_geometry_certificate`, `fourth_geometry_certificate` | Incidence and algebraic certificate; admissibility and branch choice remain explicit |
| Final rail readout and chain scaling | `final_readout`, `weighted_chain` | Modular proof; physical counting is separate |
| Rational fixed circle data | `rational_preparation`, `positive_preparation_scale` | Subfield membership and scale positivity; X-dependent hubs need constructible input |
| Sphere line and circle sections | `RectangleFixedCircleStereo.lean`: `line_image`, `circle_image` | Exact equations; no global projective-plane/sphere identification |
| Similarity and inverse projection | `similarity_circle_identity`, `finite_inverse` | Common scale, nonzero denominators |
| 2p+2 mobile finite lines | Written protocol, loop count checked in geometry scripts | Not a Lean cost-optimality theorem; excludes preparation and final inversion |
| General positive raw convergence | `Raw.global_raw_convergence` (module `RawConvergence`) | X>1, exact scalar state |
| Bilateral enclosure | `RealBracket.certified_bracket` | Exact reals; not outward-rounded executable arithmetic |
| Cubic center and local constant | `RealBracket.cube_root_halley`, `RealBracket.Local.exact_cubic_limit` | Coordinate conventions are explicit |
| Center entry-cell convergence | `RealBracket.Local.cell_convergence` | Sufficient cell, not maximal basin |
| Near-balanced Padé identification | `V14PadeTheorem.near_balanced_diagonal`, `identity_where_defined` | Ideal rational functions before rounded evaluation |
| General diagonal global convergence | `V14PadeGlobal.diagonal_global_convergence`, `diagonal_step_enclosure` | Exact scalar functions, positive starts |
| Dyadic entry and residual radius | `V14Entry.state_closed`, `worst_radius_bound` | Workload p=2^k−1 when interpreted as nested-square-root entry |
| Neutral AD reciprocal closure adds nothing | Written algebra in the reciprocal-bounds section | Not included in geometry audit; no global theorem transferred to reset-state map |
| Earlier center-defect variants | Retained V18 source `sections/05_bilateral_acceleration.tex` and companion; outside the seven protocols in V19 | Not part of fixed-circle cost theorem or the 149-declaration audit |
| 162 fixed-circle checks | `src/fixed_circle/verify.py`, `data/fixed_circle_results.json` | Finite symbolic/numerical software tests |
| 75 sphere checks and 3 infinity cases | `src/stereo/model.py`, `data/stereo_verification.json` | Ordinary floating-point tests; retain homogeneous directions |
| Work/accuracy table | `src/stereo/figures.py`, `data/benchmark.json` | Same p,X,s start; no elapsed-time interpretation |
| Historical novelty, maximal order, whole real basin | Not asserted | No proof established |

The geometry and background audit logs are kept separately to avoid inflating or conflating counts. Each figure caption states whether it is a construction, a domain plot, or a finite benchmark illustration.

## Added Pandrosion supports

- AK and centered-arc AD: explicit triangle chain, support construction and common report identity; Newton/Halley dynamics, with the older rectangle modules included in the source closure.
- Projective AD [2/1]: the direct-state degree convention is reconciled with reciprocal-state [1/2]. Existing projective incidence and order-four proofs remain in the audit.
- Decentered-arc AD: Section 2 gives the full constructible preparation, lower circle intersection, global monotone-convergence proof and logarithmic coefficient `(p-2)(p²-1)(3p+1)/1440`.
- `RectangleDecenteredArc`: ten audited algebraic declarations. `derivative_numerator`, `square_certificate` and `sign_decomposition` check the principal polynomial steps of the written global proof. Differentiation, sign reasoning, integration and convergence of the radical iterate sequence are not claimed as compiled Lean theorems.
- `src/decentered/verify.py`: 108 independent geometric checks for each of the four rectangle methods (432 total) at 160 digits, general symbolic certificates, four local Taylor checks and the common-start update table at 280 digits.
- Equality of centered/decentered AD mobile costs: explicit written protocol, with fixed preparation, parallel macros and final readout distinguished.
