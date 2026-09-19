# Geometry V22 — start here

**[Read the paper](Reciprocal_Root_Geometry_v22.pdf)** · [Source](main.tex) · [Response to the review](REVISION_NOTES.md) · [Validation](VALIDATION.md) · [Gallery](https://ivan-fr.github.io/pandrosion/)

*Geometric Root Calculators: Fixed Circles, Global Convergence, and Analog Realization* retains the construction-first organization of V21, with its five Pandrosion drawings, and integrates the new whole-branch theorem.

The fixed-circle inverse strictly reduces logarithmic error throughout its transverse real branch for every integer `p≥3`. This yields invariant-band convergence. Centered AD supplies entry from arbitrary positive starts and handles excluded finite charts. The branch-driven protocol omits the old residual gate: for the cubic it uses at most **18 joins per regular step**, including the next power/residual cache, after **12 initial joins**. A full attempted readout followed by fallback costs at most **31 expanded traces**. These are upper bounds for that binary-power protocol, not a global eight-line claim.

## Read the claims at their actual scope

| Result | Evidence |
|---|---|
| Whole-branch strict error contraction | [RectangleFixedCircleBranch](../../LeanMath/Papers/RectangleFixedCircleBranch.lean), `whole_branch_contraction`; 33 declarations in its [axiom audit](../../scripts/audit_branch.py). The theorem parameterizes the descending branch by `v`, with `Q(p,v)<0`. |
| Invariant-band convergence and global branch-driven protocol | Written compactness/continuity arguments in Sections 3.5 and 6.1. These assemblies are not advertised as additional Lean theorems. |
| Circle geometry and local fifth order | [RectangleFixedCircle](../../LeanMath/Papers/RectangleFixedCircle.lean) supplies incidence/parameter certificates and a parameterized local limit; V22 gives the inverse-branch/local-order assembly. |
| Geometric residual gate and its global switching theorem | [RectangleCircleSafeguard](../../LeanMath/Papers/RectangleCircleSafeguard.lean), including `ruler_circle_AD_global`; separate 41-declaration [audit](../../scripts/audit_circle_safeguard.py). This V21 alternative remains available. |
| Branch-driven trace counts and actual intersections | [branch_entry.py](../../research/fixed_circle_safeguard/branch_entry.py), [protocol.py](src/branch/protocol.py) and [results](src/branch/protocol_checks.json). Physical operation counting is a written, instrumented protocol inventory. |
| Endpoint certificates and centered quadratic cell equation | [Symbolic/high-precision checker](src/branch/verify.py) and [records](src/branch/checks.json). The cell equation is a design specification, not an implemented fifth-order electrical circuit. |
| Five Pandrosion constructions | MA is a reference remark; AK, AD, projective order four and decentered order five retain their drawings and derivations. Their earlier formal boundary is documented in [V21](../reciprocal_geometry_v21/README.md#claim-to-source-map). |
| Existing analog evidence | [V30](../pandrosion_analog_v30/README.md) documents the order-three AD behavioral prototype. No new SPICE campaign or fabricated-chip evidence is introduced by V22. |

Strict whole-branch contraction is not a proved uniform factor of `0.36`, nor a pairwise Lipschitz bound. Sampled ratios illustrate the theorem; they do not prove the optional gate's stronger one-half bound. The raw circle remains undefined outside its real band. Global exact convergence does not establish uniformly bounded drawings or browser floating-point reliability.

## Reproduce

From the repository root:

```sh
python3 -m pip install -r paper/reciprocal_geometry_v20/requirements.txt
python3 paper/reciprocal_geometry_v22/verify.py
bash paper/reciprocal_geometry_v22/build.sh
lake build LeanMath.Papers.RectangleFixedCircleBranch LeanMath.Papers.RectangleCircleSafeguard
python3 scripts/audit_branch.py
python3 scripts/audit_circle_safeguard.py
```

The Lean toolchain and mathlib are pinned. Tectonic or `latexmk` is needed to build the PDF; supplied figures and the generated work table allow the PDF build alone. `verify.py` regenerates symbolic checks, both 144-trajectory controllers, the 250-digit work table and the figures. It checks retained V30 records and figure provenance, without rerunning electrical simulations or compiling Lean.

The original mathematical campaigns remain in their archived V20 locations. The five Pandrosion figures are reproduced by [draw_figures.py](draw_figures.py) and [draw_pandrosion.py](draw_pandrosion.py); the branch plot by [figure.py](src/branch/figure.py); the controller drawing by [draw_safeguard.py](draw_safeguard.py). The fast-power and circuit diagrams are explicitly reused from V30.

The two controller campaigns each cover 144 trajectories at 180 decimal digits, across eight degrees through one million, three inputs and six initial log residuals. The branch-driven campaign checks real-domain failures, affine singularities, unit states and full fallback costs. These finite checks supplement the proofs.

## Sources and distribution

[Geometry V21](../reciprocal_geometry_v21/README.md), including its safeguard section and Lean source, is retained unchanged. The gallery's numerical code is unchanged by this manuscript revision; the new branch-driven implementation is the reproducible Python geometry above.

The historical name is sourced to the opening of Pappus' *Collection*, Book III, via [John B. Little's translation](https://crossworks.holycross.edu/hc_books/63/). The rectangle is a modern reconstruction, and the accelerated variants are not attributed to the ancient text.

The repository includes the [MIT License](../../LICENSE). Use [CITATION.cff](CITATION.cff) to cite V22. CI builds V22 and the archived papers, tests the mathematics, and runs the two separate axiom audits. See the [repository](https://github.com/ivan-fr/pandrosion) and its PR checks for current CI status.
