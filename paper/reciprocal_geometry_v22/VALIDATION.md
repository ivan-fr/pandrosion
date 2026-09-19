# V22 validation — 19 September 2026

The delivered paper has **19 pages (16 main-text pages) and eleven numbered figures**. All five original Pandrosion drawings remain: MA, AK, centered AD, projective order four and decentered order five. The contraction plot and the restored inverse-fold figure supplement the fixed-circle, control, binary-power and circuit figures. MA and the residual gate are retained in the appendices.

## Executed locally

- `lake build LeanMath.Papers.RectangleFixedCircleBranch` passed with the pinned toolchain and mathlib. The module's 33 declarations passed `scripts/audit_branch.py`, allowing only `propext`, `Classical.choice` and `Quot.sound`.
- The retained safeguard's independent 41-declaration audit passed again. No extra axioms or unfinished proofs were introduced.
- The complete V22 verifier passed archived symbolic, fixed-circle and decentered-arc checks; both controller campaigns; the new branch identities and endpoint bounds; centered analog identities; and retained V30 data/figure provenance.
- The new branch-driven campaign passed 144 actual geometric trajectories at 180 digits through degree one million. Every trajectory reached absolute log residual below `1e-45` within 18 steps. Maximum relative disagreement with independent scalar updates was `4.3328584e-167`.
- Extra cases exercised missing real crossings, readout singularities `(p,t)=(3,7.75),(5,16)`, exact root/unit states, and forced full fallback costs. The old gated campaign additionally retains its two-positive-root selection and gate-failure tests.
- The accuracy/work table was generated at 250 digits, and its branch-driven row was independently reproduced by actual intersections. All methods use the same start, target and reciprocal-state error convention.
- SymPy verified the exact centered quadratic cell equation and its degree-independent derivative −1 at the root. This is an algebraic check, not a new electrical simulation.
- The Tectonic build passed without undefined references or overfull boxes. Every page was rendered and inspected through a contact sheet, with full-size checks of new proofs, tables, retained geometric diagrams, the circuit page and references. No isolated spill pages remain.
- Relative documentation links, expected PDF labels and whitespace checks passed. The original V21 package was left unchanged.

## Scope

The branch audit proves strict one-step logarithmic-error reduction on the parameterized branch. The paper gives the invariant-band convergence, branch-driven global switching and concrete inverse-function/local-order assemblies as written proofs. The separately audited V21 residual-gated controller does have a formal global convergence theorem. Physical trace counts are a written inventory checked by the instrumented geometry, not a formal execution-cost semantics.

The branch graph and finite trajectories do not prove a uniform factor of 0.36, floating-point robustness, bounded drawing size or hardware performance. No new SPICE campaign was needed because the existing electrical implementation was not changed; the proposed circle cell remains unimplemented.

CI builds the new and archived PDFs, runs the two audits and new mathematical checks, and retains the broader repository campaigns. Its live status is reported by GitHub Actions rather than presumed here.

## Checks repeated for the editorial revision

- Re-ran `scripts/audit_circle_safeguard.py`: all 41 declarations passed, with only the same three permitted standard axioms.
- Re-ran `src/branch/protocol.py`: all 144 geometric trajectories at 180 digits passed, with at most 18 steps to the specified threshold; generated records and the work table are unchanged.
- Confirmed the tracked root `LICENSE` contains the MIT license and the 2026 Ivan Besevic copyright notice.
- The new `src/branch/fold.py` independently computes both positive inverse roots at `p=3,t=0.05` and checks that exactly the smaller one lies on the descending branch. It is included in the verifier and CI.
- Rebuilt and rendered the revised PDF. All eleven figures, the five Pandrosion drawings, the three appendices and theorem references are present; no overfull boxes or unresolved references remain.

This revision changes exposition, notation and figure layout. The Lean statements, endpoint certificates, controller implementations and electrical results are unchanged. The reported review explicitly identifies its author as a contributor to the branch proof; it is not treated as an independent first-reader validation of that work.
