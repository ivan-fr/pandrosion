# Geometry V25

[Manuscript](Reciprocal_Root_Geometry_v25.pdf) · [LaTeX](main.tex) · [Changes from V24](REVISION_NOTES.md) · [Validation](VALIDATION.md) · [Literature ledger](LITERATURE_REVIEW.md)

V25 makes the paper easier to enter: the worked fixed-circle construction appears in Section 2, before the reusable coordinates and proofs. V24 remains archived.

## Changes from V24

- The cubic eight-line example is introduced first, with its rectangle and rail notation given locally. Theorem 4.3 keeps its number and unchanged Lean coverage.
- The literature comparison follows the cost analysis in Section 7. The former Section 2.3, on homographies, quadratic contact and Böttcher coordinates, becomes Appendix F.
- The conclusion has a separate discussion and four explicit open questions: geometric lower bounds, conditioning/charts, equivalence within algebraic families, and formal composition of complete calculators. It does not reopen the proved whole-branch contraction result.
- The accuracy/work table explicitly distinguishes the first three per-step totals from the two controller totals that include 12 initial cache joins. The numeric entries and accounting model are unchanged; the former Table 3 is now Table 2.
- BibTeX protection preserves Halley, Euler, Book III and Padé in the rendered bibliography.

## Proof and evidence map

| Claim | Evidence and exact scope |
|---|---|
| Equivalence comparisons in Appendix F | Written [positioning argument](POSITIONING.md), classical Böttcher theorem, 18 exact symbolic checks and 10 finite integer regression cases. Outside the Lean audit. |
| Theorem 4.3, every real p>2 | [Formal claim map](LEAN_THEOREM_4_3.md): 69 audited declarations prove the uniform inequality, alternation, the unique continuous inverse, explicit residual band, invariant orbits, convergence and exact local order five. [Independent verifier](src/uniform/verify.py): 25 symbolic checks, 240 finite branch/endpoint cases and 72 trajectories at 400 digits. |
| Integer-degree branch inequality | Unchanged [RectangleFixedCircleBranch](../../LeanMath/Papers/RectangleFixedCircleBranch.lean), with 33 audited declarations. Its older proof is independent of the new convexity argument. |
| Circle geometry and local fifth order | [RectangleFixedCircle](../../LeanMath/Papers/RectangleFixedCircle.lean) supplies geometric certificates and a parameterized local limit; `RectangleFixedCircleDynamics.inverse_order_five` transports that limit to the actual inverse map. |
| Decentered global convergence and fifth order | Written Theorem 5.1; [RectangleDecenteredArc](../../LeanMath/Papers/RectangleDecenteredArc.lean) supplies algebraic certificates. |
| Branch-driven circle–AD convergence | Written Proposition 8.1, supported by 144 geometric trajectories at 180 digits. |
| Optional residual gate | Unchanged [RectangleCircleSafeguard](../../LeanMath/Papers/RectangleCircleSafeguard.lean); 41-declaration audit and a separate 144-trajectory campaign. |
| Mobile work | Explicit inventory and instrumented geometry. Not a Lean execution-cost semantics or an optimality theorem. |
| Electrical results | Retained order-three [V30 behavioral study](../pandrosion_analog_v30/README.md). No hardware implementation or new SPICE simulation of a fifth-order cell. |

## Build the paper

From this folder:

```bash
bash build.sh
```

Requires Tectonic or latexmk with the packages listed in `main.tex`. Prepared figure PDFs and `accuracy_table.tex` are included, so a PDF build does not require Lean, Python, the older manuscripts or network access to research data. A first Tectonic build may download TeX packages.

## Reproduce the mathematics

From the repository root, with Python and the versions in `requirements.txt`:

```bash
python3 paper/reciprocal_geometry_v25/src/positioning/verify.py
python3 paper/reciprocal_geometry_v25/src/uniform/verify.py
python3 paper/reciprocal_geometry_v25/verify.py
```

The first two commands are standalone and write [positioning checks](src/positioning/checks.json) and [uniform checks](src/uniform/checks.json). The full verifier also reruns the archived circle and arc incidence checks, both controllers, figures and retained V30 data/provenance checks. It needs the broader repository at the surrounding paths. Its inherited generators may refresh deterministic companion data files. The LaTeX-only ZIP is not advertised as a standalone snapshot of the entire Lean/analog repository.

Run the formal audits from the repository root with the pinned Lean/mathlib environment:

```bash
lake build LeanMath.Papers.RectangleFixedCircleTheorem43 LeanMath.Papers.RectangleCircleSafeguard
python3 scripts/audit_circle_v23.py
python3 scripts/audit_branch.py
python3 scripts/audit_circle_safeguard.py
```

All three audits allow only `propext`, `Classical.choice` and `Quot.sound`. The unchanged V23 audit checks every declaration in its three source modules, including the noncomputable inverse. These modules are part of the default Lean build; GitHub Actions also runs this audit, the positioning checks, the real-parameter verifier and the V25 PDF build. V25 outputs are in [verification](verification/); the original Lean build and audits remain in [V23 verification](../reciprocal_geometry_v23/verification/).

The [MIT license](../../LICENSE) and [citation metadata](CITATION.cff) apply. The mathematical results and source validation do not imply journal publication or an external reviewer score.
