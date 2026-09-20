# Geometry V23

[Manuscript](Reciprocal_Root_Geometry_v23.pdf) · [LaTeX](main.tex) · [Changes from V22](REVISION_NOTES.md) · [Validation](VALIDATION.md) · [Literature ledger](LITERATURE_REVIEW.md)

V23 is organized around two fifth-order root solvers and explicit geometric cost. The classical supports and exploratory analog material remain in appendices. V22 is preserved as an archive.

## Main changes

- A uniform Cayley-coordinate / strict-convexity proof replaces the degree-by-degree endpoint bounds. The scalar theorem is now proved in Lean and holds for every real p>2, and proves alternation throughout the real band. The constructions with a finite power stage still require integer p≥3.
- Decentered AD is presented as the second main result: global monotone fifth-order convergence from every positive start.
- A construction-by-construction comparison identifies classical Newton/Halley/Padé formulas, the relation to quadratic approximation, and distinctions from osculating-circle methods. The bibliography adds Melman, Amat–Busquier–Gutiérrez, Karp–Lin, Kanwar–Singh–Bakshi and Pakdemirli. It asserts no exhaustive priority result.
- The three fifth-order maps are compared in the same logarithmic error coordinate. Their coefficients are independently derived by exact series recurrences.

## Proof and evidence map

| Claim | Evidence and exact scope |
|---|---|
| Theorem 4.3, every real p>2 | [Formal claim map](LEAN_THEOREM_4_3.md): 69 audited declarations prove the uniform inequality, alternation, the unique continuous inverse, explicit residual band, invariant orbits, convergence and exact local order five. [Independent verifier](src/uniform/verify.py): 25 symbolic checks, 240 finite branch/endpoint cases and 72 trajectories at 400 digits. |
| Integer-degree branch inequality | Unchanged [RectangleFixedCircleBranch](../../LeanMath/Papers/RectangleFixedCircleBranch.lean), with 33 audited declarations. Its older proof is independent of the new convexity argument. |
| Circle geometry and local fifth order | [RectangleFixedCircle](../../LeanMath/Papers/RectangleFixedCircle.lean) supplies geometric certificates and a parameterized local limit; the new `RectangleFixedCircleDynamics.inverse_order_five` transports that limit to the actual inverse map. |
| Decentered global convergence and fifth order | Written Theorem 5.1; [RectangleDecenteredArc](../../LeanMath/Papers/RectangleDecenteredArc.lean) supplies algebraic certificates. |
| Branch-driven circle–AD convergence | Written Proposition 7.1, supported by 144 geometric trajectories at 180 digits. |
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
python3 paper/reciprocal_geometry_v23/src/uniform/verify.py
python3 paper/reciprocal_geometry_v23/verify.py
```

The first command is standalone and writes [uniform checks](src/uniform/checks.json). The full verifier also reruns the archived circle and arc incidence checks, both controllers, figures and retained V30 data/provenance checks. It needs the broader repository at the surrounding paths. Its inherited generators may refresh deterministic companion data files. The LaTeX-only ZIP is not advertised as a standalone snapshot of the entire Lean/analog repository.

Run the formal audits from the repository root with the pinned Lean/mathlib environment:

```bash
lake build LeanMath.Papers.RectangleFixedCircleTheorem43 LeanMath.Papers.RectangleCircleSafeguard
python3 scripts/audit_circle_v23.py
python3 scripts/audit_branch.py
python3 scripts/audit_circle_safeguard.py
```

All three audits allow only `propext`, `Classical.choice` and `Quot.sound`. The V23 audit checks every declaration in the three new source modules, including the noncomputable inverse. The new modules are part of the default Lean build; GitHub Actions also runs this audit, the real-parameter verifier and the V23 PDF build. Recorded local outputs are in [verification](verification/).

The [MIT license](../../LICENSE) and [citation metadata](CITATION.cff) apply. The mathematical results and source validation do not imply journal publication or an external reviewer score.
