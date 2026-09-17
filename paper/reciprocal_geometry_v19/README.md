# V19 — Reciprocal Root Geometry

**Rewritten paper: 18 pages, eight regenerated vector figures.** The 94-page V18 is preserved separately. The paper remains in English, matching the earlier manuscript; the interactive preview is in French.

## Read and explore

- `Reciprocal_Root_Geometry_v19.pdf`: the complete short paper.
- `previews/fixed_circle_stereo.html`: standalone synchronized sphere/plane preview, with rotation, construction stages, degree controls and explicit north-pole cases.
- `previews/fixed_circle_plane.html`: finite-chart planar preview from the fixed-circle study.
- `main.tex`, `references.bib`, `figures/*.pdf`: editable paper and publication-quality figures.
- `formal/`: pinned local Lean source dependency closure, geometry audit and separate background audit.
- `data/`, `src/`, `verification/`: numerical records, reproduction scripts, compilation and audit logs.

## Main results retained

The four explicitly drawn Pandrosion supports AK, centered AD, projective AD [2/1] and decentered-arc AD; a written proof of global monotone convergence and exact fifth order for the decentered arc, with its general constructible preparation; the reciprocal state and rail telescope; classical Newton/Halley and order-four projective support; rational fifth-order Padé and its global positive convergence; the new inverse-quadratic fifth-order method with 2p+2 mobile lines, rational circle data, explicit branch and p=4 chart; homogeneous continuation and similarity-normalized stereographic images; bilateral bounds and the negative neutral-AD symmetrization result; reciprocal-compression identification with diagonal Padé; the shrinking dyadic entry cell; a same-state construction-cost comparison; precise formalization boundaries.

The article is a fresh synthesis, not V18 with an appended chapter. Older wall-clock tables, circuit simulations, lengthy version histories, repeated proofs and large coefficient tables are not reproduced in the paper. Their original V18/V17 records remain at their existing workspace locations. No old benchmark is relabelled as a V19 run, and no circuit claim is transferred to the new geometric construction.

## Important distinctions

- Decentered-arc AD has a written global monotone convergence proof. Its ten Lean certificates cover algebraic identities, not yet the complete analytic convergence theorem. Its additional mobile support costs one arc and one join, exactly like centered AD; preparation differs.
- Rational Halley and rational [2/2] are globally convergent as exact scalar maps. The fixed-circle inverse has a proved fifth-order **local** limit; whole-domain contraction is not claimed.
- The literal 2p+2-line protocol assumes finite, nondegenerate joins. A projective continuation can use a point at infinity, but does not prove the same physical straightedge cost for constructing the needed parallel.
- The sphere is a display. Homogeneous incidence vectors remain authoritative because distinct infinite directions have the same image N.
- A common planar scale preserves the circle. Independent width/height normalization would produce an ellipse before projection.
- All circle-center/pole parameters depend rationally on the integer p; additional fixed rail centers are rational functions of X. Arbitrary irrational X does not make every fixed point rational.
- Historical priority and construction-cost optimality remain open. No universal order-five ceiling is asserted.

## Rebuild the paper

Tectonic or a TeX installation with latexmk is required:

```sh
bash build.sh
```

The supplied figures make this independent of Python and of the numerical reruns. The first TeX run may download packages.

## Reproduce the mathematics and figures

Install the packages in `requirements.txt` in a Python environment, then run from this directory:

```sh
python src/fixed_circle/verify.py
python src/stereo/model.py
python src/stereo/figures.py figures
python src/decentered/verify.py
python src/decentered/figures.py figures
bash build.sh
```

The fixed-circle script checks 162 geometries at 250 decimal digits and exact symbolic identities. The sphere model checks 75 regular configurations and three infinity cases. The report study checks 108 constructions for each of AK, AD, projective AD and decentered-arc AD at 160 digits, general symbolic certificates and local series at p=3,4,5,7; its accuracy table is generated at 280 digits. `data/benchmark.json` is regenerated at 280 digits by the figure script; the browser uses ordinary double precision. Source-study notes under `src/` may retain original workspace command names; use the commands above for this distribution.

## Lean

The geometry audit names exactly **149 declarations**: 101 inherited geometric statements, 28 fixed-circle statements, 10 stereographic line/circle statements and 10 decentered-arc algebraic certificates. A separate audit names 11 analytical background results used in the short synthesis; it is not included in the 149 count.

```sh
cd formal
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean BackgroundAudit.lean
```

The Lean and mathlib versions are pinned in the supplied files. Internet is needed to acquire external dependencies on a clean machine. `SOURCE_HASHES.json` checks the bundled local proof sources. Audits list only the standard axioms `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` is allowed. The written inverse-function argument connects the formally checked parametric error limit to the local radical branch. The whole rendering program, complete exceptional construction sequence and physical cost accounting are outside the formal proof boundary.

On the authoring Mac, Lake was run with the bundled Git executable in PATH because Apple Git requests Xcode license acceptance. No global Git setting was changed.

## Browser checks

`verification/check_preview.cjs` uses Playwright and installed Chrome. Make `playwright` available to Node (for example through NODE_PATH), then run:

```sh
node verification/check_preview.cjs
```

The check covers every stage for five degrees, initial and final centers at N, rotation, narrow layouts and out-of-domain inputs. It checks browser behavior, not a mathematical theorem.

`REVIEW_V19.md` records the complete mathematical and editorial reread. `src/review/check_math.py` reproduces the supplementary symbolic audit. `CLAIM_COVERAGE.md` maps the principal statements to their evidence. `CHECKS_V19.json` and `SHA256SUMS` record release validation and file integrity.
