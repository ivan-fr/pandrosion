# V20 — Reciprocal Root Geometry

**18 pages, seven vector figures, seven geometric protocols.** The paper is in English; the public interactive gallery is in French.

- [Read the paper](Reciprocal_Root_Geometry_v20.pdf)
- [Try all constructions](https://ivan-fr.github.io/pandrosion/)
- [Public repository](https://github.com/ivan-fr/pandrosion)
- [Claim-by-claim proof coverage](CLAIM_COVERAGE.md)
- [Revision review](REVIEW_V20.md)

## Changes from V19

The projective AD factorization is corrected to `(1-t)((p+1)t+5p-1)/D4`, agreeing with the existing Lean theorem. The fixed-circle protocol now has explicit finite-chart exclusions and a uniform rational preparation for every integer p ≥ 3, including p = 4. A dyadic change of scale controls the initial center near a target of one. Historical context and references have been expanded; the longer bilateral/Padé discussion is retained in `CONTEXT_SUPPLEMENT.tex`, a source fragment for the supplementary context. The first-page table includes all seven methods. No order-seven construction is claimed.

The paper keeps Pandrosion AK, centered AD, projective AD [2/1], decentered-arc AD, pencil Halley, rational Padé [2/2] and fixed-circle inverse [2/2]. The gallery computes their geometric intersections independently of the scalar formulas, offers step-by-step plane and sphere views, and retains nine earlier demonstrations.

## Rebuild and verify

From this directory, with Python dependencies and Tectonic (or latexmk) installed:

```sh
python3 -m pip install -r requirements.txt
python3 src/revision/verify.py
python3 src/review/check_math.py
python3 src/fixed_circle/verify.py
python3 src/stereo/model.py
python3 src/decentered/verify.py
bash build.sh
```

The supplied figures make the PDF build independent of Python. To regenerate construction figures, run `python3 src/stereo/figures.py figures` and `python3 src/decentered/figures.py figures`.

The new revision check proves the uniform preparation identity symbolically and samples 12,024 real-branch residuals at 90 decimal digits. Strict error decrease on the entire branch remains a **conjecture**. Other scripts check 162 fixed-circle geometries at 250 digits, 75 sphere configurations and three infinity cases, and 108 geometries for each of the four rectangle supports at 160 digits. Finite numerical tests do not establish a general theorem.

## Formal scope

The unchanged Lean snapshot contains 57 local modules. The named audit covers **149 geometric declarations**, with **11 analytical background declarations** audited separately. These are not counts of new V20 theorems. Lean and mathlib are pinned to 4.33.1.

```sh
cd formal
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean BackgroundAudit.lean
```

Only `propext`, `Classical.choice` and `Quot.sound` are permitted in these audits. `SOURCE_HASHES.json` records the bundled sources. The repository-level workflow also builds all 268 source modules and the complete umbrella library.

The uniform preparation is proved by algebraic substitution and checked by SymPy; it has not been added to Lean. Decentered-arc AD has a written global monotone-convergence proof and ten audited algebraic certificates, not a fully formalized analytic convergence theorem. The fixed-circle inverse has local convergence with explicit branch hypotheses; its whole-domain strict error decrease is conjectural. Physical construction counts, numerical conditioning and browser rendering are outside the Lean proof boundary. Preparation and final inversion are excluded from mobile counts.

## Interactive checks

At the repository root:

```sh
npm ci
npm run test:geometry
npx playwright install chromium
python3 -m http.server 8765 --directory docs
# In another terminal:
npm run test:browser
```

The main gallery has no runtime dependencies beyond its local JavaScript modules. It uses ordinary floating-point arithmetic. The archive demonstrations keep their original conventions; some original wrappers load optional UI resources from a CDN. `previews/` retains the earlier fixed-circle HTML files.

`CHECKS_V20.json` records release checks; `SHA256SUMS` covers distributed files. Build and visual-review scratch files are omitted from the repository distribution. Earlier study notes under `src/` retain their original version names and are historical records, not V20 validation claims.
