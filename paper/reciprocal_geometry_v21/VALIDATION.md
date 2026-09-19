# V21 validation — 19 September 2026

The paper contains 18 pages and nine numbered figures. Figures 2–6 retain all five requested Pandrosion constructions: linear MA, AK, centered AD, projective AD of order four and decentered AD of order five. Figure 1 is the fixed-circle device; figure 7 shows the new geometric safeguard; figures 8–9 connect geometric binary powering to the behavioral circuit.

Executed locally:

- The V21 verification entry point's archived symbolic, high-precision and centered-arithmetic checks passed. The circle campaign contains 162 independent geometries at 250 digits; the decentered campaign contains 108 at 160 digits, with checks of the other three accelerated supports as well.
- The retained V30 result checker passed, including campaign counts, error/time records and diagram provenance. No new SPICE campaign was needed: the electrical model and its evidence were not changed.
- Both V21 drawing scripts passed their readout checks. The four regenerated MA/AK/AD/projective drawings compare independently computed intersections to their scalar maps at 70 decimal digits.
- The frozen geometry axiom audit passed for 149 declarations plus 11 analytical background declarations; the separate binary-power audit passed for 22 and the centered analog audit for six. These audits check the named declarations and their transitive axioms, not every analytic statement in V21. The safeguard addition subsequently introduces one separate Lean module and audit (see below).
- The Tectonic PDF build passed without undefined references or overfull boxes. Rendered pages were inspected, including the complete decentered support, the enlarged projective readout, the electrical schematic and the final bibliography. A text-extraction check confirmed all five requested figures and the original 16-page output.
- Relative README links and whitespace checks passed.

A failed first local audit attempt was due to an absent mathlib build cache. Restoring the pinned cached dependencies allowed all three audit commands to pass; no proof changes or additional axioms were introduced.

The broader repository CI is separate and rebuilds Lean, all papers and the simulation/browser campaigns. Its outcome is reported by GitHub Actions, not presumed by this validation record.

## Safeguarded-circle addition

- `lake build LeanMath.Papers.RectangleCircleSafeguard` passed. Its 41 declarations passed a separate axiom audit with only the same three standard axioms; there are no `sorry` proofs or additional axioms.
- The geometric verifier passed 144 trajectories at 180 decimal digits, all reaching absolute log residual below `1e-45` within 18 steps. The maximum relative disagreement with independently evaluated scalar steps was `4.3328584e-167`.
- The test suite also passed full trial rejections, exact unit-product and fixed-point cases, a case with two positive inverse roots, absent real crossings and the affine singularities at `(p,t)=(3,7.75),(5,16)`. Instrumented joins, parallels and arcs match the stated upper bounds.
- The new product/control figure checks its incidences independently. The PDF now has 18 pages and nine figures, retaining all five original Pandrosion drawings. Changed pages were rendered and inspected; no overfull boxes or undefined references were found.
- CI includes the new geometry campaign, figure generator and separate axiom audit. Browser and circuit implementations are unchanged.
