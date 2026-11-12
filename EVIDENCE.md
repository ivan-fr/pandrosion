# Evidence and source availability

The reference manuscript is [V27-NR](paper/Geometric_Root_Calculators_v27.pdf), supplied by the author for this cleanup. Files retained from the repository predate that manuscript; keeping them does not establish every V27 claim.

| V27 topic | Available evidence | Scope and limits |
|---|---|---|
| Rectangle coordinates, reports, AK and centered AD | `RectangleGeometry`, `RectangleReports`, `RectangleRaw`, `RectangleNewton`, `RectangleDynamics` and their imports | Existing geometry and scalar developments; build with `lake build`. |
| Projective AD | `RectangleProjective`, `RectangleProjectiveVerification` and their imports | Existing projective construction and scalar results. |
| Decentered arc (Section 3) | `RectangleDecenteredArc`; `verification/decentered/verify.py` | Ten algebraic Lean certificates; symbolic identities and finite line/circle checks. The full global convergence argument is a written proof in the paper. |
| Nested radicals (Section 4) | Manuscript only | `NestedRadicalCubic`, `NestedRadicalRealCertificate`, `NestedRadicalReal`, `NestedRadicalAllDegrees` and the reported 104-theorem audits were not present. No retained Lean file is represented as proving these results. |
| Nested-radical work inventory and six-method comparison | Manuscript only | V27 macro checks, line/circle checks, independent comparison and validation records were not present. The retained four-method benchmark has a different scope. |
| Subdivision (Section 6) | `GeometricSubdivision`; `validation/geometric_subdivision/Audit.lean` | Retained real-degree bracket, interval invariant, rational readout and width results. The seven-theorem audit can be rerun. V27's separate geometric/numerical verifier was not present. |
| Manuscript and figures | Author-supplied PDF | V27 LaTeX, bibliography, figure generators and `build.sh` were not present; this repository cannot rebuild the PDF. |

## Retained dependency boundary

`LeanMath.lean` imports the projective verification, decentered certificates and subdivision modules. Other retained Lean files are their transitive imports, including common scalar convergence results. The decentered certificate file now imports mathlib directly instead of the unrelated fixed-circle development; its declarations and proofs are unchanged.

The source supplement required to complete V27 reproduction must include the four nested-radical modules and their imports, pinned build environment, audit scripts and records, manuscript sources, and the V27 symbolic/geometric/comparison verifiers. None has been reconstructed or claimed as verified by this cleanup.

## Numerical checks

Run `python3 verification/decentered/verify.py` after installing `requirements.txt`. The unchanged verifier uses intersections and a constructed arc radius, compares its readout with independent scalar formulas, and records the exact scope in its JSON outputs. Its example uses the reciprocal state and four methods; it is not the V27 nested-radical benchmark.

## Formal checks

`lake build` compiles every retained module through the root imports. `python3 scripts/audit_lean.py` additionally prints transitive axioms for the ten decentered certificates and seven subdivision theorems, rejecting admitted proofs or nonstandard axioms. A successful audit of this subset makes no assertion about the absent nested-radical sources.

## Merge configuration

The existing `main` protection requires legacy paper, analog and gallery job names. This cleanup keeps the Lean and mathematics status names, but removes jobs for deleted studies. Before merging, the repository owner must update the required-check list to the two retained jobs: `Complete Lean build and separate axiom audits` and `Symbolic and high precision geometry`. No branch protection is disabled or bypassed by this change.
