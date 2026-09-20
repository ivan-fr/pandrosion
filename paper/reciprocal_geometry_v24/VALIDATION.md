# V24 validation — 20 September 2026

Delivered manuscript: **23 pages**, with **15 main-text pages**, **11 numbered figures**, **25 bibliography entries** and appendices A–E. The abstract, five Pandrosion drawings, scalar solvers and Lean source modules are retained from V23. The V23 archive has not been edited.

## Executed checks for this revision

| Check | Outcome |
|---|---|
| New positioning identities | `src/positioning/verify.py`: 18 exact symbolic checks passed, including radical recovery, both discriminants, primitive-coefficient identities, residual coefficients through degree six, the fifth-order consistency relation and the conjugacy scaling law. |
| Supplementary integer cases | `S(x^p)` and its derivative have gcd one for p=3,…,12. These ten finite cases supplement the universal written proof; they do not prove its unrestricted integer claim. |
| Retained uniform verifier, rerun in V24 | 25 exact symbolic checks, 240 branch/endpoint cases and 72 scalar trajectories at 400 decimal digits. All passed. The three fifth-order coefficients are independently derived by exact power-series recurrences. |
| Complete manuscript verifier | `verify.py` passed: positioning and uniform checks, archived symbolic identities, 162 circle configurations at 250 digits, 108 arc configurations at 160 digits, both 144-trajectory controllers, original branch endpoint certificates, all geometric figures and retained V30 data/provenance. |
| Branch-driven geometric campaign | 144 trajectories at 180 digits, at most 18 steps; instrumented costs include initial work. No solver or counting convention was changed. |
| Lean audit rerun | `scripts/audit_circle_v23.py`: the same 69 declarations, including definitions, passed. The three formal modules and audit manifest are unchanged. |
| PDF compilation | Tectonic succeeded. No overfull boxes, undefined references or undefined citations in the final log. |
| Visual inspection | All 23 pages rendered and inspected in contact sheets; new Section 2.3 (page 4) and the evidence/Lean-scope page (15) inspected at 120 dpi. References, equations, tables, figures and page transitions remain readable, without clipped content or overlaps. |
| Integration | Latest entry points and citation metadata point to V24. CI includes the new positioning checks and V24 PDF build/upload, retaining the V23 PDF build. |

## Source and proof boundaries

Cabay–Labahn's original CS-89-09 scan was read at the title and printed pages 1–2, including equations (1.4)–(1.6). Buff–Epstein–Koch's author manuscript was read for the classical one-variable Böttcher theorem in its Introduction. [The source ledger](LITERATURE_REVIEW.md) distinguishes this access from sources where only an abstract was obtained.

[POSITIONING.md](POSITIONING.md) supplies the universal nonrationality proof, the primitive-polynomial/irreducibility argument and the application of Böttcher coordinates, including reality and sign. Exact symbolic checks support these written arguments. They do **not** certify analytic existence, exhaustive literature coverage or a historical priority claim, and they are **not included in Lean**.

The scalar claims of Theorem 4.3 remain formalized for every real p>2. The 69-declaration audit admits only `propext`, `Classical.choice` and `Quot.sound`, rejects `sorryAx`, and checks that every declaration in its three modules appears in the manifest. The retained integer branch and residual-gate audits cover 33 and 41 declarations, respectively. The branch-driven switching assembly and global decentered radical theorem remain written proofs with their stated supporting certificates. See [the formal claim map](LEAN_THEOREM_4_3.md).

## Build and CI provenance

The original targeted Lean build and three audit records remain in [V23 verification](../reciprocal_geometry_v23/verification/). The full hosted workflow at commit `36795fcd154cde85c7fd60b5aab7bfac17b5a2a1` completed successfully, including the complete Lean build and separate axiom audits: [GitHub Actions run 35498728117](https://github.com/ivan-fr/pandrosion/actions/runs/35498728117). This is the V23 predecessor, whose Lean sources V24 preserves, not a completed CI result for a later V24 commit. V24's new hosted run is reported separately in the PR.

Local V24 records:

- `verification/full_verifier.log`: complete mathematical and figure campaign.
- `verification/lean_v23_audit.log`: new execution of the unchanged 69-declaration audit.
- `verification/latex_build.log` and local `build/main.log`: PDF build.
- `src/positioning/checks.json`: the 18 exact checks and ten finite regression cases.
- `src/uniform/checks.json`: retained symbolic and finite real-parameter campaign, rerun.
- `src/branch/protocol_checks.json`: branch controller, exceptions and cost data.

No new electrical simulation, hardware benchmark, optimality theorem, universal classification, publication or external reviewer score is asserted.
