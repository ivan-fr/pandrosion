# V23 validation — 20 September 2026

Delivered manuscript: **22 pages**, with **14 main-text pages**, **11 numbered figures**, **23 bibliography entries** and appendices A–E. The five Pandrosion drawings are retained. V22 has not been edited.

## Executed checks

| Check | Outcome |
|---|---|
| Uniform proof checks and formula comparisons | `src/uniform/verify.py`: 25 exact symbolic checks, 240 branch/endpoint cases and 72 scalar trajectories at 400 decimal digits. All passed. |
| Independent order coefficients | Exact power-series recurrences derive the circle inverse, positive radical and rational Padé corrections through degree five. Their contact through degree four and distinct logarithmic fifth-order coefficients all passed. |
| Complete manuscript verifier | `verify.py` passed: new uniform checks, archived symbolic identities, 162 circle configurations at 250 digits, 108 arc configurations at 160 digits, both 144-trajectory controllers, original branch endpoint certificates, all geometric figures and retained V30 data/provenance. |
| Branch-driven geometric campaign | 144 trajectories at 180 digits; at most 18 steps to absolute log residual below 1e-45. Maximum relative disagreement with independent scalar updates: 4.3328584e-167. |
| Complete work totals | After displaying initial-cache costs directly in Table 3, `src/branch/protocol.py` was rerun. Instrumented geometric counters agree with the displayed branch-controller totals, including the initial 12 joins. The full-gate totals use its retained cost inventory. |
| New Lean Theorem 4.3 | Three modules compiled successfully (`lake build LeanMath.Papers.RectangleFixedCircleTheorem43`, 3196 build jobs including dependencies). `scripts/audit_circle_v23.py`: all 69 declarations passed. |
| Retained integer-degree Lean branch audit | `scripts/audit_branch.py`: 33 declarations passed. |
| Retained Lean residual-gate audit | `scripts/audit_circle_safeguard.py`: 41 declarations passed. |
| PDF compilation | Tectonic build succeeded. No overfull boxes, undefined references or undefined citations in the final LaTeX log. Ordinary font notices and a few underfull-text warnings are not mathematical failures. |
| Visual inspection | All 22 pages rendered and reviewed in contact sheets. Full-page checks covered the title, literature comparison, local/branch/arc proofs, cost tables, controller, analog appendix and references. The final Lean coverage and evidence pages (9 and 14) were re-rendered at 125 dpi and inspected after line-breaking corrections. No clipped content, overlaps or isolated spill pages remain. |
| Integration | A dedicated branch from `origin/main` contains the V23 paper, three Lean modules, complete declaration audit, default import, CI steps and updated entry points. The original worktree and its unrelated site changes were preserved. |

## Formal scope

The scalar claims of Theorem 4.3 are now formalized for every real p>2: uniform contraction, alternation, the unique continuous inverse, explicit residual bounds, invariant-band convergence, the multiplicative iteration toward X^(−1/p), and exact order five in the input-error variable. See [the declaration-level claim map](LEAN_THEOREM_4_3.md).

The new audit includes all 69 declarations in the three new source files, including noncomputable definitions. It admits only `propext`, `Classical.choice` and `Quot.sound`, and rejects `sorryAx`. The retained branch and residual-gate audits cover 33 and 41 declarations respectively. The branch-driven switching assembly and global decentered radical theorem remain written proofs with their previously stated supporting certificates.

The new target and all its dependencies were built locally. The default library import and GitHub Actions include it; the audit, real-parameter campaign, branch-controller campaign and V23 PDF build are included in CI. The optional whole-library rebuild was stopped while recompiling unrelated historical V14 polynomial certificates; no completed local full-library build is claimed. The complete build runs in the PR workflow. A local result is not presented as a completed hosted CI run.

## Reproduction records

- `verification/lean_v23_build.log`: successful target build and pinned toolchain.
- `verification/lean_v23_audit.log`: all 69 transitive axiom records.
- `verification/full_verifier.log`: full mathematical and figure campaign.
- `verification/accuracy_work.log`: final instrumented rerun after work-table clarification.
- `verification/latex_build.log` and `build/main.log`: final PDF build.
- `src/uniform/checks.json`: new symbolic results and finite real-parameter campaigns.
- `src/branch/checks.json`: retained degree-specific proof checks.
- `src/branch/protocol_checks.json`: geometric controller, exceptions and cost data.
- `LITERATURE_REVIEW.md`: primary-source access record and limits of the bibliographic comparison.

No new electrical simulation was run. No hardware performance, global optimality, exhaustive priority result, hosted CI result, publication or external reviewer score is asserted.
