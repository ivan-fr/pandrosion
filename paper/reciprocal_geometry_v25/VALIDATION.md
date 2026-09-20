# V25 validation — 20 September 2026

Delivered manuscript: **24 pages**, including **15 main-text pages**, **11 figures**, **25 bibliography entries**, and appendices A–F. The first circle construction is on page 2; Theorem 4.3 is on page 6; the cost comparison is on page 10; the conclusion is on page 15; the equivalence discussion is Appendix F, page 23.

## Editorial and mathematical checks

| Check | Result |
|---|---|
| Preservation | The abstract, every theorem/proposition statement, every proof environment, all figure files and the numeric accuracy table are identical to V24. Regenerated vector figures differed only in creation timestamps; this was verified and the original identical assets retained. Lean sources and audit manifests are unchanged. |
| Reading order | The eight-line circle is Section 2, with its rectangle and rail notation stated locally. Coordinates are Section 3, circle analysis Section 4, and costs Section 6. General positioning follows in Section 7; the technical equivalence argument is Appendix F. |
| Numbering and references | Theorem 4.3 and Theorem 5.1 keep their numbers. The switching proposition is now 8.1. The former accuracy Table 3 is Table 2. Guides and cross-references are updated; the PDF has no unresolved references or citations. |
| Initial work | The independently regenerated cost data record initial cache counts `[0,0,0,12,12]`. The caption explicitly distinguishes per-step-only totals (power included) from controller totals including the initial binary cache. No table value or counting convention changed. |
| Bibliography | The rendered reference text contains `Halley’s`, `Euler’s`, `Book III` and `A Padé family`, and none of their reported erroneous lowercase forms. All 25 entries remain present. |
| Conclusion | Two substantive paragraphs and four open questions distinguish lower bounds, conditioning/charts, classical equivalence and formal assembly. Whole-branch contraction is explicitly treated as solved. The prospective electrical experiment remains separate. |
| Complete verifier | `verify.py` passed, including 18 positioning identities, ten integer regression cases, 25 uniform identities, 240 branch/endpoint cases, 72 trajectories at 400 digits, circle/arc incidence campaigns, both controllers, figure geometry and retained V30 provenance. |
| PDF build | Tectonic succeeded, with no overfull boxes or undefined references/citations. Ordinary font notices and underfull-text warnings are not mathematical failures. |
| Visual review | All 24 pages were rendered and inspected in contact sheets. Pages 2, 4, 10, 15 and 24 were inspected at 120 dpi. The isolated fold-figure spill page from the first layout was removed; no content is clipped or overlapping. |

## Formal scope and CI provenance

The scalar circle theorem remains formally proved for every real p>2, with the same 69 audited declarations. The exact [claim map](LEAN_THEOREM_4_3.md) retains the declaration names. The arc's global radical argument, branch-driven switching assembly and Appendix F equivalence discussion retain their written-proof status and stated supporting evidence. Physical work remains an instrumented protocol inventory rather than a Lean cost semantics.

The complete workflow for commit `61b169908b1e48a3c66637d5568a8fbae89aef69` passed, including the complete Lean build, all separate axiom audits, mathematical checks, papers, browser tests and electrical campaigns: [GitHub Actions run 35500502121](https://github.com/ivan-fr/pandrosion/actions/runs/35500502121). This validates the preceding CI download fix and the unchanged formal library. It is not presented as a completed hosted run for a later V25 commit; the latest run is reported in the PR.

The cache fix makes at most three download attempts, reusing files already fetched. Persistent failure still blocks the build; proof checks are not made optional. V25 adds its PDF build/upload to the same workflow, preserving archived builds.

## Reproduction records

- `verification/full_verifier.log`: new complete execution for V25.
- `verification/editorial_checks.json`: preservation, page map, bibliography case and numeric conventions.
- `verification/latex_build.log` and local `build/main.log`: PDF compilation.
- `src/positioning/checks.json`, `src/uniform/checks.json` and `src/branch/protocol_checks.json`: regenerated exact and numerical checks.
- [V24 validation](../reciprocal_geometry_v24/VALIDATION.md): earlier exact comparison evidence and local 69-declaration audit.
- [V23 verification](../reciprocal_geometry_v23/verification/): original targeted Lean build and formal audit records.

No new literature search, solver, Lean result, electrical experiment, historical-priority claim or external reviewer score is introduced by this editorial revision.
