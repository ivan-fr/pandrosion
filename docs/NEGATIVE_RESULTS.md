# Preserved failures and limitations

- **FALSE / SUPERSEDED archived candidate:** naive 11-point exploration missed a lower basin. Corrected report gives energy about 0.007276897227420313 at pressure 1/2500 and an assembled numerical value 0.6732966045368319, below the nine-point candidate. No new 11-point campaign was started. The archived optimization was not independently rerun.
- **NUMERICALLY OBSERVED:** scalar recursive/dual-center implementations lose to matched-order Padé on retained workloads; Shanks/Wynn history acceleration is particularly slow. Old unequal preprocessing comparisons do not establish a universal speed advantage.
- **PROVED:** complete near-balanced Cayley compression coincides with diagonal Padé. Smaller indices in the squared coordinate do not mean a new lower-degree rational function.
- **PROVED:** mapping a fixed spectral interval into Cayley coordinates cannot change whether it crosses 2. Any benefit needs a changed enclosure/evaluation strategy.
- **PROVED counterexample to unqualified contraction:** raw Perron iteration can cycle (B=[[0,2],[1,0]]). Collatz enclosures remain valid; strict contraction is not automatic.
- **UNVERIFIED reported counterexamples:** trmdy campaign says arbitrary-PSD multi-pair composition and additive local pair pricing fail. Full witnesses are absent from the located public tree. Preserve this restriction rather than invent witnesses.
- **NUMERICALLY OBSERVED, non-certified archive:** all old box pruning percentages based on sampled/padded kernel derivative envelopes. Point eigenvalues are not truth labels for whole boxes.
- **REPRODUCED implementation limitation:** wide balls across sinc zero can produce indeterminate results from upstream derivative formulas outside the small-series regime. New constructor uses native Arb entire sinc with the exact same kernel expression as a value-only fallback; it never fills the gap with doubles.
- **REPRODUCED negative control:** AMTOPA's LDL probe accepts thin positive-definite entries and rejects the same lower bounds with +infinite upper bounds. This supports the reported verifier regression, but is not a replay of the entire failing certificate.
- **Integration gap:** lambda_max<2 alone cannot replace the current pair-energy acceptance predicate. Contractor classifications cannot yet reduce the certified density verifier's node count.
- **Environment failure:** editable installs ceased to appear on this Python runtime's import path; ordinary local wheel installs restored imports. Commands in the reproduction guide use ordinary installs.

## Small-block continuation: new retained negative results

- **FALSE / SUPERSEDED numerical improvement:** initial four-point p=1/1000 search returned an exact-defect minimum candidate 0.0064236497254 versus 0.0061295387928 for the old envelope. Cross-feeding the old winner into the exact objective removed the entire 0.0002941109 apparent gain. Both objectives are provably identical in the retained low-basin neighborhoods. Initial search JSON is preserved.
- **PROVED / COMPUTER-CERTIFIED method ceiling:** for the fixed trmdy kernel, direct n-point defect + arbitrary nonnegative position-pressure inequalities followed by n-point pinching cannot exceed 0.672771 (n=3) or 0.673140 (n=4). This includes exact spectral evaluation, so further numerical tuning inside this family cannot beat the nine-point candidate. It does not exclude larger-block composition or different kernels and is not a ceiling on the true zeta zero proportion.
- **No additive bonus rule:** the positive local gap D−Phi_n(E) cannot simply be added across overlapping small blocks on top of the existing certificate. Such an addition has not been proved; no assembled percentage was produced.
