# Formalization scope

`BilateralCore.lean` builds with Lean 4.33.1 and only `Std` (no mathlib download). It proves the generic field algebra of the recursive log identity, a division-free log balance in a commutative ring, and the Cayley inverse in characteristic zero. `#print axioms` reports only propext, Classical.choice and Quot.sound for all three. Replay: `lean lean/BilateralCore.lean`; log `certificates/lean-core.txt`.

This is the algebraic core **after** taking logarithms. It does not formalize positivity, Real.log/Real.rpow/Real.sqrt, the cubic Taylor expansion, spectral functional calculus, or the zeta bridge. Those remain ordinary proofs in the theorem notes. Existing workspace Lean developments predate this audit and were not substituted for these checks.
