# Mathematical evidence and source provenance

The Rust solver in this release comes from the development sources of version 0.5.0 (`pandroots-0.5.0.zip`).
Its source hashes are recorded in `provenance.json`.

The files under `lean/` are those of G8, revision 7 (38 theorems: the simultaneous rectangle, Smith
discs, the fixed-point certificate down to the inequalities the program tests, and the real-disc test),
with the build and axiom-audit log produced on 14 November 2026 in the author's Lean 4 / Mathlib
container. They provide evidence for the mathematical statements, not a formal verification of
version 0.5.0. They are not compiled by Cargo.

The formal certificate assumes valid numerical upper and lower bounds. The Rust
floating-point bounds, underflow handling, guards, fixed-point ball evaluation, multiprecision implementation,
and fallback count of unresolved clusters are not formally verified by these files.
There is no theorem of global convergence of the solver.
