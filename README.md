# Pandrosion

**Geometric Root Calculators: A ninth-order cubic construction and real-degree root solvers**

Ivan Besevic · V27-NR · 18 October 2026 · Research preprint

[Read the paper](paper/Geometric_Root_Calculators_v27.pdf) · [Evidence and source availability](EVIDENCE.md) · [Citation](CITATION.cff)

This repository accompanies the paper on positive-root constructions using the Pandrosion rectangle: classical rectangle supports, the fifth-order decentered arc, the nested-radical construction of exact cubic order nine, and real-degree subdivision enclosures.

## Contents

| Path | Purpose |
|---|---|
| [paper/Geometric_Root_Calculators_v27.pdf](paper/Geometric_Root_Calculators_v27.pdf) | Author-supplied V27-NR manuscript. |
| [LeanMath/Papers](LeanMath/Papers) | Available classical rectangle proofs, decentered algebraic certificates, subdivision results, and their required imports. |
| [verification/decentered](verification/decentered) | Independent symbolic and high-precision line/circle checks for AK, AD, projective AD and the decentered arc. |
| [validation](validation) | Axiom manifests for the decentered certificates and seven subdivision theorems. |

**Source availability:** the V27 nested-radical Lean modules, manuscript sources and full V27 verification package were absent from the repository at cleanup. The PDF describes results whose complete reproduction requires that missing supplement. The retained proofs and checks cover only the scopes listed in [EVIDENCE.md](EVIDENCE.md).

## Reproduce the available checks

```sh
python3 -m pip install -r requirements.txt
python3 verification/decentered/verify.py
```

This runs symbolic identities, local series checks and 432 geometric evaluations (108 for each of four constructions) at 160 decimal digits. It regenerates `verification.json` and a four-method benchmark at 280 digits. These are finite numerical checks, not a reproduction of the paper's six-method V27 comparison.

For formal checking, install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
lake build
python3 scripts/audit_lean.py
```

Lean and mathlib are pinned by `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`. The audit checks ten decentered algebraic certificates and seven subdivision theorems, allowing only `propext`, `Classical.choice` and `Quot.sound`. CI builds the retained Lean library and runs these audits separately from the numerical verifier.

## Repository scope

Only the current manuscript and available mathematical support are maintained here. Superseded manuscripts, circuit/SPICE studies, the old interactive gallery and unrelated solver experiments remain recoverable in Git history before this cleanup. No history was rewritten.

[MIT License](LICENSE) · Copyright © 2026 Ivan Besevic.
