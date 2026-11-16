# Pandrosion

**Geometric Root Calculators: Radical supports of orders five and nine and real-degree enclosures in the Pandrosion rectangle**

Ivan Besevic · V29 · 13 November 2026 · Research preprint

Companion: **Complex Geometric Root Calculators** · C5 · 13 November 2026

[Read the paper](paper/Geometric_Root_Calculators_v29.pdf) · [Read the complex companion](paper/Complex_Geometric_Root_Calculators_C5.pdf) · [Evidence and source availability](EVIDENCE.md) · [Citation](CITATION.cff)

This repository accompanies the paper on positive-root constructions using the Pandrosion rectangle: classical rectangle supports, the fifth-order decentered arc, the nested-radical and three-mean constructions of order nine, and real-degree subdivision enclosures. The complex companion C5 extends these iterations to a complex radicand and a real degree.

## Contents

| Path | Purpose |
|---|---|
| [paper/Geometric_Root_Calculators_v29.pdf](paper/Geometric_Root_Calculators_v29.pdf) | Current manuscript, V29 (revision of V28). Prepared with the assistance of ChatGPT (OpenAI) and Claude (Anthropic), as stated on its first page. |
| [paper/v29](paper/v29) | LaTeX sources of V29, the figure generator `genfigs.py` and the symbolic verifier `verify_v29.py`. |
| [paper/Complex_Geometric_Root_Calculators_C5.pdf](paper/Complex_Geometric_Root_Calculators_C5.pdf) | Complex companion, version C5. Prepared with the same AI assistance, as stated on its first page. |
| [paper/c5](paper/c5) | LaTeX source and figures of C5, interval-arithmetic certificates (`certify_*.py`), numerical verifiers (`verify_*.py`), construction protocols and figure scripts; see `paper/c5/README.txt`. |
| [paper/Geometric_Root_Calculators_Simultaneous_Rectangle_G8_r9.pdf](paper/Geometric_Root_Calculators_Simultaneous_Rectangle_G8_r9.pdf) | *The simultaneous rectangle*, version G8, revision 9: all the roots of a polynomial by the rectangle alone, with one certificate and a step for clusters. Describes the Rust crate [pandroots](https://crates.io/crates/pandroots) 0.12.0. Also on Zenodo, DOI [10.5281/zenodo.24257672](https://doi.org/10.5281/zenodo.24257672). Prepared with AI assistance, as stated on its first page. |
| [paper/g8](paper/g8) | Sources of G8 revision 9 as archived on Zenodo: LaTeX source and figures (`paper/`), the validation scripts, logs and results (`validation/`, with the crate source and its Lean files under `validation/pandroots`), and the results of revision 8 (`r8_results/`); see `paper/g8/README.txt`. The crate under `validation/pandroots` is now version 0.13.0, later than the note and than the Zenodo archive (which describe 0.12.0): same method at a lower cost, measured on 20 000 polynomials in `validation/bench20k` and on 50 000 small ones in `validation/bench50k`. These Lean files are checked with Lean 4.35.0 and Mathlib v4.35.0 and are not part of the `lake build` of this repository. |
| [paper/Geometric_Root_Calculators_v28.pdf](paper/Geometric_Root_Calculators_v28.pdf) | Previous version, V28, with its sources in [paper/v28](paper/v28). |
| [paper/Geometric_Root_Calculators_v27.pdf](paper/Geometric_Root_Calculators_v27.pdf) | Previous version, author-supplied V27-NR manuscript (PDF only). |
| [LeanMath/Papers](LeanMath/Papers) | Classical rectangle proofs, decentered-arc certificates with global convergence and local order five, nested-radical modules with local order nine, the contact lemma, degree and efficiency results, the three-mean support (V29), the complex half-plane, sector and slit-plane modules (C5), subdivision results, and their required imports. |
| [verification/decentered](verification/decentered) | Independent symbolic and high-precision line/circle checks for AK, AD, projective AD and the decentered arc. |
| [validation](validation) | Axiom manifests for the decentered certificates, the subdivision theorems, the nested-radical modules, the order, degree and efficiency modules, and the complex modules of C5. |

**Source availability:** the nested-radical Lean modules are now included, together with modules for the decentered arc's global convergence, the local orders five and nine, and the degree and efficiency statements. The V28, V29 and C5 manuscript sources are included; the V27 sources and the full V27 numerical verification package are still absent. The proofs and checks cover only the scopes listed in [EVIDENCE.md](EVIDENCE.md).

## Reproduce the available checks

```sh
python3 -m pip install -r requirements.txt
python3 verification/decentered/verify.py
python3 paper/v28/verify_v28.py
python3 paper/v29/verify_v29.py
(cd paper/c5 && python3 verify_complex.py && python3 verify_threemean.py)
```

This runs symbolic identities, local series checks and 432 geometric evaluations (108 for each of four constructions) at 160 decimal digits. It regenerates `verification.json` and a four-method benchmark at 280 digits. These are finite numerical checks, not a reproduction of the paper's six-method comparison. `verify_v28.py` and `verify_v29.py` recompute the constants, identities and tables of each version with exact rational arithmetic and high-precision evaluation; the C5 verifiers check the complex statements numerically and recompute the polynomial certificates of the slit-plane theorem. The C5 interval certificates `certify_*.py` additionally need `python-flint`.

To rebuild a manuscript, run `pdflatex main.tex` three times in `paper/v29`, `paper/c5` or `paper/v28`. The figures are in `figs.tex`, regenerated by `python3 genfigs.py` from exact coordinates.

For formal checking, install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
lake build
python3 scripts/audit_lean.py
```

Lean and mathlib are pinned by `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`. The audit checks 444 declarations (ten decentered algebraic certificates, seven subdivision theorems, 104 nested-radical theorems, 125 theorems on orders, degrees and efficiency, and 198 theorems of the complex companion C5), allowing only `propext`, `Classical.choice` and `Quot.sound`. CI builds the Lean library and runs these audits separately from the numerical verifier.

## Repository scope

Only the current manuscript and available mathematical support are maintained here. Superseded manuscripts, circuit/SPICE studies, the old interactive gallery and unrelated solver experiments remain recoverable in Git history before this cleanup. No history was rewritten.

[MIT License](LICENSE) · Copyright © 2026 Ivan Besevic.
