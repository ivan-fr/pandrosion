# Geometric factorization research

Start with the [report and explicit answers to Q1–Q8](report.md), then the
[general derivation](derivation.md) and [AD5 construction protocols](ad5_factorizations.md).
The [candidate ledger](candidates.json) distinguishes completed geometry,
loose constructibility bounds, restricted domains and unresolved optimality.

From the repository root:

```sh
python -m pip install -r paper/reciprocal_geometry_v20/requirements.txt
python research/geometric_factorization/symbolic_search.py
python research/geometric_factorization/benchmark.py
node research/geometric_factorization/geometry_benchmark.mjs
node scripts/test_dual_transport.mjs
lake build LeanMath.Papers.RectangleDualTransport LeanMath.Papers.RectangleFactorizationJets
python scripts/audit_dual_transport.py
```

Outputs are the three `*_results.json` files and `figures/error_maps.svg`.
The scalar benchmark intentionally records counterexamples; zero failures is
not its success criterion. The exact symbolic identities and implemented
geometry regressions are assertions. The browser tests cover all four fixed-AK
variants, automatic preparation, one-iteration control and native degree limits.

The V20 paper and its frozen audit are not changed. Higher-order candidates
are research experiments, not gallery implementations or claims of novelty.

## Completed interactive protocols

The deployed gallery receives these modes when the PR is merged:

- [Fixed AK + Newton](https://ivan-fr.github.io/pandrosion/?method=AKdual)
- [Fixed AK + Halley](https://ivan-fr.github.io/pandrosion/?method=ADdual)
- [Fixed AK + projective [2/1]](https://ivan-fr.github.io/pandrosion/?method=projectiveDual)
- [Fixed AK + decentered-arc AD5](https://ivan-fr.github.io/pandrosion/?method=arcDual)

Use the same query strings on the local gallery server before deployment.
Each click performs one iteration; setup and scaling are automatic.
