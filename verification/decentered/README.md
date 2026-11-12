# Decentered arc and classical rectangle checks

Run from the repository root:

```sh
python3 -m pip install -r requirements.txt
python3 verification/decentered/verify.py
```

The verifier is retained unchanged from the earlier geometry supplement. It constructs AK, centered AD, projective AD and decentered AD with intersections, tests 108 configurations per method at 160 decimal digits, checks symbolic decentered identities and four local series, and writes a four-method common-start benchmark at 280 digits.

`verification.json` and `benchmark.json` are regenerable records. Global convergence is a written proof in the manuscript; finite checks do not replace it. The ten Lean algebraic certificates are in `LeanMath/Papers/RectangleDecenteredArc.lean`. See [the evidence map](../../EVIDENCE.md) for the boundary with the missing V27 supplement.
