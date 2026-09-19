# Geometry V21 — start here

**[Read the paper](Reciprocal_Root_Geometry_v21.pdf)** · [Try the gallery](https://ivan-fr.github.io/pandrosion/) · [Source](main.tex) · [Revision notes](REVISION_NOTES.md)

*Geometric Root Calculators: Fixed Circles, Moving Supports, and Analog Realization* rewrites V20 around the realization problem: what geometric device performs each operation, what it costs, and how the product schedule informs an analog design.

The two central constructions are the prepared-circle inverse correction (local order five, `2p+2` mobile joins) and decentered AD (global monotone convergence, order five, one arc and one join for its support). A [geometric safeguard](../../research/fixed_circle_safeguard/README.md) now globalizes the circle algorithm with AD fallback: for the cubic, at most 28 joins per accepted step, after a 12-join initial cache. These counts include control and differ from the original eight-line local protocol. All five Pandrosion drawings are retained: linear MA, AK, centered AD, projective order-four AD and decentered order-five AD. The two rational pencil baselines also remain. Binary geometric multiplication connects them to the **order-three** centered analog prototype. There is no fifth-order electrical validation claim.

## Reproduce

From the repository root, with Python 3.12 and Tectonic (or `latexmk`):

```sh
python3 -m pip install -r paper/reciprocal_geometry_v20/requirements.txt
python3 paper/reciprocal_geometry_v21/verify.py
bash paper/reciprocal_geometry_v21/build.sh
```

The checker runs archived symbolic and high-precision geometry checks, checks the centered arithmetic, verifies retained V30 result records and regenerates the construction figures. It does **not** rerun SPICE or compile Lean. The PDF can be built independently using the supplied vector figures. CI runs geometry, Lean, SPICE and PDF builds in separate jobs.

The independently computed figures are editable in [draw_figures.py](draw_figures.py) and [draw_pandrosion.py](draw_pandrosion.py); the new control figure is in [draw.py](../../research/fixed_circle_safeguard/draw.py). The binary-product and electrical figures are reused, with attribution, from the [V30 companion](../pandrosion_analog_v30/README.md); their original drawing scripts are retained there.

## Claim-to-source map

All paths below are relative to the repository; module links open the active library, not a historical copy.

| V21 result | Source and actual scope |
|---|---|
| Rail operations and rational projector | [RectanglePencils](../../LeanMath/Papers/RectanglePencils.lean); algebraic incidences and readouts. |
| Projective AD | [RectangleProjective](../../LeanMath/Papers/RectangleProjective.lean): `geometric_readout`, `global_convergence`, `relative_order_four`. |
| Fixed circle | [RectangleFixedCircle](../../LeanMath/Papers/RectangleFixedCircle.lean): `general_geometry_certificate`, `fourth_geometry_certificate`, `final_readout`, `logarithmic_order_five`. The last theorem is a parameterized logarithmic limit. The paper supplies the inverse-function/branch assembly. |
| Uniform rational chart, including degree four | [V20 revision checker](../reciprocal_geometry_v20/src/revision/verify.py): exact symbolic identity. This newer uniform chart is not claimed as a Lean theorem. |
| Decentered arc | [RectangleDecenteredArc](../../LeanMath/Papers/RectangleDecenteredArc.lean): `square_certificate`, `sign_decomposition`, `derivative_numerator`. The complete radical convergence proof is written in V21. |
| Guarded circle + AD | [RectangleCircleSafeguard](../../LeanMath/Papers/RectangleCircleSafeguard.lean): `gate_iff_log`, `rulerMul_correct`, `rulerPower_correct`, `ruler_circle_AD_global`; 41-theorem [audit](../../scripts/audit_circle_safeguard.py). Local transfer theorems retain explicit analytic premises. |
| Binary geometric product | [RectangleFastPower](../../LeanMath/Papers/RectangleFastPower.lean): `rectangle_mul_readout`, `geometricPower_eq`, `geometric_readout`; separate [audit](../../scripts/audit_fast_power.py). |
| Centered analog arithmetic | [AnalogFastAD](../../LeanMath/Papers/AnalogFastAD.lean): six identities; separate [audit](../../scripts/audit_analog_fast_ad.py). No electrical-performance theorem. |
| Analog errors, times and campaign sizes | [V30 checker](../pandrosion_analog_v30/check_results.py) checks retained datasets; [V30 guide](../pandrosion_analog_v30/README.md) gives circuit reproduction. |

The fuller [V20 coverage table](../reciprocal_geometry_v20/CLAIM_COVERAGE.md) documents the archived proof boundary. The current source library also contains experimental developments outside the scope of this paper.

To build the formal development after installing the pinned Lean toolchain:

```sh
lake exe cache get
python3 scripts/build_lean.py
python3 scripts/audit_lean.py
python3 scripts/audit_fast_power.py
python3 scripts/audit_circle_safeguard.py
python3 scripts/audit_analog_fast_ad.py
```

`propext`, `Classical.choice` and `Quot.sound` are the allowed standard axioms in these audits. Formal algebra, analytic arguments, geometric protocol counts and circuit evidence have separate roles; an audit success is not a hardware validation.

## Cite and navigate

Use [CITATION.cff](CITATION.cff) for this paper. No DOI is assigned. The repository is [ivan-fr/pandrosion](https://github.com/ivan-fr/pandrosion).

- [Geometry V20 archive](../reciprocal_geometry_v20/README.md): detailed antecedent, historical context and original checks.
- [Analog V30 companion](../pandrosion_analog_v30/README.md): circuit topology, netlists, calibration and precision–time evidence.
- [Gallery initialization](../../docs/INITIALIZATION.md) and [fast geometric power](../../docs/FAST_POWER_EXPERIMENT.md): interface, normalization and numerical conditioning.
