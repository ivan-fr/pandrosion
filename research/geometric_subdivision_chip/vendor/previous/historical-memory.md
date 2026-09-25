# Faster memory acquisition for centered AD

The memory redesign is tested with finite-current drivers, charge injection on both edges, electrical-reference calibration, recomputed sampling noise and the original fast-power/AD arithmetic. These are behavioral engineering hypotheses. See [the protocol](PROTOCOL.md) and [model schematic](memory_model.png).

**Finding: a faster candidate, but the 1-ppm accuracy target is not robust across all nominal tests.** The 33 nF feedback combination passes the separate 64-case final validation at 5.035 ms, versus 9.585 ms for the 100 nF control. However, an additional nominal signed-error/noise corner reaches **1.287 ppm**. The 1.90× ratio therefore describes that final validation set; it is not an established all-nominal-case speedup at 1 ppm. No further tuning is performed to erase this failure.

## Final independent validation at 1 ppm

First-stage precision misses led to one explicit policy refinement. The first 48 cases were then used as development data: select the quickest fixed readout with worst error ≤0.7 ppm, retaining each arm’s hardware and clock. Freeze that choice before testing **32 new input pairs with two new seed/corner assignments each**. No further selection uses this final set.

| Implementation | Readout (ms) | Iterations / average | Passes ≤1 ppm | Worst error (ppm) |
|:--|--:|:--|:--|--:|
| 33 nF, V30 correction | 5.035 | 12 / 4 | 62/64 | 1.224 |
| 33 nF, geometric feedback | 5.035 | 12 / 8 | 64/64 | 0.9936 |
| 100 nF, finite drivers | 9.585 | 8 / 4 | 64/64 | 0.7881 |
| Archived V30 | 9.585 | 8 / 4 | 64/64 | 0.8789 |

**33 nF, V30 correction has not established an all-case 1-ppm latency advantage** in the final validation. A selected latency is not a validated target when any case misses it.

**33 nF, geometric feedback: 1.90× shorter readout time than the finite-driver 100 nF control**, with both passing all 64 final cases. This is the ratio of the frozen policies, not a proof of either architecture’s optimal possible latency. The remaining margin on the worst final case is only 0.006432 ppm. The comparison includes different fixed averaging policies, so it does not isolate an intrinsic advantage of the feedback geometry.

The archived V30 uses the older, ideal transfer-buffer model. The 100 nF control includes the same new current limits and two-edge charge law as the 33 nF design, making it the primary comparison for the memory change. The additional finite transfer buffer has no separate device noise/offset model beyond the stated shared budgets. A manufacturer macromodel or PDK could change the result.

## First-stage misses are retained

| Design | Target (ppm) | Time (ms) | Passes | Worst ppm |
|:--|--:|--:|:--|--:|
| 33 nF, V30 correction | 1 | 1.255 | 45/48 | 1.5568 |
| 33 nF, geometric feedback | 1 | 1.255 | 42/48 | 2.5749 |
| Archived V30 | 1 | 2.385 | 47/48 | 1.9275 |
| 100 nF, finite drivers | 1 | 3.585 | 48/48 | 0.9856 |
| 10 nF / 23 Ω, 10 ppm | 10 | 0.435 | 48/48 | 9.9672 |

The independently selected 10-ppm option uses a separate hardware profile and passes 48/48 first-validation cases at 0.435 ms. Its worst error is 9.9672 ppm: the remaining margin to 10 ppm is small. This is not a 1-ppm result, a universal guarantee, or the final refined 33 nF design.

## Physical tradeoffs actually included

| Profile | Memory C (nF) | Ron (Ω) | Nominal Ron C (µs) | Sampling noise at 85 °C (µV RMS) | Nominal Q/C per edge (µV) |
|:--|--:|--:|--:|--:|--:|
| control100 | 100 | 230 | 23 | 0.314 | 5 |
| small33 | 33 | 230 | 7.59 | 0.547 | 15.15 |
| small10 | 10 | 230 | 2.3 | 0.994 | 49.99 |
| small1 | 1 | 230 | 0.23 | 3.14 | 499 |
| lowR100 | 100 | 23 | 2.3 | 0.314 | 49.99 |
| lowR10 | 10 | 23 | 0.23 | 0.993 | 499 |

The chosen 33 nF memory reduces the nominal switch/memory RC from 23 to 7.59 µs. Its sampling noise grows by about √(100/33); charge and leakage voltage errors also increase. The circuit therefore retains recalibration and averaging. Both source/sink driver currents are limited to 2 mA. At a 0.7 V step, charging a 100 nF memory alone requires at least 35 µs at that current; reducing Ron cannot remove this bound.

The 23-ohm profiles deliberately pay tenfold nominal injected charge and increased parasitic capacitance. These numerical profiles are assumptions rather than ADG1211/ADG1411 device models. [Manufacturer sample/hold guidance](https://www.analog.com/en/resources/app-notes/an-1515.html) describes the charge-injection and droop mechanisms motivating this sensitivity study.

## Component sensitivity

These diagnostic trajectories use each arm’s **refined 33 nF policy**, fixed before final validation. Changed component assumptions are electrically recalibrated; they do not test drift after calibration. The feedback diagnostics also include the requested degree-one-million, X=500,000 case.

| Input / correction | Nominal | Half current | Double current | Constant charge | Double curvature | Double charge |
|:--|--:|--:|--:|--:|--:|--:|
| p=3, X=0.019 / optimized | 0.3223 | 0.3223 | 0.3435 | 0.5343 | 0.1527 | 0.1739 |
| p=5, X=1e-250 / optimized | 0.01101 | 0.01101 | 0.01101 | 0.149 | 0.08933 | 0.08933 |
| p=1000000, X=500000 / optimized | 8.476e-08 | 8.476e-08 | 8.476e-08 | 4.515e-07 | 7.405e-07 | 6.809e-07 |
| p=3, X=0.019 / feedback | 1.287 | 1.287 | 1.287 | 1.457 | 1.117 | 1.128 |
| p=5, X=1e-250 / feedback | 0.1302 | 0.1239 | 0.1302 | 0.2431 | 0.02355 | 0.0361 |
| p=1000000, X=500000 / feedback | 1.147e-07 | 1.742e-07 | 1.147e-07 | 4.515e-07 | 6.809e-07 | 6.51e-07 |

Entries are decoded-root ppm, not electrical microvolts. Three diagnostics do not establish a tolerance envelope or silicon yield.

## Numerical checks and reproducibility

9/9 worst-case readouts agree within 0.1 ppm at a four-times-finer timestep. Accuracy misses and calibration failures remain in the records. Development status counts: {'ok': 108, 'failed': 6}.

This continuation records **649 completed full-circuit transients out of 655 trials**, excluding calibration benches and pilot runs. Six development trials were rejected at calibration before a circuit transient was attempted. Final data cover p up to one million and X from 1e-220 to 1e220; earlier stages also cover 1e±250 and the requested `(p=1,000,000, X=500,000)` diagnostic.

Root decoding attenuates centered-state error by approximately 1/p. Large-degree cases cannot substitute for small-degree precision tests. Quoted times start at reset and exclude preparation, programming, calibration, converter latency and decoding. No total supply energy, area, transistor stability or fabricated-hardware speedup is inferred from capacitor values or current limits.

```sh
python3 research/analog_geometry_ad/memory_speed/memory_model.py
python3 research/analog_geometry_ad/memory_speed/memory_campaign.py
python3 -c "import sys; sys.path.insert(0,'research/analog_geometry_ad/memory_speed'); import supplement; supplement.freeze()"
python3 research/analog_geometry_ad/memory_speed/supplement.py
python3 research/analog_geometry_ad/memory_speed/refinement.py
python3 research/analog_geometry_ad/memory_speed/feedback_stress.py
python3 research/analog_geometry_ad/memory_speed/draw_memory.py
python3 research/analog_geometry_ad/memory_speed/report.py
python3 research/analog_geometry_ad/memory_speed/check_results.py
```

Use ngspice and the parent study’s Python requirements. The secondary control/10-ppm choices use development data only; the refinement intentionally uses the first validation as training, then new inputs and seeds. Source hashes and versions are recorded in `provenance.json`. CI checks a small circuit smoke test and evidence consistency, not the complete optimization campaign.
