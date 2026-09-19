# AD correction geometry: paired SPICE results

The geometric feedback cell is evaluated against both the unchanged V30 equation-level correction and a matched two-cell direct implementation. All speed claims below concern the declared behavioral model, not fabricated hardware. See [the frozen protocol](SIMULATION_PROTOCOL.md).

**Finding: a local settling improvement, but no demonstrated whole-calculator speed advantage over V30 at the 1-ppm target.** At the selected 2.385 ms policy, feedback passes 60/64 held-out inputs versus 64/64 for the V30 equation baseline. The two finite-cell topologies both add internal noise and calibration work. The isolated feedback cell is useful evidence for an implementation option, not sufficient evidence to replace the V30 architecture or claim a superior chip.

## Whole-calculator policies selected before validation

| Variant | Target (ppm) | Selected time (ms) | Iterations / averaged | Held-out passes | Worst completed error (ppm) |
|:--|--:|--:|:--|:--|--:|
| V30 equation baseline | 0.1 | — | No eligible development policy | — | — |
| V30 equation baseline | 1 | 2.385 | 2 / 1 | 64/64 (64 completed) | 0.873 |
| V30 equation baseline | 10 | 2.385 | 2 / 1 | 64/64 (64 completed) | 0.873 |
| Direct, two cells | 0.1 | — | No eligible development policy | — | — |
| Direct, two cells | 1 | 4.785 | 4 / 1 | 62/64 (64 completed) | 2.811 |
| Direct, two cells | 10 | 2.385 | 2 / 1 | 64/64 (64 completed) | 2.163 |
| Feedback, two cells | 0.1 | — | No eligible development policy | — | — |
| Feedback, two cells | 1 | 2.385 | 2 / 1 | 60/64 (64 completed) | 1.693 |
| Feedback, two cells | 10 | 2.385 | 2 / 1 | 64/64 (64 completed) | 1.693 |

**An accuracy miss invalidates the selected target claim even when ngspice completes.** A selected time with fewer passes than cases is not a validated all-case latency. The 0.1-ppm target is also allowed to fail; no post-validation reselection is performed.

Development retained 45 range/guard rejections out of 120 transients, all on the aggressive or minimum acquisition schedules. Those schedules are ineligible for selection. All 192 validation transients completed without guard rejection, but the accuracy misses above remain.

## Common fixed readout policies

| Variant | 4 iterations / average 2 at 4.785 ms | Worst ppm | 20 iterations / average 16 at 23.985 ms | Worst ppm |
|:--|:--|--:|:--|--:|
| V30 equation baseline | 64/64 ≤ 1 ppm | 0.738 | 64/64 ≤ 1 ppm | 0.423 |
| Direct, two cells | 60/64 ≤ 1 ppm | 1.528 | 64/64 ≤ 1 ppm | 0.437 |
| Feedback, two cells | 62/64 ≤ 1 ppm | 1.125 | 64/64 ≤ 1 ppm | 0.355 |

These fixed reference policies were inherited from V30, not chosen to make the new topology win. All three models use the same acquisition clocks, 100 nF memories, 230-ohm switches, shared calibration and input preparation. Added-cell variants include two additional colored-noise streams and cell calibration.

For the decoded root, `d log(root)/dq = −1/(p+q)`. A given centered-voltage error therefore has a smaller relative effect at large degrees. The degree-one-million cases do not replace the low-degree precision tests; preparation also already contributes to their initial accuracy.

## Isolated correction-cell result

The cell bench measures time after a new residual step, with the cells already powered and settled beforehand. Tolerances here are correction **volts**, not decoded-root ppm. Dynamic disturbance sources are off on this bench; finite loading, affine errors and noisy calibration measurements remain.

| Residual step w | Direct settling to 1 µV (µs) | Feedback settling to 1 µV (µs) | Feedback reduction | Feedback overshoot (V) |
|--:|--:|--:|--:|--:|
| 0.01 | 11.788 | 8.888 | 24.6% | 0 |
| 0.1 | 14.199 | 11.440 | 19.4% | 5.51484e-05 |
| 0.5 | 15.684 | 12.038 | 23.2% | 0.0142529 |
| 1 | 16.182 | 12.274 | 24.1% | 0.0715507 |
| -0.1 | 14.280 | 14.928 | -4.5% | 4.74727e-08 |

For the cubic full positive step, the feedback cell settles sooner but overshoots its equilibrium. The static geometric coordinate bounds do not bound this transient. The small negative-residual step tests a departure from the ideal initialized interval and shows why a uniform speedup should not be claimed. Eight four-times-finer timestep checks changed the 1-µV settling measurement by at most 0.0088 µs.

Calibration is essential even on the isolated cell. At `p=3, w=1`, the final absolute errors are:

| Cell profile | Direct (µV) | Feedback (µV) |
|:--|--:|--:|
| No affine error, finite load | 239.928 | 143.980 |
| Affine errors, no trim | 1592.811 | 1007.421 |
| Electrical trim applied | 0.028 | 0.031 |

The first two profiles do not settle within the 1-µV accuracy band during the recorded step response. A better intersection angle does not remove loading and component error.

## What consumes the available time

Each added correction pole is about 1 µs, whereas the nominal switch/memory RC is 23 µs and each precision acquisition window is 400 µs. Shortening the acquisition schedule changes memory transfer errors even if the correction settles earlier. The full-circuit study includes this coupling. Preparation, programming, electrical calibration, ADC latency and decoding remain outside the quoted readout times.

## Partial passive-load accounting

**The following is only the loss in the two explicit correction-cell port resistors. It is not chip energy or supply power.** Behavioral sources have no transistor/quiescent-current model.

| Degree | X | Topology | Final two-port dissipation (µW) | Energy through 4.785 ms (nJ) |
|--:|--:|:--|--:|--:|
| 3 | 0.071 | direct | 3.40484e-09 | 18.229 |
| 3 | 0.071 | feedback | 12.9604 | 62.677 |
| 7 | 1e-200 | direct | 8.11753e-09 | 7.025 |
| 7 | 1e-200 | feedback | 17.7086 | 82.461 |
| 1000000 | 500000 | direct | 3.37736e-09 | 2.249 |
| 1000000 | 500000 | feedback | 20.0001 | 92.835 |

The feedback summer holds a signal near `b≈1` at convergence, whereas the direct numerator and correction approach zero. With the modeled 50-kilohm shunt loads, that common-mode level costs passive power. Changing the physical input impedance could change this balance. A multiplier/summer versus multiplier/divider block inventory does not establish an area or energy reduction.

## Ablations and numerical reliability

| Diagnostic | Variant | Full | No inner trim | Quiet inner cells | Double inner noise | 10× slower inner poles |
|:--|:--|--:|--:|--:|--:|--:|
| p=3, X=0.071 | direct | 0.3127 | 45.17 | 0.4114 | 0.2078 | 0.6829 |
| p=3, X=0.071 | feedback | 0.2757 | 22.43 | 0.3744 | 0.1893 | 0.4114 |
| p=7, X=1e-200 | direct | 0.009634 | 16.75 | 0.005109 | 0.01416 | 0.1793 |
| p=7, X=1e-200 | feedback | 0.06729 | 8.311 | 0.007372 | 0.1487 | 0.01642 |
| p=1000000, X=500000 | direct | 9.889e-07 | 0.0001088 | 8.548e-07 | 1.108e-06 | 1.391e-06 |
| p=1000000, X=500000 | feedback | 1.078e-06 | 5.377e-05 | 8.548e-07 | 1.302e-06 | 1.183e-06 |

Ablation entries are decoded-root ppm at the fixed 20/16 policy. These are three diagnostic cases, not universal component error bounds. A particular seeded disturbance can partially cancel deterministic bias: a smaller error with doubled noise does not mean that noise improves precision or that its variance is lower.

Whole-circuit timestep checks: 4/4 decoded readouts agree within 0.1 ppm under a four-times-finer step (maximum difference 0.0000 ppm). This compares the readouts themselves, not merely their absolute reference errors. All failures and guard/clamp activations remain in the JSON records.

## Interpretation

The finite-bandwidth cell can benefit from the geometric feedback factor, but the evidence must be assessed at the complete-calculator level. A shorter isolated settling transient does not automatically reduce the memory/acquisition budget. The old V30 scalar denominator was already well conditioned after centering, so this experiment tests an implementation topology rather than a better intrinsic condition number.

No transistor process, manufacturer arithmetic macromodel or measured prototype is used. The direct divider and feedback primitives are assigned the same generic pole/load/error model. Total energy, layout area, device count and silicon speed remain uncharacterized.

## Reproduce

```sh
python3 research/analog_geometry_ad/verify.py
python3 research/analog_geometry_ad/circuit.py
python3 research/analog_geometry_ad/cell_bench.py
python3 research/analog_geometry_ad/campaign.py
python3 research/analog_geometry_ad/passive_energy.py
python3 research/analog_geometry_ad/report.py
python3 research/analog_geometry_ad/check_results.py
```

Requires ngspice and the existing `research/analog_fast_ad/requirements.txt`. Increase `PANDROSION_SPICE_TIMEOUT_SECONDS` on slower hosts; it changes only host execution limits. Development selection is saved before validation. Example decks, logs and thinned waveforms are in `examples/`.
