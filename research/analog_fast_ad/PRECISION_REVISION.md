# Precision revision and independent circuit validation

The revised behavioral circuit meets a **one-ppm relative root-error target in
64/64 held-out cases**. Every paired case improves over the earlier circuit.
The largest observed error falls from 403.5 ppm to 0.279 ppm. These are results
under the explicit electrical models below, not a universal bound or measured
chip specifications. The revised circuit retains sampled AD; the noisy adaptive
controller is tested separately and has not been wired into this SPICE design.

## Circuit changes, not just smaller imposed errors

The revision starts from the earlier **untrimmed** gain, offset, loading,
leakage, charge and voltage-noise parameters. It adds the following mechanisms:

| Element | Earlier circuit | Revised precision mode |
|---|---:|---:|
| State / next-state hold capacitors | 10 nF | 100 nF |
| Switch on resistance | 120 Ω in combined tests | 230 Ω imposed |
| Sample / transfer windows | 10 / 10 µs | 400 / 400 µs |
| Iteration period | 500 µs | 1,200 µs |
| Iterations executed | 6 | 20 |
| Results averaged at output | last one | last sixteen, after four discarded steps |
| Coefficient fractional bits | 16 | 24 |
| State ADC | 18 bits | 24 bits, calibrated |
| Memory drift correction | none | measured programmable current compensation |

Larger capacitors reduce droop, injection voltage and thermal sample noise.
They need longer acquisition: increasing capacitance while retaining the old
10 µs switches would be an invalid speed/precision comparison. The generator
now exposes these parameters and makes reset and thermal-injection pulses
one-shot over the full configured run, including runs longer than 10 ms.

The new readout averages **digitized states from separate AD iterations**, not
repeated ADC conversions of one frozen noisy state. In this noise model those
iterations are separated by far more than the colored-noise knot spacing.
Averaging does not remove a constant bias; electrical calibration handles the
modeled gain/offset terms. It would not remove unspecified correlated 1/f drift.
The averaging changes the noisy readout protocol, not the underlying exact AD
correction formula.

The final readout is at **23.985 ms**, before preparation, programming and
calibration overhead, versus 2.905 ms in the original schedule. Capacitor area,
converter cost, trim paths and current-source power have not been measured.
This is a precision-oriented mode, **not a speed or energy improvement claim**.

## Electrical calibration procedure

No desired root enters any calibration. Four independent measurements are used:

1. The existing 81-point DC electrical grid identifies the arithmetic cells,
   read buffer and correction block. Their compensation coefficients have 24
   fractional bits and synthetic 0.1 µV RMS measurement noise.
2. Four known memory voltages are observed at two hold times separated by
   100 µs. The slope estimates the leakage current. A new programmable current
   source counters it with a modeled 2 pA increment and ±1 µA range.
3. The memory transfer is measured again with current compensation enabled.
   A fitted affine adjustment corrects the sample/transfer/read-delay error.
4. Seventeen known ADC input voltages identify its affine gain and offset.
   Unlike a purely constant INL term, the revised ADC also has a sinusoidal
   code-dependent error, of one LSB amplitude and 0.2 V period, which is not
   removed by affine calibration.

The leakage-current correction matters because an uncompensated capacitor also
moves **during** the arithmetic evaluation. Correcting only the final readout
bias leaves a lag-dependent error at high temperature. Development tests exposed
this effect and motivated the additional current source before the independent
validation campaign was run.

Calibration is performed at each tested temperature before the job. The
measurements assume accurate reference voltages and known hold capacitance.
The added correction paths and compensation-current source are behavioral;
their own noise, drift, DAC imperfections, compliance and implementation area
are not validated. A 24-bit code width is not a claim of 24 effective hardware
bits. The 0.1 µV measurement uncertainty is a bench requirement in this model,
not an available fabricated calibration system. Temperature changes *after*
calibration and correlated reference errors require another budget.

## Independent validation and diagnostics

`revised_circuit.py` develops the design only on (3,2), (3,500000) and
(1000000,500000), at 25/85 °C. The architecture and numerical parameters are
then fixed for `validate_revised.py`:

- 48 pairs from twelve degrees and X=1e-300, 0.037, 1.000001, 1e300;
- sixteen independently seeded random degree/input pairs;
- alternating −20/25/85 °C, both signs of static error and independent noise
  and calibration-measurement seeds;
- original/revised comparisons on each pair, for 128 primary transients;
- a four-times-smaller timestep on the worst revised validation case.

All 64 revised results meet one ppm, and all improve relative to their paired
original result. The largest error is 2.7892e-7. Accuracy is enforced in the
script, in addition to voltage-range and denominator checks. Detailed inputs,
configurations, fitted measurements, samples and misses (if any future run
fails) are retained in `revised_validation.json`. This modest held-out set is
not a worst-case proof, a manufacturing yield estimate, or an exhaustive repeat
of the earlier 8,243-input campaign.

Five ablation transients at p=3, X=0.037, 85 °C remove improvements individually.
In that diagnostic case, removing cell calibration gives about 410 ppm;
removing ADC calibration gives 6.94 ppm; removing leakage compensation while
recalibrating the memory offset leaves 2.10 ppm. Using just the final conversion
instead of sixteen averaged iterations gives about 1.03 ppm. The complete
revision gives approximately 0.031 ppm. These are one-case diagnostics, not
universal per-block bounds.

Three original-circuit regression cases and a slow-clock noisy regression still
match their earlier results. The extension preserves the original defaults and
keeps historical experiments reproducible.

## Noisy completion-controller subsystem

`noisy_controller.py` replaces the earlier ideal completion test with:

- 2 µV RMS detector disturbances, ±1 µV fixed detector offset, and a 20-bit
  quantization step over a 4 V span;
- separate 12/24 µV enter/exit thresholds and a 10 µs dwell;
- a minimum hold interval derived from an assumed characterized upper bound
  on per-stage delay, plus an explicit timeout;
- averaging of recent candidate samples, with independent 0.5 µV RMS candidate
  disturbance; no desired root participates in the decision.

All eighteen normal jobs complete. Four injected faults (stuck candidate or
excess detector noise, at low and high p) time out without transferring a state.
A timestep-halving check is also performed. Thus the model no longer hangs
indefinitely or silently claims completion on these faults.

This controller model has ideal memory transfer and does **not** include the
revised SPICE memory, converters or all analog errors. Its delay bound is assumed,
not automatically measured. It is therefore a tested subsystem, not a validated
physical asynchronous replacement for the revised circuit's timing controls.
No proof of absence of false triggering under arbitrary noise is claimed.

## Reproduction and remaining validation boundary

```sh
python research/analog_fast_ad/revised_circuit.py
python research/analog_fast_ad/validate_revised.py
python research/analog_fast_ad/revised_ablation.py
python research/analog_fast_ad/noisy_controller.py
python research/analog_fast_ad/precision_revision_report.py
```

A dedicated CI job runs the held-out circuit validation, ablations and noisy
controller tests. The next physical or transistor-level checks must include the
new current compensation, calibration references, capacitor tolerances, converter
transfer/noise, correlated drift and actual controller/memory integration.
There is still no manufacturer/PDK sign-off or fabricated-chip measurement.

### Hosted CI execution budget

GitHub's precision job permits 600 seconds per ngspice process, two concurrent
trajectories and one BLAS/OpenMP thread per process, with a 45-minute job limit.
These are host wall-clock budgets, not simulated circuit latencies. The defaults
for local use remain 90 seconds and three workers. Override them with
`PANDROSION_SPICE_TIMEOUT_SECONDS` and `PANDROSION_SPICE_WORKERS`; positive
integers are required. Accuracy thresholds, integration steps, seeds and all
electrical parameters remain unchanged.
