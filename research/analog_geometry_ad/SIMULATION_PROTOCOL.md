# Paired simulation protocol: centered AD correction geometry

## Question and frozen comparison

Does the intersection-derived feedback correction improve the simulated root calculator under the same precision target, shared hardware model and initialization?

Three variants are compared:

1. **Legacy V30:** the archived circuit deck, including its instantaneous behavioral division and existing candidate RC. This is a reproduction baseline, not a physical divider model.
2. **Direct, two cells:** a loaded multiplier forms `n=−w b`; a loaded divider forms `δ=n/(1+a w)`.
3. **Feedback, two cells:** a loaded summer forms `m=b+aδ`; a loaded multiplier forms `δ=−w m`.

The finite cells use identical 10-ohm output resistance, 100 nF pole capacitor, 50-kilohm port load, 2 pF port capacitance and two-volt behavioral source limits at baseline. Both added-cell variants retain the original output filter and the complete V30 memories and binary chain. They receive the same per-cell gain/offset assumptions and paired, independent internal noise streams. Legacy V30 has no such explicit internal correction cells; its equation-level block must not be mistaken for a characterized divider.

`a=(1+quantized(1/p))/2` uses the same programmed reciprocal coefficient as V30. The exact identity consequently survives coefficient rounding before cell errors are imposed.

## Calibration and noise

The shared circuit calibration is unchanged from `speed_accuracy.configuration`: electrical references for the power/read cells, memory leakage and transfer, and ADC. The two new cells each receive an 81-level affine electrical calibration, with a matched unity reference for loading, 0.1-microvolt simulated measurement noise and 24-fractional-bit trims. No root is used to fit any calibration. This calibration adds work and assumed programmable correction paths; their area and energy are not modeled.

The correction-cell error laws are affine gain and offset errors, not measured device nonlinearities. Added internal noise uses the existing 10-microsecond PWL knot convention, RMS 5 microvolts at baseline, with independent seeds per cell and identical realizations in the paired topologies. It is colored disturbance, not a specified white-noise spectrum. Existing read, output and sampled-memory disturbances remain active.

## Campaign stages

- **Frozen-input cell:** 192 paired steps across two degrees (3 and one million), eight residual increments including small excursions beyond the ideal interval, two common pole scales and three error/calibration profiles. Measure absolute static error, overshoot and time to remain within 1 mV, 10 microvolts and 1 microvolt. Warmup is excluded; the new residual step is included. These are correction-voltage tolerances, not decoded-root ppm.
- **Development:** eight `(p,X)` pairs, five existing schedules, all three variants. Select fixed iteration/averaging policies for 0.1, 1 and 10 ppm using the worst completed development case. A schedule with any rejected/failed case is ineligible. Freeze the selection before validation.
- **Validation:** 64 prepared input pairs covering twelve specified degrees plus sixteen seeded log-scale random pairs, exponents up to one million, inputs from `1e-300` to `1e300`. Each pair has one assigned temperature (cycling through −20, 25 and 85 °C), signed error corner and new noise seed; this is not the full Cartesian product of input pairs and corners. All variants run on the union of selected schedules, plus the common precision schedule. Cases are held out from this campaign's development selection; this is not a statistical silicon-yield sample.
- **Temporal convergence:** rerun the worst completed validation input for each distinct selected topology/policy with a four-times-finer timestep. Retain any disagreement exceeding 0.1 ppm and do not silently endorse that result.
- **Ablations:** three diagnostic inputs under full calibration, omitted inner-cell trims, quiet inner cells, doubled inner noise and ten-times-slower inner poles. Shared memories and the power stage remain unchanged.

Failures, guard activations and accuracy misses are retained in the outputs. A success flag for ngspice alone is not an accuracy pass. The reference root is used only for scoring.

## Timing and physical limits

Report configured time from job reset to the selected state readout. Preparation, coefficient programming, electrical calibration, ADC latency and final decoding remain outside that time, as in V30. ngspice wall-clock execution time is not circuit latency.

The two-cell comparison tests an explicit finite-bandwidth **behavioral assumption**: a divider cell is assigned the same pole/load/error budget as a multiplier or summer. It cannot establish this equivalence in a fabrication process. It also cannot determine quiescent current, total energy, transistor count, layout area or production yield. Counts of nonlinear arithmetic blocks are architectural inventories only. No physical speed, energy or area advantage may be claimed from them alone.

During a complete iteration, the correction front end follows the dynamic power-chain output. The outer V30 state/sample/transfer phases are retained. The frozen-input theorem is checked on its own bench; it is not used as a substitute for simulating those moving signals.
