# Electrical validation protocol — not yet executed

This protocol applies first to one centered cell, then a buffered memory and
correction cell, before assembling a chain. No board or fabrication PDK was
provided. The CSV below is a schema, not a set of fabricated measurements.

## Test access and instrumentation

Provide access to two cell inputs, output, coefficient programming, memory state,
clock/control and supply rails. Use traceable voltage sources and a digitizer
whose combined uncertainty is below one quarter of the allocated error under
test. A temperature-controlled setup and supply-current measurement are needed.
Document probe loading, grounding, bandwidth, firmware, part grade/lot and the
uncertainty of the references. For an accepted manufacturer model, record the
unmodified model hash/version and simulator compatibility changes separately.

## Cell measurements

1. Sweep both inputs across at least −0.7 to 0.1 V at the coefficient values used
   by p=3,32,983039,1,000,000, including the smallest binary-power weight.
   Record offsets, linear/cross terms and held-out residual nonlinearities.
2. Fit calibration using a training grid, then verify on a disjoint voltage
   grid. Include reference uncertainty and finite trim resolution. Repeat with
   realistic downstream fanout; unloaded calibration is not sufficient.
3. Step through the same input range. Measure settling to the assigned absolute
   error, not just 10–90% rise time. Sweep both control phases and verify each
   cascaded stage has settled at the actual sampling instant.
4. Measure memory droop versus hold duration and charge injection versus state
   voltage, switch direction and clock edge. Include capacitor absorption.
5. Measure output noise spectrum and sampled-state distribution over repeated
   cycles. Separate low-frequency drift, reference correlation and white noise.
6. Repeat the above at temperature and supply corners. Apply stored room-
   temperature trims, then recalibrate, to distinguish removable and residual
   errors. Check repeatability after a thermal cycle.

## Chain and converter acceptance

Use an independently computed high-precision root only for scoring. Inputs must
include p=3 and the 37-stage case p=983039, the requested million-degree case,
and both extreme input magnitudes. Sweep intermediate degrees and normalization
positions; a few representatives are not a universal guarantee.

For each declared accuracy target ε, compute the total state budget
`D = ε(p−ln(2))/(1+ε)` and allocate it before testing. Propagate each measured
cell error through the chain; do not give every cell the full budget. Check ADC
and coefficient-DAC INL, drift, reference noise and clipping independently.
Report both the worst measured error and uncertainty, not only RMS or typical
precision. A failed target is a failed design criterion even if the circuit
stays within its voltage rails.

Measure latency from receipt of p,X until the decoded result is available.
Integrate **all** supply energy over the same interval. Include preparation,
programming, converters, controller and amortized recalibration. Compare with
an entirely digital solver on the same application accuracy/throughput target.
Simulation runtime is never circuit latency or energy.

Suggested measurement columns:

```csv
run_id,device_id,model_hash,temperature_C,supply_V,p,X,stage,coefficient,input_d_V,input_q_V,output_V,expected_V,error_V,uncertainty_V,hold_us,settling_us,root_relative_error,total_latency_us,total_energy_J,calibration_id,target_met
```

Do not mark the prototype hardware-validated until these measurements, or
explicitly scoped transistor-model checks, exist. In particular, a 1 ppm
uniform claim is currently contradicted by our low-degree behavioral results.
