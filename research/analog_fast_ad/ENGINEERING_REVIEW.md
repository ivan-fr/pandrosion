# Remaining simulation checks: engineering review

This follow-up closes the combined behavioral-transient and host-software
comparison gaps. It also implements a simulated electrical-reference calibration
experiment. It does **not** close physical device validation, transistor-model
validation, or energy/area measurement. The user elected to continue without
hardware or a fabrication PDK.

## Combined timed errors

`joint_spice.py` now combines, in each ngspice transient:

- Stage and correction gain/offset, port loading, finite stage settling;
- Clocked sample/hold, state leakage and switch charge injection;
- Finite programmed coefficients, including Y and 1/p;
- A finite ADC with gain, offset, INL and rounding;
- Two independent colored-voltage disturbances, at the read buffer and correction;
- A sampled memory-noise pulse per transfer, representing two lumped kT/C terms.

Colored disturbances are reproducible Gaussian **knot values**, interpolated
linearly every 10 µs. They are not specified amplifier spectral densities. With
clock scaling their correlation time scales too. The sample noise uses
sqrt(2 k T / 10 nF); it is injected as a finite-area current pulse. These are
explicit stochastic assumptions, not device noise models. Stage/summer offsets
and gains are correlated signed corners; the runs are not a statistical yield
estimate or an exhaustive worst case.

The 19 runs cover p=3,32,983039,1,000,000 at X=500,000, initial/tighter profiles,
25/+85 °C signed cases, two slow-clock hot cases, and a finer-timestep repeat.
The degree 983039 exercises the longest schedule. All range and timestep checks
pass. `meets_accuracy_target` separately records whether the accuracy goal is
met; a passing execution check must not be read as universal accuracy success.
The other X values remain covered by the earlier static population study,
not by this small combined-transient matrix.

The switch on-resistance is now 120 Ω, instead of the earlier idealized 1 Ω.
This is the headline typical scale of the
[ADG1211 data sheet, Table 1](https://www.analog.com/media/en/technical-documentation/data-sheets/adg1211_1212_1213.pdf).
The same table gives 230 Ω maximum through 85 °C under its stated supply and
signal conditions. The simplified switch is therefore **not an ADG1211 model**
and the chosen value is not a certified hot-corner bound. Off resistance,
control edges, leakage and injection are independent behavioral assumptions.
The real device also needs its own control polarity and supply arrangement.

The long-clock experiment now includes the previously omitted hot leakage and
conversion errors. It no longer reproduces the near-ideal 8e-14 result: the
slow-clock initial profile gives roughly 5.1e-8 relative error at p=1,000,000.
Slower settling is not a free precision improvement. See the generated
[results table](ENGINEERING_RESULTS.md) for the current numerical values.

## Actual calibration procedure within the behavioral model

`calibrate_cells.py` independently excites each power-chain cell, the read
buffer and the correction block with an electrical grid of 81 known pairs.
It measures the **ngspice DC outputs**, adds 0.1 µV RMS synthetic measurement
noise and rounds to 24 fractional bits. No desired root is supplied to fitting.

Least-squares fits use the cell's known polynomial basis: affine read/correction,
quadratic square cell, and bilinear multiply cell. The linear coefficient
estimates the port attenuation. The script derives source compensation
coefficients and quantizes them to 24 fractional bits, then runs the entire
clocked circuit with those trims. ADC, noise, leakage and charge errors remain
active; it does not replace the physical parameters by the tighter profile.

This requires **additional programmable correction paths and test access**.
Their own loading, noise, DAC nonlinearity, power and area are not modeled.
Calibration sources have exact reference voltages in the bench; their real
accuracy must be budgeted. The polynomial model matches the simulated cells,
so success is not evidence that unmodeled real nonlinearities can be removed.
Neither the calibration fixture nor a switching sequencer has been implemented
at transistor level. The existing `trim_target` profile remains a target, not
a specification automatically achieved by this new procedure.

For p=1,000,000, calibration improves the nominal combined result from about
2.03e-9 to 4.23e-11 in the imposed scenario. Applying the 25 °C trims at 85 °C
loses most of that benefit. Recalibrating at 85 °C is explicitly tested, but
leakage and converter errors remain. At p=3 even nominal calibration does not
meet one ppm. Temperature sensing/recalibration alone is therefore insufficient.

## End-to-end digital comparison

`benchmark.mjs` measures Node.js on the recorded host, with warmup, 21 repeated
batches and 256 varying inputs per benchmark. Input variation prevents timing a
constant-folded root result. Four paths are separated:

1. Certified dyadic preparation only;
2. Six centered AD steps on already-prepared inputs;
3. Preparation plus six entirely digital centered AD steps and decoding;
4. The ordinary library calculation `exp(log(X)/p)`.

The last path does not provide the preparation's interval certificate. Its
outputs and the centered path are independently checked against a 90-digit
reference on the 12 representative (p,X) pairs; all 24 checked outputs are
within 2e-13 relative error. Library roots are used only for this comparison,
never to initialize the analog or centered-digital algorithms.

The first nominal analog output after six steps is sampled at 2905 µs. Digital
preparation, coefficient programming, ADC conversion and final decoding must be
added to that time. On this host, the whole centered digital route for the
million-degree example takes about 179 µs, most of it preparation. The ordinary
library route has far smaller batched cost. Host timings are not MCU/ASIC
latency, and batched timing is not a single-call real-time guarantee. Even so,
**the current experiment supplies no speed advantage for analog**. More relaxed
accuracy may permit fewer steps in either architecture; these timings compare
fixed six-step runs, not optimally stopped solvers.

Energy cannot be inferred from ngspice's simulation runtime or from the currents
of ideal behavioral sources. There is no supply-current model for the analog
arithmetic, and no measured CPU energy. The appropriate accounting is

    E_analog = E_preparation + E_programming + P_core * T_core
               + E_ADC + E_decode + amortized E_calibration.

Every term must use the same workload and accuracy target as the digital
baseline. No zero-valued missing terms or unsubstantiated energy benefit are
reported. The current 10/100 nF capacitors and unrolled arithmetic stages are
functional design choices, not a demonstrated compact IC layout.

## Component-model boundary

The [AD734 product page](https://www.analog.com/en/products/ad734.html) offers
manufacturer SPICE models under its download license. The direct download attempt failed (HTTP/2 transport error, then HTTP/1.1
timeout), so no manufacturer model has been obtained or run in this work; the custom arithmetic is not a substitute for one.
The [AD734 data sheet](https://www.analog.com/media/en/technical-documentation/data-sheets/ad734.pdf)
specifies input offsets on a millivolt scale. Our microvolt residual targets
cannot be attributed to an uncalibrated AD734. A component-based implementation
must validate its pin configuration, denominator scaling, common-mode range,
loading and supply current before a chain-level claim.

[The bench protocol](BENCH_PROTOCOL.md) lists the electrical measurements and
acceptance criteria needed once components or a PDK become available. Nothing
in this repository claims those measurements have been performed.

## Reproduction

```sh
python research/analog_fast_ad/joint_spice.py
python research/analog_fast_ad/calibrate_cells.py
node research/analog_fast_ad/benchmark.mjs
python research/analog_fast_ad/validate_comparison.py
python research/analog_fast_ad/engineering_report.py
```

CI executes the first four commands. Timing values are informational and are
not used as speed assertions. Range/timestep checks, finite outputs, calibration
improvement in its stated nominal scenario and independent digital accuracy
checks are enforced. Quantified accuracy failures remain visible in the report.
