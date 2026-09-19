# Hardware accuracy: what is quantified and what remains open

Follow-up: [combined timed tests, simulated calibration and digital comparison](ENGINEERING_REVIEW.md)
now address several gaps identified below. The original `trim_target` assumptions
remain distinct from the fitted-calibration experiment.

The large-degree centered representation survives a useful first error-budget
study. It does **not** yet provide a uniform hardware accuracy across degrees.
The limiting case for root precision is small p, whereas long binary chains
make settling more difficult at large p. Sources, distributions, and timing
assumptions below are part of the experiment, not component specifications.

## An exact output error budget

Let q★ be the exact normalized root state and let q̂=q★+δ be the state digitized
for output. With the same stored digital c and p,

    reconstructed_root / true_root − 1 = −δ/(p+q★+δ).

For ideal preparation q★∈[−ln 2,0], |δ|≤D<p−ln 2 implies

    |relative error| ≤ D/(p−ln 2−D).

Hence D=ε(p−ln 2)/(1+ε) is sufficient for target relative error ε.
At p=1,000,000, a 1 ppb target permits approximately 1 mV total state error.
At p=3, a 1 ppm target permits only 2.31 µV. These are totals, not allowances
for each component separately. This bound assumes exact c storage/decoding;
front-end acquisition error in X and digital output rounding require separate
allocations. The numerical test scores against the original binary64 X using
90-digit arithmetic; rounded Y is included in the actual iteration.

The allocation table in [CHARACTERIZATION.md](CHARACTERIZATION.md) splits the
state budget into four equal parts. At p=3 and one ppm, ideal ±2 V ADC rounding
alone requires 22 bits under that allocation; actual INL, gain, offset and noise
consume more budget. Two independent kT/C sample contributions at 300 K would
require about 224 nF for a three-sigma noise allocation. Our 10 nF capacitors
therefore cannot meet that particular budget, even with ideal amplifiers.
This is a sufficient design allocation, not a universal lower bound on all
possible architectures. Oversampling, narrower ADC range, and different state
scales could change it, with acquisition-time and circuit costs.

## Behavioral population model

`characterize.py` evaluates sixteen input pairs: p=3,32,983039,1,000,000 and
X=10^−300,2,500,000,10^300. The degree 983039 exercises the maximum
37-stage binary schedule in the supported range. For each pair it draws 512 synthetic devices, evaluated at
−20, 25 and 85 °C for two profiles. Static errors remain fixed during the six
iterations. Matching random draws across temperatures isolate drift effects.
The exact distributions are committed in `characterization_results.json`.

| Assumption | untrimmed | trim_target |
|---|---:|---:|
| Per-stage offset bound | ±25 µV | ±1 µV |
| Product and correction gain bound | ±1000 ppm | ±20 ppm |
| Offset temperature coefficient bound | ±0.5 µV/°C | ±0.02 µV/°C |
| Gain temperature coefficient bound | ±10 ppm/°C | ±0.2 ppm/°C |
| Port resistance, with ±20% mismatch | 50 kΩ | 10 MΩ |
| Output resistance | 10 Ω | 10 Ω |
| Leakage magnitude bound at 25 °C | 5 nA | 50 pA |
| Effective state charge injection bound | 0.5 pC | 0.02 pC |
| Coefficient fractional bits | 16 | 24 |
| Ideal ADC bits, ±2 V | 18 | 22 |
| ADC offset/gain bounds | ±25 µV / ±100 ppm | ±1 µV / ±2 ppm |
| ADC INL bound | ±1 LSB | ±0.5 LSB |
| Additional state-referred RMS noise | 5 µV | 0.5 µV |

Static bounds use independent uniform draws across stages and error categories;
within each stage, the product and summing offset share the same draw. Leakage is assigned either sign
and, as a deliberately explicit hypothetical temperature law, its magnitude
doubles per 10 °C. Offset and gain drift are linear with independently drawn
coefficients. No foundry distribution or manufacturer thermal curve justifies
these particular numbers. Port loading is 1/(1+Rout/Rin) after every stage.
The correction block has its own offset and gain error; these were absent
from the original stressed SPICE example.

Noise is fresh Gaussian state-referred noise each iteration, plus two independent
kT/C contributions for the two hold capacitors. At 300 K, one 10 nF capacitor
contributes about 0.644 µV RMS. This is an output-referred model, **not** a
transistor noise analysis: it does not propagate each amplifier's noise spectral
density, 1/f noise, reference correlations, dielectric absorption or supply
coupling. ADC INL is a fixed bounded per-device error, not a measured code
transfer curve. Coefficient rounding includes Y and 1/p. Their DAC drift and
nonlinearities, and gain-reference correlation, are not modeled.

Charge injection is a net effective state voltage step Q/C. The memory leaks
before the next sample as well as during the 15 µs readout delay. The clock
has a 460 µs interval from state-switch release to the next candidate sample.
The population model assumes arithmetic settles before that sample. Noise and
mismatch can produce biased fixed points; no Gaussian percentile is a hard
worst-case guarantee, and 512 draws do not establish tail yield.

At X=500,000 and 85 °C, the tighter profile's 99th-percentile errors are
8.32 ppm at p=3, 0.568 ppm at p=32, and 0.0197 ppb at p=1,000,000.
Thus even the proposed tighter residual tolerances do not establish a one-ppm
product across the degree range. No population run activated the ±2 V/0.25 V
range limits, which establishes range only for these cases.

## Timed circuit cross-checks and a timing failure

`characterize_spice.py` uses ngspice to vary one source at a time for p=3 and
p=1,000,000 at X=500,000: offset, product gain, port load, leakage, state charge
injection, correction error, and stage settling. A 0.5 pC injected pulse gives
approximately 50 µV on the 10 nF state capacitor, checked independently in the
simulation. Leakage gives −37.5 µV over the final 75 µs hold window. A fourfold
smaller timestep checks the charge-pulse experiment.

For p=1,000,000, isolated 50 kΩ port loading contributes approximately 1.20 ppb;
isolated +25 µV stage offsets contribute 0.625 ppb. These are deterministic
positive-sign experiments, distinct from the population's mixed-sign draws.
At p=3, correction-block gain/offset alone gives approximately 230 ppm.
The report preserves the full numerical output rather than adding these
nonlinear contributions into a false bound.

Increasing each stage's time constant from 1 µs to 30 µs while retaining the
500 µs iteration clock produces about 248 ppb error in the million-degree
example, essentially losing the digital initializer's refinement. No range
guard triggers. **A circuit can remain in range and still fail to settle.**
With a 30-times-slower clock, the million-degree error falls to about 8×10⁻¹⁴
before ADC quantization in the near-ideal baseline model. At p=3 the longer
clock leaves about 4.56×10⁻⁸ error from finite off-state resistances. This
isolates settling recovery; it does not solve the larger leakage/noise burden
of slower real hardware. The long-clock test retains baseline near-zero leakage.

## Concrete next hardware requirements

1. Buffer the arithmetic ports, then measure residual loading under actual fanout.
   The 10 MΩ target markedly reduces the large-p loading contribution, but input
   capacitance, bandwidth and buffer noise must be measured together.
2. Characterize a centered multiply-accumulate cell and the correction divider
   separately, including small programmed coefficients. Fit offset, gain and
   nonlinear residuals using known electrical inputs; then repeat over temperature.
   No calibration algorithm or test fixture is implemented by `trim_target`.
3. Measure leakage, switch charge injection and acquisition time with the actual
   capacitor technology. A larger capacitor reduces kT/C and droop but slows
   acquisition and costs area; the present 10/100 nF values are functional
   choices, not a viable on-chip capacitor layout claim.
4. Select or characterize ADC/DAC interfaces using INL, drift and effective noise,
   not nominal bit count alone. The binary64 X input is digital; a sensor ADC
   would introduce an additional error before normalization.
5. Choose timing from the measured cell dynamics and chain length. Retest the
   combined errors at that timing, then use a transistor/PDK model before any
   claim about power, area, yield or fabricated-chip precision.

## Primary references for the error mechanisms

- Analog Devices, [AN-1515: Sample-and-Hold Circuit Using the ADG1211 Switch](https://www.analog.com/en/resources/app-notes/an-1515.html):
  switch transients, hold operation and charge-injection mitigation.
- Analog Devices, [Managing Noise in the Signal Chain, Part 2](https://www.analog.com/en/resources/technical-articles/2022/07/16/11/45/managing-noise-in-the-signal-chain-part-2-noise-and-distortion-in-data-converters.html):
  sampled thermal noise and converter noise limits.
- Analog Devices, [AD734 data sheet](https://www.analog.com/media/en/technical-documentation/data-sheets/ad734.pdf):
  multiplier interfaces and offset sensitivity at low signal levels. The custom
  behavioral arithmetic is not this device's macromodel.

These sources motivate mechanisms only. They do not certify the numerical
assumptions or the proposed trim targets above.
