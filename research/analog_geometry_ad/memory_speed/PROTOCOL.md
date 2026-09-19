# Memory/acquisition redesign: protocol

This follow-up tests memory capacitance and switch/acquisition tradeoffs while retaining the prepared centered AD map, binary power chain and arithmetic-cell assumptions. It does not change the published papers or claim a transistor implementation.

## Explicit new memory model

Both the candidate driver and the transfer buffer have a 10-ohm small-signal output resistance, 100 nF local pole capacitor and smooth 2 mA source/sink current limit. The unchanged archived V30 remains a separate reference; a 100 nF / 230-ohm memory with these added effects is the fair physical-assumption control. The root scoring and ADC model are unchanged.

Both sampling and transfer edges inject charge. Injection has a declared quadratic signal dependence `Q(V)=Q0*(1+0.1*(V/0.7)^2)`; this is a sensitivity model, not a measured device law. The existing four electrical reference levels calibrate the complete two-memory path and the leakage probe. Constant electrical reference measurements, never roots, fit the trims. Each hardware/schedule/corner combination is recalibrated. Thermal sampling noise is recomputed as `sqrt(2*k*T/C)` and existing colored arithmetic disturbances are retained. A smaller capacitor does not get the old capacitor's noise budget.

Candidate profiles span 100, 33, 10 and 1 nF with 230-ohm switches and 0.5 pC nominal injection per edge; low-resistance alternatives use 23 ohms, a declared tenfold 5 pC injection and 20 pF parasitic capacitance. These are engineering hypotheses, not specific products. Representative manufacturer references illustrate why resistance and charge cannot both be improved for free: [ADG1211](https://www.analog.com/en/products/adg1211.html), [ADG1411 datasheet](https://www.analog.com/media/en/technical-documentation/data-sheets/ADG1411_1412_1413.pdf), and [AN-1515 sample/hold application note](https://www.analog.com/en/resources/app-notes/an-1515.html). No product's complete behavior is claimed to be represented.

## Development and independent validation

Development sweeps declared hardware profiles and acquisition schedules over small degrees, large degrees and both error signs. Select the quickest fixed iteration/averaging policy meeting the worst-case target of 1 ppm (also retain 10 ppm). Freeze hardware, timing, iteration count and averaging before independent validation. The reference root is used only for scoring. All saturation/range rejections and accuracy misses remain in the records.

Validation uses fresh inputs, noise/calibration seeds and temperature assignments, including small degrees and degree one million. The selected memory is also tested with the geometric feedback correction. No readout selection may use the validation root. Refine the timestep on worst cases, test charge-law curvature and current limits, and retain failures.

Record circuit readout latency, precision, current-limit duty and peak current, acquisition dynamics and calibration residual. Do not confuse ngspice host runtime with latency. Times exclude preparation, programming, calibration, ADC latency and decoding as before. Full supply energy, area, transistor stability and production yield remain unmodeled; current limits alone do not establish them.

## One declared refinement after first-validation misses

The first 1-ppm policies missed some cases (including the archived baseline). That validation set becomes development data for a second, explicitly separate stage. Retain the already chosen hardware and clock for each arm; select the fastest fixed iteration/averaging policy whose worst error on the 48 first-validation cases is at most **0.7 ppm**, leaving a declared margin to the 1-ppm target. No second-validation value is available when choosing this policy. An arm without an eligible policy is reported as such.

The new validation has 32 fresh `(p,X)` pairs: degrees `[3,4,5,7,31,257,983039,1000000]` times `[0.043,1.000011,1e-220,1e220]`, each with two new seed/corner assignments (64 cases per arm). Test optimized direct correction, geometric feedback, the finite-current 100 nF control, and archived V30, using each arm's frozen policy. The first-stage failures remain in the report. This is one refinement, not repeated tuning until the held-out cases pass. Compare actual readouts at four-times-finer steps on each arm's worst completed case. The separately development-selected 10-ppm policy is validated on the first independent set and is not retuned.
