# Protocol frozen before the new experiments

Domain: X >= 1 and real p >= 1; numeric interface binary64. Common-comparison
cases use integer p=3,7,32,1000000 and X=2,500000. Fractional p=1.01,sqrt(2),3.7,
37.5,1000000.125 is tested separately. No continuous electrical guarantee.

1. Rerun V30 and P6 from preserved code on identical integer jobs. Keep their
   calibration and converter assumptions explicit. A separate matched-cell
   macromodel comparison uses the same pole, additive/multiplicative errors,
   quantizers, loads and timing metric for both algorithms; it is not a claim
   that their transistor counts or energy are equal.
2. Build a transistor geometric-mean cell and a positive-coefficient Padé
   readout. Test ideal-copy diagnostic level and actual transistor-mirror level.
   Electrical cell calibration uses known rational currents, never target roots.
3. Check a foundry-origin open model if usable in ngspice; retain its revision,
   license, model warnings and missing parasitic/layout limitations.
4. Development: diagonal and rational-square cell currents at 25 C. Fit gain
   and offset once; use independent currents, temperatures -20/25/85 C, supply
   +/-5%, deterministic mismatch and loads without retuning unless marked.
5. Cascade depth 1,2,4,6. Keep failed convergence, incorrect equilibria and
   unstable transients. An output that merely settles is not correct.
6. Freeze a readout policy on development cases before held-out scoring.
   Measure error over a final window and after changing input, not a favorable
   instant. Repeat representative transitions with a 4x finer timestep.
7. Measure explicit transistor supply current and energy of the defined core.
   Do not attribute behavioral source energy to a fabricated chip. Programmable
   DAC/ADC and reference costs must be timed/modelled or explicitly excluded.
   A complete digital-input/digital-output estimate must state converter and
   controller assumptions; it is not a fabricated-hardware measurement.

Targets: 100 ppm, 10 ppm, 1 ppm. Report fractional error in root-1 separately at
large p. No claim of superiority unless domain, accuracy, input/output interface
and component assumptions match. P5 is a cubic-only transistor comparator.
