# Generalist root testing and alternatives to a periodic clock

**A global periodic clock is not a mathematical requirement for root finding.**
It is how the present circuit separates evaluation from state storage. Removing
it changes the architecture and requires a new stability/timing argument.
This study tests those alternatives and considerably broadens input coverage.
It still concerns behavioral circuits, not a fabricated general-purpose chip.

## Three different architectures

1. **Periodic sampled AD.** Hold q, let the power/correction stages settle, sample
   the candidate, then transfer it to q. Two memories prevent unintended
   continuous feedback. The clocks preserve the interpretation as successive AD
   iterations. Our original 500 µs period is an imposed engineering choice, not
   a mathematical lower bound or an optimized maximum clock rate.
2. **State-dependent sampled AD.** A completion detector waits until every stage
   differs from its current drive by less than a threshold for a dwell interval,
   then transfers the candidate. This avoids a *fixed periodic* clock, but still
   needs sequencing, memory, threshold detection and nonoverlapping transfers.
   It is asynchronous control, not the disappearance of control circuitry.
3. **Continuous feedback.** A current source continuously drives the state
   capacitor toward the candidate. There are no sample/update clocks, but the
   circuit becomes a differential equation with internal lag. Its local
   convergence rate is a time-domain rate, not discrete AD's cubic order.

## Why continuous feedback can converge — and can also fail

In the ideal instantaneous-arithmetic limit, write

    u = 1 + q/p,   t = Y u^p,
    τ dq/dt_time = F(q) − q = 2u(1−t) / [1+t+(t−1)/p].

For p≥3, Y>0 and q>−p the denominator is positive. The right side is positive
below the unique root state and negative above it. Thus the ideal scalar ODE
moves toward the root and stays between its initial state and that root. This
is an argument for the instantaneous scalar model, **not the delayed circuit**.
At the equilibrium, the derivative of F(q)−q is exactly −1, so the local rate
is exponential with time constant τ. It is not an order-three discrete method.

Actual power-chain stages have their own states. Too-fast feedback can therefore
oscillate or hit a rail even though the scalar ideal equation is stable.
`clock_modes.py` removes the sample/hold switching from the SPICE circuit and
adds a continuous transconductance into the state capacitor. It tests state
time constants of 2, 20 and 200 µs with 1 µs arithmetic stages, across four
degrees and four values of X. Fifty-two transients include two timestep refinements and two extended
10 ms observations.
The final 10% of each trajectory must remain within 1 µV of the ideal state
for the recorded `stable_tail` criterion. This root reference is used only to
score trajectories; it is not connected to the feedback circuit.

The fast setting fails for longer chains. Extended 10 ms observations distinguish
slow convergence from persistent oscillation: at 20 µs state time constant,
p=1,000,000 eventually settles, while p=983039 still oscillates over the observed
window. This finite observation alone is not an infinite-time instability proof. The slow setting meets that tail
criterion in all 16 input cases tested. This does not prove stability for all
p,X or under noise/mismatch. The report retains the unstable trajectories,
clipping/denominator flags and actual observation durations. A stable endpoint
alone is not treated as stability proof.

## State-dependent updates

The adaptive controller is an independent first-order-stage RK4 simulation,
with an all-node 0.1 µV completion threshold sustained for 5 µs. It performs six
updates and never consults a root to decide when to update. Step-halving checks
its timing/state agreement. At X=500,000 it takes about 89–191 µs across the four
degrees tested, versus the original imposed millisecond schedule.

**This is an ideal-controller experiment:** memory transfer is instantaneous,
storage does not leak, and the detector has no noise, offset, loading or latency.
A 0.1 µV threshold is particularly demanding compared with our earlier assumed
microvolt noise. There is no claim that a physical detector achieves these
timings. The threshold is a local completion test, not itself a theorem bounding
the output-root error; the latter is scored independently.

The 196-job streaming experiment retains all 37 arithmetic-stage states across
successive jobs, changes programmed coefficients and normalization, resets only
the iteration state q, then uses the completion detector. Unused stage slots
act as ideal programmed unity-transfer cells with the same lag. It covers
logarithmic X sweeps and changes of p. All sampled outputs pass one ppm in this
noise-free model. This is a stream of **digitally submitted jobs with resets**,
not instantaneous tracking of a continuously varying analog X. Programming,
preparation and converter latency, physical bypass switches, and noisy completion
logic remain outside that experiment.

## Broad input campaign

The reproducible seed-based campaign now includes:

- 8,243 input pairs, with 4,278 distinct degrees: a low-degree grid, neighbors
  of powers of two, the longest 37-stage schedule, logarithmic X sweeps and
  5,000 independent random pairs.
- Extreme inputs down to the smallest positive binary64 subnormal and up to
  the largest finite binary64 value; values just below/above 1 are included.
- 24,729 six-step arithmetic evaluations across ideal and two static-error
  profiles. All ideal evaluations pass 1e-12 relative error. This tier does
  **not** model time, loading, ADC or thermal noise.
- 296 full ngspice transients: 148 pairs, each with both initial and tighter
  profiles. Twelve selected degrees and eleven X values form the main grid,
  supplemented by sixteen random pairs. Temperature/sign selections alternate;
  they are not a complete process/voltage/temperature Cartesian sweep.
- 196 streamed jobs, sixteen adaptive-controller cases and fifty-two continuous
  feedback transients, with their different assumptions kept explicit.

The timed campaign runs the combined-error model: port loading, finite settling,
sample/hold switching, leakage, injection, finite coefficients and ADC errors,
colored read/correction disturbances and lumped sampled thermal noise. Each
SPICE input pair is independently reset and generates its configured netlist;
this alone is not a validation of physical chip reconfiguration.

Every run and accuracy miss is exported. Neither a large sample count nor zero
range violations proves general hardware accuracy. For the tighter timed profile,
97 of 148 trials meet one ppm; only 28 meet one ppb. Low-degree failures are
therefore a visible design limitation, not a hidden exception.

## Automation and reproduction

The new `analog-generalist` CI job runs these campaigns on pull requests and
pushes to main. It retains reports and failed-case journals. There is no
unattended local background task or unbounded test run.

```sh
python research/analog_fast_ad/generalist_campaign.py
python research/analog_fast_ad/generalist_spice.py --workers 2
python research/analog_fast_ad/clock_modes.py
python research/analog_fast_ad/streaming_campaign.py
python research/analog_fast_ad/generalist_report.py
```

`generalist_spice.py --quick` is a small local smoke option; the dedicated CI
job runs the full matrix. Accuracy-target misses are reported separately from
execution/range checks. Continuous-loop instabilities are expected discoveries
and remain in the output rather than being discarded to make tests look green.

The supported scope remains integer **3≤p≤1,000,000** and positive finite
binary64 X. p=1, p=2, noninteger degrees, negative inputs and unbounded integers
are not claimed as implemented. A general programmable prototype is not the
same as a universal, uniformly accurate physical root calculator.
