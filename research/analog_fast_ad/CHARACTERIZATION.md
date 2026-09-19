# Behavioral accuracy characterization

Reproduce with `python research/analog_fast_ad/characterize.py`. Fixed seed: 20260919; 512 synthetic devices per case, six iterations, temperatures −20/25/85 °C. The same static mismatch draws are retained across iterations and temperatures. These are assumed distributions, not foundry statistics or measured yields.

## Joint errors

| p | X | Profile | °C | Median relative error | 99th percentile | Largest observed | Invalid |
|---:|---:|:---|---:|---:|---:|---:|---:|
| 3 | 2 | untrimmed | -20 | 0.000159 | 0.000467 | 0.000531 | 0 |
| 3 | 2 | untrimmed | 25 | 0.00014 | 0.000402 | 0.000442 | 0 |
| 3 | 2 | untrimmed | 85 | 0.000167 | 0.000591 | 0.00064 | 0 |
| 3 | 2 | trim_target | -20 | 2.82e-06 | 8.4e-06 | 1e-05 | 0 |
| 3 | 2 | trim_target | 25 | 2.79e-06 | 6.8e-06 | 8e-06 | 0 |
| 3 | 2 | trim_target | 85 | 2.82e-06 | 8.8e-06 | 1.04e-05 | 0 |
| 3 | 500000 | untrimmed | -20 | 0.000142 | 0.000433 | 0.000503 | 0 |
| 3 | 500000 | untrimmed | 25 | 0.000134 | 0.000383 | 0.000409 | 0 |
| 3 | 500000 | untrimmed | 85 | 0.000147 | 0.000546 | 0.000604 | 0 |
| 3 | 500000 | trim_target | -20 | 2.8e-06 | 7.14e-06 | 8.72e-06 | 0 |
| 3 | 500000 | trim_target | 25 | 2.72e-06 | 6.35e-06 | 7.14e-06 | 0 |
| 3 | 500000 | trim_target | 85 | 2.72e-06 | 8.32e-06 | 9.51e-06 | 0 |
| 3 | 1e+300 | untrimmed | -20 | 7.85e-05 | 0.000235 | 0.000264 | 0 |
| 3 | 1e+300 | untrimmed | 25 | 7.33e-05 | 0.000217 | 0.000229 | 0 |
| 3 | 1e+300 | untrimmed | 85 | 0.000107 | 0.000361 | 0.000433 | 0 |
| 3 | 1e+300 | trim_target | -20 | 1.58e-06 | 4.48e-06 | 5.21e-06 | 0 |
| 3 | 1e+300 | trim_target | 25 | 1.33e-06 | 4.12e-06 | 4.48e-06 | 0 |
| 3 | 1e+300 | trim_target | 85 | 1.94e-06 | 5.94e-06 | 6.78e-06 | 0 |
| 32 | 2 | untrimmed | -20 | 2.45e-05 | 5.66e-05 | 6.11e-05 | 0 |
| 32 | 2 | untrimmed | 25 | 2.53e-05 | 5.09e-05 | 5.48e-05 | 0 |
| 32 | 2 | untrimmed | 85 | 2.65e-05 | 6.5e-05 | 7.42e-05 | 0 |
| 32 | 2 | trim_target | -20 | 2.35e-07 | 7.49e-07 | 8.44e-07 | 0 |
| 32 | 2 | trim_target | 25 | 2.22e-07 | 6.92e-07 | 6.92e-07 | 0 |
| 32 | 2 | trim_target | 85 | 2.65e-07 | 8.71e-07 | 9.96e-07 | 0 |
| 32 | 500000 | untrimmed | -20 | 1.39e-05 | 2.98e-05 | 3.17e-05 | 0 |
| 32 | 500000 | untrimmed | 25 | 1.39e-05 | 2.74e-05 | 2.88e-05 | 0 |
| 32 | 500000 | untrimmed | 85 | 1.46e-05 | 3.9e-05 | 4.48e-05 | 0 |
| 32 | 500000 | trim_target | -20 | 1.53e-07 | 4.24e-07 | 4.55e-07 | 0 |
| 32 | 500000 | trim_target | 25 | 1.36e-07 | 3.91e-07 | 4.24e-07 | 0 |
| 32 | 500000 | trim_target | 85 | 1.79e-07 | 5.68e-07 | 6.36e-07 | 0 |
| 32 | 1e+300 | untrimmed | -20 | 1.55e-06 | 4.89e-06 | 6.79e-06 | 0 |
| 32 | 1e+300 | untrimmed | 25 | 1.32e-06 | 4.41e-06 | 5.84e-06 | 0 |
| 32 | 1e+300 | untrimmed | 85 | 8e-06 | 1.75e-05 | 2.11e-05 | 0 |
| 32 | 1e+300 | trim_target | -20 | 5.39e-08 | 1.85e-07 | 2.63e-07 | 0 |
| 32 | 1e+300 | trim_target | 25 | 5.39e-08 | 1.73e-07 | 2.33e-07 | 0 |
| 32 | 1e+300 | trim_target | 85 | 9.52e-08 | 3.31e-07 | 4.12e-07 | 0 |
| 1000000 | 2 | untrimmed | -20 | 3.48e-09 | 4.42e-09 | 4.74e-09 | 0 |
| 1000000 | 2 | untrimmed | 25 | 3.47e-09 | 4.32e-09 | 4.44e-09 | 0 |
| 1000000 | 2 | untrimmed | 85 | 3.47e-09 | 4.91e-09 | 5.19e-09 | 0 |
| 1000000 | 2 | trim_target | -20 | 1.79e-11 | 3.89e-11 | 4.36e-11 | 0 |
| 1000000 | 2 | trim_target | 25 | 1.69e-11 | 3.7e-11 | 3.89e-11 | 0 |
| 1000000 | 2 | trim_target | 85 | 1.74e-11 | 4.46e-11 | 4.84e-11 | 0 |
| 1000000 | 500000 | untrimmed | -20 | 1.21e-09 | 1.68e-09 | 1.93e-09 | 0 |
| 1000000 | 500000 | untrimmed | 25 | 1.21e-09 | 1.6e-09 | 1.67e-09 | 0 |
| 1000000 | 500000 | untrimmed | 85 | 1.23e-09 | 2e-09 | 2.14e-09 | 0 |
| 1000000 | 500000 | trim_target | -20 | 6.33e-12 | 1.96e-11 | 2.64e-11 | 0 |
| 1000000 | 500000 | trim_target | 25 | 6.33e-12 | 1.59e-11 | 1.87e-11 | 0 |
| 1000000 | 500000 | trim_target | 85 | 6.33e-12 | 1.97e-11 | 2.73e-11 | 0 |
| 1000000 | 1e+300 | untrimmed | -20 | 3.64e-10 | 6.52e-10 | 7.3e-10 | 0 |
| 1000000 | 1e+300 | untrimmed | 25 | 3.79e-10 | 5.93e-10 | 6.69e-10 | 0 |
| 1000000 | 1e+300 | untrimmed | 85 | 3.95e-10 | 1.08e-09 | 1.2e-09 | 0 |
| 1000000 | 1e+300 | trim_target | -20 | 3.08e-12 | 1.22e-11 | 1.69e-11 | 0 |
| 1000000 | 1e+300 | trim_target | 25 | 2.64e-12 | 1.03e-11 | 1.41e-11 | 0 |
| 1000000 | 1e+300 | trim_target | 85 | 4.04e-12 | 1.6e-11 | 1.98e-11 | 0 |
| 983039 | 2 | untrimmed | -20 | 5.34e-09 | 6.34e-09 | 6.47e-09 | 0 |
| 983039 | 2 | untrimmed | 25 | 5.33e-09 | 6.21e-09 | 6.32e-09 | 0 |
| 983039 | 2 | untrimmed | 85 | 5.32e-09 | 6.68e-09 | 7.05e-09 | 0 |
| 983039 | 2 | trim_target | -20 | 2.6e-11 | 4.91e-11 | 5.22e-11 | 0 |
| 983039 | 2 | trim_target | 25 | 2.6e-11 | 4.72e-11 | 5.12e-11 | 0 |
| 983039 | 2 | trim_target | 85 | 2.6e-11 | 5.39e-11 | 6.19e-11 | 0 |
| 983039 | 500000 | untrimmed | -20 | 3.53e-09 | 4.29e-09 | 4.46e-09 | 0 |
| 983039 | 500000 | untrimmed | 25 | 3.53e-09 | 4.15e-09 | 4.21e-09 | 0 |
| 983039 | 500000 | untrimmed | 85 | 3.53e-09 | 4.6e-09 | 4.86e-09 | 0 |
| 983039 | 500000 | trim_target | -20 | 1.72e-11 | 3.66e-11 | 4.34e-11 | 0 |
| 983039 | 500000 | trim_target | 25 | 1.72e-11 | 3.26e-11 | 3.47e-11 | 0 |
| 983039 | 500000 | trim_target | 85 | 1.72e-11 | 3.75e-11 | 4.15e-11 | 0 |
| 983039 | 1e+300 | untrimmed | -20 | 4.1e-09 | 4.88e-09 | 5.18e-09 | 0 |
| 983039 | 1e+300 | untrimmed | 25 | 4.09e-09 | 4.74e-09 | 4.88e-09 | 0 |
| 983039 | 1e+300 | untrimmed | 85 | 4.06e-09 | 5.31e-09 | 5.81e-09 | 0 |
| 983039 | 1e+300 | trim_target | -20 | 2.12e-11 | 4.06e-11 | 4.83e-11 | 0 |
| 983039 | 1e+300 | trim_target | 25 | 2.02e-11 | 3.67e-11 | 3.86e-11 | 0 |
| 983039 | 1e+300 | trim_target | 85 | 1.92e-11 | 4.34e-11 | 5.22e-11 | 0 |
| 3 | 1e-300 | untrimmed | -20 | 5.21e-05 | 0.000163 | 0.00018 | 0 |
| 3 | 1e-300 | untrimmed | 25 | 4.66e-05 | 0.000141 | 0.000152 | 0 |
| 3 | 1e-300 | untrimmed | 85 | 8.55e-05 | 0.000269 | 0.000336 | 0 |
| 3 | 1e-300 | trim_target | -20 | 1.03e-06 | 3.46e-06 | 4.54e-06 | 0 |
| 3 | 1e-300 | trim_target | 25 | 1.03e-06 | 2.76e-06 | 3.46e-06 | 0 |
| 3 | 1e-300 | trim_target | 85 | 1.37e-06 | 4.19e-06 | 4.54e-06 | 0 |
| 32 | 1e-300 | untrimmed | -20 | 2.14e-05 | 4.76e-05 | 5.06e-05 | 0 |
| 32 | 1e-300 | untrimmed | 25 | 2e-05 | 4.28e-05 | 4.67e-05 | 0 |
| 32 | 1e-300 | untrimmed | 85 | 2.09e-05 | 5.68e-05 | 6.37e-05 | 0 |
| 32 | 1e-300 | trim_target | -20 | 2.1e-07 | 6.35e-07 | 7.56e-07 | 0 |
| 32 | 1e-300 | trim_target | 25 | 1.85e-07 | 6.01e-07 | 6.35e-07 | 0 |
| 32 | 1e-300 | trim_target | 85 | 2.13e-07 | 7.87e-07 | 8.47e-07 | 0 |
| 983039 | 1e-300 | untrimmed | -20 | 2.92e-09 | 3.59e-09 | 3.72e-09 | 0 |
| 983039 | 1e-300 | untrimmed | 25 | 2.92e-09 | 3.45e-09 | 3.59e-09 | 0 |
| 983039 | 1e-300 | untrimmed | 85 | 2.89e-09 | 3.93e-09 | 4.26e-09 | 0 |
| 983039 | 1e-300 | trim_target | -20 | 1.44e-11 | 3.17e-11 | 3.67e-11 | 0 |
| 983039 | 1e-300 | trim_target | 25 | 1.44e-11 | 2.8e-11 | 2.99e-11 | 0 |
| 983039 | 1e-300 | trim_target | 85 | 1.44e-11 | 3.48e-11 | 4.25e-11 | 0 |
| 1000000 | 1e-300 | untrimmed | -20 | 1.98e-09 | 2.55e-09 | 2.76e-09 | 0 |
| 1000000 | 1e-300 | untrimmed | 25 | 1.98e-09 | 2.45e-09 | 2.59e-09 | 0 |
| 1000000 | 1e-300 | untrimmed | 85 | 1.98e-09 | 3.02e-09 | 3.14e-09 | 0 |
| 1000000 | 1e-300 | trim_target | -20 | 9.62e-12 | 2.58e-11 | 3.06e-11 | 0 |
| 1000000 | 1e-300 | trim_target | 25 | 9.62e-12 | 2.19e-11 | 2.68e-11 | 0 |
| 1000000 | 1e-300 | trim_target | 85 | 9.62e-12 | 2.87e-11 | 3.35e-11 | 0 |

## Isolated error sources at X=500,000 and 25 °C

Each row activates one source group only; these percentiles must not be added as an error bound.

| p | Profile | Source | 99th percentile relative error |
|---:|:---|:---|---:|
| 3 | untrimmed | arithmetic | 0.000277 |
| 3 | untrimmed | loading | 0.000116 |
| 3 | untrimmed | memory | 2.22e-05 |
| 3 | untrimmed | coefficients | 2.08e-06 |
| 3 | untrimmed | adc | 3.27e-05 |
| 3 | untrimmed | noise | 5.61e-06 |
| 3 | trim_target | arithmetic | 5.78e-06 |
| 3 | trim_target | loading | 5.8e-07 |
| 3 | trim_target | memory | 8.22e-07 |
| 3 | trim_target | coefficients | 4.35e-10 |
| 3 | trim_target | adc | 8.32e-07 |
| 3 | trim_target | noise | 1.14e-06 |
| 32 | untrimmed | arithmetic | 1.39e-05 |
| 32 | untrimmed | loading | 1.53e-05 |
| 32 | untrimmed | memory | 1.71e-06 |
| 32 | untrimmed | coefficients | 1.45e-07 |
| 32 | untrimmed | adc | 2.05e-06 |
| 32 | untrimmed | noise | 4.21e-07 |
| 32 | trim_target | arithmetic | 3.27e-07 |
| 32 | trim_target | loading | 7.63e-08 |
| 32 | trim_target | memory | 6.32e-08 |
| 32 | trim_target | coefficients | 2.65e-10 |
| 32 | trim_target | adc | 6.23e-08 |
| 32 | trim_target | noise | 8.59e-08 |
| 1000000 | untrimmed | arithmetic | 3.45e-10 |
| 1000000 | untrimmed | loading | 1.29e-09 |
| 1000000 | untrimmed | memory | 5.2e-11 |
| 1000000 | untrimmed | coefficients | 3.12e-12 |
| 1000000 | untrimmed | adc | 5.67e-11 |
| 1000000 | untrimmed | noise | 1.31e-11 |
| 1000000 | trim_target | arithmetic | 1e-11 |
| 1000000 | trim_target | loading | 6.43e-12 |
| 1000000 | trim_target | memory | 1.97e-12 |
| 1000000 | trim_target | coefficients | 1.53e-14 |
| 1000000 | trim_target | adc | 1.56e-12 |
| 1000000 | trim_target | noise | 2.68e-12 |
| 983039 | untrimmed | arithmetic | 5.91e-10 |
| 983039 | untrimmed | loading | 3.73e-09 |
| 983039 | untrimmed | memory | 5.4e-11 |
| 983039 | untrimmed | coefficients | 7.56e-12 |
| 983039 | untrimmed | adc | 7.23e-11 |
| 983039 | untrimmed | noise | 1.22e-11 |
| 983039 | trim_target | arithmetic | 1.49e-11 |
| 983039 | trim_target | loading | 1.86e-11 |
| 983039 | trim_target | memory | 2.02e-12 |
| 983039 | trim_target | coefficients | 2.71e-14 |
| 983039 | trim_target | adc | 2.19e-12 |
| 983039 | trim_target | noise | 2.49e-12 |

## Conservative state-domain allocations

For ideal q★ in [−ln 2,0], an additive state error |δ|≤D gives `relative error ≤ D/(p−ln 2−D)`. Thus `D=ε(p−ln 2)/(1+ε)` suffices. Divide this D into four equal allocations: conversion, deterministic memory, arithmetic/coefficients, and noise. Figures below apply to one allocation. They are individual necessary design targets under this allocation, not a system guarantee. Leakage and charge injection share the memory allocation; thermal noise and amplifier noise share the noise allocation.

| p | Target | Total q tolerance (V) | ADC ideal bits, ±2 V | Leakage ceiling (A), 460 µs / 10 nF | Charge ceiling (C), 10 nF | C floor (F), two kT/C samples, 3σ |
|---:|---:|---:|---:|---:|---:|---:|
| 3 | 1e-06 | 2.31e-06 | 22 | 1.25e-11 | 5.77e-15 | 2.24e-07 |
| 3 | 1e-09 | 2.31e-09 | 32 | 1.25e-14 | 5.77e-18 | 0.224 |
| 32 | 1e-06 | 3.13e-05 | 18 | 1.7e-10 | 7.83e-14 | 1.22e-09 |
| 32 | 1e-09 | 3.13e-08 | 28 | 1.7e-13 | 7.83e-17 | 0.00122 |
| 1000000 | 1e-06 | 1 | 4 | 5.43e-06 | 2.5e-09 | 1.19e-18 |
| 1000000 | 1e-09 | 0.001 | 13 | 5.43e-09 | 2.5e-12 | 1.19e-12 |
