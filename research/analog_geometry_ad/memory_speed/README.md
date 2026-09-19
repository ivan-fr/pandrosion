# Memory and acquisition study

[Results, including failures](RESULTS.md) · [Protocol](PROTOCOL.md) · [Circuit model](memory_model.png) · [Precision–time plot](memory_results.png)

The continuation records 649 completed circuit transients. A 33 nF memory, geometric AD feedback and eight-readout average complete the separate final 64-case set at 1 ppm in 5.035 ms, versus 9.585 ms for the finite-driver 100 nF control. An additional nominal error/noise corner reaches 1.287 ppm, so this is a faster candidate with limited precision margin, not an established all-nominal-case speedup at 1 ppm.

The code retains the exact AD map and binary-power stage. Smaller storage capacitors pay increased sampling noise and charge sensitivity; both memory drivers have finite current. The report keeps the first-stage misses, the separate refinement and new validation, and the additional diagnostic failure. These behavioral models do not characterize silicon energy, area or yield.
