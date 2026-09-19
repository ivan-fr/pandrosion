# Pandrosion Geometry and Analog Root Computation — V30

A ten-page English research preprint on the centered binary-power AD prototype.
The paper distinguishes exact arithmetic, finite-case behavioral simulation and
unimplemented physical circuitry. V17 and V20 remain unchanged.

## Build and check

From the repository root, with Tectonic or latexmk installed:

```sh
python3 paper/pandrosion_analog_v30/check_results.py
bash paper/pandrosion_analog_v30/build.sh
```

Output: `Pandrosion_Geometry_Analog_V30.pdf` in this directory. The checker uses
only the Python standard library. Included figures make PDF compilation
independent of ngspice and plotting libraries.

The underlying experiment snapshot is commit `e954910`. The research directory
contains its own reproduction commands and assumptions. Repeating simulations
is distinct from compiling the article. Selected reported errors are rounded
upward to the displayed precision (e.g. 0.652306... ppm as 0.653 ppm).

## Provenance

- `figures/fast_geometry.pdf`: binary multiplication by parallels, the p=13 schedule and its AD report. Reproduce with `python3 paper/pandrosion_analog_v30/draw_fast_geometry.py` (NumPy and Matplotlib). The script verifies the intersections and outputs `fast_geometry_checks.json`.
- Architecture: editable TikZ in `main.tex`.
- Precision comparison and timing frontier: exact copies of the research plots;
  the result checker verifies their byte identity.
- `check_results.py`: checks retained counts, error summaries, schedules, controller
  outcomes and plot provenance; it is not an independent hardware validation.
- `main.tex`: complete article, mathematics, tables and bibliography.

The six-declaration Lean audit was rerun while preparing V30. The full PDF was
rendered and visually inspected. No new transistor-level or physical validation
was performed for the manuscript.
