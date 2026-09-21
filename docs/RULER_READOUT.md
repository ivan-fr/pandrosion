# Reading the constructed root with a ruler

The main result is the measured length of **AR**, rounded to the nearest
millimetre (0.1 cm). The root estimate below it is obtained by dividing that
rounded length by the physical reference length **AU**. The reference is one
quarter of the rectangle height: 1 cm for a 4 × 2 cm rectangle, 10 cm for a
40 × 20 cm rectangle. Dimensions are listed as height × width.

For example, after convergence for the cube root of 2, the smaller drawing reads
**1.3 cm**, giving approximately **1.3**. The larger drawing reads **12.6 cm**,
giving approximately **1.26**. Changing paper size scales the entire construction;
it does not advance or reset the iteration.

## Segment construction

The rectangle carries the reciprocal state at P. The direct root therefore
needs an additional construction before it can be measured:

1. Put U on the upper rail to the right of A with AU = H/4.
2. On ray AB, put D with AD = c AB, where c is the existing calibration factor.
3. The parallel to DU through B meets the upper rail at I.
4. The parallel to PI through B meets the upper rail at R.
5. Measure the endpoint distance AR and round it to 1 mm.

Similar triangles give AI = AU/c and AR = AI/s. These identities explain the
construction; the displayed length is obtained from the endpoint distance.
`constructRulerSegment` uses homogeneous joins and intersections with parallels.
It never reads the scalar state, correction formula, or reference root to place R.
`measureWithRuler` accepts only segment endpoints, reference endpoints and paper
scale. The detailed diagram uses its own point names, including D, I and R.

In the automatic workflow, the result at step zero measures the prepared P.
Each iteration adopts the constructed P⁺, then the ruler measures that new P.
In manual exploration, it measures P⁺ once that point has been constructed.

## Precision and scope

Only the **final ruler reading** is quantized. Line/circle intersections and
calibration still use floating-point coordinates; drawing errors, finite stroke
width, ruler manufacturing error and error accumulated during manual construction
are not simulated. A stable ruler reading does not prove convergence. Internal
diagnostic values remain available inside the advanced panel.

The screen preview is fitted to its container, not physically calibrated to a
real ruler. Dense tick marks may be skipped on screen for long segments; the
reading always retains the same 1 mm graduation. The rounding interval used in
tests covers half a millimetre on either side of the measured length and does
not certify the mathematical root or physical construction accuracy.

Run `npm run test:ruler` for incidence, scalar-independence and measurement tests,
and `npm run test:browser` for iteration, paper-size and stage-visibility checks.
