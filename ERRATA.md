# V19 erratum, corrected in V20

In the projective AD discussion, the factorization for `F4(s)/s - 1` must read

```text
(1 - t) ((p + 1)t + 5p - 1) / D4(t).
```

The V19 expression `(p + 1)(1 - t)(t + 2p - 1) / D4(t)` is incorrect. The existing Lean theorem `RectangleProjective.numerator_difference` already contains the correct factorization; no proof source change was needed. V20 and `src/revision/verify.py` use the corrected expression. The sign argument and resulting convergence conclusion are unchanged.

The archived V19 PDF and its original validation records are retained unchanged. Use [V20](paper/reciprocal_geometry_v20/Reciprocal_Root_Geometry_v20.pdf) for the corrected manuscript, uniform circle preparation, explicit exceptional cases and expanded bibliography.
