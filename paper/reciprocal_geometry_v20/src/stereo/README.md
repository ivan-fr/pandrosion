# Fixed circle on the sphere — V19

The new preview uses the same scale in both planar coordinates: ξ=(x−1)/2 and η=(y−2)/2. This preserves the Euclidean circle before inverse stereographic projection. Independent width/height normalization would turn it into an ellipse.

`model.py` retains homogeneous incidence vectors. It computes joins/intersections by cross products, solves the line/circle intersection in the plane, and selects the branch with R′(v)<0. It then maps the results to the sphere. The sphere never serves as the incidence engine: all directions at infinity have the same spherical image N.

The fixed circle has sphere-plane equation −2hX−2jY+(1−c)Z+(1+c)=0, where c=h²+j²−r² in normalized coordinates. It excludes N. Every line maps to a circle through N. The ten theorems in `RectangleFixedCircleStereo.lean` certify these identities, scaling, inverse projection and similarity; they do not certify the rendering code or all exceptional projective sequences.

The new model checks 75 regular configurations and three explicit infinity cases: initial center V (s=1), final center U (t=31/4 for p=3), and fixed center F2 (X=113/10 for p=3). The numerical discrepancies and residuals are in `verification.json`. Physical parallel construction costs are not equated with an ordinary finite-point join.

The V19 paper is rewritten from the V18 record, rather than appended to it. It retains the important numerical/geometry results, adds the fixed-circle construction and sphere certificates, and removes accumulated version history and unrelated performance details from the main narrative. The older V18 package remains unchanged.
