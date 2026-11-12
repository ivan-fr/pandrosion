import LeanMath.Papers.NestedRadicalReal
import LeanMath.Papers.DecenteredArcGlobal
import LeanMath.Papers.DegreesEfficiency

/-! # Rational degrees for the two radical iterations (Proposition 4.5)

This module connects `DegreesEfficiency.rational_degree_convergence` with the global convergence
theorems `NestedRadicalReal.global_convergence` and `DecenteredArcGlobal.global_convergence`, so that
the statements for rational degrees carry no hypothesis. -/

noncomputable section
namespace LeanMath.Papers.DegreesNested
open Real Filter Function
open scoped Topology
open LeanMath.Papers.NestedRadicalReal LeanMath.Papers.DegreesEfficiency

/-- With an integer degree the residual of the nested-radical step uses an integer power only. -/
theorem step_natCast (μ : ℕ) (Y u : ℝ) :
    step (μ : ℝ) Y u = u * correction (μ : ℝ) (Y / u ^ μ) := by
  unfold step
  rw [Real.rpow_natCast]

/-- Proposition 4.5 (i) for the nested-radical support. For a rational degree `p = μ / ν` with
`μ ≥ 3`, the nested-radical iteration of integer degree `μ`, run on the input `X ^ ν`, converges to
`X ^ (1 / p)` from every positive start. -/
theorem rational_degree_nested {X u : ℝ} (hX : 0 < X) (hu : 0 < u) {μ : ℕ} (hμ : 3 ≤ μ) (ν : ℕ) :
    Tendsto (fun n : ℕ => (step (μ : ℝ) (X ^ ν))^[n] u) atTop
      (𝓝 (X ^ ((1 : ℝ) / ((μ : ℝ) / ν)))) :=
  rational_degree_convergence step
    (fun p X u hp hX hu => global_convergence p X u hp hX hu) hX hu hμ ν

/-- The same statement with the iteration written with integer powers. -/
theorem rational_degree_nested_integer_powers {X u : ℝ} (hX : 0 < X) (hu : 0 < u) {μ : ℕ}
    (hμ : 3 ≤ μ) (ν : ℕ) :
    Tendsto (fun n : ℕ => (fun v : ℝ => v * correction (μ : ℝ) (X ^ ν / v ^ μ))^[n] u) atTop
      (𝓝 (X ^ ((1 : ℝ) / ((μ : ℝ) / ν)))) := by
  have h := rational_degree_nested hX hu hμ ν
  have e : step (μ : ℝ) (X ^ ν) = fun v : ℝ => v * correction (μ : ℝ) (X ^ ν / v ^ μ) := by
    funext v
    exact step_natCast μ (X ^ ν) v
  rwa [e] at h

/-- Proposition 4.5 (i) for the decentered arc: for a rational degree `p = μ / ν` with `μ ≥ 3`, the
decentered-arc iteration of integer degree `μ`, run on the input `X ^ ν`, converges to `X ^ (1 / p)`
from every positive start. -/
theorem rational_degree_arc {X u : ℝ} (hX : 0 < X) (hu : 0 < u) {μ : ℕ} (hμ : 3 ≤ μ) (ν : ℕ) :
    Tendsto (fun n : ℕ => (DecenteredArcGlobal.step (μ : ℝ) (X ^ ν))^[n] u) atTop
      (𝓝 (X ^ ((1 : ℝ) / ((μ : ℝ) / ν)))) :=
  rational_degree_convergence DecenteredArcGlobal.step
    (fun p X u hp hX hu => DecenteredArcGlobal.global_convergence p X u hp hX hu) hX hu hμ ν

/-- With an integer degree the residual of the decentered-arc step uses an integer power only. -/
theorem arc_step_natCast (μ : ℕ) (Y u : ℝ) :
    DecenteredArcGlobal.step (μ : ℝ) Y u
      = u * DecenteredArcGlobal.correction (μ : ℝ) (Y / u ^ μ) := by
  unfold DecenteredArcGlobal.step
  rw [Real.rpow_natCast]

end LeanMath.Papers.DegreesNested
