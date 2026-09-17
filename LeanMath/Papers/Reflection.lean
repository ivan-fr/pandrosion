import LeanMath.Papers.ExponentialFamily

noncomputable section
namespace LeanMath.Papers.ExponentialFamily
open Real Set MeasureTheory ProbabilityTheory

def reflected (ν : Measure ℝ) := ν.map (fun k : ℝ => -k)

/-- Exponent reflection exchanges x and -x for an arbitrary measure. -/
theorem reflection_identity (ν : Measure ℝ) (x : ℝ) : g (reflected ν) x=g ν (-x) := by
  unfold g cgf reflected mgf
  rw [integral_map (by fun_prop) (by fun_prop)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with k
  simp only [id_eq]
  congr 1
  ring

/-- Every derivative, and hence every cumulant, has the expected parity. -/
theorem reflection_derivatives (ν : Measure ℝ) (x : ℝ) (j : ℕ) :
    iteratedDeriv j (g (reflected ν)) x = (-1:ℝ)^j * iteratedDeriv j (g ν) (-x) := by
  have he : g (reflected ν)=(fun x => g ν (-x)) := funext (reflection_identity ν)
  rw [he,iteratedDeriv_comp_neg]
  rfl

end LeanMath.Papers.ExponentialFamily
