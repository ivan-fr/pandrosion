import LeanMath.Papers.Corrections

/-! The constraints used to refute sharpness are realized by an actual law. -/
noncomputable section
namespace LeanMath.Papers
open MeasureTheory Real

def exampleLaw : Measure ℝ :=
  (1/2 : ENNReal) • Measure.dirac 1 + (1/2 : ENNReal) • Measure.dirac 3

instance exampleLaw_probability : IsProbabilityMeasure exampleLaw := by
  constructor
  simpa [exampleLaw] using ENNReal.add_halves 1

theorem exampleLaw_supported : ∀ᵐ k ∂exampleLaw, (1:ℝ) ≤ k ∧ k ≤ 3 := by
  rw [exampleLaw, ae_add_measure_iff]
  constructor <;> apply Measure.ae_smul_measure <;> simp

theorem exampleLaw_integral (f : ℝ → ℝ) :
    (∫ k, f k ∂exampleLaw) = (f 1 + f 3)/2 := by
  unfold exampleLaw
  rw [integral_add_measure ((integrable_dirac (by simp)).smul_measure (by norm_num))
    ((integrable_dirac (by simp)).smul_measure (by norm_num))]
  simp only [integral_smul_measure, integral_dirac]
  norm_num
  ring

theorem exampleLaw_mean : (∫ k, k ∂exampleLaw) = 2 := by
  rw [exampleLaw_integral]
  norm_num

theorem exampleLaw_moment : (∫ k, exp (k * log 2) ∂exampleLaw) = 5 := by
  rw [exampleLaw_integral]
  rw [show (3:ℝ)*log 2 = log 2+log 2+log 2 by ring, exp_add, exp_add]
  simp only [one_mul, exp_log (by norm_num : (0:ℝ)<2)]
  norm_num

theorem exampleLaw_certificate :
    log (5:ℝ)/3 < log 2 ∧ log 2 ≤ log 2 ∧ log 2 ≤ log 5/2 :=
  old_optimality_refuted exampleLaw (log 2) exampleLaw_supported
    exampleLaw_mean exampleLaw_moment

end LeanMath.Papers
