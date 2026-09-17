import LeanMath.Papers.ExtremalBracket

noncomputable section
namespace LeanMath.Papers.Extremal
open Real MeasureTheory Set

/-- Jensen's upper bound remains valid for negative displacements and residuals. -/
theorem negative_upper (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m n μ h z : ℝ) (hμ : 0 < μ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hmean : (∫ k, k ∂ν)=μ) (hmoment : (∫ k, exp (k*z) ∂ν)=exp h) :
    z ≤ h/μ := by
  obtain ⟨hi,he⟩ := support_integrable ν m n z hs
  have hj := exp_mean_le_mgf ν z hi he
  rw [hmean,hmoment] at hj
  exact (le_div_iff₀ hμ).mpr (by simpa [mul_comm] using exp_le_exp.mp hj)

/-- The lower support endpoint bounds the negative displacement if m>0. -/
theorem negative_lower (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m n h z : ℝ) (hm : 0 < m) (hz : z < 0)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hmoment : (∫ k, exp (k*z) ∂ν)=exp h) :
    h/m ≤ z := by
  have he := (support_integrable ν m n z hs).2
  have hi : (∫ k, exp (k*z) ∂ν) ≤ ∫ _ : ℝ, exp (m*z) ∂ν := by
    apply integral_mono_ae he (integrable_const _)
    filter_upwards [hs] with k hk
    exact exp_le_exp.mpr (mul_le_mul_of_nonpos_right hk.1 hz.le)
  rw [hmoment] at hi
  simp at hi
  exact (div_le_iff₀ hm).mpr (by simpa [mul_comm] using hi)

/-- The negative-residual part of Beyond Monomials 4.2, with no optimality claim. -/
theorem negative_bracket_bounded (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m n μ h z : ℝ) (hμ : 0 < μ) (hh : h < 0) (hz : z < 0)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hmean : (∫ k, k ∂ν)=μ) (hmoment : (∫ k, exp (k*z) ∂ν)=exp h) :
    z ≤ h/μ ∧ h/μ < 0 ∧ (0 < m → h/m ≤ z) := by
  exact ⟨negative_upper ν m n μ h z hμ hs hmean hmoment,
    div_neg_of_neg_of_pos hh hμ,fun hm => negative_lower ν m n h z hm hz hs hmoment⟩

end LeanMath.Papers.Extremal
