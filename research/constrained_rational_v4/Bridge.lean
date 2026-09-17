import Mathlib
namespace PandrosionBridge

/-- Necessary inequalities used by the concrete Farkas matrices. -/
theorem sample_relaxation (a y u q f lo hi E : ℝ) (hq : 0 < q)
    (hlo : lo ≤ f) (hhi : f ≤ hi)
    (hr : (a*y*q+a*y^3*u)/q ≤ f)
    (he : f-(a*y*q+a*y^3*u)/q ≤ E) :
    a*y^3*u+(a*y-hi)*(q-1) ≤ hi-a*y ∧
    -a*y^3*u+(lo-E-a*y)*(q-1) ≤ E+a*y-lo := by
  have hu := (div_le_iff₀ hq).mp (hr.trans hhi)
  have hl : lo-E ≤ (a*y*q+a*y^3*u)/q := by linarith
  have hl' := (le_div_iff₀ hq).mp hl
  constructor <;> nlinarith

/-- The [1/1] envelope reduction is algebraic, independently of the target. -/
theorem envelope_iff (a y A h theta : ℝ) (ha : 0 < a) (hy : 0 < y)
    (hq : 0 < 1-theta*y^2) :
    a*y + (a*y^3*A)/(1-theta*y^2) ≤ a*y+a*y^3*h ↔
    A ≤ h*(1-theta*y^2) := by
  have hc : 0 < a*y^3 := mul_pos ha (pow_pos hy 3)
  rw [add_le_add_iff_left, div_le_iff₀ hq]
  simpa only [mul_assoc] using (mul_le_mul_iff_right₀ hc (b := A) (c := h*(1-theta*y^2)))

/-- With a positive denominator, increasing A improves the approximant pointwise. -/
theorem monotone_parameter (a y A B q : ℝ) (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hq : 0 < q) (hAB : A ≤ B) :
    a*y+(a*y^3*A)/q ≤ a*y+(a*y^3*B)/q := by
  apply add_le_add_right
  apply (div_le_div_iff_of_pos_right hq).mpr
  exact mul_le_mul_of_nonneg_left hAB (mul_nonneg ha (pow_nonneg hy 3))

#print axioms sample_relaxation
#print axioms envelope_iff
#print axioms monotone_parameter
end PandrosionBridge
