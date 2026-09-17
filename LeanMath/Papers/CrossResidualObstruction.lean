import Mathlib.Tactic

namespace LeanMath.Papers.CrossResidualObstruction

/-- A perfect product residual does not certify either proportional mean. -/
theorem false_positive :
    (2:ℝ)/(1*2)=1 ∧ (1:ℝ)^3 ≠ 2 ∧ (2:ℝ)^3 ≠ 4 := by norm_num

/-- Every positive first coordinate admits a companion with perfect product. -/
theorem arbitrary_companion (x u : ℝ) (hx : 0 < x) (hu : 0 < u) :
    0 < x/u ∧ x/(u*(x/u))=1 := by
  constructor
  · exact div_pos hx hu
  · field_simp

/-- Reciprocal updates preserve the product regardless of proximity to a root. -/
theorem reciprocal_update_product (u w c : ℝ) (hc : c ≠ 0) :
    (u*c)*(w/c)=u*w := by field_simp

/-- The ordinary power residual is recovered only with a coherence condition. -/
theorem coherent_residual (x u w : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (hw : w=u^(p-1)) : x/(u*w)=x/u^p := by
  rw [hw,← pow_succ']
  congr 2
  omega

end LeanMath.Papers.CrossResidualObstruction
