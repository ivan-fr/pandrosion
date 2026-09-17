import LeanMath.Papers.CrossResidualObstruction

namespace LeanMath.Papers.CoupledPowers

theorem normalized_reversal (r : ℝ) (hr : 0 < r) (p j : ℕ) (hj : j ≤ p) :
    r^(p-j)/r^p = (r^j)⁻¹ := by
  have he : r^p = r^(p-j)*r^j := by rw [← pow_add,Nat.sub_add_cancel hj]
  rw [he]
  field_simp

theorem complementary_readout (r : ℝ) (hr : 0 < r) (p j : ℕ) (hj : j ≤ p) :
    r^p/r^(p-j) = r^j := by
  have he : r^p = r^(p-j)*r^j := by rw [← pow_add,Nat.sub_add_cancel hj]
  rw [he]
  field_simp

theorem coherence_preserved (u w c : ℝ) (p : ℕ) (hw : w=u^(p-1)) :
    w*c^(p-1)=(u*c)^(p-1) := by rw [hw,mul_pow]

/-- The exact recurrence preserves a preexisting defect; it does not repair it. -/
theorem defect_preserved (u w c : ℝ) (hu : 0 < u) (hc : 0 < c) (p : ℕ) :
    (w*c^(p-1))/(u*c)^(p-1)=w/u^(p-1) := by
  rw [mul_pow]
  field_simp

theorem pair_residual_update (X u w c : ℝ) (p : ℕ) (hp : 1 ≤ p) :
    X/((u*c)*(w*c^(p-1)))=(X/(u*w))/c^p := by
  rw [div_div]
  congr 1
  have he : c*c^(p-1)=c^p := by rw [← pow_succ']; congr 1; omega
  calc (u*c)*(w*c^(p-1))=(u*w)*(c*c^(p-1)) := by ring
       _ = (u*w)*c^p := by rw [he]

theorem residual_ratio_is_defect (X u w : ℝ) (hX : 0 < X) (hu : 0 < u)
    (hw : 0 < w) (p : ℕ) (hp : 1 ≤ p) :
    (X/u^p)/(X/(u*w))=w/u^(p-1) := by
  have he : u^p=u*u^(p-1) := by rw [← pow_succ']; congr 1; omega
  rw [he]
  field_simp

/-- Perfect cross-residual convergence with an incorrect invariant has a biased root. -/
theorem biased_fixed_equation (X u w eta : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (hw : w=eta*u^(p-1)) (hproduct : u*w=X) : eta*u^p=X := by
  rw [hw] at hproduct
  have he : u*u^(p-1)=u^p := by rw [← pow_succ']; congr 1; omega
  calc eta*u^p=eta*(u*u^(p-1)) := by rw [he]
       _ = u*(eta*u^(p-1)) := by ring
       _ = X := hproduct

end LeanMath.Papers.CoupledPowers
