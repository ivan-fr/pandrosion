import LeanMath.Papers.RectangleFixedCircleDynamics

/-! Theorem 4.3 in residual coordinates, with the explicit band in the manuscript. -/
noncomputable section
namespace LeanMath.Papers.RectangleFixedCircleTheorem43
open LeanMath.Papers.RectangleFixedCircle LeanMath.Papers.RectangleFixedCircleBranch
open LeanMath.Papers.RectangleFixedCircleUniform LeanMath.Papers.RectangleFixedCircleDynamics
open Set Filter Function
open scoped Topology

/-- The discriminant endpoints (`r p = 2 sqrt(3(p²-1))`). -/
def tauMinus (p : ℝ) := (7*p^2-4-2*p*r p)/(p^2-4)
def tauPlus (p : ℝ) := (7*p^2-4+2*p*r p)/(p^2-4)

theorem r_eq_two_sqrt (p : ℝ) (hp : 2 < p) : r p=2*Real.sqrt (3*(p^2-1)) := by
  have hs : 0≤3*(p^2-1) := by nlinarith
  have hsq := Real.sq_sqrt hs
  have hr := r_sq p (by linarith)
  have hr0 := r_nonneg p
  have hs0 := Real.sqrt_nonneg (3*(p^2-1))
  nlinarith

theorem endpoint_residual (p : ℝ) (hp : 2 < p) : N p (vplus p)/D p (vplus p)=tauMinus p := by
  have hB : p^2-4≠0 := by nlinarith
  have hD := (positive_quadratics p (vplus p) hp).2.ne'
  have hV : vplus p=(p^2+2+r p)/(p^2-4) := by
    unfold vplus uplus; field_simp [hB]; ring
  unfold tauMinus
  apply (div_eq_div_iff hD hB).mpr
  rw [hV]
  unfold N D A B C
  field_simp [hB]
  linear_combination (2*p*(p+2)*(3*p^2+p*r p+6*p+r p-6))*(r_sq p (by linarith))

theorem tau_reciprocal (p : ℝ) (hp : 2 < p) : tauMinus p*tauPlus p=1 := by
  have hB : p^2-4≠0 := by nlinarith
  unfold tauMinus tauPlus
  field_simp [hB]
  linear_combination (-4*p^2)*(r_sq p (by linarith))

theorem tau_bounds (p : ℝ) (hp : 2 < p) : 0 < tauMinus p ∧ tauMinus p < 1 ∧ 1 < tauPlus p := by
  have hv := vplus_gt_one p hp
  have hN := (positive_quadratics p (vplus p) hp).1
  have hD := (positive_quadratics p (vplus p) hp).2
  have ht0 : 0 < tauMinus p := by rw [← endpoint_residual p hp]; exact div_pos hN hD
  have ht1 : tauMinus p < 1 := by
    rw [← endpoint_residual p hp, div_lt_one hD]
    have he : D p (vplus p)-N p (vplus p)=6*p*((vplus p)^2-1) := by
      unfold D N A B C; ring
    have hv2 : 0 < (vplus p)^2-1 := by nlinarith
    have : 0 < 6*p*((vplus p)^2-1) := by positivity
    linarith
  have hprod := tau_reciprocal p hp
  have hplus : 0 < tauPlus p := by nlinarith
  exact ⟨ht0, ht1, by nlinarith⟩

theorem radius_eq (p : ℝ) (hp : 2 < p) : radius p=Real.log (tauPlus p)/p := by
  have hb := tau_bounds p hp
  have he : tauMinus p=1/tauPlus p := (eq_div_iff (by linarith)).mpr (tau_reciprocal p hp)
  unfold radius
  rw [input_eq_log_residual p (vplus p) hp, endpoint_residual p hp, he]
  simp only [one_div, Real.log_inv, neg_div, neg_neg]

theorem error_band_iff (p t : ℝ) (hp : 2 < p) (ht : 0 < t) :
    Real.log t/p ∈ errors p ↔ tauMinus p≤t ∧ t≤tauPlus p := by
  have hb := tau_bounds p hp
  have hp0 : 0 < p := by linarith
  have he : tauMinus p=1/tauPlus p := (eq_div_iff (by linarith [hb.2.2])).mpr (tau_reciprocal p hp)
  have hl : Real.log (tauMinus p) = -Real.log (tauPlus p) := by
    rw [he]; simp only [one_div, Real.log_inv]
  change -radius p≤Real.log t/p ∧ Real.log t/p≤radius p ↔ _
  rw [radius_eq p hp, ← neg_div, ← hl, div_le_div_iff_of_pos_right hp0,
    div_le_div_iff_of_pos_right hp0, Real.log_le_log_iff hb.1 ht,
    Real.log_le_log_iff ht (by linarith [hb.2.2])]

theorem open_error_band_iff (p t : ℝ) (hp : 2 < p) (ht : 0 < t) :
    |Real.log t/p| < radius p ↔ tauMinus p < t ∧ t < tauPlus p := by
  have hb := tau_bounds p hp
  have hp0 : 0 < p := by linarith
  have he : tauMinus p=1/tauPlus p := (eq_div_iff (by linarith [hb.2.2])).mpr (tau_reciprocal p hp)
  have hl : Real.log (tauMinus p) = -Real.log (tauPlus p) := by
    rw [he]; simp only [one_div, Real.log_inv]
  rw [abs_lt, radius_eq p hp, ← neg_div, ← hl, div_lt_div_iff_of_pos_right hp0,
    div_lt_div_iff_of_pos_right hp0, Real.log_lt_log_iff hb.1 ht,
    Real.log_lt_log_iff ht (by linarith [hb.2.2])]

/-- The abstractly selected correction solves the original inverse Padé equation. -/
theorem correction_residual (p : ℝ) (hp : 2 < p) (e : errors p) :
    N p (correction p hp e)/D p (correction p hp e)=Real.exp (p*(e : ℝ)) := by
  have hi := correction_input p hp e
  rw [input_eq_log_residual p _ hp] at hi
  have hlog : Real.log (N p (correction p hp e)/D p (correction p hp e))=p*(e : ℝ) := by
    have hp0 : p≠0 := by linarith
    exact (div_eq_iff hp0).mp hi |>.trans (mul_comm _ _)
  have hpos := div_pos (positive_quadratics p (correction p hp e) hp).1
    (positive_quadratics p (correction p hp e) hp).2
  rw [← hlog, Real.exp_log hpos]

/-- Existence and uniqueness on the selected branch, for every admissible residual. -/
theorem unique_correction (p t : ℝ) (hp : 2 < p) (ht : 0 < t)
    (hband : tauMinus p≤t ∧ t≤tauPlus p) :
    ∃! v : ℝ, v ∈ parameters p ∧ N p v/D p v=t := by
  let e : errors p := ⟨Real.log t/p, (error_band_iff p t hp ht).mpr hband⟩
  let v := correction p hp e
  have hv : N p v/D p v=t := by
    rw [correction_residual]
    change Real.exp (p*(Real.log t/p))=t
    have hp0 : p≠0 := by linarith
    rw [mul_div_cancel₀ _ hp0, Real.exp_log ht]
  refine ⟨v, ⟨v.property, hv⟩, ?_⟩
  intro w hw
  apply (input_strictAnti p hp).injOn hw.1 v.property
  rw [input_eq_log_residual p w hp, input_eq_log_residual p v hp, hw.2, hv]

/-- Theorem 4.3: signs, strict error reduction, invariant open band and convergence.
The local order is supplied by `inverse_order_five` and its nonzero coefficient. -/
theorem theorem_4_3 (p t : ℝ) (hp : 2 < p) (ht : 0 < t)
    (hband : tauMinus p < t ∧ t < tauPlus p) :
    ∃ e : errors p, (e : ℝ)=Real.log t/p ∧
      (t≠1 → (e : ℝ)*(step p hp e : ℝ) < 0 ∧ |(step p hp e : ℝ)| < |(e : ℝ)|) ∧
      (∀ n : ℕ, |((step p hp)^[n] e : ℝ)| < radius p) ∧
      Tendsto (fun n : ℕ => ((step p hp)^[n] e : ℝ)) atTop (𝓝 0) := by
  let e : errors p := ⟨Real.log t/p, (error_band_iff p t hp ht).mpr ⟨hband.1.le,hband.2.le⟩⟩
  refine ⟨e, rfl, ?_, ?_, orbit_converges p hp e⟩
  · intro ht1
    apply step_alternation_contraction p hp e
    intro he
    have hz : Real.log t/p=0 := congrArg Subtype.val he
    have hp0 : p≠0 := by linarith
    have hl : Real.log t=0 := (div_eq_zero_iff.mp hz).resolve_right hp0
    have : t=1 := by rw [← Real.exp_log ht, hl, Real.exp_zero]
    exact ht1 this
  · intro n
    exact lt_of_le_of_lt (orbit_invariant p hp e n) ((open_error_band_iff p t hp ht).mpr hband)

/-- The positive estimate corresponding to the logarithmic state. -/
def rootEstimate (p X : ℝ) (hp : 2 < p) (e : errors p) (n : ℕ) :=
  X^(-1/p)*Real.exp ((step p hp)^[n] e : ℝ)

theorem root_estimate_initial (p X s : ℝ) (hp : 2 < p) (hX : 0 < X) (hs : 0 < s)
    (e : errors p) (he : (e : ℝ)=Real.log (X*s^p)/p) : rootEstimate p X hp e 0=s := by
  have hp0 : p≠0 := by linarith
  change X^(-1/p)*Real.exp (e : ℝ)=s
  rw [he, Real.rpow_def_of_pos hX, ← Real.exp_add]
  calc
    Real.exp (Real.log X*(-1/p)+Real.log (X*s^p)/p) = Real.exp (Real.log s) := by
      congr 1
      rw [Real.log_mul hX.ne' (Real.rpow_pos_of_pos hs p).ne', Real.log_rpow hs]
      field_simp [hp0]; ring
    _ = s := Real.exp_log hs

theorem root_estimate_update (p X : ℝ) (hp : 2 < p) (e : errors p) (n : ℕ) :
    rootEstimate p X hp e (n+1)=rootEstimate p X hp e n*
      (correction p hp ((step p hp)^[n] e) : ℝ) := by
  unfold rootEstimate
  rw [iterate_succ_apply', estimate_step]

theorem root_estimate_residual (p X : ℝ) (hp : 2 < p) (hX : 0 < X)
    (e : errors p) (n : ℕ) :
    X*(rootEstimate p X hp e n)^p=Real.exp (p*((step p hp)^[n] e : ℝ)) := by
  have hp0 : p≠0 := by linarith
  have ha : 0 < X^(-1/p) := Real.rpow_pos_of_pos hX _
  have hs : 0 < rootEstimate p X hp e n := mul_pos ha (Real.exp_pos _)
  apply Real.log_injOn_pos (mul_pos hX (Real.rpow_pos_of_pos hs p)) (Real.exp_pos _)
  rw [Real.log_mul hX.ne' (Real.rpow_pos_of_pos hs p).ne', Real.log_rpow hs, Real.log_exp]
  unfold rootEstimate
  rw [Real.log_mul ha.ne' (Real.exp_pos _).ne', Real.log_rpow hX, Real.log_exp]
  field_simp [hp0]; ring

theorem root_estimate_converges (p X : ℝ) (hp : 2 < p) (e : errors p) :
    Tendsto (rootEstimate p X hp e) atTop (𝓝 (X^(-1/p))) :=
  estimate_converges p (X^(-1/p)) hp e

end LeanMath.Papers.RectangleFixedCircleTheorem43
