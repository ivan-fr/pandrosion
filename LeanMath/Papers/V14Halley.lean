import LeanMath.Papers.V14Defect
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Uniform one-shot error bound of Theorem 13.3, proved by differential
comparison rather than an unformalized infinite-series argument. -/
noncomputable section
namespace LeanMath.Papers.V14Halley
open Real Set
open LeanMath.Papers.Cayley

def gap (p y : ℝ) := logCoord y/p-logCoord (y/p)
def gapDeriv (p y : ℝ) := (2/(1-y^2))/p-(2/(1-(y/p)^2))/p

theorem div_mem (p y : ℝ) (hp : 1 < p) (hy : y ∈ Ioo (-1) 1) :
    y/p ∈ Ioo (-1) 1 := by
  have hp0 : 0 < p := by linarith
  constructor
  · apply (lt_div_iff₀ hp0).mpr; nlinarith [hy.1]
  · apply (div_lt_iff₀ hp0).mpr; linarith [hy.2]

theorem hasDerivAt_gap (p y : ℝ) (hp : 1 < p) (hy : y ∈ Ioo (-1) 1) :
    HasDerivAt (gap p) (gapDeriv p y) y := by
  convert! ((hasDerivAt_logCoord y hy).div_const p).sub
    ((hasDerivAt_logCoord (y/p) (div_mem p y hp hy)).comp y
      ((hasDerivAt_id y).div_const p)) using 1 <;> simp only [gap, gapDeriv, id_eq, div_eq_mul_inv, one_mul, mul_one]

theorem derivative_bounds (p rho y : ℝ) (hp : 1 < p)
    (hr0 : 0 ≤ rho) (hr1 : rho < 1) (hy0 : 0 ≤ y) (hyr : y ≤ rho) :
    0 ≤ gapDeriv p y ∧ gapDeriv p y ≤ 2*y^2/(p*(1-rho^2)) := by
  have hp0 : 0 < p := by linarith
  have hy1 : y < 1 := hyr.trans_lt hr1
  have hyv : 0 ≤ y/p := div_nonneg hy0 hp0.le
  have hle : y/p ≤ y := (div_le_iff₀ hp0).mpr (by nlinarith)
  have hv1 : y/p < 1 := hle.trans_lt hy1
  have hd : 0 < 1-y^2 := by nlinarith
  have hdv : 0 < 1-(y/p)^2 := by nlinarith
  have hdr : 0 < 1-rho^2 := by nlinarith
  have hsq : (y/p)^2 ≤ y^2 := by nlinarith
  have hsq' : y^2 ≤ rho^2 := by nlinarith
  have horder : 2/(1-(y/p)^2) ≤ 2/(1-y^2) :=
    div_le_div_of_nonneg_left (by norm_num) hd (by linarith)
  have htwo : 2 ≤ 2/(1-(y/p)^2) :=
    (le_div_iff₀ hdv).mpr (by nlinarith [sq_nonneg (y/p)])
  have hupper : (2/(1-y^2)-2)/p = 2*y^2/(p*(1-y^2)) := by field_simp; ring
  have hlast : 2*y^2/(p*(1-y^2)) ≤ 2*y^2/(p*(1-rho^2)) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos hp0 hdr) (by nlinarith)
  constructor
  · unfold gapDeriv; exact sub_nonneg.mpr (div_le_div_of_nonneg_right horder hp0.le)
  · calc
      gapDeriv p y ≤ (2/(1-y^2)-2)/p := by
        unfold gapDeriv
        rw [sub_div]
        exact sub_le_sub_left (div_le_div_of_nonneg_right htwo hp0.le) _
      _ = 2*y^2/(p*(1-y^2)) := hupper
      _ ≤ _ := hlast

/-- Uniform logarithmic bound on the positive half of the gate. -/
theorem positive_gap_bound (p rho y : ℝ) (hp : 1 < p)
    (hr0 : 0 ≤ rho) (hr1 : rho < 1) (hy0 : 0 ≤ y) (hyr : y ≤ rho) :
    0 ≤ gap p y ∧ gap p y ≤ 2*y^3/(3*p*(1-rho^2)) := by
  have hp0 : 0 < p := by linarith
  have hdr : 0 < 1-rho^2 := by nlinarith
  have hmem : ∀ t ∈ Icc 0 rho, t ∈ Ioo (-1) 1 := by
    intro t ht; exact ⟨by linarith [ht.1], ht.2.trans_lt hr1⟩
  have hmono : MonotoneOn (gap p) (Icc 0 rho) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 rho)
    · intro t ht; exact (hasDerivAt_gap p t hp (hmem t ht)).continuousAt.continuousWithinAt
    · intro t ht
      exact (hasDerivAt_gap p t hp (hmem t (interior_subset ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hasDerivAt_gap p t hp (hmem t ht')).deriv]
      exact (derivative_bounds p rho t hp hr0 hr1 ht'.1 ht'.2).1
  let f : ℝ → ℝ := fun t => 2*t^3/(3*p*(1-rho^2))-gap p t
  have hf : ∀ t ∈ Icc 0 rho, HasDerivAt f
      (2*t^2/(p*(1-rho^2))-gapDeriv p t) t := by
    intro t ht
    convert! (((((hasDerivAt_id t).pow 3).const_mul 2).div_const (3*p*(1-rho^2))).sub
      (hasDerivAt_gap p t hp (hmem t ht))) using 1
    <;> simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, mul_one]
    <;> field_simp
    <;> ring
  have hmonof : MonotoneOn f (Icc 0 rho) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 rho)
    · intro t ht; exact (hf t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hf t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hf t ht').deriv]
      exact sub_nonneg.mpr (derivative_bounds p rho t hp hr0 hr1 ht'.1 ht'.2).2
  have h0 : gap p 0 = 0 := by simp [gap, logCoord]
  have hg := hmono ⟨le_rfl, hr0⟩ ⟨hy0,hyr⟩ hy0
  have hh := hmonof ⟨le_rfl,hr0⟩ ⟨hy0,hyr⟩ hy0
  dsimp [f] at hh
  simp only [h0, zero_pow (by decide : 3 ≠ 0), mul_zero, zero_div, sub_zero] at hh
  rw [h0] at hg
  exact ⟨hg, by linarith⟩

theorem logCoord_odd (y : ℝ) : logCoord (-y) = -logCoord y := by
  simp only [logCoord, sub_neg_eq_add, ← sub_eq_add_neg]
  ring

theorem gap_odd (p y : ℝ) : gap p (-y) = -gap p y := by
  simp only [gap, neg_div, logCoord_odd]
  ring

/-- The all-points bound in the Cayley coordinate, including negative inputs. -/
theorem absolute_gap_bound (p rho y : ℝ) (hp : 1 < p)
    (hr0 : 0 ≤ rho) (hr1 : rho < 1) (hy : |y| ≤ rho) :
    |gap p y| ≤ 2*rho^3/(3*p*(1-rho^2)) := by
  have hp0 : 0 < p := by linarith
  have hdr : 0 < 1-rho^2 := by nlinarith
  have h := positive_gap_bound p rho |y| hp hr0 hr1 (abs_nonneg y) hy
  have hab : |gap p y| = gap p |y| := by
    by_cases hy0 : 0 ≤ y
    · rw [abs_of_nonneg hy0] at h ⊢; exact abs_of_nonneg h.1
    · have hy0' : y ≤ 0 := le_of_not_ge hy0
      rw [abs_of_nonpos hy0'] at h ⊢
      rw [gap_odd] at h ⊢
      exact abs_of_nonpos (by linarith [h.1])
  rw [hab]
  exact h.2.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg y) hy 3) (by norm_num))
    (by positivity))

/-- Converts any log-error bound into a rational relative-error budget. -/
theorem relative_of_log_bound (v eta : ℝ) (hv : 0 < v)
    (he0 : 0 ≤ eta) (he1 : eta < 1) (hlog : |log v| ≤ eta) :
    |v-1| ≤ eta/(1-eta) := by
  have he : 0 < 1-eta := by linarith
  have heexp := add_one_le_exp (-eta)
  rw [exp_neg] at heexp
  have hu : exp eta ≤ 1/(1-eta) := by
    apply (le_div_iff₀ he).mpr
    have h := (le_div_iff₀ (exp_pos eta)).mp (show 1-eta ≤ 1/exp eta by simpa only [one_div] using (show 1-eta ≤ (exp eta)⁻¹ by linarith))
    nlinarith
  have hvu : v ≤ exp eta := by
    rw [← exp_log hv]
    exact exp_le_exp.mpr (abs_le.mp hlog).2
  have hvl : 1-eta ≤ v := by
    have ht := add_one_le_exp (log v)
    rw [exp_log hv] at ht
    linarith [(abs_le.mp hlog).1]
  have heta : eta ≤ eta/(1-eta) := (le_div_iff₀ he).mpr (by nlinarith)
  apply abs_le.mpr
  constructor
  · linarith
  · have hlast : 1/(1-eta)-1 = eta/(1-eta) := by field_simp; ring
    linarith

/-- Theorem 13.3 stated for the actual Halley correction and positive residual. -/
theorem halley_uniform (p rho R : ℝ) (hp : 1 < p) (hr0 : 0 ≤ rho)
    (hr1 : rho < 1) (hR : 0 < R) (hy : |chi R| ≤ rho) :
    |log (C₃ p R / R^(1/p))| ≤ 2*rho^3/(3*p*(1-rho^2)) := by
  have hm := chi_mem R hR
  have hdm := div_mem p (chi R) hp hm
  have hC : 0 < C₃ p R := by
    change 0 < unchi (1/p*chi R)
    rw [show 1/p*chi R=chi R/p by ring]
    exact unchi_pos _ hdm
  have hid : log (C₃ p R / R^(1/p)) = -gap p (chi R) := by
    rw [log_div hC.ne' (rpow_pos_of_pos hR _).ne',log_rpow hR]
    unfold C₃ P₁ a₁
    rw [show 1/p*chi R=chi R/p by ring, ← logCoord_eq _ hdm]
    have hh := logCoord_eq (chi R) hm
    rw [unchi_chi R hR] at hh
    rw [← hh]
    unfold gap; ring
  rw [hid,abs_neg]
  exact absolute_gap_bound p rho (chi R) hp hr0 hr1 hy

end LeanMath.Papers.V14Halley
