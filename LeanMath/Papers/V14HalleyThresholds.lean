import LeanMath.Papers.V14Halley
import LeanMath.Papers.V14Entry
import LeanMath.Papers.V14EntryFamily
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Exact rational verification of the two numerical Halley thresholds in §13.3. -/
noncomputable section
namespace LeanMath.Papers.V14HalleyThresholds
open Real Set
open LeanMath.Papers.Cayley LeanMath.Papers.V14Entry LeanMath.Papers.V14Halley

/-- A rational upper radius for the workload |log X| <= 1000 log 2. -/
def radius (p : ℝ) : ℝ := 500*(6931471808/10000000000)/(p+1)
def eta (p : ℝ) : ℝ := 2*(radius p)^3/(3*p*(1-(radius p)^2))
def epsilon : ℝ := 1/2^52

theorem tanh_le_self (x : ℝ) (hx : 0≤x) : tanh x ≤ x := by
  let f := fun t : ℝ => t*cosh t-sinh t
  have hd : ∀ t : ℝ, HasDerivAt f (t*sinh t) t := by
    intro t
    convert! ((hasDerivAt_id t).mul (hasDerivAt_cosh t)).sub (hasDerivAt_sinh t) using 1 <;> simp only [id_eq] <;> ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro t ht; exact (hd t).continuousAt.continuousWithinAt
    · intro t ht; exact (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t).deriv]
      have ht0 : 0≤t := interior_subset ht
      exact mul_nonneg ht0 (sinh_nonneg_iff.mpr ht0)
  have h := hm (by simp) hx hx
  dsimp [f] at h
  simp only [zero_mul,sinh_zero,sub_self] at h
  rw [tanh_eq_sinh_div_cosh]
  exact (div_le_iff₀ (cosh_pos x)).mpr (by linarith)

theorem entry_radius (p X : ℝ) (hp : 0<p) (hX : 0<X) (hwork : |log X|≤1000*log 2) :
    |chi (LeanMath.Papers.V14Entry.residual p X 1)| ≤ radius p := by
  have hlog : 0<log 2 := log_pos (by norm_num)
  have hr := worst_radius_bound p X (1000*log 2) hp hX hwork 1
  simp only [pow_one] at hr
  have hlin := tanh_le_self (1000*log 2/(2*(p+1))) (by positivity)
  apply hr.trans (hlin.trans _)
  have hbound : log 2 ≤ (6931471808:ℝ)/10000000000 := by
    have h := log_two_lt_d9.le
    norm_num at h ⊢
    exact h
  unfold radius
  apply (div_le_div_iff₀ (by positivity : 0<2*(p+1)) (by linarith : 0<p+1)).mpr
  nlinarith

/-- Actual approximation after one exact recurrent entry followed by Halley. -/
def oneShot (p X : ℝ) : ℝ := approximation p X 1*C₃ p (LeanMath.Papers.V14Entry.residual p X 1)

theorem oneShot_ratio (p X : ℝ) (hp : 0<p) (hX : 0<X) :
    oneShot p X/X^(1/p)=C₃ p (LeanMath.Papers.V14Entry.residual p X 1)/(LeanMath.Papers.V14Entry.residual p X 1)^(1/p) := by
  have hentry : approximation p X 1*(LeanMath.Papers.V14Entry.residual p X 1)^(1/p)=X^(1/p) := by
    unfold approximation LeanMath.Papers.V14Entry.residual
    rw [← rpow_mul hX.le,← rpow_add hX]
    congr 1
    field_simp
    <;> ring
  unfold oneShot
  rw [← hentry]
  have hu := (rpow_pos_of_pos hX ((1-(1/(p+1))^1)/p)).ne'
  change approximation p X 1≠0 at hu
  field_simp

theorem oneShot_bound (p X : ℝ) (hp : 1<p) (hX : 0<X) (hwork : |log X|≤1000*log 2)
    (hr : radius p<1) (he : eta p<1) :
    |oneShot p X/X^(1/p)-1| ≤ eta p/(1-eta p) := by
  have hp0 : 0<p := by linarith
  have hr0 : 0≤radius p := by unfold radius; positivity
  have hR : 0<LeanMath.Papers.V14Entry.residual p X 1 := rpow_pos_of_pos hX _
  have hC : 0<C₃ p (LeanMath.Papers.V14Entry.residual p X 1) := by
    change 0<unchi (1/p*chi (LeanMath.Papers.V14Entry.residual p X 1))
    rw [show 1/p*chi (LeanMath.Papers.V14Entry.residual p X 1)=chi (LeanMath.Papers.V14Entry.residual p X 1)/p by ring]
    exact unchi_pos _ (div_mem p _ hp (chi_mem _ hR))
  have he0 : 0≤eta p := by
    have hh : 0<1-(radius p)^2 := by nlinarith
    unfold eta; positivity
  rw [oneShot_ratio p X hp0 hX]
  exact relative_of_log_bound _ (eta p) (div_pos hC (rpow_pos_of_pos hR _)) he0 he
    (halley_uniform p (radius p) _ hp hr0 hr hR (entry_radius p X hp0 hX hwork))

/-- The paper's strict 1.655 epsilon threshold, checked with rational arithmetic. -/
theorem threshold_524287 (X : ℝ) (hX : 0<X) (hwork : |log X|≤1000*log 2) :
    |oneShot 524287 X/X^(1/(524287:ℝ))-1| < (1655/1000)*epsilon := by
  have hh := oneShot_bound 524287 X (by norm_num) hX hwork
    (by norm_num [radius]) (by norm_num [eta,radius])
  exact hh.trans_lt (by norm_num [eta,radius,epsilon])

/-- The paper's strict 0.104 epsilon threshold, checked with rational arithmetic. -/
theorem threshold_1048575 (X : ℝ) (hX : 0<X) (hwork : |log X|≤1000*log 2) :
    |oneShot 1048575 X/X^(1/(1048575:ℝ))-1| < (104/1000)*epsilon := by
  have hh := oneShot_bound 1048575 X (by norm_num) hX hwork
    (by norm_num [radius]) (by norm_num [eta,radius])
  exact hh.trans_lt (by norm_num [eta,radius,epsilon])

/-- The same one-shot update written with the selected dyadic denominator and propagated residual. -/
def selectedOneShot (p : ℕ) (X : ℝ) : ℝ :=
  let v := LeanMath.Papers.Dyadic.correction p (LeanMath.Papers.Dyadic.denominator p 0) X
  v*C₃ p (X/v^p)

theorem selectedOneShot_eq (k : ℕ) (hk : 2≤k) (X : ℝ) (hX : 0<X) :
    selectedOneShot (2^k-1) X=oneShot (2^k-1 : ℕ) X := by
  have hpow : 4 ≤ (2:ℕ)^k := by
    calc 4 = (2:ℕ)^2 := by norm_num
         _ ≤ 2^k := Nat.pow_le_pow_right (by decide) hk
  have hp : (0:ℝ)<(2^k-1 : ℕ) := by exact_mod_cast (show 0<(2:ℕ)^k-1 by omega)
  have hu : approximation (2^k-1 : ℕ) X 1 = X^(1/((2^k-1 : ℕ)+1 : ℝ)) := by
    unfold approximation
    congr 1
    simp only [pow_one]
    field_simp
    <;> ring
  unfold selectedOneShot oneShot
  dsimp only
  rw [LeanMath.Papers.V14EntryFamily.chosen_residual k hk X hX,
    LeanMath.Papers.V14EntryFamily.chosen_correction k hk X,hu]
  simp only [LeanMath.Papers.V14Entry.residual,pow_one]

theorem selected_threshold_524287 (X : ℝ) (hX : 0<X) (hwork : |log X|≤1000*log 2) :
    |selectedOneShot 524287 X/X^(1/(524287:ℝ))-1| < (1655/1000)*epsilon := by
  have h := selectedOneShot_eq 19 (by norm_num) X hX
  norm_num only [Nat.reducePow,Nat.reduceSub,Nat.cast_ofNat] at h
  rw [h]
  exact threshold_524287 X hX hwork

theorem selected_threshold_1048575 (X : ℝ) (hX : 0<X) (hwork : |log X|≤1000*log 2) :
    |selectedOneShot 1048575 X/X^(1/(1048575:ℝ))-1| < (104/1000)*epsilon := by
  have h := selectedOneShot_eq 20 (by norm_num) X hX
  norm_num only [Nat.reducePow,Nat.reduceSub,Nat.cast_ofNat] at h
  rw [h]
  exact threshold_1048575 X hX hwork

end LeanMath.Papers.V14HalleyThresholds
