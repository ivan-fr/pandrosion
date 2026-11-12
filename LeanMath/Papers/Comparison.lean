import LeanMath.Papers.Cayley
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace LeanMath.Papers.Cayley
open Real Set

theorem P₅_one_lt (p : ℝ) (hp : 1 < p) : P₅ p 1 < 1 := by
  have hp0 : 0 < p := by linarith
  have ha := (factors_pos p hp).1
  have he : 1 - P₅ p 1 = (p-1)*A p/(15*p^5) := by
    unfold P₅ a₁ a₃ a₅ A
    field_simp
    <;> ring
  have h : 0 < (p-1)*A p/(15*p^5) := by positivity
  linarith

theorem P₅_bounds (p y : ℝ) (hp : 1 < p) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ P₅ p y ∧ P₅ p y < 1 := by
  obtain ⟨h1,h3,h5⟩ := coefficients_pos p hp
  have h3y : y^3 ≤ 1 := pow_le_one₀ hy0 hy1
  have h5y : y^5 ≤ 1 := pow_le_one₀ hy0 hy1
  have hle : P₅ p y ≤ P₅ p 1 := by
    unfold P₅
    simp only [one_pow, mul_one]
    linarith [mul_le_mul_of_nonneg_left hy1 h1.le,
      mul_le_mul_of_nonneg_left h3y h3.le, mul_le_mul_of_nonneg_left h5y h5.le]
  exact ⟨by unfold P₅; positivity, hle.trans_lt (P₅_one_lt p hp)⟩

def logCoord (y : ℝ) := log (1+y) - log (1-y)
def logGap (p y : ℝ) := logCoord (P₅ p y) - logCoord y / p

theorem logCoord_eq (y : ℝ) (hy : y ∈ Ioo (-1) 1) :
    logCoord y = log (unchi y) := by
  unfold logCoord unchi
  rw [log_div (by linarith [hy.1] : 1+y ≠ 0) (by linarith [hy.2] : 1-y ≠ 0)]

theorem hasDerivAt_logCoord (y : ℝ) (hy : y ∈ Ioo (-1) 1) :
    HasDerivAt logCoord (2/(1-y^2)) y := by
  have hplus : 1+y ≠ 0 := by linarith [hy.1]
  have hminus : 1-y ≠ 0 := by linarith [hy.2]
  have hs : 1-y^2 ≠ 0 := by nlinarith [hy.1,hy.2]
  convert! (((hasDerivAt_id y).const_add 1).log hplus).sub
    (((hasDerivAt_id y).const_sub 1).log hminus) using 1
  simp only [id_eq]
  field_simp
  <;> ring

theorem hasDerivAt_logGap (p y : ℝ) (hp : 1 < p) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    HasDerivAt (logGap p)
      (2/(1-(P₅ p y)^2)*(a₁ p+3*a₃ p*y^2+5*a₅ p*y^4) - (2/(1-y^2))/p) y := by
  have hy : y ∈ Ioo (-1) 1 := ⟨by linarith,hy1⟩
  have hb := P₅_bounds p y hp hy0 hy1.le
  have ht : P₅ p y ∈ Ioo (-1) 1 := ⟨by linarith [hb.1],hb.2⟩
  exact ((hasDerivAt_logCoord (P₅ p y) ht).comp y (hasDerivAt_P₅ p y)).sub
    ((hasDerivAt_logCoord y hy).div_const p)

theorem logGap_deriv_neg (p y : ℝ) (hp : 1 < p) (hy0 : 0 < y) (hy1 : y < 1) :
    deriv (logGap p) y < 0 := by
  rw [(hasDerivAt_logGap p y hp hy0.le hy1).deriv]
  have hb := P₅_bounds p y hp hy0.le hy1.le
  have hd1 : 0 < 1-(P₅ p y)^2 := by nlinarith [hb.1,hb.2]
  have hd2 : 0 < 1-y^2 := by nlinarith
  have hp0 : p ≠ 0 := by linarith
  have he :
      2/(1-(P₅ p y)^2)*(a₁ p+3*a₃ p*y^2+5*a₅ p*y^4) - (2/(1-y^2))/p =
      2*((1-y^2)*(a₁ p+3*a₃ p*y^2+5*a₅ p*y^4)-(1/p)*(1-(P₅ p y)^2)) /
        ((1-(P₅ p y)^2)*(1-y^2)) := by
    field_simp
    <;> ring
  rw [he]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num)
    (residual_negative p y hp hy0 hy1)) (mul_pos hd1 hd2)

/-- The differential residual proves the global logarithmic comparison. -/
theorem logGap_negative (p y : ℝ) (hp : 1 < p) (hy0 : 0 < y) (hy1 : y < 1) :
    logCoord (P₅ p y) < logCoord y / p := by
  have ha : StrictAntiOn (logGap p) (Ico 0 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Ico 0 1)
    · intro t ht
      exact (hasDerivAt_logGap p t hp ht.1 ht.2).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ico] at ht
      exact logGap_deriv_neg p t hp ht.1 ht.2
  have h := ha (show (0:ℝ) ∈ Ico 0 1 by norm_num) ⟨hy0.le,hy1⟩ hy0
  have hz : logGap p 0 = 0 := by simp [logGap,logCoord,P₅]
  rw [hz] at h
  exact sub_neg.mp h

theorem unchi_pos (y : ℝ) (hy : y ∈ Ioo (-1) 1) : 0 < unchi y := by
  exact div_pos (by linarith [hy.1]) (by linarith [hy.2])

theorem C₇_above_one_below_root (p R : ℝ) (hp : 1 < p) (hR : 1 < R) :
    1 < C₇ p R ∧ C₇ p R < R ^ (1/p) := by
  have hR0 : 0 < R := by linarith
  have hy : chi R ∈ Ioo (-1) 1 := chi_mem R hR0
  have hy0 : 0 < chi R := by unfold chi; positivity
  have hb := P₅_bounds p (chi R) hp hy0.le hy.2.le
  have hpos : 0 < P₅ p (chi R) := by
    have hh := truncations_ordered p (chi R) hp hy0
    exact hh.1.trans (hh.2.1.trans hh.2.2)
  have ht : P₅ p (chi R) ∈ Ioo (-1) 1 := ⟨by linarith,hb.2⟩
  have hcpos : 0 < C₇ p R := unchi_pos _ ht
  constructor
  · unfold C₇ unchi
    apply (one_lt_div (by linarith : 0 < 1-P₅ p (chi R))).mpr
    linarith
  · have h := logGap_negative p (chi R) hp hy0 hy.2
    rw [logCoord_eq _ ht, logCoord_eq _ hy, unchi_chi R hR0] at h
    apply (log_lt_log_iff hcpos (rpow_pos_of_pos hR0 _)).mp
    rw [log_rpow hR0]
    simpa only [C₇, div_eq_mul_inv, one_div, mul_comm, mul_one] using h

theorem P₅_mem (p y : ℝ) (hp : 1 < p) (hy : y ∈ Ioo (-1) 1) :
    P₅ p y ∈ Ioo (-1) 1 := by
  by_cases h : 0 ≤ y
  · have hb := P₅_bounds p y hp h hy.2.le
    exact ⟨by linarith [hb.1],hb.2⟩
  · have hb := P₅_bounds p (-y) hp (by linarith) (by linarith [hy.1])
    rw [P₅_odd] at hb
    exact ⟨by linarith [hb.2],by linarith [hb.1]⟩

theorem hasDerivAt_logGap_all (p y : ℝ) (hp : 1 < p) (hy : y ∈ Ioo (-1) 1) :
    HasDerivAt (logGap p)
      (2/(1-(P₅ p y)^2)*(a₁ p+3*a₃ p*y^2+5*a₅ p*y^4) - (2/(1-y^2))/p) y := by
  exact ((hasDerivAt_logCoord (P₅ p y) (P₅_mem p y hp hy)).comp y
    (hasDerivAt_P₅ p y)).sub ((hasDerivAt_logCoord y hy).div_const p)

theorem C₇_pos (p R : ℝ) (hp : 1 < p) (hR : 0 < R) : 0 < C₇ p R :=
  unchi_pos _ (P₅_mem p (chi R) hp (chi_mem R hR))

theorem continuousAt_C₇ (p R : ℝ) (hp : 1 < p) (hR : 0 < R) :
    ContinuousAt (C₇ p) R := by
  have ht := P₅_mem p (chi R) hp (chi_mem R hR)
  have hchi : ContinuousAt chi R := by
    unfold chi
    exact (continuousAt_id.sub continuousAt_const).div
      (continuousAt_id.add continuousAt_const) (by linarith)
  have hf := (hasDerivAt_P₅ p (chi R)).continuousAt.comp hchi
  exact (continuousAt_const.add hf).div (continuousAt_const.sub hf) (by linarith [ht.2])

theorem C₇_one (p : ℝ) : C₇ p 1 = 1 := by simp [C₇,unchi,P₅,chi]

theorem C₇_below_one_above_root (p R : ℝ) (hp : 1 < p) (hR0 : 0 < R) (hR1 : R < 1) :
    R ^ (1/p) < C₇ p R ∧ C₇ p R < 1 := by
  have hc := C₇_pos p R hp hR0
  have hr := rpow_pos_of_pos hR0 (1/p)
  have hi : 1 < R⁻¹ := (one_lt_inv₀ hR0).mpr hR1
  obtain ⟨h1,h2⟩ := C₇_above_one_below_root p R⁻¹ hp hi
  rw [C₇_reciprocal p R hR0] at h1 h2
  rw [inv_rpow hR0.le] at h2
  refine ⟨(inv_lt_inv₀ hc hr).mp h2, ?_⟩
  exact (one_lt_inv₀ hc).mp h1

end LeanMath.Papers.Cayley
