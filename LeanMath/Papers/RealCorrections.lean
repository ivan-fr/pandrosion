import LeanMath.Papers.Bilateral
import LeanMath.Papers.Family

noncomputable section
namespace LeanMath.Papers.RealCorrections
open Real
open LeanMath.Papers.Cayley

/-- Counterexample to the uniform overshoot claim for 0<p<1 (Theorem 8.2). -/
theorem subunit_counterexample : C₅ (1/2) 3 = 7 ∧ (7:ℝ) < 3^((1:ℝ)/(1/2)) := by
  constructor
  · norm_num [C₅,unchi,P₃,a₁,a₃,chi]
  · norm_num

theorem subunit_coefficient_sign : 0 < a₅ (1/2) ∧ a₃ (1/2) < 0 := by
  norm_num [a₅,a₃]

/-- At degree one the geometric center is exact, so a strict inequality is false. -/
theorem degree_one_exact (R : ℝ) (hR : 0 < R) : RealBracket.center 1 R=R := by
  simp only [RealBracket.center,RealBracket.upper,RealBracket.lower,sub_self,rpow_zero,mul_one,inv_inv]
  simpa only [←sq] using sqrt_sq hR.le

theorem center_three_eq_C₃ (R : ℝ) (hR : 0 < R) : RealBracket.center 3 R=C₃ 3 R := by
  rw [RealBracket.cube_root_halley R hR,halley_formula 3 R (by norm_num) hR]
  norm_num
  field_simp
  <;> ring

theorem C₃_lt_C₇ (p R : ℝ) (hp : 1 < p) (hR : 1 < R) : C₃ p R < C₇ p R := by
  have hR0 : 0 < R := by linarith
  have hy := chi_mem R hR0
  have hy0 : 0 < chi R := div_pos (by linarith) (by linarith)
  have ho := truncations_ordered p (chi R) hp hy0
  have hb := P₅_mem p (chi R) hp hy
  have h1 : 0 < 1-P₁ p (chi R) := by linarith [ho.2.1,ho.2.2,hb.2]
  have h5 : 0 < 1-P₅ p (chi R) := by linarith [hb.2]
  unfold C₃ C₇ unchi
  apply (div_lt_div_iff₀ h1 h5).mpr
  nlinarith [ho.2.1,ho.2.2]

/-- The order-seven correction is strictly above the geometric center at p=3. -/
theorem center_three_lt_C₇ (R : ℝ) (hR : 1 < R) : RealBracket.center 3 R < C₇ 3 R := by
  rw [center_three_eq_C₃ R (by linarith)]
  exact C₃_lt_C₇ 3 R (by norm_num) hR

/-- Thus the order-seven logarithmic width is strictly smaller than half the
original width, contradicting the equality asserted in Corollary 8.4. -/
theorem cubic_width_strict (R : ℝ) (hR : 1 < R) :
    log (RealBracket.upper 3 R)-log (C₇ 3 R) <
      (log (RealBracket.upper 3 R)-log (RealBracket.lower 3 R))/2 := by
  have hR0 : 0 < R := by linarith
  have hc := RealBracket.center_pos 3 R (by norm_num) hR0
  have h7 := C₇_pos 3 R (by norm_num) hR0
  have h := (log_lt_log_iff hc h7).mpr (center_three_lt_C₇ R hR)
  have hw := RealBracket.half_width 3 R (by norm_num) hR0
  rw [log_div (RealBracket.upper_pos 3 R (by norm_num) hR0).ne' hc.ne',
    log_div (RealBracket.upper_pos 3 R (by norm_num) hR0).ne'
      (RealBracket.lower_pos 3 R (by norm_num) hR0).ne'] at hw
  linarith

end LeanMath.Papers.RealCorrections
