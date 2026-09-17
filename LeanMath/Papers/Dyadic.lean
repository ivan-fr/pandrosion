import Mathlib.Algebra.Order.Round
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanMath.Papers.Dyadic
open Real Filter
open scoped Topology

def rho (p D : ℝ) : ℝ := 1-p*(round (D/p):ℝ)/D
def correction (p D R : ℝ) := R^((round (D/p):ℝ)/D)
def denominator (p s : ℕ) : ℕ := 2^(Nat.clog 2 p+s)

theorem round_error (p D : ℝ) (hp : 0 < p) (hD : 0 < D) :
    |rho p D| ≤ p/(2*D) := by
  have he : rho p D = (p/D)*(D/p-(round (D/p):ℝ)) := by
    unfold rho
    field_simp
    <;> ring
  rw [he,abs_mul,abs_of_pos (div_pos hp hD)]
  have h := mul_le_mul_of_nonneg_left (abs_sub_round (D/p)) (div_pos hp hD).le
  convert! h using 1 <;> first | rfl | ring

theorem strict_precision_bound (p D : ℝ) (N : ℕ) (hp : 0 < p)
    (hN : 0 < N) (hD : p*N ≤ D) : |rho p D| < 1/(2*(N:ℝ)) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hD0 : 0 < D := (mul_pos hp hN0).trans_le hD
  rcases lt_or_eq_of_le hD with hlt | heq
  · have hb := round_error p D hp hD0
    have hfrac : p/(2*D) < 1/(2*(N:ℝ)) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    exact hb.trans_lt hfrac
  · have hratio : D/p = (N:ℝ) := by rw [←heq]; field_simp
    have hz : rho p D=0 := by
      unfold rho
      rw [hratio]
      simp only [round_natCast,Int.cast_natCast]
      rw [heq]
      field_simp
      norm_num
    rw [hz,abs_zero]
    positivity

/-- Lemma 5.1, the printed strict precision bound, including the exact case. -/
theorem dyadic_strict_bound (p s : ℕ) (hp : 0 < p) :
    |rho p (denominator p s)| < 1/((2:ℝ)^(s+1)) := by
  have hbase := Nat.le_pow_clog (by decide : 1<2) p
  have hD : p*2^s ≤ denominator p s := by
    unfold denominator
    rw [pow_add]
    exact Nat.mul_le_mul_right (2^s) hbase
  have h := strict_precision_bound p (denominator p s) (2^s)
    (by exact_mod_cast hp) (by positivity) (by exact_mod_cast hD)
  simpa only [Nat.cast_pow,Nat.cast_ofNat,pow_succ'] using h

/-- Exact logarithmic error map for the real-degree update. -/
theorem log_error_linear (p D r u : ℝ) (hr : 0 < r) (hu : 0 < u) :
    log ((u*correction p D ((r/u)^p))/r) = rho p D * log (u/r) := by
  have hru : 0 < r/u := div_pos hr hu
  have hR : 0 < (r/u)^p := rpow_pos_of_pos hru _
  unfold correction rho
  rw [log_div (mul_ne_zero hu.ne' (rpow_pos_of_pos hR _).ne') hr.ne',
    log_mul hu.ne' (rpow_pos_of_pos hR _).ne',log_rpow hR,log_rpow hru,
    log_div hr.ne' hu.ne',log_div hu.ne' hr.ne']
  ring

theorem residual_recurrence (p D R : ℝ) (hR : 0 < R) :
    R/(correction p D R)^p = R^(rho p D) := by
  unfold correction rho
  rw [←rpow_mul hR.le,rpow_sub hR,rpow_one]
  congr 2
  ring

/-- Repeated exact dyadic updates eventually enter every positive log-error cell. -/
theorem finite_entry (p s : ℕ) (hp : 0 < p) (e ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, |(rho p (denominator p s))^n*e| < ε := by
  have hb := dyadic_strict_bound p s hp
  have hpow : (1:ℝ) ≤ 2^(s+1) := one_le_pow₀ (by norm_num)
  have hfrac : 1/((2:ℝ)^(s+1)) ≤ 1 := (div_le_one (by positivity)).mpr hpow
  have hrho : |rho p (denominator p s)| < 1 := hb.trans_le hfrac
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg (rho p (denominator p s))) hrho
  have hte := ht.mul_const |e|
  have hevent : ∀ᶠ n : ℕ in atTop, |rho p (denominator p s)|^n*|e| < ε := by
    apply (tendsto_order.mp hte).2 ε
    simpa using hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  refine ⟨N,fun n hn => ?_⟩
  simpa only [abs_mul,abs_pow] using hN n hn

end LeanMath.Papers.Dyadic
