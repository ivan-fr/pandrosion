import LeanMath.Papers.Dyadic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Nearest-integer choices, explicit entry counts, and nested-square-root evaluation. -/
noncomputable section
namespace LeanMath.Papers.V14DyadicChoices
open Real Filter
open scoped Topology

def coefficient (p D : ℝ) (m : ℤ) := 1-p*m/D

theorem nearest_bound (p D : ℝ) (m : ℤ) (hp : 0<p) (hD : 0<D)
    (hm : |(m:ℝ)-D/p|≤1/2) : |coefficient p D m|≤p/(2*D) := by
  have he : coefficient p D m=(p/D)*(D/p-m) := by
    unfold coefficient
    field_simp
    <;> ring
  rw [he,abs_mul,abs_of_pos (div_pos hp hD),abs_sub_comm]
  have hh := mul_le_mul_of_nonneg_left hm (div_pos hp hD).le
  convert! hh using 1 <;> ring

theorem precision_bound (p D : ℝ) (m : ℤ) (s : ℕ) (hp : 0<p)
    (hD : p*2^s≤D) (hm : |(m:ℝ)-D/p|≤1/2) :
    |coefficient p D m|≤1/(2:ℝ)^(s+1) := by
  have hD0 : 0<D := lt_of_lt_of_le (by positivity) hD
  apply (nearest_bound p D m hp hD0 hm).trans
  apply (div_le_div_iff₀ (by positivity : 0<2*D) (by positivity : 0<(2:ℝ)^(s+1))).mpr
  rw [pow_succ]
  nlinarith

theorem dyadic_bound (p s : ℕ) (hp : 0<p) (m : ℤ)
    (hm : |(m:ℝ)-(Dyadic.denominator p s:ℝ)/p|≤1/2) :
    |coefficient p (Dyadic.denominator p s) m|≤1/(2:ℝ)^(s+1) := by
  apply precision_bound p _ m s (by exact_mod_cast hp) _ hm
  have hb := Nat.mul_le_mul_right (2^s) (Nat.le_pow_clog (by decide : 1<2) p)
  simpa [Dyadic.denominator,pow_add] using (show (p:ℝ)*2^s≤(2:ℝ)^(Nat.clog 2 p)*2^s by exact_mod_cast hb)

theorem nearest_positive (p D : ℝ) (m : ℤ) (hp : 0<p) (hD : p≤D)
    (hm : |(m:ℝ)-D/p|≤1/2) : 0<m := by
  have hd : 1≤D/p := (le_div_iff₀ hp).mpr (by simpa using hD)
  have hpos : (0:ℝ)<m := by linarith [(abs_le.mp hm).1]
  exact_mod_cast hpos

theorem log_update (p D r u : ℝ) (m : ℤ) (hr : 0<r) (hu : 0<u) :
    log ((u*((r/u)^p)^((m:ℝ)/D))/r)=coefficient p D m*log (u/r) := by
  have hru := div_pos hr hu
  have hR := rpow_pos_of_pos hru p
  rw [log_div (mul_pos hu (rpow_pos_of_pos hR _)).ne' hr.ne',
    log_mul hu.ne' (rpow_pos_of_pos hR _).ne',log_rpow hR,log_rpow hru,
    log_div hr.ne' hu.ne',log_div hu.ne' hr.ne']
  unfold coefficient
  ring

def entryCount (e b : ℝ) : ℕ := ⌈log (|e|/b)/log 2⌉₊

/-- A half-contraction reaches the closed log-error cell within the printed ceiling count. -/
theorem entry_count_bound (a e b : ℝ) (ha : |a|≤1/2) (hb : 0<b) (he : b < |e|) :
    |a^(entryCount e b)*e|≤b := by
  let n := entryCount e b
  have hc : log (|e|/b)/log 2≤(n:ℝ) := Nat.le_ceil _
  have hlog : 0<log 2 := log_pos (by norm_num)
  have hp : |e|/b≤(2:ℝ)^n := by
    apply (log_le_log_iff (div_pos (by linarith) hb) (by positivity)).mp
    rw [log_pow]
    exact (div_le_iff₀ hlog).mp hc
  have hh : |a^n*e|≤(1/2:ℝ)^n*|e| := by
    rw [abs_mul,abs_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) ha n) (abs_nonneg _)
  apply hh.trans
  rw [div_pow,one_pow,one_div,mul_comm,←div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0<(2:ℝ)^n)).mpr
  have hv := (div_le_iff₀ hb).mp hp
  nlinarith

def squareRoots : ℕ → ℝ → ℝ
  | 0, R => R
  | k+1, R => sqrt (squareRoots k R)

theorem squareRoots_eq (k : ℕ) (R : ℝ) (hR : 0<R) :
    squareRoots k R=R^(1/(2:ℝ)^k) := by
  induction k with
  | zero => simp [squareRoots]
  | succ k ih =>
    rw [squareRoots,ih,sqrt_eq_rpow,←rpow_mul hR.le]
    congr 1
    rw [pow_succ]
    ring

theorem nested_evaluation (k : ℕ) (m : ℤ) (R : ℝ) (hR : 0<R) :
    (squareRoots k R)^m=R^((m:ℝ)/(2:ℝ)^k) := by
  rw [squareRoots_eq k R hR,←rpow_intCast,←rpow_mul hR.le]
  congr 1
  ring

/-- The same radical propagates the residual, allowing a negative exponent. -/
theorem radical_residual (k : ℕ) (m : ℤ) (p R : ℝ) (hR : 0<R) :
    R/(R^((m:ℝ)/(2:ℝ)^k))^p=(squareRoots k R)^((2:ℝ)^k-p*m) := by
  rw [squareRoots_eq k R hR,←rpow_mul hR.le,←rpow_mul hR.le]
  nth_rw 1 [←rpow_one R]
  rw [←rpow_sub hR]
  congr 1
  field_simp
  <;> ring

/-- Logarithmic errors of any positive orbit follow the exact geometric recurrence. -/
theorem orbit_log (p D r : ℝ) (m : ℤ) (u : ℕ → ℝ) (hr : 0<r)
    (hu : ∀ n, 0<u n)
    (hstep : ∀ n, u (n+1)=u n*((r/u n)^p)^((m:ℝ)/D)) (n : ℕ) :
    log (u n/r)=(coefficient p D m)^n*log (u 0/r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hstep n,log_update p D r (u n) m hr (hu n),ih,pow_succ]
    ring

/-- Every orbit with a positive initial approximation stays positive. -/
theorem orbit_positive (p D r : ℝ) (m : ℤ) (u : ℕ → ℝ) (hr : 0<r) (hu0 : 0<u 0)
    (hstep : ∀ n, u (n+1)=u n*((r/u n)^p)^((m:ℝ)/D)) : ∀ n, 0<u n := by
  intro n
  induction n with
  | zero => exact hu0
  | succ n ih =>
    rw [hstep n]
    exact mul_pos ih (rpow_pos_of_pos (rpow_pos_of_pos (div_pos hr ih) _) _)

/-- The printed ceiling bound applies directly to a positive dyadic orbit. -/
theorem orbit_entry (p : ℕ) (hp : 0<p) (m : ℤ) (r b : ℝ) (u : ℕ → ℝ)
    (hr : 0<r) (hb : 0<b) (hu0 : 0<u 0)
    (hm : |(m:ℝ)-(Dyadic.denominator p 0:ℝ)/p|≤1/2)
    (hstep : ∀ n, u (n+1)=u n*((r/u n)^(p:ℝ))^((m:ℝ)/(Dyadic.denominator p 0)))
    (he : b < |log (u 0/r)|) :
    |log (u (entryCount (log (u 0/r)) b)/r)|≤b := by
  have hu := orbit_positive p (Dyadic.denominator p 0) r m u hr hu0 hstep
  rw [orbit_log p (Dyadic.denominator p 0) r m u hr hu hstep]
  apply entry_count_bound _ _ b _ hb he
  simpa using dyadic_bound p 0 hp m hm

/-- For integer degree, the radical residual exponent is a signed integer. -/
theorem integer_radical_residual (k p : ℕ) (m : ℤ) (R : ℝ) (hR : 0<R) :
    R/(R^((m:ℝ)/(2:ℝ)^k))^p=(squareRoots k R)^((2:ℤ)^k-(p:ℤ)*m) := by
  have hh := radical_residual k m p R hR
  simpa only [←rpow_intCast,Int.cast_sub,Int.cast_pow,Int.cast_ofNat,Int.cast_mul,
    Int.cast_natCast,rpow_natCast] using hh

end LeanMath.Papers.V14DyadicChoices
