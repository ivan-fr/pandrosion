import LeanMath.Papers.V14PadeTheorem
import Mathlib.Algebra.Polynomial.Derivative

/-! Positive-coefficient hypergeometric polynomials for diagonal root Padé approximants. -/
noncomputable section
namespace LeanMath.Papers.V14DiagonalPolynomials
open Polynomial Finset

/-- Coefficients of ₂F₁(-d,-d-a;1-a;R), terminating at degree d. -/
def c (a : ℝ) (d : ℕ) : ℕ → ℝ
  | 0 => 1
  | k+1 => c a d k * (((d:ℝ)-k)*(d+a-k)) / (((k:ℝ)+1)*(k+1-a))

def poly (a : ℝ) (d : ℕ) : ℝ[X] := ∑ k ∈ range (d+1), monomial k (c a d k)

theorem c_zero (a : ℝ) (d : ℕ) : c a d 0=1 := rfl

theorem c_vanish (a : ℝ) (d k : ℕ) (hk : d<k) : c a d k=0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le (show d ≤ k by omega) with he | he
    · subst k; simp [c]
    · simp [c,ih he]

theorem coeff_poly (a : ℝ) (d k : ℕ) : (poly a d).coeff k=c a d k := by
  simp only [poly,finsetSum_coeff,coeff_monomial]
  by_cases hk : k<d+1
  · simp [hk]
  · simp [hk,c_vanish a d k (by omega)]

theorem c_pos (a : ℝ) (ha : -1<a ∧ a<1) (d k : ℕ) (hk : k ≤ d) : 0<c a d k := by
  induction k with
  | zero => norm_num [c]
  | succ k ih =>
    have hkd : (k:ℝ)+1 ≤ d := by exact_mod_cast hk
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    exact div_pos (mul_pos (ih (by omega)) (mul_pos (by linarith) (by linarith [ha.1])))
      (mul_pos (by positivity) (by linarith [ha.2]))

theorem c_nonneg (a : ℝ) (ha : -1<a ∧ a<1) (d k : ℕ) : 0 ≤ c a d k := by
  by_cases hk : k ≤ d
  · exact (c_pos a ha d k hk).le
  · rw [c_vanish a d k (by omega)]

theorem poly_pos (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    0 < (poly a d).eval R := by
  rw [poly,eval_finsetSum]
  apply sum_pos'
  · intro k hk
    simp only [eval_monomial]
    exact mul_nonneg (c_nonneg a ha d k) (pow_nonneg hR k)
  · refine ⟨0,by simp,?_⟩
    simp [c]

theorem coefficient_recurrence (a : ℝ) (ha : a<1) (d k : ℕ) :
    ((k:ℝ)+1)*(k+1-a)*c a d (k+1) = ((d:ℝ)-k)*(d+a-k)*c a d k := by
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hd : (k:ℝ)+1-a ≠ 0 := by linarith
  rw [c]
  field_simp [hd]

def theta (P : ℝ[X]) : ℝ[X] := X*P.derivative

theorem coeff_theta (P : ℝ[X]) (k : ℕ) : (theta P).coeff k=(k:ℝ)*P.coeff k := by
  cases k with
  | zero => simp [theta]
  | succ k => simp [theta,coeff_X_mul,coeff_derivative]; ring

theorem theta_equation (a : ℝ) (ha : a<1) (d : ℕ) :
    theta (theta (poly a d)) - C a * theta (poly a d) =
    X * (theta (theta (poly a d)) - C (2*d+a)*theta (poly a d) + C (d*(d+a))*poly a d) := by
  apply Polynomial.ext
  intro k
  cases k with
  | zero => simp [coeff_sub,coeff_theta]
  | succ k =>
    simp only [coeff_sub,coeff_add,coeff_C_mul,coeff_theta,coeff_X_mul,coeff_poly,Nat.cast_add,Nat.cast_one]
    have h := coefficient_recurrence a ha d k
    nlinarith [h]

theorem differential_equation (a : ℝ) (ha : a<1) (d : ℕ) :
    X*(1-X)*(poly a d).derivative.derivative +
      (C (1-a)+C (2*d+a-1)*X)*(poly a d).derivative - C (d*(d+a))*poly a d=0 := by
  have h := theta_equation a ha d
  simp only [theta,derivative_mul,derivative_X,one_mul] at h
  have he : X * (X*(1-X)*(poly a d).derivative.derivative +
      (C (1-a)+C (2*d+a-1)*X)*(poly a d).derivative - C (d*(d+a))*poly a d)=0 := by
    simp only [map_sub,map_add,map_mul,map_ofNat,map_natCast,map_one] at h ⊢
    linear_combination h
  exact (mul_eq_zero.mp he).resolve_left X_ne_zero

theorem degree_le (a : ℝ) (d : ℕ) : (poly a d).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_poly,c_vanish a d k hk]

theorem theta_degree_le (a : ℝ) (d : ℕ) : (theta (poly a d)).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_theta,coeff_poly,c_vanish a d k hk,mul_zero]

theorem eval_at_zero (a : ℝ) (d : ℕ) : (poly a d).eval 0=1 := by
  rw [← coeff_zero_eq_eval_zero,coeff_poly,c_zero]

end LeanMath.Papers.V14DiagonalPolynomials
