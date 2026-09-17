import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

noncomputable section
namespace LeanMath.Papers.SeriesReversion
open Polynomial

/-- The degree-six jet in Horner form, with zero constant term. -/
def jet (a b c d e f : ℝ) : Polynomial ℝ :=
  X*(C a+X*(C b+X*(C c+X*(C d+X*(C e+X*C f)))))

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem jet_coefficient (a b c d e f : ℝ) (j : ℕ) :
    (jet a b c d e f).coeff j =
      if j=1 then a else if j=2 then b else if j=3 then c else
      if j=4 then d else if j=5 then e else if j=6 then f else 0 := by
  by_cases hj : j ≤ 6
  · interval_cases j <;> norm_num [jet,Polynomial.coeff_X_mul,Polynomial.coeff_C]
  · have h7 : 7 ≤ j := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h7
    rw [Nat.add_comm 7 k]
    simp [jet,Polynomial.coeff_X_mul,Polynomial.coeff_C]

theorem product_coefficient_0 (p q : Polynomial ℝ) :
    (p*q).coeff 0=p.coeff 0*q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ]
  <;> ring

theorem product_coefficient_1 (p q : Polynomial ℝ) :
    (p*q).coeff 1=p.coeff 0*q.coeff 1 + p.coeff 1*q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ]
  <;> ring

theorem product_coefficient_2 (p q : Polynomial ℝ) :
    (p*q).coeff 2=p.coeff 0*q.coeff 2 + p.coeff 1*q.coeff 1 + p.coeff 2*q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ]
  <;> ring

theorem product_coefficient_3 (p q : Polynomial ℝ) :
    (p*q).coeff 3=p.coeff 0*q.coeff 3 + p.coeff 1*q.coeff 2 + p.coeff 2*q.coeff 1 + p.coeff 3*q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ]
  <;> ring

theorem product_coefficient_4 (p q : Polynomial ℝ) :
    (p*q).coeff 4=p.coeff 0*q.coeff 4 + p.coeff 1*q.coeff 3 + p.coeff 2*q.coeff 2 + p.coeff 3*q.coeff 1 + p.coeff 4*q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ]
  <;> ring

theorem product_coefficient_5 (p q : Polynomial ℝ) :
    (p*q).coeff 5=p.coeff 0*q.coeff 5 + p.coeff 1*q.coeff 4 + p.coeff 2*q.coeff 3 + p.coeff 3*q.coeff 2 + p.coeff 4*q.coeff 1 + p.coeff 5*q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ]
  <;> ring

theorem product_coefficient_6 (p q : Polynomial ℝ) :
    (p*q).coeff 6=p.coeff 0*q.coeff 6 + p.coeff 1*q.coeff 5 + p.coeff 2*q.coeff 4 + p.coeff 3*q.coeff 3 + p.coeff 4*q.coeff 2 + p.coeff 5*q.coeff 1 + p.coeff 6*q.coeff 0 := by
  rw [Polynomial.coeff_mul]
  norm_num [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ]
  <;> ring

theorem composition_coefficients (a b c d e f u v w x y z : ℝ) (j : Fin 7) :
    ((jet a b c d e f).comp (jet u v w x y z)).coeff j =
      (![0,
        a*u,
        a*v+b*u^2,
        a*w+2*b*u*v+c*u^3,
        a*x+b*(2*u*w+v^2)+3*c*u^2*v+d*u^4,
        a*y+b*(2*u*x+2*v*w)+c*(3*u^2*w+3*u*v^2)+4*d*u^3*v+e*u^5,
        a*z+b*(2*u*y+2*v*x+w^2)+c*(3*u^2*x+6*u*v*w+v^3)+
          d*(4*u^3*w+6*u^2*v^2)+5*e*u^4*v+f*u^6] : Fin 7 → ℝ) j := by
  change ((X*(C a+X*(C b+X*(C c+X*(C d+X*(C e+X*C f)))))).comp
    (jet u v w x y z)).coeff j = _
  simp only [Polynomial.mul_comp,Polynomial.add_comp,Polynomial.X_comp,Polynomial.C_comp]
  fin_cases j <;>
    norm_num [product_coefficient_0, product_coefficient_1, product_coefficient_2, product_coefficient_3, product_coefficient_4, product_coefficient_5, product_coefficient_6,jet_coefficient,Polynomial.coeff_C] <;> ring

def c1 (a : ℝ) := 1/a
def c2 (a b : ℝ) := -b/a^3
def c3 (a b c : ℝ) := (2*b^2-a*c)/a^5
def c4 (a b c d : ℝ) := (5*a*b*c-a^2*d-5*b^3)/a^7
def c5 (a b c d e : ℝ) := (6*a^2*b*d+3*a^2*c^2+14*b^4-a^3*e-21*a*b^2*c)/a^9
def c6 (a b c d e f : ℝ) :=
  (7*a^3*b*e+7*a^3*c*d+84*a*b^3*c-a^4*f-28*a^2*b^2*d-28*a^2*b*c^2-42*b^5)/a^11

/-- Appendix A: the printed inverse coefficients cancel every term through degree six. -/
theorem inverse_jet_six (a b c d e f : ℝ) (ha : a ≠ 0) (j : Fin 7) :
    ((jet a b c d e f).comp
      (jet (c1 a) (c2 a b) (c3 a b c) (c4 a b c d) (c5 a b c d e) (c6 a b c d e f))).coeff j =
      (X : Polynomial ℝ).coeff j := by
  rw [composition_coefficients]
  fin_cases j <;> norm_num [c1,c2,c3,c4,c5,c6,Polynomial.coeff_X] <;> field_simp [ha] <;> ring

end LeanMath.Papers.SeriesReversion
