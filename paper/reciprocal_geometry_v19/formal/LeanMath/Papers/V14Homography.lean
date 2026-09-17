import LeanMath.Papers.V14Fused
import LeanMath.Papers.V14Pade
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Clearing the Cayley substitution preserves a common degree bound. -/
noncomputable section
namespace LeanMath.Papers.V14Homography
open Polynomial Finset

/-- Homogeneous substitution y=(R-1)/(R+1), cleared to degree d. -/
def clear (P : ℝ[X]) (d : ℕ) : ℝ[X] :=
  ∑ k ∈ range (d+1), C (P.coeff k)*(X-1)^k*(X+1)^(d-k)

theorem clear_degree (P : ℝ[X]) (d : ℕ) : (clear P d).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  have hk' : k ≤ d := by simpa using (Nat.le_of_lt_succ (mem_range.mp hk))
  have hm : ((X:ℝ[X])-1).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
  have hp : ((X:ℝ[X])+1).natDegree ≤ 1 := natDegree_add_le_of_degree_le (by simp) (by simp)
  have h1 := natDegree_pow_le (p:=((X:ℝ[X])-1)) (n:=k)
  have h2 := natDegree_pow_le (p:=((X:ℝ[X])+1)) (n:=d-k)
  have h3 := natDegree_mul_le (p:=C (P.coeff k)) (q:=((X:ℝ[X])-1)^k)
  have h4 := natDegree_mul_le (p:=C (P.coeff k)*((X:ℝ[X])-1)^k) (q:=((X:ℝ[X])+1)^(d-k))
  simp only [natDegree_C,zero_add] at h3
  have hh1 : ((X-1:ℝ[X])^k).natDegree ≤ k := h1.trans (by simpa using Nat.mul_le_mul_left k hm)
  have hh2 : ((X+1:ℝ[X])^(d-k)).natDegree ≤ d-k := h2.trans (by simpa using Nat.mul_le_mul_left (d-k) hp)
  omega

theorem clear_eval (P : ℝ[X]) (d : ℕ) (hd : P.natDegree ≤ d) (R : ℝ)
    (hR : R+1 ≠ 0) :
    (clear P d).eval R = P.eval ((R-1)/(R+1))*(R+1)^d := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  simp only [clear,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_sub,eval_add,eval_X,eval_one,sum_mul]
  apply sum_congr rfl
  intro k hk
  have hkd : k ≤ d := Nat.le_of_lt_succ (mem_range.mp hk)
  rw [div_pow]
  conv_rhs => rw [show d = k+(d-k) from (Nat.add_sub_of_le hkd).symm,pow_add]
  field_simp
  <;> ring

/-- One common homogeneous degree cancels between numerator and denominator. -/
theorem quotient_eval (P Q : ℝ[X]) (d : ℕ) (hP : P.natDegree ≤ d)
    (hQ : Q.natDegree ≤ d) (R : ℝ) (hR : R+1 ≠ 0) :
    (clear P d).eval R/(clear Q d).eval R =
      P.eval ((R-1)/(R+1))/Q.eval ((R-1)/(R+1)) := by
  rw [clear_eval P d hP R hR,clear_eval Q d hQ R hR]
  exact mul_div_mul_right _ _ (pow_ne_zero d hR)

/-- Proposition 11.1: degree bound in the original residual R. -/
theorem fused_residual_degree (Pg Qg Ph Qh : ℝ[X]) (dg dh : ℕ)
    (hpg : Pg.natDegree ≤ dg) (hqg : Qg.natDegree ≤ dg)
    (hph : Ph.natDegree ≤ dh) (hqh : Qh.natDegree ≤ dh) :
    ∃ A B : ℝ[X], A.natDegree ≤ 2*dg+2*dh+4 ∧ B.natDegree ≤ 2*dg+2*dh+4 ∧
      ∀ R : ℝ, 0 < R → A.eval R/B.eval R =
        V14Fused.fused Pg Qg Ph Qh (LeanMath.Papers.Cayley.chi R) := by
  let P := V14Fused.numerator Pg Qg Ph Qh
  let Q := P.comp (-X)
  let d := 2*dg+2*dh+4
  have hP : P.natDegree ≤ d := V14Fused.numerator_degree _ _ _ _ _ _ hpg hqg hph hqh
  have hQ : Q.natDegree ≤ d := by
    have hh := natDegree_comp_le (p:=P) (q:=-(X:ℝ[X]))
    simp only [natDegree_neg,natDegree_X,mul_one] at hh
    exact hh.trans hP
  refine ⟨clear P d,clear Q d,clear_degree _ _,clear_degree _ _,fun R hR => ?_⟩
  rw [quotient_eval P Q d hP hQ R (by linarith)]
  simp [P,Q,V14Fused.fused,LeanMath.Papers.Cayley.chi]

end LeanMath.Papers.V14Homography
