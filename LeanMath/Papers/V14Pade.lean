import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

/-! Algebraic Padé lifting and uniqueness. The target formal series is explicit
in the hypotheses; no equality with an analytic root is assumed by fiat. -/
noncomputable section
namespace LeanMath.Papers.V14Pade
open Polynomial

abbrev PS := PowerSeries ℝ

def numerator (P Q : ℝ[X]) := Q.comp (X^2)+X*P.comp (X^2)
def denominator (P Q : ℝ[X]) := Q.comp (X^2)-X*P.comp (X^2)

def Matches (F : PS) (P Q : ℝ[X]) (n : ℕ) : Prop :=
  (PowerSeries.X:PS)^n ∣ (Q:PS)*F-(P:PS)

/-- The polynomial-to-series map commutes with substitution y↦y². -/
theorem expand_polynomial (P : ℝ[X]) :
    PowerSeries.expand 2 (by decide) (P:PS) = (P.comp (X^2):ℝ[X]) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [map_add,hP,hQ]
  | monomial n a =>
    simp only [Polynomial.coe_monomial,PowerSeries.expand_monomial]
    simp
    rw [← pow_mul]
    exact PowerSeries.monomial_eq_C_mul_X_pow a (2*n)

/-- Near-balanced indices give degree m+n+1 in the unsquared coordinate. -/
theorem lifted_degrees (P Q : ℝ[X]) (m n : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n)
    (hbal : n=m ∨ n=m+1) :
    (numerator P Q).natDegree ≤ m+n+1 ∧
    (denominator P Q).natDegree ≤ m+n+1 := by
  have heP := natDegree_comp_le (p:=P) (q:=(X:ℝ[X])^2)
  have heQ := natDegree_comp_le (p:=Q) (q:=(X:ℝ[X])^2)
  simp only [natDegree_X_pow] at heP heQ
  have hm := natDegree_mul_le (p:=(X:ℝ[X])) (q:=P.comp (X^2))
  simp only [natDegree_X] at hm
  have h1 : (Q.comp (X^2)).natDegree ≤ m+n+1 := by rcases hbal with h | h <;> omega
  have h2 : (X*P.comp (X^2)).natDegree ≤ m+n+1 := by rcases hbal with h | h <;> omega
  exact ⟨natDegree_add_le_of_degree_le h1 h2,by simpa [denominator] using natDegree_sub_le_of_le h1 h2⟩

/-- Contact-order doubling plus one under reciprocal lifting. The displayed
relation on F is exactly F=(1+y S(y²))/(1-y S(y²)), without division. -/
theorem lift_contact (S F : PS) (P Q : ℝ[X]) (d : ℕ)
    (hmatch : Matches S P Q d)
    (htarget : F-1 = PowerSeries.X*PowerSeries.expand 2 (by decide) S*(F+1)) :
    Matches F (numerator P Q) (denominator P Q) (2*d+1) := by
  obtain ⟨W,hW⟩ := hmatch
  have hex := congrArg (PowerSeries.expand 2 (by decide)) hW
  simp only [map_sub,map_mul,map_pow,PowerSeries.expand_X,expand_polynomial] at hex
  unfold Matches numerator denominator
  refine ⟨PowerSeries.expand 2 (by decide) W*(F+1), ?_⟩
  simp only [Polynomial.coe_sub,Polynomial.coe_add,Polynomial.coe_mul,Polynomial.coe_X]
  have hid : ((Q.comp (X^2):ℝ[X]):PS)*F-((Q.comp (X^2):ℝ[X]):PS) =
      ((Q.comp (X^2):ℝ[X]):PS)*(F-1) := by ring
  calc
    _ = PowerSeries.X*((Q.comp (X^2):ℝ[X]):PS)*PowerSeries.expand 2 (by decide) S*(F+1)-
        PowerSeries.X*((P.comp (X^2):ℝ[X]):PS)*(F+1) := by
      have h := congrArg (fun z : PS => ((Q.comp (X^2):ℝ[X]):PS)*z) htarget
      linear_combination h
    _ = PowerSeries.X*(((Q.comp (X^2):ℝ[X]):PS)*PowerSeries.expand 2 (by decide) S-
        ((P.comp (X^2):ℝ[X]):PS))*(F+1) := by ring
    _ = _ := by rw [hex]; simp only [←pow_mul]; ring

/-- Padé uniqueness: two type-(d,d) pairs matching the same series through
order 2d have identical cross products. No analytic or numerical oracle. -/
theorem diagonal_unique (F : PS) (P Q A B : ℝ[X]) (d : ℕ)
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d)
    (hmatch : Matches F P Q (2*d+1)) (hamatch : Matches F A B (2*d+1)) :
    P*B=A*Q := by
  have hdegree : (P*B-A*Q).natDegree ≤ 2*d := by
    have h1 := natDegree_mul_le_of_le hP hB
    have h2 := natDegree_mul_le_of_le hA hQ
    have h3 := natDegree_sub_le_of_le h1 h2
    simpa [two_mul] using h3
  have hdvd : (PowerSeries.X:PS)^(2*d+1) ∣ ((P*B-A*Q:ℝ[X]):PS) := by
    have hh := dvd_sub (dvd_mul_of_dvd_right hamatch (Q:PS))
      (dvd_mul_of_dvd_right hmatch (B:PS))
    convert hh using 1 <;> simp only [Polynomial.coe_sub,Polynomial.coe_mul] <;> ring
  apply sub_eq_zero.mp
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_zero]
  by_cases hk : k < 2*d+1
  · have h := PowerSeries.X_pow_dvd_iff.mp hdvd k hk
    simpa only [Polynomial.coeff_coe] using h
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- The lifted approximant is the unique diagonal member for the lifted target
in the Cayley variable, at every near-balanced index. -/
theorem near_balanced_identification (S F : PS) (P Q A B : ℝ[X]) (m n : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ n) (hbal : n=m ∨ n=m+1)
    (hmatch : Matches S P Q (m+n+1))
    (htarget : F-1 = PowerSeries.X*PowerSeries.expand 2 (by decide) S*(F+1))
    (hA : A.natDegree ≤ m+n+1) (hB : B.natDegree ≤ m+n+1)
    (hdiag : Matches F A B (2*(m+n+1)+1)) :
    numerator P Q*B=A*denominator P Q := by
  have hd := lifted_degrees P Q m n hP hQ hbal
  exact diagonal_unique F _ _ A B _ hd.1 hd.2 hA hB
    (lift_contact S F P Q _ hmatch htarget) hdiag

end LeanMath.Papers.V14Pade
