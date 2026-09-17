import LeanMath.Papers.V14DiagonalConvergence
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Coprime.Lemmas

/-! No hidden common factors or positive-axis holes in any type-(d,d) representative. -/
noncomputable section
namespace LeanMath.Papers.V14DiagonalRegularity
open Polynomial
open LeanMath.Papers.V14DiagonalPolynomials LeanMath.Papers.V14DiagonalWronskian
open LeanMath.Papers.V14DiagonalContact

theorem coprime_at_one (P : ℝ[X]) (hP : P.eval 1≠0) : IsCoprime P (X-1) := by
  have hi : Irreducible (X-1 : ℝ[X]) := by simpa using irreducible_X_sub_C (1:ℝ)
  rcases hi.isCoprime_or_dvd P with h|h
  · exact h.symm
  · have he := (dvd_iff_isRoot).mp (show X-C (1:ℝ) ∣ P by simpa using h)
    exact (hP he).elim

theorem coprime_polys (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) :
    IsCoprime (poly a d) (poly (-a) d) := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  have hcop := (coprime_at_one (poly a d) (poly_pos a ha0 d 1 (by norm_num)).ne').pow_right (n := 2*d)
  apply IsRelPrime.isCoprime
  intro q hqA hqB
  have hqE : q ∣ errorPolynomial a d := by
    unfold errorPolynomial
    apply dvd_sub
    · exact dvd_mul_of_dvd_right hqB _
    · apply dvd_mul_of_dvd_right
      exact dvd_sub (dvd_mul_of_dvd_right hqB _) (dvd_mul_of_dvd_left hqA _)
  rw [error_identity a ha0 d] at hqE
  have hu : IsUnit (C a : ℝ[X]) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha.1.ne')
  have hqpow : q ∣ (X-1)^(2*d) := hu.dvd_mul_left.mp hqE
  exact hcop.isUnit_of_dvd' hqA hqpow

theorem coprime_pair (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) :
    IsCoprime (numerator a d) (denominator a d) := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  have hu : IsUnit (C ((poly (-a) d).eval 1) : ℝ[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (poly_pos (-a) ha' d 1 (by norm_num)).ne')
  have hv : IsUnit (C ((poly a d).eval 1) : ℝ[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr (poly_pos a ha0 d 1 (by norm_num)).ne')
  exact (isCoprime_mul_units_left hu hv _ _).mpr (coprime_polys a ha d)

theorem denominator_degree (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) : (denominator a d).natDegree=d := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  apply natDegree_eq_of_le_of_coeff_ne_zero ((natDegree_C_mul_le _ _).trans (degree_le (-a) d))
  rw [coeff_C_mul,coeff_poly]
  exact mul_ne_zero (poly_pos a ha0 d 1 (by norm_num)).ne' (c_pos (-a) ha' d d le_rfl).ne'

/-- Any diagonal pair has a nonzero denominator at every positive residual. -/
theorem diagonal_regular (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) (A B : ℝ[X])
    (hAB : LeanMath.Papers.V14PadeTheorem.IsDiagonal a d A B) (R : ℝ) (hR : 0<R) : B.eval R≠0 := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  have hc := isDiagonal a ha0 d
  have he := LeanMath.Papers.V14AnalyticUniqueness.rational_unique _ _ A B d (fun R : ℝ => R^a)
    hc.1 hc.2.1 hAB.1 hAB.2.1 hc.2.2.1 hAB.2.2.1 hc.2.2.2 hAB.2.2.2
  have hdvd : denominator a d ∣ B := (coprime_pair a ha d).symm.dvd_of_dvd_mul_left
    (he.symm ▸ dvd_mul_left (denominator a d) A)
  obtain ⟨q,hq⟩ := hdvd
  have hB0 : B≠0 := by intro h; apply hAB.2.2.1; simp [h]
  have hD0 : denominator a d≠0 := by intro h; apply hc.2.2.1; simp [h]
  have hq0 : q≠0 := by intro h; apply hB0; simp [hq,h]
  have hn : q.natDegree=0 := by
    have hh := hAB.2.1
    rw [hq,natDegree_mul hD0 hq0,denominator_degree a ha d] at hh
    omega
  have hqc : q=C (q.coeff 0) := eq_C_of_natDegree_eq_zero hn
  have hqv : q.coeff 0≠0 := by intro h; apply hq0; rw [hqc,h,map_zero]
  rw [hq,hqc,eval_mul,eval_C,denominator,eval_mul,eval_C]
  exact mul_ne_zero (mul_ne_zero (poly_pos a ha0 d 1 (by norm_num)).ne'
    (poly_pos (-a) ha' d R hR.le).ne') hqv

/-- All type-(d,d) Padé representatives agree on the whole positive axis. -/
theorem diagonal_value (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) (A B : ℝ[X])
    (hAB : LeanMath.Papers.V14PadeTheorem.IsDiagonal a d A B) (R : ℝ) (hR : 0<R) :
    A.eval R/B.eval R=LeanMath.Papers.V14DiagonalError.correction a d R := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  have hc := isDiagonal a ha0 d
  have he := LeanMath.Papers.V14AnalyticUniqueness.rational_unique _ _ A B d (fun R : ℝ => R^a)
    hc.1 hc.2.1 hAB.1 hAB.2.1 hc.2.2.1 hAB.2.2.1 hc.2.2.2 hAB.2.2.2
  have hD := diagonal_regular a ha d (numerator a d) (denominator a d) hc R hR
  have hB := diagonal_regular a ha d A B hAB R hR
  have hv : A.eval R/B.eval R=(numerator a d).eval R/(denominator a d).eval R := by
    apply (div_eq_div_iff hB hD).mpr
    simpa only [eval_mul] using (congrArg (Polynomial.eval R) he).symm
  simpa [numerator,denominator,LeanMath.Papers.V14DiagonalError.correction,mul_comm] using hv

end LeanMath.Papers.V14DiagonalRegularity
