import LeanMath.Papers.V14DiagonalWronskian

/-! Bounds keeping the logarithmic derivative positive on the entire positive axis. -/
noncomputable section
namespace LeanMath.Papers.V14DiagonalBounds
open Polynomial Finset
open LeanMath.Papers.V14DiagonalPolynomials LeanMath.Papers.V14DiagonalWronskian

theorem endpoint_terms (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (hd : 0<d)
    (R : ℝ) (hR : 0≤R) : 1+c a d d*R^d ≤ (poly a d).eval R := by
  have hsub : ({0,d} : Finset ℕ) ⊆ range (d+1) := by intro k hk; simp at hk; rcases hk with rfl|rfl <;> simp
  have hh := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun k => c a d k*R^k) (by intros; exact mul_nonneg (c_nonneg a ha d _) (pow_nonneg hR _))
  simpa [poly,eval_finsetSum,eval_monomial,hd.ne',Ne.symm hd.ne',c] using hh

theorem product_dominates_power (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) (hd : 0<d)
    (R : ℝ) (hR : 0<R) : (R-1)^(2*d) < (poly a d).eval R*(poly (-a) d).eval R := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  have hA := endpoint_terms a ha0 d hd R hR.le
  have hB := endpoint_terms (-a) ha' d hd R hR.le
  have hAp := poly_pos a ha0 d R hR.le
  have hBp := poly_pos (-a) ha' d R hR.le
  have hca := c_pos a ha0 d d le_rfl
  have hcb := c_pos (-a) ha' d d le_rfl
  have hprod := mul_le_mul hA hB (by positivity) hAp.le
  have he : (c a d d*R^d)*(c (-a) d d*R^d)=R^(2*d) := by
    rw [mul_mul_mul_comm,top_product a ha d,one_mul,← pow_add,two_mul]
  by_cases h : R ≤ 1
  · have hpow : (R-1)^(2*d) ≤ 1 := by
      rw [show (R-1)^(2*d)=((R-1)^2)^d by rw [pow_mul]]
      apply pow_le_one₀ (sq_nonneg _)
      nlinarith
    nlinarith [mul_pos hca (pow_pos hR d),mul_pos hcb (pow_pos hR d),pow_pos hR (2*d)]
  · have hpow : (R-1)^(2*d) ≤ R^(2*d) := pow_le_pow_left₀ (by linarith) (by linarith) _
    nlinarith [mul_pos hca (pow_pos hR d),mul_pos hcb (pow_pos hR d)]

end LeanMath.Papers.V14DiagonalBounds
