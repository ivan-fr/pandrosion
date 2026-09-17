import LeanMath.Papers.V14DiagonalError
import LeanMath.Papers.V14DiagonalBounds

/-! Global strict enclosures for every positive diagonal degree. -/
noncomputable section
namespace LeanMath.Papers.V14DiagonalOrdering
open Real Polynomial Filter Set
open scoped Topology
open LeanMath.Papers.V14DiagonalPolynomials LeanMath.Papers.V14DiagonalError

def logCorrection (a : ℝ) (d : ℕ) (R : ℝ) := a*log R-logError a d R

theorem logCorrection_eq (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0<R) :
    logCorrection a d R=log (correction a d R) := by
  rw [logCorrection,logError_eq a ha d R hR]; ring

theorem logCorrection_strictMono (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) (hd : 0<d) :
    StrictMonoOn (logCorrection a d) (Ioi 0) := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  have hder : ∀ R, 0<R → HasDerivAt (logCorrection a d)
      (a/R-a*(R-1)^(2*d)/(R*(poly a d).eval R*(poly (-a) d).eval R)) R := by
    intro R hR
    exact ((hasDerivAt_log hR.ne').const_mul a).sub (hasDerivAt_logError a ha0 d R hR)
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro R hR; exact (hder R hR).continuousAt.continuousWithinAt
  · intro R hR
    rw [interior_Ioi] at hR
    rw [(hder R hR).deriv]
    have hA := poly_pos a ha0 d R hR.le
    have hB := poly_pos (-a) ha' d R hR.le
    have hb := V14DiagonalBounds.product_dominates_power a ha d hd R hR
    apply sub_pos.mpr
    apply (div_lt_div_iff₀ (mul_pos (mul_pos hR hA) hB) hR).mpr
    nlinarith [mul_pos ha.1 (sub_pos.mpr hb),mul_pos hR (mul_pos ha.1 (sub_pos.mpr hb))]

theorem error_positive (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 1<R) :
    0<logError a d R := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  have hm : StrictMonoOn (logError a d) (Icc 1 R) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 1 R)
    · intro t ht
      exact (hasDerivAt_logError a ha0 d t (by linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0<t := by linarith [ht.1]
      rw [(hasDerivAt_logError a ha0 d t ht0).deriv]
      exact div_pos (mul_pos ha.1 (pow_pos (by linarith [ht.1]) _))
        (mul_pos (mul_pos ht0 (poly_pos a ha0 d t ht0.le)) (poly_pos (-a) ha' d t ht0.le))
  simpa only [logError_one] using hm ⟨le_rfl,hR.le⟩ ⟨hR.le,le_rfl⟩ hR

theorem error_negative (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0<R) (hR1 : R<1) :
    logError a d R<0 := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  have ha' : -1 < -a ∧ -a<1 := by constructor <;> linarith [ha.1,ha.2]
  have hm : StrictMonoOn (logError a d) (Icc R 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc R 1)
    · intro t ht
      exact (hasDerivAt_logError a ha0 d t (hR.trans_le ht.1)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht0 : 0<t := hR.trans ht.1
      rw [(hasDerivAt_logError a ha0 d t ht0).deriv]
      have hp : 0<(t-1)^(2*d) := by
        rw [pow_mul]
        exact pow_pos (sq_pos_of_ne_zero (by linarith [ht.2])) _
      exact div_pos (mul_pos ha.1 hp)
        (mul_pos (mul_pos ht0 (poly_pos a ha0 d t ht0.le)) (poly_pos (-a) ha' d t ht0.le))
  simpa only [logError_one] using hm ⟨le_rfl,hR1.le⟩ ⟨hR1.le,le_rfl⟩ hR1

theorem above_one_below_root (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) (hd : 0<d)
    (R : ℝ) (hR : 1<R) : 1<correction a d R ∧ correction a d R<R^a := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  have hR0 : 0<R := by linarith
  have hc := correction_pos a ha0 d R hR0
  have hm := logCorrection_strictMono a ha d hd (by norm_num : (1:ℝ)∈Ioi 0) hR0 hR
  rw [logCorrection_eq a ha0 d 1 (by norm_num),correction_one a ha0 d,log_one,
    logCorrection_eq a ha0 d R hR0] at hm
  have he := error_positive a ha d R hR
  rw [logError_eq a ha0 d R hR0] at he
  refine ⟨(log_pos_iff hc.le).mp hm,?_⟩
  apply (log_lt_log_iff hc (rpow_pos_of_pos hR0 a)).mp
  rw [log_rpow hR0]
  linarith

theorem below_one_above_root (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) (hd : 0<d)
    (R : ℝ) (hR : 0<R) (hR1 : R<1) : R^a<correction a d R ∧ correction a d R<1 := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  have hc := correction_pos a ha0 d R hR
  have hm := logCorrection_strictMono a ha d hd hR (by norm_num : (1:ℝ)∈Ioi 0) hR1
  rw [logCorrection_eq a ha0 d 1 (by norm_num),correction_one a ha0 d,log_one,
    logCorrection_eq a ha0 d R hR] at hm
  have he := error_negative a ha d R hR hR1
  rw [logError_eq a ha0 d R hR] at he
  constructor
  · apply (log_lt_log_iff (rpow_pos_of_pos hR a) hc).mp
    rw [log_rpow hR]; linarith
  · exact (log_neg_iff hc).mp hm

end LeanMath.Papers.V14DiagonalOrdering
