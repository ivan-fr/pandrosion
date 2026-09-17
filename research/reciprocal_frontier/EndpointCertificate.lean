import LeanMath.Papers.V14DiagonalOrdering

/-! Research extension: an endpoint criterion for ideal diagonal root Padé functions.
This is a consequence of the existing logarithmic derivative identity, not a claim
of historical novelty. No statement concerns rounded coefficients or execution. -/
noncomputable section
namespace LeanMath.Research.EndpointCertificate
open Real Set
open LeanMath.Papers.V14DiagonalPolynomials LeanMath.Papers.V14DiagonalError

/-- Signed relative error of the canonical, ideal diagonal approximant. -/
def relativeError (a : ℝ) (d : ℕ) (R : ℝ) := correction a d R / R^a - 1

theorem logError_monotone (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) :
    MonotoneOn (logError a d) (Ioi 0) := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  have han : -1 < -a ∧ -a<1 := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro x hx; exact (hasDerivAt_logError a ha0 d x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hasDerivAt_logError a ha0 d x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    rw [(hasDerivAt_logError a ha0 d x hx).deriv]
    have he : 0 ≤ (x-1)^(2*d) := by rw [pow_mul]; positivity
    exact div_nonneg (mul_nonneg ha.1.le he)
      (mul_nonneg (mul_nonneg hx.le (poly_pos a ha0 d x hx.le).le)
        (poly_pos (-a) han d x hx.le).le)

theorem relativeError_eq (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0<R) :
    relativeError a d R=exp (-logError a d R)-1 := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  rw [logError_eq a ha0 d R hR]
  have he : -(a*log R-log (correction a d R))=log (correction a d R)-log R*a := by ring
  rw [he,exp_sub,exp_log (correction_pos a ha0 d R hR),←rpow_def_of_pos hR]
  rfl

theorem relativeError_antitone (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) :
    AntitoneOn (relativeError a d) (Ioi 0) := by
  intro x hx y hy hxy
  rw [relativeError_eq a ha d x hx,relativeError_eq a ha d y hy]
  exact sub_le_sub_right (exp_le_exp.mpr (neg_le_neg (logError_monotone a ha d hx hy hxy))) 1

/-- A global, sharp two-endpoint bound on any positive compact interval. -/
theorem endpoint_bound (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ)
    (L U R : ℝ) (hL : 0<L) (hR : R ∈ Icc L U) :
    |relativeError a d R| ≤ max |relativeError a d L| |relativeError a d U| := by
  have hpos : 0<R := hL.trans_le hR.1
  have hU : 0<U := hpos.trans_le hR.2
  have hlow := relativeError_antitone a ha d hpos hU hR.2
  have hupp := relativeError_antitone a ha d hL hpos hR.1
  apply abs_le.mpr
  constructor
  · have h := neg_abs_le (relativeError a d U)
    have hm := le_max_right |relativeError a d L| |relativeError a d U|
    linarith
  · exact hupp.trans ((le_abs_self _).trans (le_max_left _ _))

/-- Uniform certification is equivalent to two scalar inequalities, including d=0. -/
theorem uniform_iff_endpoints (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ)
    (L U tolerance : ℝ) (hL : 0<L) (hLU : L≤U) :
    (∀ R ∈ Icc L U, |relativeError a d R| ≤ tolerance) ↔
      |relativeError a d L| ≤ tolerance ∧ |relativeError a d U| ≤ tolerance := by
  constructor
  · intro h; exact ⟨h L ⟨le_rfl,hLU⟩,h U ⟨hLU,le_rfl⟩⟩
  · rintro ⟨hl,hu⟩ R hR
    exact (endpoint_bound a ha d L U R hL hR).trans (max_le hl hu)

end LeanMath.Research.EndpointCertificate

#print axioms LeanMath.Research.EndpointCertificate.logError_monotone
#print axioms LeanMath.Research.EndpointCertificate.relativeError_eq
#print axioms LeanMath.Research.EndpointCertificate.relativeError_antitone
#print axioms LeanMath.Research.EndpointCertificate.endpoint_bound
#print axioms LeanMath.Research.EndpointCertificate.uniform_iff_endpoints
