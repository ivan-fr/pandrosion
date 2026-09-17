import research.reciprocal_frontier.JointAsymptotic

noncomputable section
namespace LeanMath.Research.EffectiveBounds
open Real Set Polynomial
open LeanMath.Papers.V14DiagonalPolynomials LeanMath.Papers.V14DiagonalError
open LeanMath.Research.JointAsymptotic LeanMath.Research.EndpointCertificate

theorem polynomial_monotone (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) :
    MonotoneOn (fun x : ℝ => (poly a d).eval x) (Ici 0) := by
  intro x hx y hy hxy
  simp only [poly,eval_finsetSum,eval_monomial]
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy k) (c_nonneg a ha d k)

theorem denominator_positive (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0<R) :
    0<denominatorValue a d R := by
  have han : -1 < -a ∧ -a<1 := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  exact mul_pos (mul_pos hR (poly_pos a ha d R hR.le)) (poly_pos (-a) han d R hR.le)

theorem denominator_monotone (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) :
    MonotoneOn (denominatorValue a d) (Ioi 0) := by
  intro x hx y hy hxy
  have han : -1 < -a ∧ -a<1 := ⟨by linarith [ha.2],by linarith [ha.1]⟩
  have hxa : 0≤x := hx.le
  have hya : 0≤y := hy.le
  exact mul_le_mul
    (mul_le_mul hxy (polynomial_monotone a ha d hxa hya hxy) (poly_pos a ha d x hx.le).le hy.le)
    (polynomial_monotone (-a) han d hxa hya hxy)
    (poly_pos (-a) han d x hx.le).le
    (mul_pos hy (poly_pos a ha d y hy.le)).le

def lowerLogBound (a R : ℝ) (d : ℕ) :=
  |a| * |R-1|^(2*d+1)/((2*(d:ℝ)+1)*denominatorValue a d (max 1 R))
def upperLogBound (a R : ℝ) (d : ℕ) :=
  |a| * |R-1|^(2*d+1)/((2*(d:ℝ)+1)*denominatorValue a d (min 1 R))

/-- Explicit two-sided bounds valid at every degree and every positive residual. -/
theorem log_error_bounds (a R : ℝ) (d : ℕ) (ha : -1<a ∧ a<1) (hR : 0<R) :
    lowerLogBound a R d ≤ |logError a d R| ∧
    |logError a d R| ≤ upperLogBound a R d := by
  obtain ⟨t,ht,he⟩ := error_mean_value a R d ha hR
  have hx := segment_positive R t hR ⟨ht.1.le,ht.2.le⟩
  have hmin : 0<min (1:ℝ) R := lt_min (by norm_num) hR
  have hmax : 0<max (1:ℝ) R := lt_max_of_lt_left (by norm_num)
  have hl : min 1 R≤1+(R-1)*t := by
    rcases le_total 1 R with h | h
    · rw [min_eq_left h]; nlinarith [mul_nonneg (sub_nonneg.mpr h) ht.1.le]
    · rw [min_eq_right h]; nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr ht.2.le)]
  have hu : 1+(R-1)*t≤max 1 R := by
    rcases le_total 1 R with h | h
    · rw [max_eq_right h]; nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr ht.2.le)]
    · rw [max_eq_left h]; nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) ht.1.le]
  rw [he,abs_div,abs_mul,abs_pow,abs_of_pos (mul_pos (by positivity) (denominator_positive a ha d _ hx))]
  dsimp [lowerLogBound,upperLogBound]
  constructor
  · exact div_le_div_of_nonneg_left (by positivity)
      (mul_pos (by positivity) (denominator_positive a ha d _ hx))
      (mul_le_mul_of_nonneg_left (denominator_monotone a ha d hx hmax hu) (by positivity))
  · exact div_le_div_of_nonneg_left (by positivity)
      (mul_pos (by positivity) (denominator_positive a ha d _ hmin))
      (mul_le_mul_of_nonneg_left (denominator_monotone a ha d hmin hx hl) (by positivity))

theorem exponential_absolute_bounds (x : ℝ) :
    1-exp (-|x|) ≤ |exp (-x)-1| ∧ |exp (-x)-1| ≤ exp |x|-1 := by
  by_cases hx : 0≤x
  · rw [abs_of_nonneg hx,abs_of_nonpos (sub_nonpos.mpr ((exp_le_one_iff).mpr (neg_nonpos.mpr hx)))]
    constructor
    · linarith
    · have hh := add_one_le_exp x
      have hn := add_one_le_exp (-x)
      linarith
  · have hx := le_of_not_ge hx
    rw [abs_of_nonpos hx,abs_of_nonneg (sub_nonneg.mpr (one_le_exp_iff.mpr (neg_nonneg.mpr hx)))]
    constructor
    · have hh := add_one_le_exp x
      have hn := add_one_le_exp (-x)
      simp only [neg_neg]
      linarith
    · rfl

/-- Finite-parameter bounds on the actual relative error, with no limiting regime. -/
theorem relative_error_bounds (a R : ℝ) (d : ℕ) (ha : 0<a ∧ a<1) (hR : 0<R) :
    1-exp (-lowerLogBound a R d) ≤ |relativeError a d R| ∧
    |relativeError a d R| ≤ exp (upperLogBound a R d)-1 := by
  have hb := log_error_bounds a R d ⟨by linarith [ha.1],ha.2⟩ hR
  rw [relativeError_eq a ha d R hR]
  have he := exponential_absolute_bounds (logError a d R)
  constructor
  · exact (sub_le_sub_left (exp_le_exp.mpr (neg_le_neg hb.1)) 1).trans he.1
  · exact he.2.trans (sub_le_sub_right (exp_le_exp.mpr hb.2) 1)

def necessaryBound (p ell : ℝ) (d : ℕ) :=
  max (1-exp (-lowerLogBound (1/p) (exp (-ell/(p+1))) d))
      (1-exp (-lowerLogBound (1/p) (exp (ell/(p+1))) d))
def sufficientBound (p ell : ℝ) (d : ℕ) :=
  max (exp (upperLogBound (1/p) (exp (-ell/(p+1))) d)-1)
      (exp (upperLogBound (1/p) (exp (ell/(p+1))) d)-1)

theorem worst_error_bounds (p ell : ℝ) (d : ℕ) (hp : 1<p) :
    necessaryBound p ell d ≤ worstError p ell d ∧
    worstError p ell d ≤ sufficientBound p ell d := by
  have ha : 0<1/p ∧ 1/p<1 :=
    ⟨one_div_pos.mpr (by linarith),(div_lt_one (by linarith : 0<p)).mpr hp⟩
  have hl := relative_error_bounds (1/p) (exp (-ell/(p+1))) d ha (exp_pos _)
  have hu := relative_error_bounds (1/p) (exp (ell/(p+1))) d ha (exp_pos _)
  exact ⟨max_le_max hl.1 hu.1,max_le_max hl.2 hu.2⟩

/-- A finite certificate: an upper bound accepts d, and lower bounds reject
all smaller degrees. This is a sufficient certificate, not a complete algorithm. -/
theorem certified_minimal_degree (p ell tol : ℝ) (d : ℕ) (hp : 1<p)
    (accept : sufficientBound p ell d ≤ tol)
    (reject : ∀ j<d, tol<necessaryBound p ell j) :
    worstError p ell d ≤ tol ∧ ∀ j<d, tol<worstError p ell j := by
  constructor
  · exact (worst_error_bounds p ell d hp).2.trans accept
  · intro j hj
    exact (reject j hj).trans_le (worst_error_bounds p ell j hp).1

theorem certified_uniform_degree (p ell tol : ℝ) (d : ℕ) (hp : 1<p) (hell : 0≤ell)
    (accept : sufficientBound p ell d ≤ tol)
    (reject : ∀ j<d, tol<necessaryBound p ell j) :
    (∀ R ∈ Icc (exp (-ell/(p+1))) (exp (ell/(p+1))), |relativeError (1/p) d R|≤tol) ∧
    ∀ j<d, ¬(∀ R ∈ Icc (exp (-ell/(p+1))) (exp (ell/(p+1))), |relativeError (1/p) j R|≤tol) := by
  have hh := certified_minimal_degree p ell tol d hp accept reject
  constructor
  · exact (worstError_certificate p ell d hp hell tol).mpr hh.1
  · intro j hj hu
    exact (not_le_of_gt (hh.2 j hj)) ((worstError_certificate p ell j hp hell tol).mp hu)

end LeanMath.Research.EffectiveBounds

#print axioms LeanMath.Research.EffectiveBounds.polynomial_monotone
#print axioms LeanMath.Research.EffectiveBounds.denominator_positive
#print axioms LeanMath.Research.EffectiveBounds.denominator_monotone
#print axioms LeanMath.Research.EffectiveBounds.log_error_bounds
#print axioms LeanMath.Research.EffectiveBounds.exponential_absolute_bounds
#print axioms LeanMath.Research.EffectiveBounds.relative_error_bounds
#print axioms LeanMath.Research.EffectiveBounds.worst_error_bounds
#print axioms LeanMath.Research.EffectiveBounds.certified_minimal_degree
#print axioms LeanMath.Research.EffectiveBounds.certified_uniform_degree
