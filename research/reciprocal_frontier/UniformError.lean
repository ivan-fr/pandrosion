import research.reciprocal_frontier.ProductIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

noncomputable section
namespace LeanMath.Research.UniformError
open Real Set Filter Polynomial MeasureTheory
open scoped Topology
open LeanMath.Papers.V14DiagonalPolynomials LeanMath.Papers.V14DiagonalError
open LeanMath.Research.UniformTransfer LeanMath.Research.ProductIdentity
open LeanMath.Research.JointAsymptotic LeanMath.Research.EffectiveBounds

def kernel (a : ℝ) (d : ℕ) (R : ℝ) :=
  (R-1)^(2*d)/denominatorValue a d R

def referenceError (d : ℕ) (R : ℝ) := ∫ t in (1:ℝ)..R, kernel 0 d t

theorem kernel_continuous (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0<R) :
    ContinuousAt (kernel a d) R := by
  apply ContinuousAt.div
  · fun_prop
  · exact (continuousAt_id.mul (poly a d).continuous.continuousAt).mul (poly (-a) d).continuous.continuousAt
  · exact (denominator_positive a ha d R hR).ne'

theorem reference_derivative (d : ℕ) (R : ℝ) (hR : 0<R) :
    HasDerivAt (referenceError d) (kernel 0 d R) R := by
  apply intervalIntegral.integral_hasDerivAt_right
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht0 : 0<t := (lt_min (by norm_num : (0:ℝ)<1) hR).trans_le ht.1
    exact (kernel_continuous 0 (by norm_num) d t ht0).continuousWithinAt
  · exact ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun t ht => kernel_continuous 0 (by norm_num) d t ht) R hR
  · exact kernel_continuous 0 (by norm_num) d R hR

theorem reference_one (d : ℕ) : referenceError d 1=0 := by simp [referenceError]

theorem kernel_bounds (a : ℝ) (ha : -1<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0<R) :
    delta a d*kernel 0 d R≤kernel a d R ∧ kernel a d R≤kernel 0 d R := by
  have hp := polynomial_bounds a ha d R hR.le
  have hd := delta_positive a ha d
  have hA := denominator_positive a ha d R hR
  have h0 := denominator_positive 0 (by norm_num) d R hR
  have hn : 0≤(R-1)^(2*d) := by rw [pow_mul]; positivity
  have hlo : denominatorValue 0 d R≤denominatorValue a d R := by
    dsimp [denominatorValue]; simp only [neg_zero]
    nlinarith [mul_le_mul_of_nonneg_left hp.1 hR.le]
  have hhi : delta a d*denominatorValue a d R≤denominatorValue 0 d R := by
    have hh := (le_div_iff₀ hd).mp hp.2
    dsimp [denominatorValue]; simp only [neg_zero]
    nlinarith [mul_le_mul_of_nonneg_left hh hR.le]
  constructor
  · dsimp [kernel]
    rw [←mul_div_assoc]
    apply (div_le_div_iff₀ h0 hA).mpr
    nlinarith [mul_le_mul_of_nonneg_left hhi hn]
  · exact div_le_div_of_nonneg_left hn h0 hlo

theorem kernel_positive (d : ℕ) (R : ℝ) (hR : 0<R) (hne : R≠1) : 0<kernel 0 d R := by
  apply div_pos
  · rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)) _
  · exact denominator_positive 0 (by norm_num) d R hR

theorem reference_mean_value (d : ℕ) (R : ℝ) (hR : 0<R) :
    ∃ t ∈ Ioo (0:ℝ) 1, referenceError d R=(R-1)*kernel 0 d (1+(R-1)*t) := by
  let f := fun t : ℝ => referenceError d (1+(R-1)*t)
  let f' := fun t : ℝ => kernel 0 d (1+(R-1)*t)*(R-1)
  have hf : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (f' t) t := by
    intro t ht
    simpa only [f,f',Function.comp_def,id_eq,mul_one] using (reference_derivative d _ (segment_positive R t hR ht)).comp t
      (((hasDerivAt_id t).const_mul (R-1)).const_add 1)
  obtain ⟨t,ht,he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' (by norm_num : (0:ℝ)<1)
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => hf t ⟨ht.1.le,ht.2.le⟩)
    id (fun _ : ℝ => (1:ℝ)) (by fun_prop) (fun t _ => hasDerivAt_id t)
  refine ⟨t,ht,?_⟩
  simpa [f,f',reference_one,mul_comm] using he.symm

theorem reference_nonzero (d : ℕ) (R : ℝ) (hR : 0<R) (hne : R≠1) : referenceError d R≠0 := by
  obtain ⟨t,ht,he⟩ := reference_mean_value d R hR
  rw [he]
  have hx : 1+(R-1)*t≠1 := by
    intro hh
    have hz : (R-1)*t=0 := by linarith
    exact (mul_ne_zero (sub_ne_zero.mpr hne) ht.1.ne') hz
  exact mul_ne_zero (sub_ne_zero.mpr hne)
    (kernel_positive d _ (segment_positive R t hR ⟨ht.1.le,ht.2.le⟩) hx).ne'

/-- Complete, unconditional finite-product transfer for all degrees and all positive residuals. -/
theorem uniform_transfer (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0<R) (hne : R≠1) :
    delta a d≤logError a d R/(a*referenceError d R) ∧
    logError a d R/(a*referenceError d R)≤1 := by
  have ha0 : -1<a ∧ a<1 := ⟨by linarith [ha.1],ha.2⟩
  let f := fun t : ℝ => logError a d (1+(R-1)*t)
  let f' := fun t : ℝ => (a*kernel a d (1+(R-1)*t))*(R-1)
  let g := fun t : ℝ => referenceError d (1+(R-1)*t)
  let g' := fun t : ℝ => kernel 0 d (1+(R-1)*t)*(R-1)
  have hf : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (f' t) t := by
    intro t ht
    convert! (hasDerivAt_logError a ha0 d _ (segment_positive R t hR ht)).comp t
      (((hasDerivAt_id t).const_mul (R-1)).const_add 1) using 1
    dsimp [f',kernel,denominatorValue]
    ring
  have hg : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt g (g' t) t := by
    intro t ht
    simpa only [g,g',Function.comp_def,id_eq,mul_one] using (reference_derivative d _ (segment_positive R t hR ht)).comp t
      (((hasDerivAt_id t).const_mul (R-1)).const_add 1)
  obtain ⟨t,ht,he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' (by norm_num : (0:ℝ)<1)
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => hf t ⟨ht.1.le,ht.2.le⟩)
    g g' (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht => hg t ⟨ht.1.le,ht.2.le⟩)
  simp only [f,g,f',g',mul_zero,add_zero,mul_one,add_sub_cancel,logError_one,reference_one,sub_zero] at he
  have hx := segment_positive R t hR ⟨ht.1.le,ht.2.le⟩
  have hxne : 1+(R-1)*t≠1 := by
    intro hh
    have hz : (R-1)*t=0 := by linarith
    exact (mul_ne_zero (sub_ne_zero.mpr hne) ht.1.ne') hz
  have hk := kernel_positive d _ hx hxne
  have hJ := reference_nonzero d R hR hne
  have he' : referenceError d R*(a*kernel a d (1+(R-1)*t))=
      logError a d R*kernel 0 d (1+(R-1)*t) := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr hne)
    simpa only [mul_assoc] using he
  have hr : logError a d R/(a*referenceError d R)=
      kernel a d (1+(R-1)*t)/kernel 0 d (1+(R-1)*t) := by
    apply (div_eq_div_iff (mul_ne_zero ha.1.ne' hJ) hk.ne').mpr
    nlinarith [he']
  rw [hr]
  have hb := kernel_bounds a ha0 d _ hx
  exact ⟨(le_div_iff₀ hk).mpr hb.1,(div_le_one hk).mpr hb.2⟩

theorem delta_product (a : ℝ) (d : ℕ) :
    delta a d=∏ j ∈ Finset.range d, (1-a^2/((j:ℝ)+1)^2) := by
  induction d with
  | zero => simp [delta]
  | succ d ih => simp only [delta,Finset.prod_range_succ,ih]

theorem sinc_le_delta (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) :
    sin (π*a)/(π*a)≤delta a d := by
  have hn : π*a≠0 := (mul_pos pi_pos ha.1).ne'
  have hl : Tendsto (delta a) atTop (𝓝 (sin (π*a)/(π*a))) := by
    have hh := (Real.tendsto_euler_sin_prod a).div_const (π*a)
    convert hh using 1
    ext n
    rw [←delta_product]
    field_simp [ha.1.ne']
  apply le_of_tendsto hl
  filter_upwards [eventually_ge_atTop d] with n hn
  exact delta_antitone a ⟨by linarith [ha.1],ha.2⟩ hn

/-- Degree- and residual-independent comparison constant. No unproved product identity is assumed. -/
theorem uniform_sinc_transfer (a : ℝ) (ha : 0<a ∧ a<1) (d : ℕ) (R : ℝ) (hR : 0<R) (hne : R≠1) :
    sin (π*a)/(π*a)≤logError a d R/(a*referenceError d R) ∧
    logError a d R/(a*referenceError d R)≤1 := by
  have hh := uniform_transfer a ha d R hR hne
  exact ⟨(sinc_le_delta a ha d).trans hh.1,hh.2⟩

/-- Root-exponent form, directly expressing the relative discrepancy from the reference model. -/
theorem root_uniform_transfer (p : ℝ) (hp : 1<p) (d : ℕ) (R : ℝ) (hR : 0<R) (hne : R≠1) :
    0≤1-p*logError (1/p) d R/referenceError d R ∧
    1-p*logError (1/p) d R/referenceError d R≤1-sin (π/p)/(π/p) := by
  have hp0 : 0<p := by linarith
  have hh := uniform_sinc_transfer (1/p) ⟨one_div_pos.mpr hp0,(div_lt_one hp0).mpr hp⟩ d R hR hne
  have hJ := reference_nonzero d R hR hne
  have he : logError (1/p) d R/((1/p)*referenceError d R)=p*logError (1/p) d R/referenceError d R := by
    field_simp
  rw [he] at hh
  have hpi : π*(1/p)=π/p := by ring
  rw [hpi] at hh
  constructor <;> linarith [hh.1,hh.2]

end LeanMath.Research.UniformError

#print axioms LeanMath.Research.UniformError.kernel_continuous
#print axioms LeanMath.Research.UniformError.reference_derivative
#print axioms LeanMath.Research.UniformError.reference_one
#print axioms LeanMath.Research.UniformError.kernel_bounds
#print axioms LeanMath.Research.UniformError.kernel_positive
#print axioms LeanMath.Research.UniformError.reference_mean_value
#print axioms LeanMath.Research.UniformError.reference_nonzero
#print axioms LeanMath.Research.UniformError.uniform_transfer
#print axioms LeanMath.Research.UniformError.delta_product
#print axioms LeanMath.Research.UniformError.sinc_le_delta
#print axioms LeanMath.Research.UniformError.uniform_sinc_transfer
#print axioms LeanMath.Research.UniformError.root_uniform_transfer
