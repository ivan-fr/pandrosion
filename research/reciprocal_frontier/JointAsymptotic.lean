import research.reciprocal_frontier.EndpointCertificate
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Analysis.Calculus.DSlope

noncomputable section
namespace LeanMath.Research.JointAsymptotic
open Real Set Filter Polynomial
open scoped Topology
open LeanMath.Papers.V14DiagonalPolynomials LeanMath.Papers.V14DiagonalError

def denominatorValue (a : ℝ) (d : ℕ) (R : ℝ) :=
  R*(poly a d).eval R*(poly (-a) d).eval R

theorem coefficient_continuous (d k : ℕ) (a : ℝ) (ha : a<1) :
    ContinuousAt (fun b : ℝ => c b d k) a := by
  induction k with
  | zero => exact continuousAt_const
  | succ k ih =>
    apply ContinuousAt.div
    · exact ih.mul (continuousAt_const.mul ((continuousAt_const.add continuousAt_id).sub continuousAt_const))
    · exact continuousAt_const.mul (continuousAt_const.sub continuousAt_id)
    · have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      dsimp
      exact mul_ne_zero (by positivity) (by linarith)

theorem polynomial_continuous (d : ℕ) (a R : ℝ) (ha : a<1) :
    ContinuousAt (fun z : ℝ×ℝ => (poly z.1 d).eval z.2) (a,R) := by
  simp only [poly,eval_finsetSum,eval_monomial]
  have hh : ∀ s : Finset ℕ, ContinuousAt (fun z : ℝ×ℝ => ∑ k ∈ s, c z.1 d k*z.2^k) (a,R) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ×ℝ => (0:ℝ)) (a,R))
    | @insert k s hk ih =>
      simp only [Finset.sum_insert hk]
      exact (((coefficient_continuous d k a ha).comp continuousAt_fst).mul (continuousAt_snd.pow k)).add ih
  exact hh _

theorem coefficient_zero (d k : ℕ) : c 0 d k=(d.choose k:ℝ)^2 := by
  induction k with
  | zero => simp [c]
  | succ k ih =>
    by_cases hk : k<d
    · have he : (d.choose (k+1):ℝ)*((k:ℝ)+1)=(d.choose k:ℝ)*((d:ℝ)-k) := by
        have hh := congrArg (fun n : ℕ => (n:ℝ)) (Nat.choose_succ_right_eq d k)
        simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub hk.le] using hh
      rw [c,ih]
      simp only [add_zero,sub_zero]
      apply (div_eq_iff (by positivity : ((k:ℝ)+1)*((k:ℝ)+1)≠0)).mpr
      nlinarith [sq_nonneg ((d.choose (k+1):ℝ)*((k:ℝ)+1)-(d.choose k:ℝ)*((d:ℝ)-k)),
        congrArg (fun x : ℝ => x^2) he]
    · rw [c_vanish 0 d (k+1) (by omega),Nat.choose_eq_zero_of_lt (by omega)]
      norm_num

theorem polynomial_zero_one (d : ℕ) : (poly 0 d).eval 1=((2*d).choose d:ℝ) := by
  simp only [poly,eval_finsetSum,eval_monomial,one_pow,mul_one,coefficient_zero]
  exact_mod_cast Nat.sum_range_choose_sq d

theorem segment_positive (R t : ℝ) (hR : 0<R) (ht : t ∈ Icc 0 1) :
    0<1+(R-1)*t := by
  by_cases h : t=0
  · simp [h]
  · have hp : 0<R*t := mul_pos hR (lt_of_le_of_ne ht.1 (Ne.symm h))
    nlinarith [ht.2]

/-- Cauchy's mean value theorem exposes the exact joint remainder. -/
theorem error_mean_value (a R : ℝ) (d : ℕ) (ha : -1<a ∧ a<1) (hR : 0<R) :
    ∃ t ∈ Ioo (0:ℝ) 1,
      logError a d R = a*(R-1)^(2*d+1) /
        ((2*(d:ℝ)+1)*denominatorValue a d (1+(R-1)*t)) := by
  let f := fun t : ℝ => logError a d (1+(R-1)*t)
  let f' := fun t : ℝ => a*(R-1)^(2*d+1)*t^(2*d)/denominatorValue a d (1+(R-1)*t)
  have hf : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f (f' t) t := by
    intro t ht
    have hh := (hasDerivAt_logError a ha d (1+(R-1)*t) (segment_positive R t hR ht)).comp t
      (((hasDerivAt_id t).const_mul (R-1)).const_add 1)
    convert! hh using 1
    dsimp [f',denominatorValue]
    rw [add_sub_cancel_left,mul_pow,pow_succ]
    ring
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t^(2*d+1))
      ((2*(d:ℝ)+1)*t^(2*d)) t := by
    intro t
    convert! (hasDerivAt_id t).pow (2*d+1) using 1
    simp
  obtain ⟨t,ht,he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' (by norm_num : (0:ℝ)<1)
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => hf t ⟨ht.1.le,ht.2.le⟩)
    (fun t : ℝ => t^(2*d+1)) (fun t => (2*(d:ℝ)+1)*t^(2*d))
    (by fun_prop) (fun t _ => hg t)
  simp only [one_pow,zero_pow (by omega : 2*d+1≠0),sub_zero] at he
  have h0 : f 0=0 := by simp [f,logError_one]
  have h1 : f 1=logError a d R := by simp [f]
  rw [h0,h1,sub_zero] at he
  dsimp [f'] at he
  have ht0 : t^(2*d)≠0 := pow_ne_zero _ ht.1.ne'
  have hd0 : denominatorValue a d (1+(R-1)*t)≠0 := by
    have hx := segment_positive R t hR ⟨ht.1.le,ht.2.le⟩
    have han : -1 < -a ∧ -a<1 := ⟨by linarith [ha.2],by linarith [ha.1]⟩
    exact (mul_pos (mul_pos hx (poly_pos a ha d _ hx.le)) (poly_pos (-a) han d _ hx.le)).ne'
  refine ⟨t,ht,?_⟩
  have hm : 2*(d:ℝ)+1≠0 := by positivity
  field_simp [hd0] at he
  apply (eq_div_iff (mul_ne_zero hm hd0)).mpr
  nlinarith [he]

/-- The intermediate point is selected only to express a remainder; no continuity
of this selection is assumed or needed. -/
theorem exists_fraction (a R : ℝ) (d : ℕ) :
    ∃ t ∈ Icc (0:ℝ) 1, (-1<a ∧ a<1) → 0<R →
      logError a d R = a*(R-1)^(2*d+1) /
        ((2*(d:ℝ)+1)*denominatorValue a d (1+(R-1)*t)) := by
  by_cases h : (-1<a ∧ a<1) ∧ 0<R
  · obtain ⟨t,ht,he⟩ := error_mean_value a R d h.1 h.2
    exact ⟨t,⟨ht.1.le,ht.2.le⟩,fun _ _ => he⟩
  · refine ⟨0,by norm_num,?_⟩
    intro ha hR
    exact (h ⟨ha,hR⟩).elim

def fraction (a R : ℝ) (d : ℕ) := Classical.choose (exists_fraction a R d)

theorem fraction_mem (a R : ℝ) (d : ℕ) : fraction a R d ∈ Icc (0:ℝ) 1 :=
  (Classical.choose_spec (exists_fraction a R d)).1

def factor (a R : ℝ) (d : ℕ) :=
  1/((2*(d:ℝ)+1)*denominatorValue a d (1+(R-1)*fraction a R d))

theorem error_factor (a R : ℝ) (d : ℕ) (ha : -1<a ∧ a<1) (hR : 0<R) :
    logError a d R=a*(R-1)^(2*d+1)*factor a R d := by
  have hh := (Classical.choose_spec (exists_fraction a R d)).2 ha hR
  simpa only [fraction,factor,div_eq_mul_inv,one_mul] using hh

theorem intermediate_tendsto {ι : Type*} {l : Filter ι} (a R : ι → ℝ) (d : ℕ)
    (hR : Tendsto R l (𝓝 1)) :
    Tendsto (fun i => 1+(R i-1)*fraction (a i) (R i) d) l (𝓝 1) := by
  have hz : Tendsto (fun i => (R i-1)*fraction (a i) (R i) d) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun i => norm_nonneg _) (fun i => ?_)
      (by simpa using (hR.sub_const 1).norm)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (fraction_mem _ _ _).1]
    exact mul_le_of_le_one_right (abs_nonneg _) (fraction_mem _ _ _).2
  simpa using hz.const_add 1

/-- The joint coefficient has its limit for every path (a,R) -> (0,1). -/
theorem factor_tendsto {ι : Type*} {l : Filter ι} (a R : ι → ℝ) (d : ℕ)
    (ha : Tendsto a l (𝓝 0)) (hR : Tendsto R l (𝓝 1)) :
    Tendsto (fun i => factor (a i) (R i) d) l
      (𝓝 (1/((2*(d:ℝ)+1)*((2*d).choose d:ℝ)^2))) := by
  have hx := intermediate_tendsto a R d hR
  have hp := (polynomial_continuous d 0 1 (by norm_num)).tendsto.comp (ha.prodMk_nhds hx)
  have hn := (polynomial_continuous d 0 1 (by norm_num)).tendsto.comp
    ((by simpa using ha.neg : Tendsto (fun i => -a i) l (𝓝 0)).prodMk_nhds hx)
  have hd := (hx.mul hp).mul hn
  simp only [Function.comp_def,polynomial_zero_one,one_mul] at hd
  have hc : 0<((2*d).choose d:ℝ) := by
    rw [←polynomial_zero_one]
    exact poly_pos 0 (by norm_num) d 1 (by norm_num)
  have ht := (tendsto_const_nhds (x := (1:ℝ)) (f := l)).div (hd.const_mul (2*(d:ℝ)+1)) (by positivity)
  convert ht using 1 <;> simp only [factor,denominatorValue,pow_two]
  ext i
  dsimp

/-- Joint normalized remainder, valid along arbitrary nondegenerate paths. -/
theorem normalized_error_tendsto {ι : Type*} {l : Filter ι} (a R : ι → ℝ) (d : ℕ)
    (ha : Tendsto a l (𝓝 0)) (hR : Tendsto R l (𝓝 1))
    (hv : ∀ᶠ i in l, (-1<a i ∧ a i<1) ∧ 0<R i ∧ a i≠0 ∧ R i≠1) :
    Tendsto (fun i => logError (a i) d (R i)/(a i*(R i-1)^(2*d+1))) l
      (𝓝 (1/((2*(d:ℝ)+1)*((2*d).choose d:ℝ)^2))) := by
  apply (factor_tendsto a R d ha hR).congr'
  filter_upwards [hv] with i hi
  rw [error_factor (a i) (R i) d hi.1 hi.2.1]
  exact (mul_div_cancel_left₀ _ (mul_ne_zero hi.2.2.1 (pow_ne_zero _ (sub_ne_zero.mpr hi.2.2.2)))).symm

/-- A general scaling law; the root application takes a=1/p and scale=p. -/
theorem scaled_error_tendsto {ι : Type*} {l : Filter ι} (a R scale : ι → ℝ)
    (d : ℕ) (c : ℝ) (ha : Tendsto a l (𝓝 0)) (hR : Tendsto R l (𝓝 1))
    (hs : Tendsto (fun i => scale i*(R i-1)) l (𝓝 c))
    (hv : ∀ᶠ i in l, (-1<a i ∧ a i<1) ∧ 0<R i ∧ scale i*a i=1) :
    Tendsto (fun i => scale i^(2*d+2)*logError (a i) d (R i)) l
      (𝓝 (c^(2*d+1)/((2*(d:ℝ)+1)*((2*d).choose d:ℝ)^2))) := by
  have hh := (hs.pow (2*d+1)).mul (factor_tendsto a R d ha hR)
  simp only [div_eq_mul_inv,one_mul] at hh ⊢
  apply hh.congr'
  filter_upwards [hv] with i hi
  rw [error_factor (a i) (R i) d hi.1 hi.2.1]
  have he : scale i^(2*d+2)*a i=(scale i*a i)*scale i^(2*d+1) := by
    rw [show 2*d+2=(2*d+1)+1 by omega,pow_succ]; ring
  rw [mul_pow]
  calc
    scale i^(2*d+1)*(R i-1)^(2*d+1)*factor (a i) (R i) d =
        (scale i*a i)*scale i^(2*d+1)*(R i-1)^(2*d+1)*factor (a i) (R i) d := by rw [hi.2.2,one_mul]
    _ = scale i^(2*d+2)*(a i*(R i-1)^(2*d+1)*factor (a i) (R i) d) := by rw [←he]; ring

theorem entry_exponent_tendsto (ell : ℝ) :
    Tendsto (fun p : ℝ => ell/(p+1)) atTop (𝓝 0) := by
  have hh : Tendsto (fun p : ℝ => p+1) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using (tendsto_inv_atTop_zero.comp hh).const_mul ell

theorem scaled_entry_tendsto (ell : ℝ) :
    Tendsto (fun p : ℝ => p*(exp (ell/(p+1))-1)) atTop (𝓝 ell) := by
  have he := entry_exponent_tendsto ell
  have hd := ((continuousAt_dslope_same.mpr (hasDerivAt_exp 0).differentiableAt).tendsto.comp he)
  simp only [dslope_same,Real.deriv_exp,exp_zero] at hd
  have hi := entry_exponent_tendsto 1
  have hh : Tendsto (fun p : ℝ => ell*(1-1/(p+1))) atTop (𝓝 ell) := by
    simpa using (hi.const_sub 1).const_mul ell
  have hl := hh.mul hd
  simp only [mul_one] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (2:ℝ)] with p hp
  have hn : p+1≠0 := by linarith
  have hs := sub_smul_dslope exp (0:ℝ) (ell/(p+1))
  simp only [sub_zero,smul_eq_mul,exp_zero] at hs
  rw [←hs]
  simp only [Function.comp_def]
  field_simp
  ring

/-- The fixed-degree joint law for the exact preprocessed residual. -/
theorem root_log_error_tendsto (ell : ℝ) (d : ℕ) :
    Tendsto (fun p : ℝ => p^(2*d+2)*logError (1/p) d (exp (ell/(p+1)))) atTop
      (𝓝 (ell^(2*d+1)/((2*(d:ℝ)+1)*((2*d).choose d:ℝ)^2))) := by
  apply scaled_error_tendsto (fun p : ℝ => 1/p) (fun p => exp (ell/(p+1))) id d ell
  · simpa using (tendsto_inv_atTop_zero : Tendsto (fun p : ℝ => p⁻¹) atTop (𝓝 0))
  · simpa only [Function.comp_def,exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp (entry_exponent_tendsto ell)
  · exact scaled_entry_tendsto ell
  · filter_upwards [eventually_ge_atTop (2:ℝ)] with p hp
    have hp0 : 0<p := by linarith
    refine ⟨⟨by linarith [one_div_pos.mpr hp0], (div_lt_one hp0).mpr (by linarith)⟩,exp_pos _,?_⟩
    simp [hp0.ne']

open LeanMath.Research.EndpointCertificate

theorem root_log_error_zero (ell : ℝ) (d : ℕ) :
    Tendsto (fun p : ℝ => logError (1/p) d (exp (ell/(p+1)))) atTop (𝓝 0) := by
  have ha : Tendsto (fun p : ℝ => 1/p) atTop (𝓝 0) := by simpa using (tendsto_inv_atTop_zero : Tendsto (fun p : ℝ => p⁻¹) atTop (𝓝 0))
  have hR : Tendsto (fun p : ℝ => exp (ell/(p+1))) atTop (𝓝 1) := by
    simpa only [Function.comp_def,exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp (entry_exponent_tendsto ell)
  have hh := (ha.mul ((hR.sub_const 1).pow (2*d+1))).mul (factor_tendsto _ _ d ha hR)
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2:ℝ)] with p hp
  have hp0 : 0<p := by linarith
  exact (error_factor (1/p) _ d ⟨by linarith [one_div_pos.mpr hp0],(div_lt_one hp0).mpr (by linarith)⟩ (exp_pos _)).symm

theorem root_relative_error_tendsto (ell : ℝ) (d : ℕ) :
    Tendsto (fun p : ℝ => p^(2*d+2)*relativeError (1/p) d (exp (ell/(p+1)))) atTop
      (𝓝 (-(ell^(2*d+1)/((2*(d:ℝ)+1)*((2*d).choose d:ℝ)^2)))) := by
  have hz : Tendsto (fun p : ℝ => -logError (1/p) d (exp (ell/(p+1)))) atTop (𝓝 0) := by
    simpa using (root_log_error_zero ell d).neg
  have hd := (continuousAt_dslope_same.mpr (hasDerivAt_exp 0).differentiableAt).tendsto.comp hz
  simp only [dslope_same,Real.deriv_exp,exp_zero,Function.comp_def] at hd
  have hh := (root_log_error_tendsto ell d).neg.mul hd
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2:ℝ)] with p hp
  have hp0 : 0<p := by linarith
  rw [relativeError_eq (1/p) ⟨one_div_pos.mpr hp0,(div_lt_one hp0).mpr (by linarith)⟩ d _ (exp_pos _)]
  have hs := sub_smul_dslope exp (0:ℝ) (-logError (1/p) d (exp (ell/(p+1))))
  simp only [sub_zero,smul_eq_mul,exp_zero] at hs
  rw [←hs]
  ring

/-- Exact uniform relative-error certificate for the preprocessed interval. -/
def worstError (p ell : ℝ) (d : ℕ) :=
  max |relativeError (1/p) d (exp (-ell/(p+1)))|
      |relativeError (1/p) d (exp (ell/(p+1)))|

theorem worstError_certificate (p ell : ℝ) (d : ℕ) (hp : 1<p) (hell : 0≤ell) (tol : ℝ) :
    (∀ R ∈ Icc (exp (-ell/(p+1))) (exp (ell/(p+1))),
      |relativeError (1/p) d R|≤tol) ↔ worstError p ell d≤tol := by
  have hp0 : 0<p := by linarith
  have hLU : exp (-ell/(p+1))≤exp (ell/(p+1)) := by
    apply exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  rw [uniform_iff_endpoints (1/p) ⟨one_div_pos.mpr hp0,(div_lt_one hp0).mpr hp⟩ d _ _ tol (exp_pos _) hLU]
  exact max_le_iff.symm

theorem root_absolute_error_tendsto (ell : ℝ) (d : ℕ) :
    Tendsto (fun p : ℝ => p^(2*d+2)*|relativeError (1/p) d (exp (ell/(p+1)))|) atTop
      (𝓝 |ell^(2*d+1)/((2*(d:ℝ)+1)*((2*d).choose d:ℝ)^2)|) := by
  have hh := (root_relative_error_tendsto ell d).abs
  simp only [abs_neg] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2:ℝ)] with p hp
  rw [abs_mul,abs_of_nonneg (pow_nonneg (by linarith : 0≤p) _)]

/-- Main result: the exact worst-case relative error has an explicit asymptotic
constant at every fixed degree, including degree zero. -/
theorem worstError_tendsto (ell : ℝ) (d : ℕ) (hell : 0≤ell) :
    Tendsto (fun p : ℝ => p^(2*d+2)*worstError p ell d) atTop
      (𝓝 (ell^(2*d+1)/((2*(d:ℝ)+1)*((2*d).choose d:ℝ)^2))) := by
  have hn := root_absolute_error_tendsto (-ell) d
  have hp := root_absolute_error_tendsto ell d
  have hc : 0≤ell^(2*d+1)/((2*(d:ℝ)+1)*((2*d).choose d:ℝ)^2) := by positivity
  have he : (-ell)^(2*d+1)= -(ell^(2*d+1)) := by
    simp only [pow_add,pow_mul,neg_sq,pow_one,mul_neg]
  rw [he,neg_div,abs_neg,abs_of_nonneg hc] at hn
  rw [abs_of_nonneg hc] at hp
  have hh := hn.max hp
  rw [max_self] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2:ℝ)] with p hp
  exact (mul_max_of_nonneg _ _ (pow_nonneg (by linarith : 0≤p) _)).symm

end LeanMath.Research.JointAsymptotic

#print axioms LeanMath.Research.JointAsymptotic.coefficient_continuous
#print axioms LeanMath.Research.JointAsymptotic.polynomial_continuous
#print axioms LeanMath.Research.JointAsymptotic.coefficient_zero
#print axioms LeanMath.Research.JointAsymptotic.polynomial_zero_one
#print axioms LeanMath.Research.JointAsymptotic.segment_positive
#print axioms LeanMath.Research.JointAsymptotic.error_mean_value
#print axioms LeanMath.Research.JointAsymptotic.exists_fraction
#print axioms LeanMath.Research.JointAsymptotic.fraction_mem
#print axioms LeanMath.Research.JointAsymptotic.error_factor
#print axioms LeanMath.Research.JointAsymptotic.intermediate_tendsto
#print axioms LeanMath.Research.JointAsymptotic.factor_tendsto
#print axioms LeanMath.Research.JointAsymptotic.normalized_error_tendsto
#print axioms LeanMath.Research.JointAsymptotic.scaled_error_tendsto
#print axioms LeanMath.Research.JointAsymptotic.entry_exponent_tendsto
#print axioms LeanMath.Research.JointAsymptotic.scaled_entry_tendsto
#print axioms LeanMath.Research.JointAsymptotic.root_log_error_tendsto
#print axioms LeanMath.Research.JointAsymptotic.root_log_error_zero
#print axioms LeanMath.Research.JointAsymptotic.root_relative_error_tendsto
#print axioms LeanMath.Research.JointAsymptotic.worstError_certificate
#print axioms LeanMath.Research.JointAsymptotic.root_absolute_error_tendsto
#print axioms LeanMath.Research.JointAsymptotic.worstError_tendsto
