import LeanMath.Papers.RectangleFixedCircleUniform
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-! Existence, uniqueness, continuity and iteration of the selected real inverse branch.
The closed scalar branch also includes tangent endpoints; regular geometric steps
use its interior. No continuity or convergence hypothesis about the solver is assumed.
-/
noncomputable section
namespace LeanMath.Papers.RectangleFixedCircleDynamics
open LeanMath.Papers.RectangleFixedCircle LeanMath.Papers.RectangleFixedCircleBranch
open LeanMath.Papers.RectangleFixedCircleUniform
open Set Filter Function
open scoped Topology

/-- Correction interval, with its two tangency endpoints. -/
def parameters (p : ℝ) : Set ℝ := Icc (1/vplus p) (vplus p)
/-- Radius of the symmetric interval of logarithmic errors. -/
def radius (p : ℝ) := -input p (vplus p)
def errors (p : ℝ) : Set ℝ := Icc (-radius p) (radius p)

theorem vplus_gt_one (p : ℝ) (hp : 2 < p) : 1 < vplus p := by
  have := uplus_pos p hp
  unfold vplus; linarith

theorem parameter_bounds (p : ℝ) (hp : 2 < p) :
    0 < 1/vplus p ∧ 1/vplus p < 1 ∧ 1 < vplus p := by
  have hv := vplus_gt_one p hp
  exact ⟨by positivity, (div_lt_one (by linarith)).mpr hv, hv⟩

theorem Q_factor (p v : ℝ) (hp : 2 < p) :
    Q p v = (p^2-4)*(v-1/vplus p)*(v-vplus p) := by
  have hn : vplus p≠0 := by have := vplus_gt_one p hp; linarith
  have he : Q p v*vplus p-(p^2-4)*(v*vplus p-1)*(v-vplus p)=v*Q p (vplus p) := by
    unfold Q; ring
  rw [Q_vplus p hp] at he
  field_simp [hn]
  nlinarith only [he]

theorem Q_neg_interior (p v : ℝ) (hp : 2 < p)
    (hv : v ∈ Ioo (1/vplus p) (vplus p)) : Q p v < 0 := by
  rw [Q_factor p v hp]
  exact mul_neg_of_pos_of_neg (mul_pos (by nlinarith) (sub_pos.mpr hv.1)) (sub_neg.mpr hv.2)

theorem Q_nonpos_parameters (p v : ℝ) (hp : 2 < p) (hv : v ∈ parameters p) : Q p v≤0 := by
  rw [Q_factor p v hp]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by nlinarith) (sub_nonneg.mpr hv.1)) (sub_nonpos.mpr hv.2)

theorem parameters_iff (p v : ℝ) (hp : 2 < p) : v ∈ parameters p ↔ Q p v≤0 := by
  refine ⟨Q_nonpos_parameters p v hp, ?_⟩
  intro hQ
  have hb := parameter_bounds p hp
  have hp4 : 0 < p^2-4 := by nlinarith
  rw [Q_factor p v hp] at hQ
  constructor
  · by_contra h
    have h1 : v-1/vplus p < 0 := by linarith
    have h2 : v-vplus p < 0 := by linarith [hb.2.1, hb.2.2]
    have := mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hp4 h1) h2
    linarith
  · by_contra h
    have h1 : 0 < v-1/vplus p := by linarith [hb.2.1, hb.2.2]
    have h2 : 0 < v-vplus p := by linarith
    have := mul_pos (mul_pos hp4 h1) h2
    linarith

theorem input_continuous (p : ℝ) (hp : 2 < p) : Continuous (input p) :=
  continuous_iff_continuousAt.mpr fun v => (input_deriv p v hp).continuousAt

theorem input_strictAnti (p : ℝ) (hp : 2 < p) : StrictAntiOn (input p) (parameters p) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (input_continuous p hp).continuousOn
  intro v hv
  rw [interior_Icc] at hv
  rw [(input_deriv p v hp).deriv]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) (Q_neg_interior p v hp hv))
    (mul_pos (positive_quadratics p v hp).1 (positive_quadratics p v hp).2)

theorem one_mem_parameters (p : ℝ) (hp : 2 < p) : (1:ℝ) ∈ parameters p :=
  ⟨(parameter_bounds p hp).2.1.le, (parameter_bounds p hp).2.2.le⟩

theorem radius_pos (p : ℝ) (hp : 2 < p) : 0 < radius p := by
  have hb := parameter_bounds p hp
  have hh := input_strictAnti p hp (one_mem_parameters p hp)
    (show vplus p ∈ parameters p from ⟨by linarith [hb.2.1, hb.2.2], le_rfl⟩) hb.2.2
  rw [input_one] at hh
  exact neg_pos.mpr hh

theorem input_mapsTo (p : ℝ) (hp : 2 < p) : MapsTo (input p) (parameters p) (errors p) := by
  intro v hv
  have hb := parameter_bounds p hp
  have hl : 1/vplus p ∈ parameters p := ⟨le_rfl, by linarith [hb.2.1, hb.2.2]⟩
  have hu : vplus p ∈ parameters p := ⟨by linarith [hb.2.1, hb.2.2], le_rfl⟩
  have h1 := (input_strictAnti p hp).antitoneOn hv hu hv.2
  have h2 := (input_strictAnti p hp).antitoneOn hl hv hv.1
  rw [input_reciprocal p (vplus p) hp (by linarith [hb.2.2])] at h2
  exact ⟨by simpa [errors, radius] using h1, h2⟩

theorem input_surjOn (p : ℝ) (hp : 2 < p) : SurjOn (input p) (parameters p) (errors p) := by
  have hb := parameter_bounds p hp
  have hle : 1/vplus p ≤ vplus p := by linarith [hb.2.1, hb.2.2]
  have hh := intermediate_value_Icc' hle (input_continuous p hp).continuousOn
  rw [input_reciprocal p (vplus p) hp (by linarith [hb.2.2])] at hh
  intro e he
  exact hh (by simpa only [errors, radius, neg_neg] using he)

/-- The selected inverse is the inverse of an explicitly proved homeomorphism. -/
def inputHomeomorph (p : ℝ) (hp : 2 < p) : parameters p ≃ₜ errors p := by
  letI : CompactSpace (parameters p) := by unfold parameters; infer_instance
  let f : parameters p → errors p := fun v => ⟨input p v, input_mapsTo p hp v.property⟩
  have hinj : Injective f := by
    intro v w h
    apply Subtype.ext
    exact (input_strictAnti p hp).injOn v.property w.property (congrArg Subtype.val h)
  have hsurj : Surjective f := by
    intro e
    obtain ⟨v, hv, he⟩ := input_surjOn p hp e.property
    exact ⟨⟨v,hv⟩, Subtype.ext he⟩
  let equiv := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hc : Continuous equiv := by
    exact ((input_continuous p hp).comp continuous_subtype_val).subtype_mk _
  exact hc.homeoOfEquivCompactToT2

/-- Unique descending correction for each error in the closed band. -/
def correction (p : ℝ) (hp : 2 < p) (e : errors p) : parameters p :=
  (inputHomeomorph p hp).symm e

theorem correction_input (p : ℝ) (hp : 2 < p) (e : errors p) :
    input p (correction p hp e) = e := by
  convert! congrArg Subtype.val ((inputHomeomorph p hp).apply_symm_apply e) using 1

theorem correction_continuous (p : ℝ) (hp : 2 < p) : Continuous (correction p hp) :=
  (inputHomeomorph p hp).symm.continuous

/-- The fixed point in logarithmic coordinates. -/
def zeroError (p : ℝ) (hp : 2 < p) : errors p :=
  ⟨0, ⟨by have := radius_pos p hp; linarith, (radius_pos p hp).le⟩⟩

theorem correction_zero (p : ℝ) (hp : 2 < p) :
    (correction p hp (zeroError p hp) : ℝ) = 1 := by
  apply (input_strictAnti p hp).injOn (correction p hp (zeroError p hp)).property
    (one_mem_parameters p hp)
  rw [correction_input, input_one]; rfl

theorem output_mapsTo (p : ℝ) (hp : 2 < p) : MapsTo (output p) (parameters p) (errors p) := by
  intro v hv
  by_cases h1 : v=1
  · subst v; rw [output_one]; exact (zeroError p hp).property
  · have hv0 := lt_of_lt_of_le (parameter_bounds p hp).1 hv.1
    have hc := (real_branch_alternation_contraction p v hp hv0 h1
      (Q_nonpos_parameters p v hp hv)).2
    have hi := input_mapsTo p hp hv
    have hb : |input p v| ≤ radius p := abs_le.mpr hi
    have ho : |output p v| ≤ radius p := le_trans hc.le hb
    exact abs_le.mp ho

/-- The scalar iteration as a self-map of the complete, symmetric error band. -/
def step (p : ℝ) (hp : 2 < p) (e : errors p) : errors p :=
  ⟨output p (correction p hp e), output_mapsTo p hp (correction p hp e).property⟩

theorem step_eq (p : ℝ) (hp : 2 < p) (e : errors p) :
    (step p hp e : ℝ) = (e : ℝ)+Real.log (correction p hp e) := by
  change input p (correction p hp e)+_ = _
  rw [correction_input]

theorem step_zero (p : ℝ) (hp : 2 < p) : step p hp (zeroError p hp) = zeroError p hp := by
  apply Subtype.ext
  change output p (correction p hp (zeroError p hp)) = 0
  rw [correction_zero, output_one]

theorem step_continuous (p : ℝ) (hp : 2 < p) : Continuous (step p hp) := by
  have hc : ContinuousOn (output p) (parameters p) := by
    intro v hv
    exact (output_deriv p v hp
      (lt_of_lt_of_le (parameter_bounds p hp).1 hv.1).ne').continuousAt.continuousWithinAt
  exact (hc.domRestrict.comp (correction_continuous p hp)).subtype_mk _

theorem step_alternation_contraction (p : ℝ) (hp : 2 < p) (e : errors p) (he : e≠zeroError p hp) :
    (e : ℝ)*(step p hp e : ℝ) < 0 ∧ |(step p hp e : ℝ)| < |(e : ℝ)| := by
  have hv := (correction p hp e).property
  have h1 : (correction p hp e : ℝ)≠1 := by
    intro h
    apply he; apply Subtype.ext
    have hi := correction_input p hp e
    rw [h, input_one] at hi
    exact hi.symm
  have hh := real_branch_alternation_contraction p (correction p hp e) hp
    (lt_of_lt_of_le (parameter_bounds p hp).1 hv.1) h1 (Q_nonpos_parameters p _ hp hv)
  rw [correction_input] at hh
  exact hh

theorem step_abs_le (p : ℝ) (hp : 2 < p) (e : errors p) :
    |(step p hp e : ℝ)| ≤ |(e : ℝ)| := by
  by_cases he : e=zeroError p hp
  · subst e; rw [step_zero]
  · exact (step_alternation_contraction p hp e he).2.le

/-- In particular every open-band start remains strictly inside that band. -/
theorem orbit_invariant (p : ℝ) (hp : 2 < p) (e : errors p) (n : ℕ) :
    |((step p hp)^[n] e : ℝ)| ≤ |(e : ℝ)| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply']
    exact le_trans (step_abs_le p hp _) ih

/-- Compactness and strict reduction prove convergence of every scalar orbit. -/
theorem orbit_converges (p : ℝ) (hp : 2 < p) (e : errors p) :
    Tendsto (fun n : ℕ => ((step p hp)^[n] e : ℝ)) atTop (𝓝 0) := by
  let x : ℕ → errors p := fun n => (step p hp)^[n] e
  have hx (n : ℕ) : x (n+1) = step p hp (x n) := iterate_succ_apply' _ _ _
  have hm : Antitone (fun n => |(x n : ℝ)|) := antitone_nat_of_succ_le fun n => by
    rw [hx]; exact step_abs_le p hp _
  have hb : BddBelow (range (fun n => |(x n : ℝ)|)) :=
    ⟨0, by rintro _ ⟨n,rfl⟩; exact abs_nonneg _⟩
  let ell := ⨅ n, |(x n : ℝ)|
  have ht : Tendsto (fun n => |(x n : ℝ)|) atTop (𝓝 ell) := tendsto_atTop_ciInf hm hb
  obtain ⟨a, ha, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq (fun n => (x n).property)
  let a' : errors p := ⟨a,ha⟩
  have hlim' : Tendsto (x ∘ φ) atTop (𝓝 a') := tendsto_subtype_rng.mpr hlim
  have hval : |a|=ell := tendsto_nhds_unique hlim.abs (ht.comp hφ.tendsto_atTop)
  have hnext : Tendsto (fun n => |(step p hp (x (φ n)) : ℝ)|) atTop
      (𝓝 |(step p hp a' : ℝ)|) :=
    ((continuous_subtype_val.comp (step_continuous p hp)).continuousAt.tendsto.comp hlim').abs
  have hnextell : Tendsto (fun n => |(step p hp (x (φ n)) : ℝ)|) atTop (𝓝 ell) := by
    have hh := (ht.comp (tendsto_add_atTop_nat 1)).comp hφ.tendsto_atTop
    simpa only [Function.comp_def, hx] using hh
  have hout : |(step p hp a' : ℝ)|=ell := tendsto_nhds_unique hnext hnextell
  have ha0 : a'=zeroError p hp := by
    by_contra hn
    have hh := (step_alternation_contraction p hp a' hn).2
    change |(step p hp a' : ℝ)| < |a| at hh
    rw [hval, hout] at hh
    exact lt_irrefl _ hh
  have hell : ell=0 := by
    have : a=0 := congrArg Subtype.val ha0
    rw [this, abs_zero] at hval
    exact hval.symm
  rw [hell] at ht
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ht)

/-- Actual positive estimates converge to the selected positive root `a`. -/
theorem estimate_converges (p a : ℝ) (hp : 2 < p) (e : errors p) :
    Tendsto (fun n : ℕ => a*Real.exp ((step p hp)^[n] e : ℝ)) atTop (𝓝 a) := by
  simpa using tendsto_const_nhds.mul (Real.continuous_exp.continuousAt.tendsto.comp
    (orbit_converges p hp e))

/-- This error iteration is exactly the multiplicative circle update. -/
theorem estimate_step (p a : ℝ) (hp : 2 < p) (e : errors p) :
    a*Real.exp (step p hp e : ℝ) = (a*Real.exp (e : ℝ))*(correction p hp e : ℝ) := by
  have hv : 0 < (correction p hp e : ℝ) :=
    lt_of_lt_of_le (parameter_bounds p hp).1 (correction p hp e).property.1
  rw [step_eq, Real.exp_add, Real.exp_log hv]; ring

/-- The exact order-five limit for the inverse map itself, in the actual error variable. -/
theorem inverse_order_five (p : ℝ) (hp : 2 < p) :
    Tendsto (fun e : errors p => (step p hp e : ℝ)/(e : ℝ)^5)
      (𝓝[≠] (zeroError p hp)) (𝓝 (-(p^2-1)*(p^2-4)/720)) := by
  let u : errors p → ℝ := fun e => (correction p hp e : ℝ)-1
  have hu0 : u (zeroError p hp)=0 := by simp [u, correction_zero]
  have hc : Continuous u := (continuous_subtype_val.comp (correction_continuous p hp)).sub continuous_const
  have ht : Tendsto u (𝓝[≠] (zeroError p hp)) (𝓝[≠] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · rw [← hu0]; exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with e he
      change u e ≠ 0
      intro hz
      apply he
      apply Subtype.ext
      have hv : (correction p hp e : ℝ)=1 := by dsimp [u] at hz; linarith
      have hi := correction_input p hp e
      rw [hv, input_one] at hi
      exact hi.symm
  have hi (e : errors p) : inputLog p (u e) = (e : ℝ) := by
    have he : 1+u e = (correction p hp e : ℝ) := by dsimp [u]; ring
    simpa only [inputLog, he, input] using correction_input p hp e
  have ho (e : errors p) : outputLog p (u e) = (step p hp e : ℝ) := by
    have he : 1+u e = (correction p hp e : ℝ) := by dsimp [u]; ring
    simp only [outputLog, hi, he, step_eq]
  simpa only [Function.comp_def, hi, ho] using (logarithmic_order_five p hp).comp ht

theorem order_five_coefficient_neg (p : ℝ) (hp : 2 < p) : -(p^2-1)*(p^2-4)/720 < 0 := by
  have h1 : 0 < p^2-1 := by nlinarith
  have h4 : 0 < p^2-4 := by nlinarith
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos h1) h4) (by norm_num)

end LeanMath.Papers.RectangleFixedCircleDynamics
