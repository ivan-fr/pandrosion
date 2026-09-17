import LeanMath.Papers.Corrections
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace LeanMath.Papers.Extremal
open Real MeasureTheory Set Filter

theorem weights_sum (m n μ : ℝ) (hmn : m < n) :
    (n-μ)/(n-m)+(μ-m)/(n-m)=1 := by field_simp [(sub_pos.mpr hmn).ne']; ring

theorem weights_mean (m n μ : ℝ) (hmn : m < n) :
    (n-μ)/(n-m)*m+(μ-m)/(n-m)*n=μ := by field_simp [(sub_pos.mpr hmn).ne']; ring

theorem endpoint_zero (m n μ : ℝ) (hmn : m < n) : endpointMGF m n μ 0 = 1 := by
  simpa [endpointMGF] using weights_sum m n μ hmn

theorem continuous_endpoint (m n μ : ℝ) : Continuous (endpointMGF m n μ) := by
  unfold endpointMGF
  fun_prop

theorem hasDerivAt_endpoint (m n μ t : ℝ) : HasDerivAt (endpointMGF m n μ)
    ((n-μ)/(n-m)*m*exp (m*t)+(μ-m)/(n-m)*n*exp (n*t)) t := by
  convert! ((((hasDerivAt_id t).const_mul m).exp).const_mul ((n-μ)/(n-m))).add
    ((((hasDerivAt_id t).const_mul n).exp).const_mul ((μ-m)/(n-m))) using 1 <;>
    simp [endpointMGF, mul_comm,mul_left_comm,mul_assoc]

theorem signed_exp_increment (k t : ℝ) (ht : 0 ≤ t) : 0 ≤ k*(exp (k*t)-1) := by
  by_cases hk : 0 ≤ k
  · exact mul_nonneg hk (sub_nonneg.mpr (one_le_exp (mul_nonneg hk ht)))
  · have hkt : k*t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hk) ht
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hk)
      (sub_nonpos.mpr (exp_le_one_iff.mpr hkt))

theorem endpoint_deriv_pos (m n μ t : ℝ) (hm : m < μ) (hn : μ < n)
    (hμ : 0 < μ) (ht : 0 ≤ t) : 0 < deriv (endpointMGF m n μ) t := by
  rw [(hasDerivAt_endpoint m n μ t).deriv]
  have hmn : m < n := hm.trans hn
  have hw1 : 0 ≤ (n-μ)/(n-m) := by positivity
  have hw2 : 0 ≤ (μ-m)/(n-m) := by positivity
  have hmean := weights_mean m n μ hmn
  nlinarith [mul_nonneg hw1 (signed_exp_increment m t ht),
    mul_nonneg hw2 (signed_exp_increment n t ht)]

theorem endpoint_strictMono (m n μ : ℝ) (hm : m < μ) (hn : μ < n) (hμ : 0 < μ) :
    StrictMonoOn (endpointMGF m n μ) (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) (continuous_endpoint m n μ).continuousOn
  intro t ht
  rw [interior_Ici] at ht
  exact endpoint_deriv_pos m n μ t hm hn hμ (le_of_lt ht)

theorem endpoint_jensen (m n μ t : ℝ) (hm : m < μ) (hn : μ < n) :
    exp (μ*t) ≤ endpointMGF m n μ t :=
  exp_chord m n μ t (hm.trans hn) hm.le hn.le

theorem endpoint_lt_max (m n μ t : ℝ) (hm : m < μ) (hn : μ < n) (ht : 0 < t) :
    endpointMGF m n μ t < exp (n*t) := by
  have hmn := hm.trans hn
  have hw : 0 < (n-μ)/(n-m) := by positivity
  have hs := weights_sum m n μ hmn
  have he : exp (m*t) < exp (n*t) := exp_lt_exp.mpr (mul_lt_mul_of_pos_right hmn ht)
  unfold endpointMGF
  have hs' := congrArg (fun v : ℝ => v*exp (n*t)) hs
  nlinarith [mul_lt_mul_of_pos_left he hw]

/-- Existence and uniqueness of the positive endpoint-law inverse. -/
theorem exists_unique_beta (m n μ h : ℝ) (hm : m < μ) (hn : μ < n)
    (hμ : 0 < μ) (hh : 0 < h) :
    ∃! β : ℝ, 0 < β ∧ endpointMGF m n μ β = exp h := by
  let T := h/μ+1
  have hT : 0 < T := by dsimp [T]; positivity
  have hupper : exp h < endpointMGF m n μ T := by
    have he : h < μ*T := by dsimp [T]; field_simp; nlinarith
    exact (exp_lt_exp.mpr he).trans_le (endpoint_jensen m n μ T hm hn)
  have hlower : endpointMGF m n μ 0 < exp h := by
    rw [endpoint_zero m n μ (hm.trans hn)]
    exact one_lt_exp_iff.mpr hh
  obtain ⟨β,hβ,hval⟩ := intermediate_value_Icc hT.le
    (continuous_endpoint m n μ).continuousOn ⟨hlower.le,hupper.le⟩
  have hβpos : 0 < β := by
    rcases lt_or_eq_of_le hβ.1 with he | he
    · exact he
    · rw [←he] at hval
      linarith
  refine ⟨β,⟨hβpos,hval⟩,?_⟩
  intro γ hγ
  exact (endpoint_strictMono m n μ hm hn hμ).injOn hγ.1.le hβpos.le (hγ.2.trans hval.symm)

/-- Complete corrected inverse bracket, including its strict improvement over h/n.
The measure may have continuous support and negative exponents. -/
theorem corrected_bracket (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m n μ h z : ℝ) (hm : m < μ) (hn : μ < n) (hμ : 0 < μ)
    (hh : 0 < h) (hz : 0 < z)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hi : Integrable (fun k : ℝ => k) ν)
    (he : Integrable (fun k : ℝ => exp (k*z)) ν)
    (hmean : (∫ k, k ∂ν)=μ) (hmoment : (∫ k, exp (k*z) ∂ν)=exp h) :
    ∃ β : ℝ, 0 < β ∧ endpointMGF m n μ β=exp h ∧ h/n < β ∧ β ≤ z ∧ z ≤ h/μ := by
  obtain ⟨β,⟨hβ,hβval⟩,_⟩ := exists_unique_beta m n μ h hm hn hμ hh
  have hmono := endpoint_strictMono m n μ hm hn hμ
  have hn0 : 0 < n := hμ.trans hn
  have hq : 0 < h/n := div_pos hh hn0
  have hqval : endpointMGF m n μ (h/n) < exp h := by
    have hl := endpoint_lt_max m n μ (h/n) hm hn hq
    have hnh : n*(h/n)=h := by field_simp
    rwa [hnh] at hl
  have hstrict : h/n < β := by
    by_contra hbad
    have hb := hmono.monotoneOn hβ.le hq.le (le_of_not_gt hbad)
    rw [hβval] at hb
    linarith
  have hc := mgf_le_endpoint ν m n z (hm.trans hn) hs hi he
  rw [hmean,hmoment] at hc
  have hle : β ≤ z := by
    by_contra hbad
    have hb := hmono hz.le hβ.le (lt_of_not_ge hbad)
    rw [hβval] at hb
    linarith
  have hj := exp_mean_le_mgf ν z hi he
  rw [hmean,hmoment] at hj
  have hupper : z ≤ h/μ := (le_div_iff₀ hμ).mpr (by
    simpa [mul_comm] using exp_le_exp.mp hj)
  exact ⟨β,hβ,hβval,hstrict,hle,hupper⟩

theorem support_integrable (ν : Measure ℝ) [IsFiniteMeasure ν] (m n z : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) :
    Integrable (fun k : ℝ => k) ν ∧ Integrable (fun k : ℝ => exp (k*z)) ν := by
  let M := max |m| |n|
  have hb : ∀ᵐ k ∂ν, |k| ≤ M := by
    filter_upwards [hs] with k hk
    apply abs_le.mpr
    have hmM : |m| ≤ M := le_max_left _ _
    have hnM : |n| ≤ M := le_max_right _ _
    constructor <;> linarith [neg_abs_le m,le_abs_self n,hk.1,hk.2]
  constructor
  · exact Integrable.of_bound (by fun_prop) M (by simpa only [Real.norm_eq_abs] using hb)
  · apply Integrable.of_bound (by fun_prop) (exp (M*|z|))
    filter_upwards [hb] with k hk
    rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    calc k*z ≤ |k*z| := le_abs_self _
         _ = |k| * |z| := abs_mul _ _
         _ ≤ M*|z| := mul_le_mul_of_nonneg_right hk (abs_nonneg z)

/-- Proposition 1 with exactly the bounded-support hypotheses: integrability
is a consequence, not an extra assumption. -/
theorem corrected_bracket_bounded (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m n μ h z : ℝ) (hm : m < μ) (hn : μ < n) (hμ : 0 < μ)
    (hh : 0 < h) (hz : 0 < z) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hmean : (∫ k, k ∂ν)=μ) (hmoment : (∫ k, exp (k*z) ∂ν)=exp h) :
    ∃ β : ℝ, 0 < β ∧ endpointMGF m n μ β=exp h ∧ h/n < β ∧ β ≤ z ∧ z ≤ h/μ := by
  obtain ⟨hi,he⟩ := support_integrable ν m n z hs
  exact corrected_bracket ν m n μ h z hm hn hμ hh hz hs hi he hmean hmoment

end LeanMath.Papers.Extremal
