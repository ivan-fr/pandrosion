import LeanMath.Papers.BranchConvergence
import LeanMath.Papers.MonomialBoundary
import LeanMath.Papers.LocalOrder
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
namespace LeanMath.Papers.NewtonLocal
open Real Filter Set
open scoped Topology

def error (f : ℝ → ℝ) (r x : ℝ) := x+(f r-f x)/deriv f x-r

theorem error_derivative (f : ℝ → ℝ) (r x : ℝ) (hf : ContDiff ℝ 2 f)
    (hx : deriv f x ≠ 0) :
    HasDerivAt (error f r) ((f x-f r)*deriv (deriv f) x/(deriv f x)^2) x := by
  have h1 := ((hf.differentiable (by norm_num)) x).hasDerivAt
  have h2 := (hf.differentiable_deriv_two x).hasDerivAt
  convert! (((hasDerivAt_id x).add ((h1.const_sub (f r)).div h2 hx)).sub_const r) using 1
  field_simp
  <;> ring

/-- Exact quadratic leading coefficient of a Newton step, at a simple root. -/
theorem quadratic_limit (f : ℝ → ℝ) (r : ℝ) (hf : ContDiff ℝ 2 f)
    (hr : deriv f r ≠ 0) :
    Tendsto (fun x => error f r x/(x-r)^2) (𝓝[≠] r)
      (𝓝 (deriv (deriv f) r/(2*deriv f r))) := by
  have hc1 := hf.continuous_deriv (by norm_num)
  have hc2 : Continuous (deriv (deriv f)) := (hf.deriv' : ContDiff ℝ 1 (deriv f)).continuous_deriv_one
  have hn : ∀ᶠ x in 𝓝[≠] r, deriv f x ≠ 0 :=
    mem_nhdsWithin_of_mem_nhds (hc1.continuousAt.eventually_ne hr)
  have hs := (((hf.differentiable (by norm_num)) r).hasDerivAt).tendsto_slope
  have ht := (hs.mul (hc2.tendsto r |>.mono_left nhdsWithin_le_nhds)).div
    ((tendsto_const_nhds.mul ((hc1.tendsto r |>.mono_left nhdsWithin_le_nhds).pow 2)))
    (show (2:ℝ)*(deriv f r)^2 ≠ 0 by positivity)
  have he : deriv f r*deriv (deriv f) r/(2*(deriv f r)^2)=deriv (deriv f) r/(2*deriv f r) := by
    field_simp
  rw [he] at ht
  apply HasDerivAt.lhopital_zero_nhdsNE
    (f' := fun x => (f x-f r)*deriv (deriv f) x/(deriv f x)^2)
    (g' := fun x => 2*(x-r))
  · filter_upwards [hn] with x hx
    exact error_derivative f r x hf hx
  · apply Eventually.of_forall
    intro x
    convert! ((hasDerivAt_id x).sub_const r).pow 2 using 1 <;> simp
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hx)
  · have hc : ContinuousAt (error f r) r := by
      exact (continuousAt_id.add ((continuousAt_const.sub hf.continuous.continuousAt).div
        hc1.continuousAt hr)).sub_const r
    simpa [error] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · have hc : ContinuousAt (fun x : ℝ => (x-r)^2) r := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · apply ht.congr'
    filter_upwards [self_mem_nhdsWithin,hn] with x hx hdx
    dsimp only [Pi.div_apply,Pi.mul_apply]
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hx,hdx]
    <;> ring

open MeasureTheory ProbabilityTheory ExponentialFamily

/-- Local linear factor of the envelope iteration. -/
theorem envelope_linear_limit (ν : Measure ℝ) [IsFiniteMeasure ν] (m n r : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) :
    Tendsto (fun x => (envelopeStep ν n (g ν r) x-r)/(x-r)) (𝓝[≠] r)
      (𝓝 (1-deriv (g ν) r/n)) := by
  have h := ((analytic ν m n hs r).differentiableAt.hasDerivAt).tendsto_slope
  have hh := (tendsto_const_nhds (x := (1:ℝ))).sub (h.div_const n)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [slope_def_field]
  unfold envelopeStep
  by_cases hn : n=0
  · subst n
    simp [sub_ne_zero.mpr hx]
  · field_simp [sub_ne_zero.mpr hx,hn]
    <;> ring

/-- The Newton coefficient is variance divided by twice the mean exponent. -/
theorem mean_quadratic_limit (ν : Measure ℝ) [IsFiniteMeasure ν] (m n r : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : deriv (g ν) r ≠ 0) :
    Tendsto (fun x => (meanStep ν (g ν r) x-r)/(x-r)^2) (𝓝[≠] r)
      (𝓝 (Var[id; law ν r]/(2*deriv (g ν) r))) := by
  have hf : ContDiff ℝ 2 (g ν) :=
    (show AnalyticOnNhd ℝ (g ν) univ from fun x _ => analytic ν m n hs x).contDiff
  have hv : deriv (deriv (g ν)) r=Var[id; law ν r] := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using second_derivative_variance ν m n r hs
  simpa only [error,meanStep,hv] using quadratic_limit (g ν) r hf hr

/-- The same leading coefficient, in the cumulant notation of Theorem 5.1. -/
theorem mean_quadratic_cumulants (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n r : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : deriv (g ν) r ≠ 0) :
    Tendsto (fun x => (meanStep ν (g ν r) x-r)/(x-r)^2) (𝓝[≠] r)
      (𝓝 (cumulant ν r 2/(2*cumulant ν r 1))) := by
  rw [cumulant_hierarchy ν m n r hs 2 (by norm_num),
    cumulant_hierarchy ν m n r hs 1 (by norm_num),second_derivative_variance ν m n r hs]
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using mean_quadratic_limit ν m n r hs hr

/-- On a nondegenerate increasing branch the envelope factor lies strictly between zero and one. -/
theorem envelope_factor_mem_unit (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n r : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ k ∂ν, k=c) (hr : 0 < deriv (g ν) r) :
    1-deriv (g ν) r/n ∈ Ioo 0 1 := by
  have hlt : deriv (g ν) r < n :=
    (mean_strictly_increasing ν m n hs hnd (show r < r+1 by linarith)).trans_le
      (mean_in_support ν m n (r+1) hs).2
  have hn : 0 < n := hr.trans hlt
  have hpos := div_pos hr hn
  have hsmall : deriv (g ν) r/n < 1 := (div_lt_one hn).mpr hlt
  constructor <;> linarith

/-- Nondegeneracy makes the quadratic Newton coefficient strictly positive. -/
theorem mean_coefficient_positive (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν] (m n r : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ k ∂ν, k=c) (hr : 0 < deriv (g ν) r) :
    0 < Var[id; law ν r]/(2*deriv (g ν) r) :=
  div_pos (variance_positive ν m n r hs hnd) (mul_pos (by norm_num) hr)

/-- The mean-exponent method is exact in one step for every nonzero monomial exponent. -/
theorem monomial_mean_exact (ν : Measure ℝ) [IsProbabilityMeasure ν] (p r x : ℝ)
    (hp : ∀ᵐ k ∂ν, k=p) (hp0 : p ≠ 0) : meanStep ν (g ν r) x=r := by
  have he : g ν=(fun t : ℝ => t*p) := funext (fun t => monomial_log_partition ν p t hp)
  have hd : deriv (g ν) x=p := by
    rw [he]
    simpa using ((hasDerivAt_id x).mul_const p).deriv
  unfold meanStep
  rw [hd,he]
  field_simp
  <;> ring

/-- With the exact monomial support endpoint the envelope step is also exact. -/
theorem monomial_envelope_exact (ν : Measure ℝ) [IsProbabilityMeasure ν] (p r x : ℝ)
    (hp : ∀ᵐ k ∂ν, k=p) (hp0 : p ≠ 0) : envelopeStep ν p (g ν r) x=r := by
  unfold envelopeStep
  rw [monomial_log_partition ν p r hp,monomial_log_partition ν p x hp]
  field_simp
  <;> ring

end LeanMath.Papers.NewtonLocal
