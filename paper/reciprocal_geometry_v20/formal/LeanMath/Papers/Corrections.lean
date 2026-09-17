import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Tactic

/-!
Corrections to the supplied papers. No claim is made here that all results in
the papers have been formalized. See FORMALIZATION.md for the exact scope.

The note's Proposition 1 uses an exponential chord. We prove that chord and
its expectation bound for arbitrary probability measures, including continuous
and signed exponent supports. Integrability assumptions are explicit.
-/

noncomputable section

namespace LeanMath.Papers
open Real MeasureTheory
open scoped BigOperators

/-- Note, Proposition 1: the endpoint distribution's moment generating function. -/
def endpointMGF (m n μ t : ℝ) : ℝ :=
  (n - μ) / (n - m) * exp (m * t) +
  (μ - m) / (n - m) * exp (n * t)

theorem exp_chord (m n k t : ℝ) (hmn : m < n) (hmk : m ≤ k) (hkn : k ≤ n) :
    exp (k * t) ≤ endpointMGF m n k t := by
  have hd : 0 < n - m := sub_pos.mpr hmn
  have hs : (n - k) / (n - m) + (k - m) / (n - m) = 1 := by
    field_simp
    ring
  have hc := convexOn_exp.2 (Set.mem_univ (m * t)) (Set.mem_univ (n * t))
    (div_nonneg (sub_nonneg.mpr hkn) hd.le)
    (div_nonneg (sub_nonneg.mpr hmk) hd.le) hs
  have he : (n - k) / (n - m) * (m * t) +
      (k - m) / (n - m) * (n * t) = k * t := by
    field_simp
    <;> ring
  simpa only [smul_eq_mul, he, endpointMGF] using hc

/-- The chord bound depends only on the support endpoints and the mean. -/
theorem mgf_le_endpoint
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (m n t : ℝ)
    (hmn : m < n) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hi : Integrable (fun k : ℝ => k) ν)
    (he : Integrable (fun k : ℝ => exp (k * t)) ν) :
    (∫ k, exp (k * t) ∂ν) ≤ endpointMGF m n (∫ k, k ∂ν) t := by
  have hc : Integrable (fun k => endpointMGF m n k t) ν := by
    unfold endpointMGF
    exact (((integrable_const n).sub hi).div_const (n-m) |>.mul_const _).add
      ((hi.sub (integrable_const m)).div_const (n-m) |>.mul_const _)
  have h := integral_mono_ae he hc (hs.mono fun k hk => exp_chord m n k t hmn hk.1 hk.2)
  have hi₁ : Integrable (fun k : ℝ => (n-k)/(n-m)*exp (m*t)) ν := (((integrable_const n).sub hi).div_const (n-m)).mul_const (exp (m*t))
  have hi₂ : Integrable (fun k : ℝ => (k-m)/(n-m)*exp (n*t)) ν := ((hi.sub (integrable_const m)).div_const (n-m)).mul_const (exp (n*t))
  unfold endpointMGF at h ⊢
  have hnsub : (∫ k, n - k ∂ν) = n - ∫ k, k ∂ν := by
    simpa using integral_sub (integrable_const n) hi
  have hmsub : (∫ k, k - m ∂ν) = (∫ k, k ∂ν) - m := by
    simpa using integral_sub hi (integrable_const m)
  rw [integral_add hi₁ hi₂, integral_mul_const, integral_mul_const,
    integral_div, integral_div, hnsub, hmsub] at h
  simpa using h

/-- Jensen supplies the other side of the corrected bracket. -/
theorem exp_mean_le_mgf
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ)
    (hi : Integrable (fun k : ℝ => k) ν)
    (he : Integrable (fun k : ℝ => exp (k * t)) ν) :
    exp ((∫ k, k ∂ν) * t) ≤ ∫ k, exp (k * t) ∂ν := by
  have h := convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    (hi.mul_const t) he
  simpa only [integral_mul_const] using h

/-- A correction satisfying the two-mass majorant for m=1,n=3,μ=2,h=log 5
is at least log 2. This is a uniform improvement, not just one numerical test. -/
theorem improved_lower_bound (z : ℝ)
    (hz : (5 : ℝ) ≤ endpointMGF 1 3 2 z) : log 2 ≤ z := by
  by_contra hn
  have hz2 : z < log 2 := lt_of_not_ge hn
  have he1 : exp z < 2 := by
    calc exp z < exp (log 2) := exp_lt_exp.mpr hz2
         _ = 2 := exp_log (by norm_num)
  have he3 : exp (3 * z) < 8 := by
    have h := exp_lt_exp.mpr (mul_lt_mul_of_pos_left hz2 (by norm_num : (0:ℝ)<3))
    have h3 : exp (3 * log 2) = 8 := by
      rw [show 3 * log 2 = log 2 + log 2 + log 2 by ring, exp_add, exp_add]
      rw [exp_log (by norm_num : (0:ℝ)<2)]
      norm_num
    rwa [h3] at h
  norm_num [endpointMGF] at hz
  linarith

/-- The original lower endpoint is strictly smaller than the valid new one. -/
theorem old_lower_strictly_weaker : log (5 : ℝ) / 3 < log 2 := by
  have h : log (5 : ℝ) < log 8 := log_lt_log (by norm_num) (by norm_num)
  have h8 : log (8 : ℝ) = 3 * log 2 := by
    convert log_pow (2 : ℝ) 3 using 1 <;> norm_num
  rw [h8] at h
  linarith

theorem corrected_lower_attained : endpointMGF 1 3 2 (log 2) = 5 := by
  unfold endpointMGF
  rw [show (3:ℝ) * log 2 = log 2 + log 2 + log 2 by ring, exp_add, exp_add]
  simp only [one_mul, exp_log (by norm_num : (0:ℝ)<2)]
  norm_num

/-- The counterexample to optimality covers arbitrary probability measures. -/
theorem correction_of_beyond_theorem_4_2
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (z : ℝ)
    (hs : ∀ᵐ k ∂ν, (1:ℝ) ≤ k ∧ k ≤ 3)
    (hi : Integrable (fun k : ℝ => k) ν)
    (he : Integrable (fun k : ℝ => exp (k * z)) ν)
    (hmean : (∫ k, k ∂ν) = 2)
    (hmoment : (∫ k, exp (k * z) ∂ν) = 5) :
    log (5 : ℝ) / 3 < log 2 ∧ log 2 ≤ z ∧ z ≤ log 5 / 2 := by
  have hc := mgf_le_endpoint ν 1 3 z (by norm_num) hs hi he
  rw [hmean, hmoment] at hc
  have hj := exp_mean_le_mgf ν z hi he
  rw [hmean, hmoment] at hj
  have hj' : 2 * z ≤ log 5 := by
    apply exp_le_exp.mp
    rwa [exp_log (by norm_num : (0:ℝ)<5)]
  exact ⟨old_lower_strictly_weaker, improved_lower_bound z hc, by linarith⟩

/-- On the support in the counterexample, integrability is automatic. -/
theorem bounded_support_integrable
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (z : ℝ)
    (hs : ∀ᵐ k ∂ν, (1:ℝ) ≤ k ∧ k ≤ 3) :
    Integrable (fun k : ℝ => k) ν ∧ Integrable (fun k : ℝ => exp (k*z)) ν := by
  have hb : ∀ᵐ k ∂ν, |k| ≤ 3 := hs.mono fun k hk => by
    rw [abs_of_nonneg (by linarith : 0 ≤ k)]
    exact hk.2
  constructor
  · exact Integrable.of_bound (by fun_prop) 3 (by simpa only [Real.norm_eq_abs] using hb)
  · apply Integrable.of_bound (by fun_prop) (exp (3*|z|))
    filter_upwards [hb] with k hk
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    calc k*z ≤ |k*z| := le_abs_self _
         _ = |k| * |z| := abs_mul _ _
         _ ≤ 3*|z| := mul_le_mul_of_nonneg_right hk (abs_nonneg z)

/-- Same counterexample with only the paper's support, mean and moment hypotheses. -/
theorem old_optimality_refuted
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (z : ℝ)
    (hs : ∀ᵐ k ∂ν, (1:ℝ) ≤ k ∧ k ≤ 3)
    (hmean : (∫ k, k ∂ν) = 2)
    (hmoment : (∫ k, exp (k*z) ∂ν) = 5) :
    log (5:ℝ)/3 < log 2 ∧ log 2 ≤ z ∧ z ≤ log 5/2 := by
  obtain ⟨hi,he⟩ := bounded_support_integrable ν z hs
  exact correction_of_beyond_theorem_4_2 ν z hs hi he hmean hmoment

/-- No rational function, even with complex coefficients, squares to X.
Thus a dyadic square-root update is not a rational map of the input. This
refutes the rational-function clause of Reciprocal Geometry, Theorem 11.7,
under its uniform functional interpretation. It does not refute convergence. -/
theorem no_rational_square_root (K : Type*) [Field K] :
    ¬ ∃ f : RatFunc K, f ^ 2 = RatFunc.X := by
  rintro ⟨f, hf⟩
  have hn : f ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hf
    exact RatFunc.X_ne_zero hf.symm
  have hd := congrArg RatFunc.intDegree hf
  rw [pow_two, RatFunc.intDegree_mul hn hn, RatFunc.intDegree_X] at hd
  omega

end LeanMath.Papers
