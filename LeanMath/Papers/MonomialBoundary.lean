import LeanMath.Papers.ExponentialFamily

noncomputable section
namespace LeanMath.Papers.ExponentialFamily
open Real Set MeasureTheory ProbabilityTheory

/-- The normalized residual and its reciprocal always have product at least one. -/
theorem reciprocal_product_ge_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (m n t : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) : 1 ≤ mgf id ν t * mgf id ν (-t) := by
  have hc := (convex ν m n hs).2 (mem_univ t) (mem_univ (-t))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at hc
  rw [show (1/2:ℝ)*t+1/2*(-t)=0 by ring] at hc
  have hz : g ν 0=0 := cgf_zero
  rw [hz] at hc
  have hh : 0 ≤ g ν t+g ν (-t) := by linarith
  have he := exp_le_exp.mpr hh
  rwa [exp_zero,exp_add,g,exp_cgf (X := id) (exponential_integrable ν m n t hs),
    exp_cgf (X := id) (exponential_integrable ν m n (-t) hs)] at he

theorem reciprocal_product_gt_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (m n t : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n)
    (hnd : ¬ ∃ c : ℝ, ∀ᵐ k ∂ν, k=c) (ht : t ≠ 0) :
    1 < mgf id ν t * mgf id ν (-t) := by
  have hc := (strictly_convex ν m n hs hnd).2 (mem_univ t) (mem_univ (-t))
    (by intro h; apply ht; linarith : t ≠ -t)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  simp only [smul_eq_mul] at hc
  rw [show (1/2:ℝ)*t+1/2*(-t)=0 by ring] at hc
  have hz : g ν 0=0 := cgf_zero
  rw [hz] at hc
  have hh : 0 < g ν t+g ν (-t) := by linarith
  have he := exp_lt_exp.mpr hh
  rwa [exp_zero,exp_add,g,exp_cgf (X := id) (exponential_integrable ν m n t hs),
    exp_cgf (X := id) (exponential_integrable ν m n (-t) hs)] at he

theorem monomial_mgf (ν : Measure ℝ) [IsProbabilityMeasure ν] (p t : ℝ)
    (hp : ∀ᵐ k ∂ν, k=p) : mgf id ν t=exp (t*p) := by
  change (∫ k, exp (t*k) ∂ν)=exp (t*p)
  calc (∫ k, exp (t*k) ∂ν)=(∫ _ : ℝ, exp (t*p) ∂ν) := by
         apply integral_congr_ae
         filter_upwards [hp] with k hk
         rw [hk]
       _ = exp (t*p) := by simp

theorem monomial_log_partition (ν : Measure ℝ) [IsProbabilityMeasure ν] (p t : ℝ)
    (hp : ∀ᵐ k ∂ν, k=p) : g ν t=t*p := by
  change log (mgf id ν t)=t*p
  rw [monomial_mgf ν p t hp,log_exp]

/-- Equality at one nonzero log-ratio characterizes the monomial stratum. -/
theorem reciprocal_equality_iff_monomial (ν : Measure ℝ) [IsProbabilityMeasure ν] (m n t : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (ht : t ≠ 0) :
    mgf id ν t * mgf id ν (-t)=1 ↔ ∃ p : ℝ, ∀ᵐ k ∂ν, k=p := by
  constructor
  · intro he
    by_contra hnd
    have h := reciprocal_product_gt_one ν m n t hs hnd ht
    linarith
  · rintro ⟨p,hp⟩
    rw [monomial_mgf ν p t hp,monomial_mgf ν p (-t) hp,←exp_add]
    rw [show t*p+(-t)*p=0 by ring,exp_zero]

end LeanMath.Papers.ExponentialFamily
