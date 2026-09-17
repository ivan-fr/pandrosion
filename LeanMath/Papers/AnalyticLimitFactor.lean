import LeanMath.Papers.CumulantOrder

noncomputable section
namespace LeanMath.Papers.AnalyticLimitFactor
open Real Filter Set
open scoped Topology

/-- A finite normalized limit forces an analytic function to have the corresponding power factor. -/
theorem factor_of_limit (f : ℝ → ℝ) (n : ℕ) (L : ℝ) (hf : AnalyticAt ℝ f 0)
    (hlim : Tendsto (fun e : ℝ => f e/e^n) (𝓝[≠] 0) (𝓝 L)) :
    ∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧ A 0=L ∧ ∀ᶠ e in 𝓝 0, f e=e^n*A e := by
  induction n generalizing f L with
  | zero =>
    have h : Tendsto f (𝓝[≠] 0) (𝓝 L) := by simpa using hlim
    have he : f 0=L := tendsto_nhds_unique (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) h
    exact ⟨f,hf,he,Eventually.of_forall (by intro e; simp)⟩
  | succ n ih =>
    have hp : Tendsto (fun e : ℝ => e^(n+1)) (𝓝[≠] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun e : ℝ => e^(n+1)) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hz : Tendsto f (𝓝[≠] 0) (𝓝 0) := by
      have h := hlim.mul hp
      simp only [mul_zero] at h
      apply h.congr'
      filter_upwards [self_mem_nhdsWithin] with e he
      field_simp [show e ≠ 0 from he]
    have h0 : f 0=0 := tendsto_nhds_unique (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hz
    obtain ⟨F,hF,hEq⟩ := hf.exists_eventuallyEq_sum_add_pow_mul 1
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,iteratedDeriv_zero,h0,
      smul_zero,mul_zero,zero_add,pow_one,smul_eq_mul] at hEq
    have hflim : Tendsto (fun e : ℝ => F e/e^n) (𝓝[≠] 0) (𝓝 L) := by
      apply hlim.congr'
      filter_upwards [mem_nhdsWithin_of_mem_nhds hEq,self_mem_nhdsWithin] with e he he0
      rw [he,pow_succ]
      field_simp [show e ≠ 0 from he0]
    obtain ⟨A,hA,hA0,hAEq⟩ := ih F L hF hflim
    refine ⟨A,hA,hA0,?_⟩
    filter_upwards [hEq,hAEq] with e he hAe
    rw [he,hAe,pow_succ]
    ring

/-- Analyticity strengthens a leading-term limit to a full next-power remainder. -/
theorem expansion_of_limit (f : ℝ → ℝ) (n : ℕ) (L : ℝ) (hf : AnalyticAt ℝ f 0)
    (hlim : Tendsto (fun e : ℝ => f e/e^n) (𝓝[≠] 0) (𝓝 L)) :
    ∃ B : ℝ → ℝ, AnalyticAt ℝ B 0 ∧ ∀ᶠ e in 𝓝 0, f e=L*e^n+e^(n+1)*B e := by
  obtain ⟨A,hA,hA0,hEq⟩ := factor_of_limit f n L hf hlim
  obtain ⟨B,hB,hBEq⟩ := hA.exists_eventuallyEq_sum_add_pow_mul 1
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,iteratedDeriv_zero,hA0,
    Nat.factorial_zero,Nat.cast_one,pow_zero,div_one,one_smul,pow_one,smul_eq_mul] at hBEq
  refine ⟨B,hB,?_⟩
  filter_upwards [hEq,hBEq] with e he hBe
  rw [he,hBe,pow_succ]
  ring

open MeasureTheory ExponentialFamily AnalyticReversion MovingTaylor CumulantOrder

/-- The actual cumulant method has the full seventh-order expansion and an analytic eighth-order remainder. -/
theorem full_expansion (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : cumulant ν r 1 ≠ 0) :
    ∃ B : ℝ → ℝ, AnalyticAt ℝ B 0 ∧ ∀ᶠ e in 𝓝 0,
      cumulantStep ν (g ν r) (r+e)-r=errorCoefficient ν r*e^7+e^8*B e := by
  apply expansion_of_limit _ 7 _ _ (full_error_limit ν m n r hs hr)
  have h : AnalyticAt ℝ (cumulantStep ν (g ν r)) (r+0) := by
    simpa using cumulantStep_analytic ν m n (g ν r) r hs hr
  exact (h.comp (show AnalyticAt ℝ (fun e : ℝ => r+e) 0 by fun_prop)).fun_sub analyticAt_const

theorem full_remainder_bigO (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (m n r : ℝ) (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : cumulant ν r 1 ≠ 0) :
    (fun e : ℝ => cumulantStep ν (g ν r) (r+e)-r-errorCoefficient ν r*e^7)
      =O[𝓝 0] (fun e : ℝ => e^8) := by
  obtain ⟨B,hB,hEq⟩ := full_expansion ν m n r hs hr
  apply (BranchTaylor.analytic_remainder_bigO B 8 hB).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hEq] with e he
  linarith

end LeanMath.Papers.AnalyticLimitFactor
