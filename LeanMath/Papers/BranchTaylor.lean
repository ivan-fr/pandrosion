import LeanMath.Papers.NewtonLocal
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
namespace LeanMath.Papers.BranchTaylor
open Real Filter Set MeasureTheory ProbabilityTheory
open scoped Topology
open ExponentialFamily

/-- An analytic remainder gives the full second-order envelope expansion. -/
theorem envelope_expansion (ν : Measure ℝ) [IsFiniteMeasure ν] (m n r : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) :
    ∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧ ∀ᶠ e in 𝓝 0,
      envelopeStep ν n (g ν r) (r+e)-r=(1-deriv (g ν) r/n)*e+e^2*A e := by
  have hf : AnalyticAt ℝ (fun e : ℝ => g ν (r+e)) 0 := by
    have hfr : AnalyticAt ℝ (g ν) (r+0) := by simpa using analytic ν m n hs r
    exact hfr.comp (show AnalyticAt ℝ (fun e : ℝ => r+e) 0 by fun_prop)
  obtain ⟨A,hA,hEq⟩ := hf.exists_eventuallyEq_sum_add_pow_mul 2
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,iteratedDeriv_zero,
    iteratedDeriv_comp_const_add,iteratedDeriv_succ,Nat.factorial_zero,Nat.factorial_one,
    Nat.cast_one,pow_zero,pow_one,div_one,smul_eq_mul,mul_one,one_mul,add_zero] at hEq
  refine ⟨fun e => -A e/n,by fun_prop,?_⟩
  filter_upwards [hEq] with e he
  unfold envelopeStep
  rw [he]
  ring

/-- Newton's full quadratic expansion, with an analytic cubic remainder. -/
theorem newton_expansion (f : ℝ → ℝ) (r : ℝ) (hf : AnalyticAt ℝ f r)
    (hr : deriv f r ≠ 0) :
    ∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧ ∀ᶠ e in 𝓝 0,
      NewtonLocal.error f r (r+e)=deriv (deriv f) r/(2*deriv f r)*e^2+e^3*A e := by
  have hshift : AnalyticAt ℝ (fun e : ℝ => f (r+e)) 0 := by
    have hfr : AnalyticAt ℝ f (r+0) := by simpa using hf
    exact hfr.comp (show AnalyticAt ℝ (fun e : ℝ => r+e) 0 by fun_prop)
  have hdshift : AnalyticAt ℝ (fun e : ℝ => deriv f (r+e)) 0 := by
    have hfr : AnalyticAt ℝ (deriv f) (r+0) := by simpa using hf.deriv
    exact hfr.comp (show AnalyticAt ℝ (fun e : ℝ => r+e) 0 by fun_prop)
  obtain ⟨F,hF,hFEq⟩ := hshift.exists_eventuallyEq_sum_add_pow_mul 3
  obtain ⟨G,hG,hGEq⟩ := hdshift.exists_eventuallyEq_sum_add_pow_mul 2
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,iteratedDeriv_zero,
    iteratedDeriv_comp_const_add,iteratedDeriv_succ,Nat.factorial_zero,Nat.factorial_one,
    Nat.factorial_two,Nat.cast_one,Nat.cast_ofNat,pow_zero,pow_one,div_one,smul_eq_mul,
    mul_one,one_mul,add_zero] at hFEq hGEq
  let A := fun e : ℝ =>
    (deriv f r*(G e-F e)-(deriv (deriv f) r)^2/2-e*deriv (deriv f) r*G e/2)/
      (deriv f r*deriv f (r+e))
  have hA : AnalyticAt ℝ A 0 := by
    unfold A
    apply AnalyticAt.div
    · fun_prop
    · exact analyticAt_const.mul hdshift
    · simpa using mul_ne_zero hr hr
  have hn : ∀ᶠ e in 𝓝 0, deriv f (r+e) ≠ 0 := by
    exact hdshift.continuousAt.eventually_ne (by simpa using hr)
  refine ⟨A,hA,?_⟩
  filter_upwards [hFEq,hGEq,hn] with e he hd hne
  unfold NewtonLocal.error A
  rw [he]
  field_simp [hr,hne]
  rw [hd]
  ring

/-- Analytic remainder factors imply the printed big-O remainder estimate. -/
theorem analytic_remainder_bigO (A : ℝ → ℝ) (j : ℕ) (hA : AnalyticAt ℝ A 0) :
    (fun e : ℝ => e^j*A e) =O[𝓝 0] (fun e : ℝ => e^j) := by
  simpa using (Asymptotics.isBigO_refl (fun e : ℝ => e^j) (𝓝 0)).mul
    (hA.continuousAt.tendsto.isBigO_one ℝ)

theorem envelope_remainder_bigO (ν : Measure ℝ) [IsFiniteMeasure ν] (m n r : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) :
    (fun e : ℝ => envelopeStep ν n (g ν r) (r+e)-r-(1-deriv (g ν) r/n)*e)
      =O[𝓝 0] (fun e : ℝ => e^2) := by
  obtain ⟨A,hA,he⟩ := envelope_expansion ν m n r hs
  apply (analytic_remainder_bigO A 2 hA).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [he] with e he
  linarith

/-- The quadratic Newton expansion with the tilted variance coefficient. -/
theorem mean_expansion (ν : Measure ℝ) [IsFiniteMeasure ν] (m n r : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : deriv (g ν) r ≠ 0) :
    ∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧ ∀ᶠ e in 𝓝 0,
      meanStep ν (g ν r) (r+e)-r=Var[id; law ν r]/(2*deriv (g ν) r)*e^2+e^3*A e := by
  have hv : deriv (deriv (g ν)) r=Var[id; law ν r] := by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using second_derivative_variance ν m n r hs
  simpa only [NewtonLocal.error,meanStep,hv] using
    newton_expansion (g ν) r (analytic ν m n hs r) hr

theorem mean_remainder_bigO (ν : Measure ℝ) [IsFiniteMeasure ν] (m n r : ℝ)
    (hs : ∀ᵐ k ∂ν, m ≤ k ∧ k ≤ n) (hr : deriv (g ν) r ≠ 0) :
    (fun e : ℝ => meanStep ν (g ν r) (r+e)-r-Var[id; law ν r]/(2*deriv (g ν) r)*e^2)
      =O[𝓝 0] (fun e : ℝ => e^3) := by
  obtain ⟨A,hA,he⟩ := mean_expansion ν m n r hs hr
  apply (analytic_remainder_bigO A 3 hA).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [he] with e he
  linarith

end LeanMath.Papers.BranchTaylor
