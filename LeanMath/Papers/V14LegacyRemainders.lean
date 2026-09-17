import LeanMath.Papers.CayleyCubic
import LeanMath.Papers.CayleyQuintic
import LeanMath.Papers.BilateralHybrid
import LeanMath.Papers.V14AnalyticLocal
import LeanMath.Papers.V14OddRemainder

/-! Full printed local remainders for the inherited Cayley and center formulas. -/
noncomputable section
namespace LeanMath.Papers.V14LegacyRemainders
open Real Filter Asymptotics
open scoped Topology
open LeanMath.Papers.Cayley

theorem reciprocal_error_odd (C : ℝ → ℝ) (p : ℝ)
    (hC : ∀ R, 0<R → C R⁻¹=(C R)⁻¹) (e : ℝ) :
    -e+log (C (exp (-p*(-e))))= -(e+log (C (exp (-p*e)))) := by
  rw [show -p*(-e)= -(-p*e) by ring,exp_neg,hC _ (exp_pos _),log_inv]
  ring

theorem error_analytic (C : ℝ → ℝ) (p : ℝ) (hC : AnalyticAt ℝ C 1) (h1 : C 1=1) :
    AnalyticAt ℝ (fun e => e+log (C (exp (-p*e)))) 0 := by
  have he : AnalyticAt ℝ (fun e : ℝ => exp (-p*e)) 0 := by fun_prop
  have hc : AnalyticAt ℝ (fun e : ℝ => C (exp (-p*e))) 0 := by
    exact hC.comp_of_eq he (by norm_num)
  exact analyticAt_id.add (hc.log (by simpa [h1]))

theorem cubic_analytic (p : ℝ) : AnalyticAt ℝ (C₃ p) 1 := by
  unfold C₃ P₁ chi unchi
  fun_prop (disch := norm_num)

theorem quintic_analytic (p : ℝ) : AnalyticAt ℝ (C₅ p) 1 := by
  unfold C₅ P₃ chi unchi
  fun_prop (disch := norm_num)

theorem septic_analytic (p : ℝ) : AnalyticAt ℝ (C₇ p) 1 := by
  unfold C₇ P₅ chi unchi
  fun_prop (disch := norm_num)

theorem cubic_remainder (p : ℝ) (hp : 1<p) :
    (fun e : ℝ => Cubic.error p e-(p^2-1)/12*e^3) =O[𝓝 0] (fun e => e^5) := by
  apply V14OddRemainder.odd_leading_remainder _ 3 _ (by decide)
  · exact error_analytic _ p (cubic_analytic p) (by simp [C₃,P₁,chi,unchi])
  · exact reciprocal_error_odd _ p (fun R hR => C₃_reciprocal p R hR)
  · simp [Cubic.error,C₃,P₁,chi,unchi]
  · exact Cubic.exact_order p hp

theorem quintic_remainder (p : ℝ) (hp : 1<p) :
    (fun e : ℝ => Quintic.error p e-(p^2-1)*(3*p^2-2)/240*e^5) =O[𝓝 0] (fun e => e^7) := by
  apply V14OddRemainder.odd_leading_remainder _ 5 _ (by decide)
  · exact error_analytic _ p (quintic_analytic p) (by simp [C₅,P₃,chi,unchi])
  · exact reciprocal_error_odd _ p (fun R hR => C₅_reciprocal p R hR)
  · simp [Quintic.error,C₅,P₃,chi,unchi]
  · exact Quintic.exact_order p hp

theorem septic_remainder (p : ℝ) (hp : 1<p) :
    (fun e : ℝ => logError p e-(p^2-1)*(45*p^4-53*p^2+17)/20160*e^7)
      =O[𝓝 0] (fun e => e^9) := by
  apply V14OddRemainder.odd_leading_remainder _ 7 _ (by decide)
  · exact error_analytic _ p (septic_analytic p) (by simp [C₇,P₅,chi,unchi])
  · exact reciprocal_error_odd _ p (fun R hR => C₇_reciprocal p R hR)
  · simp [logError,C₇,P₅,chi,unchi]
  · exact exact_order_seven p hp

theorem center_remainder (p : ℝ) (hp : 2<p) :
    (fun e : ℝ => RealBracket.Local.error p e-(p-2)*(p-1)^2/6*e^3)
      =O[𝓝 0] (fun e => e^5) := by
  apply V14OddRemainder.odd_leading_remainder _ 3 _ (by decide)
  · exact error_analytic _ p (V14AnalyticLocal.center_analytic p hp)
      (RealBracket.center_one p (by linarith))
  · exact reciprocal_error_odd _ p (fun R hR => RealBracket.center_reciprocal p R (by linarith) hR)
  · simp [RealBracket.Local.error,RealBracket.center_one p (by linarith : 1<p)]
  · convert RealBracket.Local.exact_cubic_limit p (by linarith) using 1 <;>
      simp only [RealBracket.Local.coefficient] <;> congr 1 <;> ring

end LeanMath.Papers.V14LegacyRemainders
