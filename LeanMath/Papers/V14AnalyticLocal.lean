import LeanMath.Papers.V14Cell
import LeanMath.Papers.V14ScalarSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Analyticity and positivity of the exact center-defect corrections. -/
noncomputable section
namespace LeanMath.Papers.V14AnalyticLocal
open Real Filter Set
open scoped Topology
open LeanMath.Papers.RealBracket LeanMath.Papers.Cayley LeanMath.Papers.V14Local

theorem center_analytic (p : ℝ) (hp : 2 < p) : AnalyticAt ℝ (center p) 1 := by
  have hl : AnalyticAt ℝ (logCenter p) 1 := by
    unfold logCenter
    fun_prop (disch := norm_num <;> linarith)
  have hh := hl.rexp
  simp only [Function.comp_def] at hh
  apply hh.congr
  filter_upwards [Ioi_mem_nhds (by norm_num : (0:ℝ)<1)] with R hR
  rw [← log_center p R (by linarith) hR,exp_log (center_pos p R (by linarith) hR)]

theorem Q_analytic (i : Index) (a y : ℝ) : AnalyticAt ℝ (Q i a) y := by
  change AnalyticAt ℝ (fun x => Q i a x) y
  cases i <;> simp only [Q,V14Coefficients.Q9,V14Coefficients.Q7,V14Coefficients.Q5,V14Coefficients.Q3] <;> fun_prop

theorem correction_one (i : Index) (p : ℝ) (hp : 2 < p) : correction i p 1=1 := by
  simp [correction,center_one p (by linarith),chi,Q_zero,unchi]

theorem correction_analytic (i : Index) (p : ℝ) (hp : 2 < p) : AnalyticAt ℝ (correction i p) 1 := by
  have hc : AnalyticAt ℝ chi 1 := by unfold chi; fun_prop (disch := norm_num)
  have hq : AnalyticAt ℝ (fun R => Q i (V14Defect.a p) (chi R)) 1 :=
    (Q_analytic i _ _).comp hc
  have hu : AnalyticAt ℝ (fun R => unchi (Q i (V14Defect.a p) (chi R))) 1 := by
    unfold unchi
    exact (analyticAt_const.add hq).div (analyticAt_const.sub hq)
      (by simp [chi,Q_zero])
  exact (center_analytic p hp).mul hu

theorem correction_positive_near_one (i : Index) (p : ℝ) (hp : 2 < p) :
    ∀ᶠ R : ℝ in 𝓝 1, 0 < correction i p R := by
  have ht := (correction_analytic i p hp).continuousAt.tendsto
  apply ht.eventually
  rw [correction_one i p hp]
  exact Ioi_mem_nhds (by norm_num)

theorem error_analytic (i : Index) (p : ℝ) (hp : 2 < p) : AnalyticAt ℝ (rootLogError i p) 0 := by
  have hc : AnalyticAt ℝ (fun e : ℝ => correction i p (exp (-p*e))) 0 := by
    have hi : AnalyticAt ℝ (fun e : ℝ => exp (-p*e)) 0 := by fun_prop
    have hh := (correction_analytic i p hp)
    exact hh.comp_of_eq hi (by norm_num)
  exact analyticAt_id.add (hc.log (by simp [correction_one i p hp]))

end LeanMath.Papers.V14AnalyticLocal
