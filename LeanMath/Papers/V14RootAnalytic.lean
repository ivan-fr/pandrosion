import LeanMath.Papers.V14RootSeries
import LeanMath.Papers.V14Defect
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! The explicit formal root series converges to the actual positive real root. -/
noncomputable section
namespace LeanMath.Papers.V14RootAnalytic
open Real Set PowerSeries Finset
open LeanMath.Papers.Cayley LeanMath.Papers.V14RootSeries

theorem binomial_hasSum (a y : ℝ) (hy : |y| < 1) :
    HasSum (fun n => coeff n (PowerSeries.binomialSeries ℝ a)*y^n) ((1+y)^a) := by
  have hm : y ∈ Metric.eball (0:ℝ) 1 := by
    simpa [Metric.mem_eball,edist_dist,Real.dist_eq] using ENNReal.ofReal_lt_one.mpr hy
  have hh := (one_add_rpow_hasFPowerSeriesOnBall_zero (a:=a)).hasSum hm
  simpa [PowerSeries.binomialSeries_coeff,_root_.binomialSeries,FormalMultilinearSeries.ofScalars_apply_eq,
    mul_comm] using hh

theorem reflected_binomial_hasSum (a y : ℝ) (hy : |y| < 1) :
    HasSum (fun n => coeff n (rescale (-1) (PowerSeries.binomialSeries ℝ (-a)))*y^n)
      ((1-y)^(-a)) := by
  have hh := binomial_hasSum (-a) (-y) (by simpa using hy)
  convert! hh using 1
  · funext n
    rw [coeff_rescale,neg_pow]
    ring

/-- A coefficient-level Cauchy product; this is the bridge between formal and analytic multiplication. -/
theorem cauchy_coeff (F G : PowerSeries ℝ) (y : ℝ) (n : ℕ) :
    coeff n (F*G)*y^n = ∑ kl ∈ antidiagonal n, (coeff kl.1 F*y^kl.1)*(coeff kl.2 G*y^kl.2) := by
  rw [coeff_mul,sum_mul]
  apply sum_congr rfl
  intro kl hkl
  have hn := mem_antidiagonal.mp hkl
  rw [← hn,pow_add]
  ring

/-- Convergent expansion of the actual positive root on the full Cayley interval. -/
theorem root_hasSum (a y : ℝ) (hy : |y| < 1) :
    HasSum (fun n => coeff n (rootSeries a)*y^n) ((unchi y)^a) := by
  have hf := binomial_hasSum a y hy
  have hg := reflected_binomial_hasSum a y hy
  have hfn := (summable_norm_iff).mpr hf.summable
  have hgn := (summable_norm_iff).mpr hg.summable
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm
  have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  rw [hf.tsum_eq,hg.tsum_eq] at he
  have hroot : (unchi y)^a=(1+y)^a*(1-y)^(-a) := by
    unfold unchi
    have hh := abs_lt.mp hy
    rw [div_rpow (by linarith [hh.1]) (by linarith [hh.2]),rpow_neg (by linarith [hh.2])]
    rfl
  rw [hroot,he]
  convert! hs.hasSum using 1
  funext n
  exact cauchy_coeff _ _ y n

/-- The coefficient series is a genuine Taylor expansion, not just a formal solution. -/
theorem root_hasFPowerSeries (a : ℝ) :
    HasFPowerSeriesAt (fun y : ℝ => (unchi y)^a)
      (FormalMultilinearSeries.ofScalars ℝ (fun n => coeff n (rootSeries a))) 0 := by
  let F := FormalMultilinearSeries.ofScalars ℝ (fun n => coeff n (rootSeries a))
  have hs : Summable (fun n => ‖F n‖*(1/2:ℝ)^n) := by
    have hh := (root_hasSum a (1/2) (by norm_num)).summable.norm
    simpa [F,FormalMultilinearSeries.ofScalars_norm,norm_mul,norm_pow] using hh
  have hr : (1/2:ENNReal) ≤ F.radius := by
    convert! F.le_radius_of_summable (r:=(1/2:NNReal)) hs using 1 <;> norm_num
  refine ⟨1/2,hr,by norm_num,?_⟩
  intro y hy
  have hy' : |y| < 1/2 := by
    have hyenn : ENNReal.ofReal |y| < ENNReal.ofReal (1/2:ℝ) := by
      simpa [Metric.mem_eball,edist_dist,Real.dist_eq] using hy
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1/2)).mp hyenn
  have hh := root_hasSum a y (by linarith)
  simpa [F,FormalMultilinearSeries.ofScalars_apply_eq,mul_comm] using hh

end LeanMath.Papers.V14RootAnalytic
