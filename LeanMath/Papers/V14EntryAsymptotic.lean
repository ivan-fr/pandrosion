import LeanMath.Papers.V14Entry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The sharp one-entry radius is asymptotic to B/(2p). -/
noncomputable section
namespace LeanMath.Papers.V14EntryAsymptotic
open Real Filter
open scoped Topology

theorem tanh_slope : Tendsto (fun x : ℝ => tanh x/x) (𝓝[≠] 0) (𝓝 1) := by
  have hd : HasDerivAt tanh 1 0 := by
    have hh := (hasDerivAt_sinh (0:ℝ)).div (hasDerivAt_cosh (0:ℝ)) (by norm_num)
    have he : tanh = sinh / cosh := by funext x; exact tanh_eq_sinh_div_cosh x
    simpa [he] using hh
  have he : slope tanh 0 = (fun x : ℝ => tanh x/x) := by
    funext x; simp [slope_def_field]
  simpa only [he] using hd.tendsto_slope

/-- The asymptotic is valid for all real p tending to infinity, hence for the degree family. -/
theorem radius_ratio (B : ℝ) (hB : B ≠ 0) :
    Tendsto (fun p : ℝ => tanh (B/(2*(p+1)))/(B/(2*p))) atTop (𝓝 1) := by
  have ht : Tendsto (fun p : ℝ => p+1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hz : Tendsto (fun p : ℝ => B/(2*(p+1))) atTop (𝓝 0) := by
    have h := ht.const_div_atTop (B/2)
    convert! h using 1
    funext p; field_simp
  have hne : Tendsto (fun p : ℝ => B/(2*(p+1))) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hz,?_⟩
    filter_upwards [eventually_gt_atTop (0:ℝ)] with p hp
    exact div_ne_zero hB (by positivity)
  have hc : Tendsto (fun p : ℝ => p/(p+1)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1:ℝ))).sub (ht.const_div_atTop 1)
    norm_num only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with p hp
    field_simp
    ring
  have h := (tanh_slope.comp hne).mul hc
  norm_num only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with p hp
  simp only [Function.comp_def]
  field_simp

/-- The printed equivalent along p = 2^k - 1, for a positive fixed workload L. -/
theorem degree_family_ratio (L : ℝ) (hL : 0 < L) :
    Tendsto (fun k : ℕ => tanh (L*log 2/(2*((2:ℝ)^k-1+1))) /
      (L*log 2/(2*((2:ℝ)^k-1)))) atTop (𝓝 1) := by
  have ht : Tendsto (fun k : ℕ => (2:ℝ)^k-1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1:ℝ)
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  exact (radius_ratio (L*log 2) (mul_ne_zero hL.ne' (log_pos (by norm_num)).ne')).comp ht

end LeanMath.Papers.V14EntryAsymptotic
