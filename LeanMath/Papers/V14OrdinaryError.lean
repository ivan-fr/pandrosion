import LeanMath.Papers.V14LegacyRemainders
import Mathlib.Analysis.Calculus.DSlope

/-! Transfer of logarithmic local order to ordinary root error. -/
noncomputable section
namespace LeanMath.Papers.V14OrdinaryError
open Real Filter Asymptotics
open scoped Topology

def coordinate (r d : ℝ) := log ((r+d)/r)
def ordinary (f : ℝ → ℝ) (r d : ℝ) := r*(exp (f (coordinate r d))-1)

theorem coordinate_zero (r : ℝ) (hr : 0<r) : coordinate r 0=0 := by
  simp [coordinate,hr.ne']

theorem coordinate_derivative (r : ℝ) (hr : 0<r) :
    HasDerivAt (coordinate r) (1/r) 0 := by
  have hh := (((hasDerivAt_id (0:ℝ)).const_add r).div_const r).log
    (by simpa using (show r/r≠0 by simp [hr.ne']))
  unfold coordinate
  convert! hh using 1 <;> simp [hr.ne']

theorem coordinate_punctured (r : ℝ) (hr : 0<r) :
    Tendsto (coordinate r) (𝓝[≠] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · simpa only [coordinate_zero r hr] using
      (coordinate_derivative r hr).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show -r<(0:ℝ) by linarith))] with d hd hpos
    change coordinate r d≠0
    change -r<d at hpos
    intro hz
    have he : (r+d)/r=1 := log_injOn_pos (div_pos (by linarith) hr) (by norm_num)
      (by simpa [coordinate] using hz)
    have hh := (div_eq_one_iff_eq hr.ne').mp he
    exact (show d≠0 from hd) (by linarith)

/-- No analyticity assumption is needed: continuity and the leading limit suffice. -/
theorem transfer_limit (f : ℝ → ℝ) (r k : ℝ) (m : ℕ) (hr : 0<r)
    (hf : ContinuousAt f 0) (hf0 : f 0=0)
    (ht : Tendsto (fun e : ℝ => f e/e^m) (𝓝[≠] 0) (𝓝 k)) :
    Tendsto (fun d : ℝ => ordinary f r d/d^m) (𝓝[≠] 0) (𝓝 (k*r^(1-(m:ℝ)))) := by
  have hc := coordinate_punctured r hr
  have hs : Tendsto (fun d : ℝ => coordinate r d/d) (𝓝[≠] 0) (𝓝 (1/r)) := by
    have hh := (coordinate_derivative r hr).tendsto_slope
    have he : slope (coordinate r) 0=(fun d : ℝ => coordinate r d/d) := by
      funext d
      simp [slope_def_field,coordinate_zero r hr]
    simpa only [he] using hh
  have hfc : Tendsto (fun d => f (coordinate r d)) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [hf0,Function.comp_def] using hf.tendsto.comp (hc.mono_right nhdsWithin_le_nhds)
  have hd : Tendsto (fun d => dslope exp 0 (f (coordinate r d))) (𝓝[≠] 0) (𝓝 1) := by
    have hh := (continuousAt_dslope_same.mpr (hasDerivAt_exp 0).differentiableAt).tendsto.comp hfc
    simpa [Function.comp_def] using hh
  have hh := (((hd.mul (ht.comp hc)).mul (hs.pow m)).const_mul r)
  have hk : r*((1*k)*(1/r)^m)=k*r^(1-(m:ℝ)) := by
    rw [rpow_sub hr,rpow_one,rpow_natCast,div_pow,one_pow]
    ring
  rw [hk] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin,hc.eventually self_mem_nhdsWithin] with d hd0 he0
  have hdne : d≠0 := hd0
  have hene : coordinate r d≠0 := he0
  have hexp := sub_smul_dslope exp (0:ℝ) (f (coordinate r d))
  simp only [sub_zero,smul_eq_mul,exp_zero] at hexp
  dsimp [ordinary,Function.comp_def]
  rw [←hexp]
  rw [div_pow]
  field_simp [hdne,hene]
  <;> ring

/-- The printed ordinary-error expansion, with coefficient k*r^(1-m). -/
theorem transfer_remainder (f : ℝ → ℝ) (r k : ℝ) (m : ℕ) (hr : 0<r) (hm : 0<m)
    (hf : ContinuousAt f 0) (hf0 : f 0=0)
    (ht : Tendsto (fun e : ℝ => f e/e^m) (𝓝[≠] 0) (𝓝 k)) :
    (fun d => ordinary f r d-k*r^(1-(m:ℝ))*d^m) =o[𝓝 0] (fun d => d^m) := by
  apply V14OddRemainder.leading_limit_littleO _ m _ hm
  · simp [ordinary,coordinate_zero r hr,hf0]
  · exact transfer_limit f r k m hr hf hf0 ht

/-- For an actual update U, conjugacy identifies the constructed error with U(r+d)-r. -/
theorem ordinary_eq_update (U f : ℝ → ℝ) (r d : ℝ) (hr : 0<r) (hU : 0<U (r+d))
    (hlog : log (U (r+d)/r)=f (coordinate r d)) : ordinary f r d=U (r+d)-r := by
  unfold ordinary
  rw [←hlog,exp_log (div_pos hU hr)]
  field_simp

/-- Direct form for the actual root update, using its logarithmic error identity near the root. -/
theorem update_remainder (U f : ℝ → ℝ) (r k : ℝ) (m : ℕ) (hr : 0<r) (hm : 0<m)
    (hf : ContinuousAt f 0) (hf0 : f 0=0)
    (ht : Tendsto (fun e : ℝ => f e/e^m) (𝓝[≠] 0) (𝓝 k))
    (hU : ∀ᶠ d in 𝓝 0, 0<U (r+d) ∧ log (U (r+d)/r)=f (coordinate r d)) :
    (fun d => U (r+d)-r-k*r^(1-(m:ℝ))*d^m) =o[𝓝 0] (fun d => d^m) := by
  apply (transfer_remainder f r k m hr hm hf hf0 ht).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hU] with d hd
  rw [ordinary_eq_update U f r d hr hd.1 hd.2]

theorem transferred_coefficient_pos (r k : ℝ) (m : ℕ) (hr : 0<r) (hk : 0<k) :
    0<k*r^(1-(m:ℝ)) := mul_pos hk (rpow_pos_of_pos hr _)

end LeanMath.Papers.V14OrdinaryError
