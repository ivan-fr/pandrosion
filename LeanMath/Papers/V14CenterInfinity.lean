import LeanMath.Papers.Bilateral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Exact factorization and the large-residual asymptotic of the bilateral center. -/
noncomputable section
namespace LeanMath.Papers.V14CenterInfinity
open Real Filter
open scoped Topology
open LeanMath.Papers.RealBracket

def factor (p R : ℝ) := ((p-1)*R+1)/(R+p-1)

theorem factor_pos (p R : ℝ) (hp : 1<p) (hR : 0<R) : 0<factor p R := by
  unfold factor
  exact div_pos (by positivity) (by linarith)

theorem center_factorization (p R : ℝ) (hp : 1<p) (hR : 0<R) :
    center p R=R^((3-p)/2)*(factor p R)^((p-1)/2) := by
  apply log_injOn_pos (center_pos p R hp hR)
    (mul_pos (rpow_pos_of_pos hR _) (rpow_pos_of_pos (factor_pos p R hp hR) _))
  rw [log_center p R hp hR,log_mul (rpow_pos_of_pos hR _).ne'
    (rpow_pos_of_pos (factor_pos p R hp hR) _).ne',log_rpow hR,log_rpow (factor_pos p R hp hR)]
  unfold logCenter factor
  rw [log_div (by positivity : (p-1)*R+1≠0) (by linarith : R+p-1≠0)]
  ring

theorem factor_limit (p : ℝ) : Tendsto (factor p) atTop (𝓝 (p-1)) := by
  have h1 := tendsto_id.const_div_atTop (1:ℝ)
  have h2 := tendsto_id.const_div_atTop (p-1)
  have hh := ((tendsto_const_nhds (x := p-1)).add h1).div ((tendsto_const_nhds (x := (1:ℝ))).add h2) (by norm_num : (1:ℝ)+0≠0)
  simp only [add_zero,div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  dsimp [factor]
  field_simp
  <;> ring

theorem factor_power_limit (p : ℝ) (hp : 1<p) :
    Tendsto (fun R => (factor p R)^((p-1)/2)) atTop (𝓝 ((p-1)^((p-1)/2))) :=
  (factor_limit p).rpow_const (Or.inl (by linarith))

/-- The quotient by the printed leading expression tends to one. -/
theorem asymptotic_ratio (p : ℝ) (hp : 1<p) :
    Tendsto (fun R => center p R/((p-1)^((p-1)/2)*R^((3-p)/2))) atTop (𝓝 1) := by
  have hc : 0<(p-1)^((p-1)/2) := rpow_pos_of_pos (by linarith) _
  have hh := (factor_power_limit p hp).div_const ((p-1)^((p-1)/2))
  rw [div_self hc.ne'] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  rw [center_factorization p R hp hR]
  have hr := (rpow_pos_of_pos hR ((3-p)/2)).ne'
  field_simp

/-- For degree greater than three, the center tends to zero at large positive residual. -/
theorem center_tends_zero (p : ℝ) (hp : 3<p) : Tendsto (center p) atTop (𝓝 0) := by
  have hr : Tendsto (fun R : ℝ => R^((3-p)/2)) atTop (𝓝 0) := by
    have he : (3-p)/2= -((p-3)/2) := by ring
    rw [he]
    exact tendsto_rpow_neg_atTop (by linarith : 0<(p-3)/2)
  have hh := hr.mul (factor_power_limit p (by linarith))
  rw [zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  exact (center_factorization p R (by linarith) hR).symm

/-- Thus positive residuals eventually give a correction smaller than one. -/
theorem eventually_below_one (p : ℝ) (hp : 3<p) : ∀ᶠ R in atTop, center p R<1 :=
  (center_tends_zero p hp).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))

/-- At large residuals the unguarded center update moves the residual farther above one. -/
theorem eventually_residual_increases (p : ℝ) (hp : 3<p) :
    ∀ᶠ R : ℝ in atTop, 1<R ∧ R<R/(center p R)^p := by
  filter_upwards [eventually_below_one p hp,eventually_gt_atTop (1:ℝ)] with R hc hR
  have hR0 : 0<R := by linarith
  have hg := center_pos p R (by linarith) hR0
  have hgpow := rpow_pos_of_pos hg p
  have hlt := rpow_lt_one hg.le hc (by linarith : 0<p)
  refine ⟨hR,(lt_div_iff₀ hgpow).mpr ?_⟩
  nlinarith

end LeanMath.Papers.V14CenterInfinity
