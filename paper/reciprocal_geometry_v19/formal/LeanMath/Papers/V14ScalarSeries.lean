import LeanMath.Papers.V14RootAnalytic
import Mathlib.Analysis.Analytic.Uniqueness

/-! Scalar analytic expansions with explicit ordinary power-series coefficients. -/
noncomputable section
namespace LeanMath.Papers.V14ScalarSeries
open PowerSeries Filter
open scoped Topology

def Represents (F : PowerSeries ℝ) (f : ℝ → ℝ) : Prop :=
  HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ (fun n => coeff n F)) 0

theorem represents_iff (F : PowerSeries ℝ) (f : ℝ → ℝ) : Represents F f ↔
    ∀ᶠ y : ℝ in 𝓝 0, HasSum (fun n => coeff n F*y^n) (f y) := by
  simp [Represents,hasFPowerSeriesAt_iff,mul_comm]

theorem exists_series (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) :
    ∃ F : PowerSeries ℝ, Represents F f := by
  obtain ⟨p,hp⟩ := hf
  refine ⟨mk p.coeff,?_⟩
  simpa [Represents,hasFPowerSeriesAt_iff] using hp

theorem unique (F G : PowerSeries ℝ) (f g : ℝ → ℝ)
    (hf : Represents F f) (hg : Represents G g) (he : f =ᶠ[𝓝 0] g) : F=G := by
  have hh := hf.eq_formalMultilinearSeries_of_eventually hg he
  ext n
  simpa using congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p.coeff n) hh

theorem add (F G : PowerSeries ℝ) (f g : ℝ → ℝ)
    (hf : Represents F f) (hg : Represents G g) : Represents (F+G) (fun y => f y+g y) := by
  rw [represents_iff] at hf hg ⊢
  filter_upwards [hf,hg] with y hf hg
  simpa [add_mul] using hf.add hg

theorem sub (F G : PowerSeries ℝ) (f g : ℝ → ℝ)
    (hf : Represents F f) (hg : Represents G g) : Represents (F-G) (fun y => f y-g y) := by
  rw [represents_iff] at hf hg ⊢
  filter_upwards [hf,hg] with y hf hg
  simpa [sub_mul] using hf.sub hg

theorem const (c : ℝ) : Represents (C c) (fun _ => c) := by
  rw [represents_iff]
  filter_upwards [] with y
  convert! hasSum_single 0 (fun n hn => show coeff n (C c)*y^n=0 by simp [coeff_C,hn]) using 1
  simp [coeff_C]

theorem one : Represents (1:PowerSeries ℝ) (fun _ => 1) := by simpa using const 1

theorem mul (F G : PowerSeries ℝ) (f g : ℝ → ℝ)
    (hf : Represents F f) (hg : Represents G g) : Represents (F*G) (fun y => f y*g y) := by
  rw [represents_iff] at hf hg ⊢
  filter_upwards [hf,hg] with y hf hg
  have hfn := hf.summable.norm
  have hgn := hg.summable.norm
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm
  have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  rw [hf.tsum_eq,hg.tsum_eq] at he
  rw [he]
  convert! hs.hasSum using 1
  funext n
  exact V14RootAnalytic.cauchy_coeff F G y n

/-- The formal reciprocal coordinate represents the genuine root coordinate. -/
theorem coordinate_represents (a : ℝ) :
    Represents (V14RootSeries.coordinate a)
      (fun y => ((LeanMath.Papers.Cayley.unchi y)^a-1)/((LeanMath.Papers.Cayley.unchi y)^a+1)) := by
  let f : ℝ → ℝ := fun y => (LeanMath.Papers.Cayley.unchi y)^a
  let g : ℝ → ℝ := fun y => (f y-1)/(f y+1)
  have hf : Represents (V14RootSeries.rootSeries a) f := V14RootAnalytic.root_hasFPowerSeries a
  have hf0 : f 0=1 := by simp [f,LeanMath.Papers.Cayley.unchi]
  have hgA : AnalyticAt ℝ g 0 := (hf.analyticAt.sub analyticAt_const).div
    (hf.analyticAt.add analyticAt_const) (by rw [hf0]; norm_num)
  obtain ⟨G,hG⟩ := exists_series g hgA
  have hprod := mul G (V14RootSeries.rootSeries a+1) g (fun y => f y+1) hG
    (add _ _ f _ hf one)
  have hsub := sub (V14RootSeries.rootSeries a) 1 f _ hf one
  have hid : G*(V14RootSeries.rootSeries a+1)=V14RootSeries.rootSeries a-1 := by
    apply unique _ _ _ _ hprod hsub
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1)] with y hy
    have hp := Real.rpow_pos_of_pos (LeanMath.Papers.Cayley.unchi_pos y hy) a
    change (f y-1)/(f y+1)*(f y+1)=f y-1
    exact div_mul_cancel₀ _ (by dsimp [f]; linarith)
  have hn : V14RootSeries.rootSeries a+1 ≠ 0 := by
    intro hz
    have hh := congrArg constantCoeff hz
    simp [V14RootSeries.root_constant] at hh
  have he : G=V14RootSeries.coordinate a := mul_right_cancel₀ hn
    (hid.trans (V14RootSeries.coordinate_equation a).symm)
  rw [he] at hG
  exact hG

end LeanMath.Papers.V14ScalarSeries
