import LeanMath.Papers.V14ScalarSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Identification of the compressed series with the S-function in the paper. -/
noncomputable section
namespace LeanMath.Papers.V14CompressedAnalytic
open Real Set Filter PowerSeries
open scoped Topology
open LeanMath.Papers.Cayley LeanMath.Papers.V14RootSeries

def rootCoordinate (a y : ℝ) := ((unchi y)^a-1)/((unchi y)^a+1)
def paperS (a z : ℝ) := tanh (a*artanh (sqrt z))/sqrt z

theorem root_coordinate_formula (a y : ℝ) (hy : y ∈ Ioo (-1) 1) :
    rootCoordinate a y=tanh (a*artanh y) := by
  have hpow : (unchi y)^a=exp (2*(a*artanh y)) := by
    rw [rpow_def_of_pos (unchi_pos y hy),V14Defect.log_unchi y hy]
    congr 1; ring
  unfold rootCoordinate
  rw [hpow,← V14Defect.unchi_tanh]
  have ht : 1-tanh (a*artanh y) ≠ 0 := by linarith [tanh_lt_one (a*artanh y)]
  unfold unchi
  field_simp
  <;> ring

/-- Odd coefficients alone account for the entire reciprocal coordinate. -/
theorem compressed_sum (a y : ℝ) (hy : y ≠ 0)
    (hh : HasSum (fun n => coeff n (coordinate a)*y^n) (rootCoordinate a y)) :
    HasSum (fun n => coeff n (compressed a)*(y^2)^n) (rootCoordinate a y/y) := by
  have ho : Summable (fun n => coeff (2*n+1) (coordinate a)*y^(2*n+1)) :=
    hh.summable.comp_injective (i:=fun n : ℕ => 2*n+1) (fun i j h => by dsimp at h; omega)
  have he : HasSum (fun n => coeff (2*n) (coordinate a)*y^(2*n)) 0 := by
    simpa only [even_coordinate_coeff,zero_mul] using (hasSum_zero : HasSum (fun _ : ℕ => (0:ℝ)) 0)
  have htotal := HasSum.even_add_odd (f:=fun n => coeff n (coordinate a)*y^n) he ho.hasSum
  have hv := hh.unique htotal
  simp only [zero_add] at hv
  have hodd : HasSum (fun n => coeff (2*n+1) (coordinate a)*y^(2*n+1)) (rootCoordinate a y) := by
    rw [hv]; exact ho.hasSum
  have hd := hodd.div_const y
  convert! hd using 1
  funext n
  simp only [compressed,coeff_mk,pow_add,pow_one,←pow_mul]
  field_simp
  <;> ring

/-- On the positive z-axis this is precisely tanh(a artanh(sqrt z))/sqrt z. -/
theorem compressed_paper_sum (a : ℝ) :
    ∀ᶠ z : ℝ in 𝓝 0, 0 < z →
      HasSum (fun n => coeff n (compressed a)*z^n) (paperS a z) := by
  have hcoord := (V14ScalarSeries.represents_iff _ _).mp (V14ScalarSeries.coordinate_represents a)
  have hsqrt : Tendsto sqrt (𝓝 0) (𝓝 0) := by simpa using continuous_sqrt.tendsto 0
  have hh := hsqrt.eventually hcoord
  have hcell : ∀ᶠ z : ℝ in 𝓝 0, sqrt z ∈ Ioo (-1) 1 :=
    hsqrt.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hh,hcell] with z hz hcell hz0
  have hm := compressed_sum a (sqrt z) (sqrt_pos_of_pos hz0).ne' hz
  rw [sq_sqrt hz0.le,root_coordinate_formula a (sqrt z) hcell] at hm
  exact hm

/-- The compressed coefficients define an analytic germ on both sides of zero. -/
theorem compressed_radius_pos (a : ℝ) :
    0 < (FormalMultilinearSeries.ofScalars ℝ (fun n => coeff n (compressed a))).radius := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (compressed_paper_sum a)
  let z : ℝ := r/2
  have hz : 0 < z := by dsimp [z]; positivity
  have hzr : z ∈ Metric.ball (0:ℝ) r := by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hz]
    dsimp [z]; linarith
  have hs := (hball hzr hz).summable.norm
  let F := FormalMultilinearSeries.ofScalars ℝ (fun n => coeff n (compressed a))
  have hs' : Summable (fun n => ‖F n‖*z^n) := by
    simpa [F,FormalMultilinearSeries.ofScalars_norm,norm_mul,norm_pow,Real.norm_eq_abs,abs_of_pos hz] using hs
  let r0 : NNReal := ⟨z,hz.le⟩
  have hb := F.le_radius_of_summable (r:=r0) hs'
  have hr0 : (0:ENNReal) < (r0:ENNReal) := ENNReal.coe_pos.mpr hz
  exact hr0.trans_le hb

def germ (a : ℝ) : ℝ → ℝ :=
  (FormalMultilinearSeries.ofScalars ℝ (fun n => coeff n (compressed a))).sum

theorem germ_represents (a : ℝ) : V14ScalarSeries.Represents (compressed a) (germ a) :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall _ (compressed_radius_pos a)).hasFPowerSeriesAt

theorem germ_eq_paper (a : ℝ) :
    ∀ᶠ z : ℝ in 𝓝 0, 0 < z → germ a z=paperS a z := by
  have hs := (V14ScalarSeries.represents_iff _ _).mp (germ_represents a)
  filter_upwards [hs,compressed_paper_sum a] with z hz hp hz0
  exact hz.unique (hp hz0)

theorem root_first_coeff (a : ℝ) : coeff 1 (rootSeries a)=2*a := by
  have hc : constantCoeff (rescale (-1) (PowerSeries.binomialSeries ℝ (-a)))=1 := by
    rw [← coeff_zero_eq_constantCoeff_apply,coeff_rescale]
    simp
  simp [rootSeries,coeff_one_mul,hc,coeff_rescale,PowerSeries.binomialSeries_coeff]
  ring

theorem compressed_constant (a : ℝ) : coeff 0 (compressed a)=a := by
  have hh := congrArg (coeff 1) (coordinate_equation a)
  have hc0 : constantCoeff (coordinate a)=0 := by
    simpa only [Nat.mul_zero,coeff_zero_eq_constantCoeff_apply] using even_coordinate_coeff a 0
  simp [coeff_one_mul,hc0,root_constant,root_first_coeff] at hh
  rw [compressed,coeff_mk]
  norm_num only [Nat.mul_zero,Nat.zero_add]
  linarith

theorem germ_zero (a : ℝ) : germ a 0=a := by
  have hh := (germ_represents a).coeff_zero (fun _ => (1:ℝ))
  simpa [FormalMultilinearSeries.ofScalars_apply_eq,compressed_constant] using hh.symm

end LeanMath.Papers.V14CompressedAnalytic
