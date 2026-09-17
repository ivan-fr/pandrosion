import LeanMath.Papers.V14PadeNormalization
import LeanMath.Papers.V14RootAnalytic

/-! Contact orders are unchanged by the Cayley change of local variable. -/
noncomputable section
namespace LeanMath.Papers.V14Contact
open Real Set Filter Asymptotics
open scoped Topology
open LeanMath.Papers.Cayley

def forward (h : ℝ) := h/(2+h)
def backward (y : ℝ) := 2*y/(1-y)

theorem forward_zero : forward 0=0 := by norm_num [forward]
theorem backward_zero : backward 0=0 := by norm_num [backward]

theorem forward_differentiable : DifferentiableAt ℝ forward 0 := by
  unfold forward; fun_prop (disch := norm_num)
theorem backward_differentiable : DifferentiableAt ℝ backward 0 := by
  unfold backward; fun_prop (disch := norm_num)

theorem forward_tendsto : Tendsto forward (𝓝 0) (𝓝 0) := by
  simpa only [forward_zero] using forward_differentiable.continuousAt.tendsto
theorem backward_tendsto : Tendsto backward (𝓝 0) (𝓝 0) := by
  simpa only [backward_zero] using backward_differentiable.continuousAt.tendsto

theorem forward_bigO : forward =O[𝓝 0] (fun h : ℝ => h) := by
  simpa only [forward_zero,sub_zero] using forward_differentiable.isBigO_sub
theorem backward_bigO : backward =O[𝓝 0] (fun y : ℝ => y) := by
  simpa only [backward_zero,sub_zero] using backward_differentiable.isBigO_sub

theorem unchi_forward (h : ℝ) (hh : 2+h ≠ 0) : unchi (forward h)=1+h := by
  unfold unchi forward
  field_simp
  <;> ring

theorem one_add_backward (y : ℝ) (hy : 1-y ≠ 0) : 1+backward y=unchi y := by
  unfold backward unchi
  field_simp
  <;> ring

/-- Big-O contact at R=1 is equivalent to contact at y=0, in both directions. -/
theorem contact_iff (f : ℝ → ℝ) (n : ℕ) :
    (fun y : ℝ => f (unchi y)) =O[𝓝 0] (fun y => y^n) ↔
    (fun h : ℝ => f (1+h)) =O[𝓝 0] (fun h => h^n) := by
  constructor
  · intro hf
    have hh := (hf.comp_tendsto forward_tendsto).trans (forward_bigO.pow n)
    apply hh.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1)] with h hm
    simp only [Function.comp_apply,unchi_forward h (by linarith [hm.1])]
  · intro hf
    have hh := (hf.comp_tendsto backward_tendsto).trans (backward_bigO.pow n)
    apply hh.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1)] with y hm
    simp only [Function.comp_apply,one_add_backward y (by linarith [hm.2])]

/-- Polynomial contact after clearing a degree-d denominator is a contact in R itself. -/
theorem cleared_contact (P Q : Polynomial ℝ) (d n : ℕ) (a : ℝ)
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (hc : (fun y : ℝ => P.eval y/Q.eval y-(unchi y)^a) =O[𝓝 0] (fun y => y^n)) :
    (fun h : ℝ => (V14Homography.clear P d).eval (1+h)/(V14Homography.clear Q d).eval (1+h)
      -(1+h)^a) =O[𝓝 0] (fun h => h^n) := by
  have hh := (hc.comp_tendsto forward_tendsto).trans (forward_bigO.pow n)
  apply hh.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1)] with h hm
  simp only [Function.comp_apply,unchi_forward h (by linarith [hm.1])]
  rw [V14Homography.quotient_eval P Q d hP hQ (1+h) (by linarith [hm.1])]
  congr 2 <;> unfold forward <;> congr 1 <;> ring

end LeanMath.Papers.V14Contact
