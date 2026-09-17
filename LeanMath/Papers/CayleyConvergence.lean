import LeanMath.Papers.Comparison
import LeanMath.Papers.MonotoneIteration
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
namespace LeanMath.Papers.Cayley
open Real Filter Function
open scoped Topology

def rootStep (p r u : ℝ) := u * C₇ p ((r/u)^p)
def step (p x u : ℝ) := u * C₇ p (x/u^p)

theorem rootStep_below (p r u : ℝ) (hp : 1 < p) (hr : 0 < r)
    (hu : 0 < u) (hur : u < r) : u < rootStep p r u ∧ rootStep p r u < r := by
  have hp0 : 0 < p := by linarith
  have hru : 1 < r/u := (one_lt_div hu).mpr hur
  obtain ⟨h1,h2⟩ := C₇_above_one_below_root p ((r/u)^p) hp (one_lt_rpow hru hp0)
  have hroot : ((r/u)^p)^(1/p) = r/u := by
    rw [one_div,rpow_rpow_inv (div_pos hr hu).le hp0.ne']
  rw [hroot] at h2
  constructor
  · simpa [rootStep] using mul_lt_mul_of_pos_left h1 hu
  · have h := mul_lt_mul_of_pos_left h2 hu
    have he : u*(r/u)=r := by field_simp
    rwa [he] at h

theorem rootStep_above (p r u : ℝ) (hp : 1 < p) (hr : 0 < r)
    (hur : r < u) : r < rootStep p r u ∧ rootStep p r u < u := by
  have hu : 0 < u := hr.trans hur
  have hp0 : 0 < p := by linarith
  have hru : r/u < 1 := (div_lt_one hu).mpr hur
  have hru0 : 0 < r/u := div_pos hr hu
  obtain ⟨h1,h2⟩ := C₇_below_one_above_root p ((r/u)^p) hp
    (rpow_pos_of_pos hru0 _) (rpow_lt_one hru0.le hru hp0)
  have hroot : ((r/u)^p)^(1/p) = r/u := by
    rw [one_div,rpow_rpow_inv hru0.le hp0.ne']
  rw [hroot] at h1
  constructor
  · have h := mul_lt_mul_of_pos_left h1 hu
    have he : u*(r/u)=r := by field_simp
    rwa [he] at h
  · simpa [rootStep] using mul_lt_mul_of_pos_left h2 hu

theorem step_eq_rootStep (p x r u : ℝ) (hr : 0 < r) (hu : 0 < u)
    (hx : r^p = x) : step p x u = rootStep p r u := by
  unfold step rootStep
  rw [div_rpow hr.le hu.le,hx]

theorem continuousAt_step (p x u : ℝ) (hp : 1 < p) (hx : 0 < x) (hu : 0 < u) :
    ContinuousAt (step p x) u := by
  have hp0 : 0 < p := by linarith
  have huPow : 0 < u^p := rpow_pos_of_pos hu p
  have hf : ContinuousAt (fun u : ℝ => x/u^p) u :=
    continuousAt_const.div (continuousAt_id.rpow_const (Or.inr hp0.le)) huPow.ne'
  exact continuousAt_id.mul ((continuousAt_C₇ p (x/u^p) hp (div_pos hx huPow)).comp (f := fun t : ℝ => x/t^p) hf)

/-- Reciprocal Geometry 6.5, seventh-order formula: convergence itself is now
proved for every real degree p>1 and every positive starting estimate. -/
theorem global_convergence (p x u : ℝ) (hp : 1 < p) (hx : 0 < x) (hu : 0 < u) :
    Tendsto (fun n : ℕ => (step p x)^[n] u) atTop (𝓝 (x^(1/p))) := by
  let r := x^(1/p)
  have hr : 0 < r := rpow_pos_of_pos hx _
  have hp0 : p ≠ 0 := by linarith
  have hroot : r^p=x := by
    dsimp [r]
    rw [one_div,rpow_inv_rpow hx.le hp0]
  apply Iteration.converge (step p x) r u hr hu
  · exact fun t ht => continuousAt_step p x t hp hx ht
  · rw [step_eq_rootStep p x r r hr hr hroot]
    simp [rootStep,hr.ne',C₇_one]
  · intro t ht htr
    rw [step_eq_rootStep p x r t hr ht hroot]
    exact rootStep_below p r t hp hr ht htr
  · intro t htr
    rw [step_eq_rootStep p x r t hr (hr.trans htr) hroot]
    exact rootStep_above p r t hp hr htr

end LeanMath.Papers.Cayley
