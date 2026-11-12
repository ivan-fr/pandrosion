import LeanMath.Papers.MonotoneIteration
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
namespace LeanMath.Papers.Certified
open Real Filter Function
open scoped Topology

def step (C : ℝ → ℝ) (p x u : ℝ) := u*C (x/u^p)

/-- The global convergence argument is independent of the particular kernel. -/
theorem global (C : ℝ → ℝ) (p x u : ℝ) (hp : 0 < p) (hx : 0 < x) (hu : 0 < u)
    (hc : ∀ R, 0 < R → ContinuousAt C R) (hone : C 1=1)
    (hplus : ∀ R, 1 < R → 1 < C R ∧ C R < R^(1/p))
    (hminus : ∀ R, 0 < R → R < 1 → R^(1/p) < C R ∧ C R < 1) :
    Tendsto (fun n : ℕ => (step C p x)^[n] u) atTop (𝓝 (x^(1/p))) := by
  let r := x^(1/p)
  have hr : 0 < r := rpow_pos_of_pos hx _
  have hrpow : r^p=x := by dsimp [r]; rw [one_div,rpow_inv_rpow hx.le hp.ne']
  have hratio : ∀ t, 0 < t → x/t^p=(r/t)^p := by
    intro t ht
    rw [div_rpow hr.le ht.le,hrpow]
  have hroot : ∀ t, 0 < t → ((r/t)^p)^(1/p)=r/t := by
    intro t ht
    rw [one_div,rpow_rpow_inv (div_pos hr ht).le hp.ne']
  have hcancel : ∀ t, 0 < t → t*(r/t)=r := by intro t ht; field_simp
  apply Iteration.converge (step C p x) r u hr hu
  · intro t ht
    have htPow := rpow_pos_of_pos ht p
    have hf : ContinuousAt (fun t : ℝ => x/t^p) t :=
      continuousAt_const.div (continuousAt_id.rpow_const (Or.inr hp.le)) htPow.ne'
    exact continuousAt_id.mul ((hc _ (div_pos hx htPow)).comp (f := fun t:ℝ => x/t^p) hf)
  · unfold step
    rw [hratio r hr]
    simp [hr.ne',hone]
  · intro t ht htr
    have hratio1 : 1 < r/t := (one_lt_div ht).mpr htr
    obtain ⟨h1,h2⟩ := hplus ((r/t)^p) (one_lt_rpow hratio1 hp)
    rw [hroot t ht] at h2
    unfold step
    rw [hratio t ht]
    constructor
    · simpa using mul_lt_mul_of_pos_left h1 ht
    · have h := mul_lt_mul_of_pos_left h2 ht
      rwa [hcancel t ht] at h
  · intro t htr
    have ht := hr.trans htr
    have hratio1 : r/t < 1 := (div_lt_one ht).mpr htr
    obtain ⟨h1,h2⟩ := hminus ((r/t)^p) (rpow_pos_of_pos (div_pos hr ht) _)
      (rpow_lt_one (div_pos hr ht).le hratio1 hp)
    rw [hroot t ht] at h1
    unfold step
    rw [hratio t ht]
    constructor
    · have h := mul_lt_mul_of_pos_left h1 ht
      rwa [hcancel t ht] at h
    · simpa using mul_lt_mul_of_pos_left h2 ht

end LeanMath.Papers.Certified
