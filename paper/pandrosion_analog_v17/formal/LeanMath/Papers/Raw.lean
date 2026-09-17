import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! Reciprocal Geometry, Theorem 2.1, in a root-free equivalent form. -/
noncomputable section
namespace LeanMath.Papers.Raw
open scoped BigOperators

def S (p : ℕ) (s : ℝ) := ∑ j ∈ Finset.range p, s ^ j
def step (p : ℕ) (x s : ℝ) := 1 - (x-1)/(x*S p s)

theorem bridge (p : ℕ) (s : ℝ) : (1-s)*S p s = 1-s^p := by
  simpa [S, mul_comm] using geom_sum_mul_neg s p

theorem S_pos (p : ℕ) (s : ℝ) (hp : 1 ≤ p) (hs : 0 < s) : 0 < S p s := by
  apply Finset.sum_pos
  · intro i hi
    exact pow_pos hs i
  · exact ⟨0, Finset.mem_range.mpr hp⟩

theorem fixed_iff (p : ℕ) (x s : ℝ) (hp : 1 ≤ p) (hx : 0 < x) (hs : 0 < s) :
    step p x s = s ↔ x*s^p = 1 := by
  have hd : x * S p s ≠ 0 := (mul_pos hx (S_pos p s hp hs)).ne'
  have hb := bridge p s
  unfold step
  constructor
  · intro h
    have he : (x-1)/(x*S p s) = 1-s := by linarith
    have he' := (div_eq_iff hd).mp he
    nlinarith [congrArg (fun t : ℝ => x*t) hb]
  · intro h
    have he : (x-1)/(x*S p s) = 1-s := by
      apply (div_eq_iff hd).mpr
      nlinarith [congrArg (fun t : ℝ => x*t) hb]
    linarith

theorem visible_readout (p : ℕ) (x s : ℝ) (hp : 1 ≤ p) (hs : 0 < s)
    (hfix : x*s^p = 1) : x*s^(p-1) = s⁻¹ := by
  have hpow : s^p = s^(p-1)*s := by
    rw [← pow_succ]
    congr 1
    omega
  rw [← one_div]
  apply (eq_div_iff hs.ne').mpr
  rw [mul_assoc, ← hpow]
  exact hfix

theorem fixed_point_unique (p : ℕ) (x s t : ℝ) (hp : 1 ≤ p)
    (hx : 0 < x) (hs : 0 < s) (ht : 0 < t)
    (hf : step p x s = s) (hg : step p x t = t) : s = t := by
  have h₁ := (fixed_iff p x s hp hx hs).mp hf
  have h₂ := (fixed_iff p x t hp hx ht).mp hg
  apply (pow_left_inj₀ hs.le ht.le (by omega : p ≠ 0)).mp
  exact mul_left_cancel₀ hx.ne' (h₁.trans h₂.symm)

theorem readout_is_positive_root (p : ℕ) (x s : ℝ) (hp : 1 ≤ p)
    (hx : 0 < x) (hs : 0 < s) (hf : step p x s = s) :
    0 < x*s^(p-1) ∧ (x*s^(p-1))^p = x := by
  have h := (fixed_iff p x s hp hx hs).mp hf
  rw [visible_readout p x s hp hs h]
  refine ⟨inv_pos.mpr hs, ?_⟩
  rw [inv_pow]
  apply (inv_eq_iff_eq_inv).mpr
  rw [← one_div]
  apply (eq_div_iff hx.ne').mpr
  simpa [mul_comm] using h

end LeanMath.Papers.Raw
