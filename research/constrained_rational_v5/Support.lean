import research.constrained_rational_v5.CompleteLower
namespace PandrosionTarget

theorem ratio_mem (N D : ℝ) (hd : 0 < D) (hm : 0 < D-N) (hp : 0 < D+N) :
    N/D ∈ Set.Ioo (-1:ℝ) 1 := by
  constructor
  · apply (lt_div_iff₀ hd).mpr; linarith
  · apply (div_lt_iff₀ hd).mpr; linarith

theorem H_ratio (p : ℕ) (y N D : ℝ) (hd : D ≠ 0) :
    H p y (N/D) = ((1+y)*(D-N)^p-(1-y)*(D+N)^p)/D^p := by
  have hm : 1-N/D = (D-N)/D := by field_simp
  have hp : 1+N/D = (D+N)/D := by field_simp
  rw [H, hm, hp, div_pow, div_pow]
  ring

theorem lower_ratio (p : ℕ) (hp : 0 < p) (y N D : ℝ)
    (hy : y ∈ Set.Ioo (-1:ℝ) 1) (hd : 0 < D) (hm : 0 < D-N) (hplus : 0 < D+N)
    (h : 0 ≤ (1+y)*(D-N)^p-(1-y)*(D+N)^p) : N/D ≤ target p y := by
  apply lower_gate p hp y (N/D) hy (ratio_mem N D hd hm hplus)
  rw [H_ratio p y N D hd.ne']
  exact div_nonneg h (pow_pos hd p).le

theorem upper_ratio (p : ℕ) (hp : 0 < p) (y N D : ℝ)
    (hy : y ∈ Set.Ioo (-1:ℝ) 1) (hd : 0 < D) (hm : 0 < D-N) (hplus : 0 < D+N)
    (h : (1+y)*(D-N)^p-(1-y)*(D+N)^p ≤ 0) : target p y ≤ N/D := by
  apply upper_gate p hp y (N/D) hy (ratio_mem N D hd hm hplus)
  rw [H_ratio p y N D hd.ne']
  exact div_nonpos_of_nonpos_of_nonneg h (pow_pos hd p).le
end PandrosionTarget


namespace PositiveCertificate
noncomputable def repr (n k : ℕ) (w : Fin (n+1) → ℕ) (L H D y : ℝ) :=
  y^k * ∑ i : Fin (n+1), (w i : ℝ) * (D*y-L)^i.val * (H-D*y)^(n-i.val)

theorem repr_nonnegative (n k : ℕ) (w : Fin (n+1) → ℕ) (L H D y : ℝ)
    (hy : 0 ≤ y) (hl : 0 ≤ D*y-L) (hh : 0 ≤ H-D*y) :
    0 ≤ repr n k w L H D y := by
  unfold repr
  apply mul_nonneg (pow_nonneg hy k)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hl _)) (pow_nonneg hh _)

theorem from_identity (f : ℝ → ℝ) (n k S : ℕ) (w : Fin (n+1) → ℕ)
    (L H D y : ℝ) (hS : 0 < S) (hy : 0 ≤ y) (hl : 0 ≤ D*y-L) (hh : 0 ≤ H-D*y)
    (identity : (S:ℝ)*f y = repr n k w L H D y) : 0 ≤ f y := by
  have hp := repr_nonnegative n k w L H D y hy hl hh
  rw [← identity] at hp
  exact nonneg_of_mul_nonneg_right hp (by exact_mod_cast hS)
end PositiveCertificate
