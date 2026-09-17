import research.constrained_rational_v5.Support
namespace HornerCertificate
noncomputable def bern : List ℕ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a::w, u, v => (a:ℝ)*v^w.length+u*bern w u v

theorem bern_nonnegative (w : List ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ bern w u v := by
  induction w with
  | nil => simp [bern]
  | cons a w ih =>
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hv _)) (mul_nonneg hu ih)

noncomputable def repr (k : ℕ) (w : List ℕ) (L H D y : ℝ) := y^k * bern w (D*y-L) (H-D*y)
theorem from_identity (f : ℝ → ℝ) (k S : ℕ) (w : List ℕ)
    (L H D y : ℝ) (hS : 0 < S) (hy : 0 ≤ y) (hl : 0 ≤ D*y-L) (hh : 0 ≤ H-D*y)
    (identity : (S:ℝ)*f y = repr k w L H D y) : 0 ≤ f y := by
  have hp : 0 ≤ repr k w L H D y := mul_nonneg (pow_nonneg hy k) (bern_nonnegative w _ _ hl hh)
  rw [← identity] at hp
  exact nonneg_of_mul_nonneg_right hp (by exact_mod_cast hS)
end HornerCertificate
