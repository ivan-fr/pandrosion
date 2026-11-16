import Mathlib

/-! # The test of the certificate from the smallest gap (pandroots 0.13.0)

The fixed-point certificate (`FixedPointCertificate.lean`) asks, for the point `k`,

  `σ_k = ∑_{l ≠ k} w_l / g_kl < 1/2`  and  `w_k τ_k < 1/4`,  `τ_k = ∑_{l ≠ k} w_l / g_kl²`,

with `w_l ≥ 0` upper bounds of the `|W_l|` and `g_kl > 0` lower bounds of the gaps.  Since version 0.13.0
the program first looks at the smallest gap `g` of the point and at `W = ∑_l w_l` (all the points, `k`
included): if `W / g < 1/2` and `w_k W / g² < 1/4`, the disc passes and the two sums are not formed.

* `div_le_div_gap`, `sum_div_le`, `sum_div_sq_le`: `∑ w_l / g_l ≤ (∑ w_l) / g` and the same with squares,
  when `0 < g ≤ g_l`;
* `quick_test`: the two inequalities of the certificate follow from the two inequalities on `W` and `g`.

Not formalised: the rounding of `W`, of the smallest gap and of the two quotients in double precision
(the program multiplies the bounds by `(1 + (2 m + 16) 2^-52)^3` before comparing). -/

namespace LeanMath.Papers.CertificateGap

/-- A larger gap gives a smaller term. -/
theorem div_le_div_gap {w g g0 : ℝ} (hw : 0 ≤ w) (hg0 : 0 < g0) (hg : g0 ≤ g) : w / g ≤ w / g0 := by
  have hgp : 0 < g := lt_of_lt_of_le hg0 hg
  have key : w / g0 - w / g = w * (g - g0) / (g0 * g) := by
    rw [div_sub_div _ _ (ne_of_gt hg0) (ne_of_gt hgp)]
    ring
  have hnn : 0 ≤ w * (g - g0) / (g0 * g) :=
    div_nonneg (mul_nonneg hw (sub_nonneg.mpr hg)) (le_of_lt (mul_pos hg0 hgp))
  linarith

/-- `∑ w_l / g_l ≤ (∑ w_l) / g` when every gap is at least `g > 0`. -/
theorem sum_div_le {ι : Type*} (s : Finset ι) (w g : ι → ℝ) (g0 : ℝ) (hg0 : 0 < g0)
    (hw : ∀ l ∈ s, 0 ≤ w l) (hg : ∀ l ∈ s, g0 ≤ g l) :
    ∑ l ∈ s, w l / g l ≤ (∑ l ∈ s, w l) / g0 := by
  rw [Finset.sum_div]
  exact Finset.sum_le_sum fun l hl => div_le_div_gap (hw l hl) hg0 (hg l hl)

/-- The same with the squares of the gaps. -/
theorem sum_div_sq_le {ι : Type*} (s : Finset ι) (w g : ι → ℝ) (g0 : ℝ) (hg0 : 0 < g0)
    (hw : ∀ l ∈ s, 0 ≤ w l) (hg : ∀ l ∈ s, g0 ≤ g l) :
    ∑ l ∈ s, w l / (g l) ^ 2 ≤ (∑ l ∈ s, w l) / g0 ^ 2 := by
  have hsq : ∀ l ∈ s, g0 ^ 2 ≤ (fun l => (g l) ^ 2) l := by
    intro l hl
    have h1 : 0 ≤ (g l - g0) * (g l + g0) :=
      mul_nonneg (sub_nonneg.mpr (hg l hl)) (le_of_lt (add_pos (lt_of_lt_of_le hg0 (hg l hl)) hg0))
    show g0 ^ 2 ≤ (g l) ^ 2
    nlinarith [h1]
  exact sum_div_le s w (fun l => (g l) ^ 2) (g0 ^ 2) (pow_pos hg0 2) hw hsq

/-- The test of the program: with `W` the sum of all the bounds and `g` a lower bound of the gaps of the
point `k`, `W / g < 1/2` and `w_k W / g² < 1/4` give the two inequalities of the certificate. -/
theorem quick_test {ι : Type*} [DecidableEq ι] (t : Finset ι) (k : ι) (w g : ι → ℝ) (g0 : ℝ)
    (hg0 : 0 < g0) (hw : ∀ l ∈ t, 0 ≤ w l) (hk : 0 ≤ w k) (hg : ∀ l ∈ t.erase k, g0 ≤ g l)
    (h1 : (∑ l ∈ t, w l) / g0 < 1 / 2) (h2 : w k * ((∑ l ∈ t, w l) / g0 ^ 2) < 1 / 4) :
    ∑ l ∈ t.erase k, w l / g l < 1 / 2 ∧ w k * ∑ l ∈ t.erase k, w l / (g l) ^ 2 < 1 / 4 := by
  have hwe : ∀ l ∈ t.erase k, 0 ≤ w l := fun l hl => hw l (Finset.mem_of_mem_erase hl)
  have hsub : ∑ l ∈ t.erase k, w l ≤ ∑ l ∈ t, w l :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset k t) (fun i hi _ => hw i hi)
  have hsq : 0 < g0 ^ 2 := pow_pos hg0 2
  -- a smaller numerator gives a smaller quotient
  have mono : ∀ d : ℝ, 0 < d → (∑ l ∈ t.erase k, w l) / d ≤ (∑ l ∈ t, w l) / d := by
    intro d hd
    have e : (∑ l ∈ t, w l) / d - (∑ l ∈ t.erase k, w l) / d
        = ((∑ l ∈ t, w l) - (∑ l ∈ t.erase k, w l)) / d := by ring
    have hnn : 0 ≤ ((∑ l ∈ t, w l) - (∑ l ∈ t.erase k, w l)) / d :=
      div_nonneg (sub_nonneg.mpr hsub) (le_of_lt hd)
    linarith
  have s1 := sum_div_le (t.erase k) w g g0 hg0 hwe hg
  have s2 := sum_div_sq_le (t.erase k) w g g0 hg0 hwe hg
  have m1 := mono g0 hg0
  have m2 := mono (g0 ^ 2) hsq
  refine ⟨by linarith, ?_⟩
  have s3 : w k * ∑ l ∈ t.erase k, w l / (g l) ^ 2 ≤ w k * ((∑ l ∈ t, w l) / g0 ^ 2) :=
    mul_le_mul_of_nonneg_left (le_trans s2 m2) hk
  linarith

end LeanMath.Papers.CertificateGap
