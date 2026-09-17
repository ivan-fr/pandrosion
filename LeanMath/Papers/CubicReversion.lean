import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-! Degree-two vector reversion and a quantitative cubic error bound.
The analytic path lemma proves a Taylor remainder from explicit derivative data;
the reversion lemma accepts this remainder, not an assumed order of the candidate. -/
noncomputable section
namespace LeanMath.Papers.CubicReversion
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem third_direction_bound
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E) (M : ℝ)
    (hM : ‖T‖ ≤ M) (s : E) : ‖T (fun _ => s)‖ ≤ M * ‖s‖^3 := by
  calc
    ‖T (fun _ => s)‖ ≤ ‖T‖ * ∏ _ : Fin 3, ‖s‖ := T.le_opNorm _
    _ = ‖T‖ * ‖s‖^3 := by simp
    _ ≤ M * ‖s‖^3 := mul_le_mul_of_nonneg_right hM (pow_nonneg (norm_nonneg s) _)

/-- A vector-valued Taylor estimate along [0,1]. The constant M/2 is deliberately
the non-sharp bound supplied by Mathlib's mean-value remainder (not M/6). -/
theorem path_taylor_bound (φ : ℝ → E) (s v₁ v₂ : E) (M : ℝ)
    (hφ : ContDiffOn ℝ 3 φ (Icc 0 1))
    (h₁ : iteratedDerivWithin 1 φ (Icc 0 1) 0 = v₁)
    (h₂ : iteratedDerivWithin 2 φ (Icc 0 1) 0 = v₂)
    (h₃ : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 3 φ (Icc 0 1) t‖ ≤ M * ‖s‖^3) :
    ‖φ 1 - φ 0 - v₁ - (1/2 : ℝ) • v₂‖ ≤ (M/2) * ‖s‖^3 := by
  have ht := taylor_mean_remainder_bound (n := 2) (by norm_num : (0 : ℝ) ≤ 1)
    hφ (by norm_num : (1 : ℝ) ∈ Icc 0 1) h₃
  have he : taylorWithinEval φ 2 (Icc 0 1) 0 1 = φ 0 + v₁ + (1/2 : ℝ) • v₂ := by
    norm_num [show (2 : ℕ) = 1+1 from rfl, taylorWithinEval_succ, h₁, h₂]
  rw [he] at ht
  convert ht using 1
  · congr 1
    abel
  · norm_num
    ring

def newtonDirection (J : E ≃L[ℝ] E) (r : E) : E := -J.symm r

def cubicCorrection (J : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (r : E) : E :=
  let s := newtonDirection J r
  s - (1/2 : ℝ) • J.symm (B s s)

theorem bilinear_diagonal_difference (B : E →L[ℝ] E →L[ℝ] E) (h s : E) :
    B h h - B s s = B (h-s) h + B s (h-s) := by
  simp only [map_sub, sub_apply]
  abel

/-- Cubic error of the actual inverse-Taylor polynomial. Here h is the exact
correction from the current point to a root and r is the current residual.
The remainder condition follows from Taylor at that root displacement. -/
theorem cubic_error (J : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (r h : E) (K H M : ℝ) (hK : 0 ≤ K) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hJ : ∀ v, ‖J.symm v‖ ≤ K * ‖v‖)
    (hB : ∀ u v, ‖B u v‖ ≤ H * ‖u‖ * ‖v‖)
    (hh : ‖h‖ ≤ 1)
    (hrem : ‖r + J h + (1/2 : ℝ) • B h h‖ ≤ M * ‖h‖^3) :
    let A := K * (H/2 + M)
    ‖cubicCorrection J B r - h‖ ≤ K * (M + H*A*(2+A)/2) * ‖h‖^3 := by
  let s := newtonDirection J r
  let e := r + J h + (1/2 : ℝ) • B h h
  let A := K * (H/2 + M)
  have hA : 0 ≤ A := mul_nonneg hK (by positivity)
  have he : ‖e‖ ≤ M * ‖h‖^3 := hrem
  have hid : s-h = J.symm ((1/2 : ℝ) • B h h - e) := by
    simp [s, newtonDirection, e, map_add]
    abel
  have hd : ‖s-h‖ ≤ A * ‖h‖^2 := by
    rw [hid]
    calc
      ‖J.symm ((1/2 : ℝ) • B h h - e)‖ ≤ K * ‖(1/2 : ℝ) • B h h - e‖ := hJ _
      _ ≤ K * (‖(1/2 : ℝ) • B h h‖ + ‖e‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) hK
      _ ≤ A * ‖h‖^2 := by
        rw [norm_smul]
        norm_num
        have hb := hB h h
        have hp : ‖h‖^3 ≤ ‖h‖^2 := by nlinarith [norm_nonneg h, sq_nonneg ‖h‖]
        have hm := mul_le_mul_of_nonneg_left hp hM
        dsimp [A]
        nlinarith
  have hs : ‖s‖ ≤ (1+A) * ‖h‖ := by
    have ht := norm_add_le (s-h) h
    rw [sub_add_cancel] at ht
    have hp : ‖h‖^2 ≤ ‖h‖ := by nlinarith [norm_nonneg h]
    have ha := mul_le_mul_of_nonneg_left hp hA
    nlinarith
  have hi : cubicCorrection J B r - h =
      J.symm ((1/2 : ℝ) • (B h h - B s s) - e) := by
    change s - (1/2 : ℝ) • J.symm (B s s) - h = _
    rw [smul_sub, map_sub, map_sub, map_smul, map_smul]
    have hi' := congrArg (fun v => v - (1/2 : ℝ) • J.symm (B s s)) hid
    simp only [map_sub, map_smul] at hi'
    convert hi' using 1 <;> abel
  have hb : ‖B h h - B s s‖ ≤ H * A * (2+A) * ‖h‖^3 := by
    rw [bilinear_diagonal_difference]
    calc
      ‖B (h-s) h + B s (h-s)‖ ≤ ‖B (h-s) h‖ + ‖B s (h-s)‖ := norm_add_le _ _
      _ ≤ H * ‖h-s‖ * ‖h‖ + H * ‖s‖ * ‖h-s‖ := add_le_add (hB _ _) (hB _ _)
      _ ≤ H * (A*‖h‖^2) * ‖h‖ + H * ((1+A)*‖h‖) * (A*‖h‖^2) := by
        rw [norm_sub_rev h s]
        gcongr
      _ = H * A * (2+A) * ‖h‖^3 := by ring
  rw [hi]
  change ‖J.symm ((1/2 : ℝ) • (B h h - B s s) - e)‖ ≤ _
  calc
    _ ≤ K * ‖(1/2 : ℝ) • (B h h - B s s) - e‖ := hJ _
    _ ≤ K * (‖(1/2 : ℝ) • (B h h - B s s)‖ + ‖e‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hK
    _ ≤ K * (M + H*A*(2+A)/2) * ‖h‖^3 := by
      rw [norm_smul]
      norm_num
      nlinarith

/-- Operator norms supply the inverse and bilinear bounds used by `cubic_error`. -/
theorem cubic_error_opNorm (J : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (r h : E) (M : ℝ) (hM : 0 ≤ M) (hh : ‖h‖ ≤ 1)
    (hrem : ‖r + J h + (1/2 : ℝ) • B h h‖ ≤ M * ‖h‖^3) :
    let K := ‖J.symm.toContinuousLinearMap‖
    let H := ‖B‖
    let A := K * (H/2 + M)
    ‖cubicCorrection J B r - h‖ ≤ K * (M + H*A*(2+A)/2) * ‖h‖^3 :=
  cubic_error J B r h _ _ M J.symm.toContinuousLinearMap.opNorm_nonneg B.opNorm_nonneg hM
    J.symm.toContinuousLinearMap.le_opNorm B.le_opNorm₂ hh hrem

/-- End-to-end cubic bound from a regular path to a root and its first three jets.
The path's third derivative bound is explicit, rather than a candidate-order hypothesis. -/
theorem cubic_error_from_path (J : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (r h : E) (φ : ℝ → E) (M₃ : ℝ) (hM : 0 ≤ M₃) (hh : ‖h‖ ≤ 1)
    (hφ : ContDiffOn ℝ 3 φ (Icc 0 1)) (hstart : φ 0 = r) (hroot : φ 1 = 0)
    (h₁ : iteratedDerivWithin 1 φ (Icc 0 1) 0 = J h)
    (h₂ : iteratedDerivWithin 2 φ (Icc 0 1) 0 = B h h)
    (h₃ : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 3 φ (Icc 0 1) t‖ ≤ M₃ * ‖h‖^3) :
    let K := ‖J.symm.toContinuousLinearMap‖
    let H := ‖B‖
    let M := M₃/2
    let A := K * (H/2 + M)
    ‖cubicCorrection J B r - h‖ ≤ K * (M + H*A*(2+A)/2) * ‖h‖^3 := by
  have ht := path_taylor_bound φ h (J h) (B h h) M₃ hφ h₁ h₂ h₃
  rw [hstart,hroot] at ht
  have he : (0 : E)-r-J h-(1/2 : ℝ) • B h h = -(r+J h+(1/2 : ℝ) • B h h) := by abel
  rw [he, norm_neg] at ht
  exact cubic_error_opNorm J B r h (M₃/2) (by positivity) hh ht

end LeanMath.Papers.CubicReversion
