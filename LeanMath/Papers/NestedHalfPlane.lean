import LeanMath.Papers.ArcHalfPlane
import LeanMath.Papers.NestedOrderNine

/-! # The half-plane theorem for the nested-radical support

The complex nested support, with principal square roots, is holomorphic with values off the
negative axis on the closed right half-plane (origin removed), commutes with conjugation, coincides
on the positive axis with the real support of `NestedRadicalReal`, and its residual map has contact
of order nine at `1`. With the boundary inequality `0 ≤ arg φ (i y) ≤ π / p` as its only hypothesis,
the residual map contracts the Cayley coordinate with exponent nine.
The boundary inequality itself is certified by interval arithmetic outside Lean. -/

noncomputable section
namespace LeanMath.Papers.NestedHalfPlane

open Metric Filter Topology Asymptotics Set
open LeanMath.Papers.ComplexRoots LeanMath.Papers.ComplexHalfPlane LeanMath.Papers.ArcHalfPlane
open LeanMath.Papers.NestedRadicalReal (originalA originalB originalC)

/-! ## Principal square root -/

/-- Principal square root, `exp (log z / 2)`. -/
def csqrt (z : ℂ) : ℂ := Complex.exp (Complex.log z / 2)

theorem csqrt_sq {z : ℂ} (hz : z ≠ 0) : csqrt z ^ 2 = z := by
  unfold csqrt
  rw [← Complex.exp_nat_mul]
  have e : ((2 : ℕ) : ℂ) * (Complex.log z / 2) = Complex.log z := by push_cast; ring
  rw [e, Complex.exp_log hz]

theorem csqrt_re_pos {z : ℂ} (hz : z ∈ Complex.slitPlane) : 0 < (csqrt z).re := by
  unfold csqrt
  rw [Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have e : Complex.log z / 2 = ((1 / 2 : ℝ) : ℂ) * Complex.log z := by push_cast; ring
  rw [e, Complex.im_ofReal_mul, Complex.log_im]
  have h1 := Complex.neg_pi_lt_arg z
  have h2 : Complex.arg z < Real.pi :=
    lt_of_le_of_ne (Complex.arg_le_pi _) (Complex.mem_slitPlane_iff_arg.mp hz).1
  constructor <;> linarith

theorem csqrt_re_sq {z : ℂ} (hz : z ≠ 0) : (csqrt z).re ^ 2 - (csqrt z).im ^ 2 = z.re := by
  have h := congrArg Complex.re (csqrt_sq hz)
  simp only [pow_two, Complex.mul_re] at h
  linear_combination h

theorem csqrt_re_im {z : ℂ} (hz : z ≠ 0) : 2 * (csqrt z).re * (csqrt z).im = z.im := by
  have h := congrArg Complex.im (csqrt_sq hz)
  simp only [pow_two, Complex.mul_im] at h
  linear_combination h

theorem csqrt_conj {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    csqrt ((starRingEnd ℂ) z) = (starRingEnd ℂ) (csqrt z) := by
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_eq_iff_real.mpr ⟨2, by norm_num⟩
  unfold csqrt
  rw [Complex.log_conj _ (Complex.mem_slitPlane_iff_arg.mp hz).1, ← Complex.exp_conj, map_div₀, h2]

theorem csqrt_differentiableAt {f : ℂ → ℂ} {t : ℂ} (hf : DifferentiableAt ℂ f t)
    (hz : f t ∈ Complex.slitPlane) : DifferentiableAt ℂ (fun x => csqrt (f x)) t :=
  ((hf.clog hz).div_const 2).cexp

theorem csqrt_ofReal {r : ℝ} (hr : 0 < r) : csqrt (r : ℂ) = ((Real.sqrt r : ℝ) : ℂ) := by
  unfold csqrt
  rw [sqrt_eq_exp hr, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_log hr.le]
  simp

theorem inv_re_le {D : ℂ} {d : ℝ} (hd : 0 < d) (hD : d ≤ D.re) : (D⁻¹).re ≤ 1 / d := by
  have hpos : 0 < D.re := lt_of_lt_of_le hd hD
  have hns : D.re * D.re ≤ Complex.normSq D := by
    rw [Complex.normSq_apply]; nlinarith [mul_self_nonneg D.im]
  have hnspos : 0 < Complex.normSq D := lt_of_lt_of_le (mul_pos hpos hpos) hns
  rw [Complex.inv_re]
  have h1 : D.re / Complex.normSq D ≤ 1 / D.re := by
    rw [div_le_div_iff₀ hnspos hpos]; linarith
  exact h1.trans (one_div_le_one_div_of_le hd hD)

theorem mul_mem_slitPlane {z₁ z₂ : ℂ} (h1 : 0 ≤ z₁.re) (h10 : z₁ ≠ 0) (h2 : 0 < z₂.re) :
    z₁ * z₂ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff, Complex.mul_re, Complex.mul_im]
  by_cases h : z₁.re * z₂.im + z₁.im * z₂.re = 0
  · left
    have e : (z₁.re * z₂.re - z₁.im * z₂.im) * z₂.re = z₁.re * (z₂.re ^ 2 + z₂.im ^ 2) := by
      linear_combination -z₂.im * h
    have hsum : 0 < z₂.re ^ 2 + z₂.im ^ 2 := by positivity
    have hre : 0 < z₁.re := by
      rcases h1.lt_or_eq with h3 | h3
      · exact h3
      · exfalso
        apply h10
        have him : z₁.im = 0 := by
          rw [← h3, zero_mul, zero_add] at h
          rcases mul_eq_zero.mp h with h4 | h4
          · exact h4
          · exact absurd h4 h2.ne'
        apply Complex.ext
        · simp [← h3]
        · simp [him]
    have h5 : 0 < z₁.re * (z₂.re ^ 2 + z₂.im ^ 2) := mul_pos hre hsum
    by_contra hneg
    have hneg' : z₁.re * z₂.re - z₁.im * z₂.im ≤ 0 := le_of_not_gt hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg' h2.le
    linarith
  · right; exact h

theorem corr_mem_slitPlane {p : ℝ} (hp : 2 < p) {q t : ℂ} (hq : 0 < q.re) (ht : 0 ≤ t.re) :
    corr (p : ℂ) q t ∈ Complex.slitPlane := by
  have h := mul_pos (by linarith : (0 : ℝ) < p - 1) hq
  apply div_mem_slitPlane
  · rw [num_re]; linarith
  · rw [den_re]; linarith

theorem corr_den_ne_zero {p : ℝ} (hp : 2 < p) {q : ℂ} (hq : 0 < q.re) :
    1 + ((p : ℂ) - 1) * q ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  rw [den_re, Complex.zero_re] at h1
  have := mul_pos (by linarith : (0 : ℝ) < p - 1) hq
  linarith

/-! ## Coefficients -/

theorem coeff_bounds {p : ℝ} (hp : 2 < p) :
    0 < originalA p ∧ originalA p ≤ 1 / 12 ∧ 0 < originalB p ∧ originalB p ≤ 7 / 40 ∧
      0 < originalC p ∧ originalC p ≤ 121 / 2520 := by
  have hp0 : 0 < p := by linarith
  have hh : ∃ h : ℝ, h = 1 / p := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ := hh
  have h0 : 0 < h := by rw [hh]; positivity
  have h1 : h < 1 / 2 := by
    rw [hh, div_lt_div_iff₀ hp0 (by norm_num)]; linarith
  have e1 : 2 / p = 2 * h := by rw [hh]; ring
  have e3 : 185 / p = 185 * h := by rw [hh]; ring
  have e4 : 67 / p ^ 2 = 67 * h ^ 2 := by rw [hh]; field_simp
  have e5 : 1 / p ^ 3 = h ^ 3 := by rw [hh]; field_simp
  have hsq : h ^ 2 < 1 / 4 := by nlinarith
  have hcu : h ^ 3 < 1 / 8 := by nlinarith [pow_pos h0 2]
  have hsq0 : 0 < h ^ 2 := by positivity
  have hcu0 : 0 < h ^ 3 := by positivity
  unfold originalA originalB originalC
  rw [e1, e3, e4, e5, ← hh]
  have hden : 0 < 840 * (h + 3) := by linarith
  refine ⟨by linarith, by linarith, by positivity, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by norm_num)]; nlinarith
  · exact div_pos (by linarith) hden
  · rw [div_le_iff₀ hden]; nlinarith

/-! ## The complex nested support -/

/-- `w = (t - 1) ^ 2 / t`. -/
def wC (t : ℂ) : ℂ := (t - 1) ^ 2 / t

def DC (p : ℝ) (t : ℂ) : ℂ := 1 + (originalC p : ℂ) * wC t

def ρ2C (p : ℝ) (t : ℂ) : ℂ := 1 + (originalB p : ℂ) * wC t / DC p t

def ρC (p : ℝ) (t : ℂ) : ℂ := csqrt (ρ2C p t)

def innerC (p : ℝ) (t : ℂ) : ℂ := 1 + (originalA p : ℂ) * wC t / ρC p t

/-- The radicand `t (1 + a w / sqrt (1 + b w / (1 + c w)))`. -/
def QN (p : ℝ) (t : ℂ) : ℂ := t * innerC p t

/-- The nested support. -/
def qN (p : ℝ) (t : ℂ) : ℂ := csqrt (QN p t)

/-- The correction of the nested support. -/
def φN (p : ℝ) (t : ℂ) : ℂ := corr (p : ℂ) (qN p t) t

theorem wC_re_ge {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) : -2 ≤ (wC t).re := by
  have e : wC t = t + t⁻¹ - 2 := by unfold wC; field_simp; ring
  have h1 : 0 ≤ t.re / Complex.normSq t := div_nonneg ht (Complex.normSq_nonneg t)
  rw [e, Complex.sub_re, Complex.add_re, Complex.inv_re]
  have h2 : (2 : ℂ).re = 2 := by norm_num
  rw [h2]
  linarith

theorem DC_re (p : ℝ) (t : ℂ) : (DC p t).re = 1 + originalC p * (wC t).re := by
  unfold DC; rw [Complex.add_re, Complex.re_ofReal_mul, Complex.one_re]

theorem DC_im (p : ℝ) (t : ℂ) : (DC p t).im = originalC p * (wC t).im := by
  unfold DC; rw [Complex.add_im, Complex.im_ofReal_mul, Complex.one_im, zero_add]

theorem DC_re_ge {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    1 - 2 * originalC p ≤ (DC p t).re := by
  obtain ⟨_, _, _, _, hC, _⟩ := coeff_bounds hp
  rw [DC_re]
  have := mul_le_mul_of_nonneg_left (wC_re_ge ht ht0) hC.le
  linarith

theorem DC_ne_zero {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) : DC p t ≠ 0 := by
  obtain ⟨_, _, _, _, _, hC'⟩ := coeff_bounds hp
  intro h
  have h1 := DC_re_ge hp ht ht0
  rw [h, Complex.zero_re] at h1
  linarith

theorem ρ2C_re_ge {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    3 / 5 ≤ (ρ2C p t).re := by
  obtain ⟨_, _, hB, hB', hC, hC'⟩ := coeff_bounds hp
  have hD := DC_ne_zero hp ht ht0
  have hCc : (originalC p : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  have hd : 0 < 1 - 2 * originalC p := by linarith
  have e : (originalB p : ℂ) * wC t / DC p t
      = ((originalB p / originalC p : ℝ) : ℂ) * (1 - (DC p t)⁻¹) := by
    have hw : wC t = (DC p t - 1) / (originalC p : ℂ) := by
      unfold DC; rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hCc]
    rw [hw]; push_cast; field_simp
  have hinv := inv_re_le hd (DC_re_ge hp ht ht0)
  unfold ρ2C
  rw [e, Complex.add_re, Complex.one_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re]
  have h3 : -(2 * originalC p / (1 - 2 * originalC p)) ≤ 1 - ((DC p t)⁻¹).re := by
    have e2 : 1 - 1 / (1 - 2 * originalC p) = -(2 * originalC p / (1 - 2 * originalC p)) := by
      field_simp; ring
    linarith
  have hBC : 0 ≤ originalB p / originalC p := (div_pos hB hC).le
  have h4 := mul_le_mul_of_nonneg_left h3 hBC
  have e3 : originalB p / originalC p * -(2 * originalC p / (1 - 2 * originalC p))
      = -(2 * originalB p / (1 - 2 * originalC p)) := by field_simp
  have h5 : 2 * originalB p / (1 - 2 * originalC p) ≤ 2 / 5 := by
    rw [div_le_iff₀ hd]; linarith
  linarith

theorem ρ2C_mem {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    ρ2C p t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  linarith [ρ2C_re_ge hp ht ht0]

theorem ρ2C_im_mul {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    0 ≤ (ρ2C p t).im * (wC t).im := by
  obtain ⟨_, _, hB, _, _, _⟩ := coeff_bounds hp
  have hns : 0 < Complex.normSq (DC p t) := Complex.normSq_pos.mpr (DC_ne_zero hp ht ht0)
  have e : (ρ2C p t).im = originalB p * ((wC t).im / Complex.normSq (DC p t)) := by
    unfold ρ2C
    rw [Complex.add_im, Complex.one_im, zero_add, mul_div_assoc, Complex.im_ofReal_mul,
      Complex.div_im, DC_re, DC_im]
    congr 1
    field_simp
    ring
  rw [e]
  have : originalB p * ((wC t).im / Complex.normSq (DC p t)) * (wC t).im
      = originalB p * ((wC t).im ^ 2 / Complex.normSq (DC p t)) := by ring
  rw [this]
  positivity

theorem ρC_re_ge {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    3 / 4 ≤ (ρC p t).re := by
  have hmem := ρ2C_mem hp ht ht0
  have hpos : 0 < (ρC p t).re := csqrt_re_pos hmem
  have hsq := csqrt_re_sq (Complex.slitPlane_ne_zero hmem)
  have h35 := ρ2C_re_ge hp ht ht0
  unfold ρC
  unfold ρC at hpos
  by_contra hlt
  have hlt' : (csqrt (ρ2C p t)).re < 3 / 4 := lt_of_not_ge hlt
  nlinarith [sq_nonneg (csqrt (ρ2C p t)).im]

theorem ρC_ne_zero {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) : ρC p t ≠ 0 := by
  intro h
  have h1 := ρC_re_ge hp ht ht0
  rw [h, Complex.zero_re] at h1
  linarith

theorem ρC_im_mul {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    0 ≤ (ρC p t).im * (wC t).im := by
  have hmem := ρ2C_mem hp ht ht0
  have hre := ρC_re_ge hp ht ht0
  have h2 := csqrt_re_im (Complex.slitPlane_ne_zero hmem)
  have h3 := ρ2C_im_mul hp ht ht0
  unfold ρC at hre ⊢
  rw [← h2] at h3
  have h4 : 0 < 2 * (csqrt (ρ2C p t)).re := by linarith
  by_contra hneg
  have hneg' : (csqrt (ρ2C p t)).im * (wC t).im < 0 := lt_of_not_ge hneg
  have := mul_pos h4 (neg_pos.mpr hneg')
  nlinarith

theorem innerC_re_ge {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    7 / 9 ≤ (innerC p t).re := by
  obtain ⟨hA, hA', _, _, _, _⟩ := coeff_bounds hp
  have hre := ρC_re_ge hp ht ht0
  have hρpos : 0 < (ρC p t).re := by linarith
  have hns : (ρC p t).re * (ρC p t).re ≤ Complex.normSq (ρC p t) := by
    rw [Complex.normSq_apply]; nlinarith [mul_self_nonneg (ρC p t).im]
  have hnspos : 0 < Complex.normSq (ρC p t) := lt_of_lt_of_le (mul_pos hρpos hρpos) hns
  have hk : (ρC p t).re / Complex.normSq (ρC p t) ≤ 4 / 3 := by
    have h1 : (ρC p t).re / Complex.normSq (ρC p t) ≤ 1 / (ρC p t).re := by
      rw [div_le_div_iff₀ hnspos hρpos]; linarith
    have h2 : 1 / (ρC p t).re ≤ 1 / (3 / 4) := one_div_le_one_div_of_le (by norm_num) hre
    have h3 : (1 : ℝ) / (3 / 4) = 4 / 3 := by norm_num
    linarith
  have hk0 : 0 ≤ (ρC p t).re / Complex.normSq (ρC p t) := div_nonneg hρpos.le hnspos.le
  have hw := wC_re_ge ht ht0
  have him := ρC_im_mul hp ht ht0
  have hdiv : -(8 / 3) ≤ (wC t / ρC p t).re := by
    rw [Complex.div_re]
    have t1 : (wC t).re * (ρC p t).re / Complex.normSq (ρC p t)
        = (wC t).re * ((ρC p t).re / Complex.normSq (ρC p t)) := by ring
    have t2 : 0 ≤ (wC t).im * (ρC p t).im / Complex.normSq (ρC p t) :=
      div_nonneg (by linarith [mul_comm (wC t).im (ρC p t).im]) hnspos.le
    have t3 : -2 * ((ρC p t).re / Complex.normSq (ρC p t))
        ≤ (wC t).re * ((ρC p t).re / Complex.normSq (ρC p t)) :=
      mul_le_mul_of_nonneg_right hw hk0
    rw [t1]
    linarith
  unfold innerC
  rw [Complex.add_re, Complex.one_re, mul_div_assoc, Complex.re_ofReal_mul]
  have := mul_le_mul_of_nonneg_left hdiv hA.le
  nlinarith

theorem innerC_re_pos {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    0 < (innerC p t).re := by linarith [innerC_re_ge hp ht ht0]

theorem QN_mem {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    QN p t ∈ Complex.slitPlane :=
  mul_mem_slitPlane ht ht0 (innerC_re_pos hp ht ht0)

theorem qN_re_pos {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    0 < (qN p t).re := csqrt_re_pos (QN_mem hp ht ht0)

theorem φN_mem {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    φN p t ∈ Complex.slitPlane :=
  corr_mem_slitPlane hp (qN_re_pos hp ht ht0) ht

/-! ## Holomorphy -/

theorem wC_differentiableAt {t : ℂ} (ht0 : t ≠ 0) : DifferentiableAt ℂ wC t :=
  ((differentiableAt_id.sub_const 1).pow 2).div differentiableAt_id ht0

theorem ρ2C_differentiableAt {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    DifferentiableAt ℂ (ρ2C p) t := by
  have hw := wC_differentiableAt ht0
  have hD : DifferentiableAt ℂ (DC p) t := (differentiableAt_const _).add (hw.const_mul _)
  exact (differentiableAt_const _).add ((hw.const_mul _).div hD (DC_ne_zero hp ht ht0))

theorem QN_differentiableAt {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    DifferentiableAt ℂ (QN p) t := by
  have hw := wC_differentiableAt ht0
  have hρ : DifferentiableAt ℂ (ρC p) t :=
    csqrt_differentiableAt (ρ2C_differentiableAt hp ht ht0) (ρ2C_mem hp ht ht0)
  have hin : DifferentiableAt ℂ (innerC p) t :=
    (differentiableAt_const _).add ((hw.const_mul _).div hρ (ρC_ne_zero hp ht ht0))
  exact differentiableAt_id.mul hin

theorem φN_differentiableAt {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    DifferentiableAt ℂ (φN p) t := by
  have hq : DifferentiableAt ℂ (qN p) t :=
    csqrt_differentiableAt (QN_differentiableAt hp ht ht0) (QN_mem hp ht ht0)
  exact (differentiableAt_id.add (hq.const_mul _)).div
    ((differentiableAt_const _).add (hq.const_mul _))
    (corr_den_ne_zero hp (qN_re_pos hp ht ht0))

/-! ## Conjugation symmetry -/

theorem φN_conj {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    φN p ((starRingEnd ℂ) t) = (starRingEnd ℂ) (φN p t) := by
  have hw : wC ((starRingEnd ℂ) t) = (starRingEnd ℂ) (wC t) := by simp [wC]
  have hD : DC p ((starRingEnd ℂ) t) = (starRingEnd ℂ) (DC p t) := by simp [DC, hw]
  have hρ2 : ρ2C p ((starRingEnd ℂ) t) = (starRingEnd ℂ) (ρ2C p t) := by simp [ρ2C, hw, hD]
  have hρ : ρC p ((starRingEnd ℂ) t) = (starRingEnd ℂ) (ρC p t) := by
    unfold ρC; rw [hρ2, csqrt_conj (ρ2C_mem hp ht ht0)]
  have hin : innerC p ((starRingEnd ℂ) t) = (starRingEnd ℂ) (innerC p t) := by
    simp [innerC, hw, hρ]
  have hQ : QN p ((starRingEnd ℂ) t) = (starRingEnd ℂ) (QN p t) := by simp [QN, hin]
  have hq : qN p ((starRingEnd ℂ) t) = (starRingEnd ℂ) (qN p t) := by
    unfold qN; rw [hQ, csqrt_conj (QN_mem hp ht ht0)]
  unfold φN corr
  rw [hq]
  simp

/-! ## Order of contact from a real limit, for a general correction -/

/-- Real form of the contact of order `m` of the residual map at `t = 1`. -/
theorem real_residual_bound_gen (p : ℝ) (hp : 0 < p) (corrR : ℝ → ℝ) (m : ℕ) (hm : m ≠ 0) (c : ℝ)
    (h1 : corrR 1 = 1)
    (hlim : Tendsto (fun e : ℝ => (e + Real.log (corrR (Real.exp (-p * e)))) / e ^ m) (𝓝[≠] 0)
      (𝓝 c)) :
    ∃ C ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∀ x : ℝ, |x| < ρ →
      |(1 + x) * Real.exp (-(p * Real.log (corrR (1 + x)))) - 1| ≤ C * |x| ^ m := by
  have hp0 : 0 < p := hp
  obtain ⟨δ, hδ, hδf⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hlim) 1 one_pos
  set s := 2 / p + 1 with hs
  have hspos : 0 < s := by positivity
  set K := p * (|c| + 1) * s ^ m with hK
  have hKpos : 0 < K := mul_pos (mul_pos hp0 (by positivity)) (pow_pos hspos m)
  have hδs : 0 < δ / s := div_pos hδ hspos
  refine ⟨2 * K, min (min (1 / 2) (δ / s)) (1 / K), by positivity,
    (min_le_left _ _).trans (min_le_left _ _), ?_⟩
  intro x hx
  have hx2 : |x| < 1 / 2 := lt_of_lt_of_le hx ((min_le_left _ _).trans (min_le_left _ _))
  have hxδ : s * |x| < δ := by
    have h : |x| < δ / s := lt_of_lt_of_le hx ((min_le_left _ _).trans (min_le_right _ _))
    have := (lt_div_iff₀ hspos).mp h
    linarith [mul_comm s |x|]
  have hxK : |x| < 1 / K := lt_of_lt_of_le hx (min_le_right _ _)
  have hxb := abs_lt.mp hx2
  have htpos : 0 < 1 + x := by linarith
  by_cases hx0 : x = 0
  · subst hx0
    rw [add_zero, h1]
    simp [hm]
  · have hlog : |Real.log (1 + x)| ≤ 2 * |x| := by
      have hup : Real.log (1 + x) ≤ x := by
        have := Real.log_le_sub_one_of_pos htpos
        linarith
      have hinv : (1 + x)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ htpos (by norm_num)]
        linarith
      have hlow : x * (1 + x)⁻¹ ≤ Real.log (1 + x) := by
        have h := Real.one_sub_inv_le_log_of_pos htpos
        have e : 1 - (1 + x)⁻¹ = x * (1 + x)⁻¹ := by field_simp; ring
        linarith
      have hprod : |x * (1 + x)⁻¹| ≤ |x| * 2 := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr htpos)]
        exact mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
      have h3 := neg_abs_le (x * (1 + x)⁻¹)
      have h4 := le_abs_self x
      have h5 := abs_nonneg x
      rw [abs_le]
      constructor <;> linarith
    set e := -Real.log (1 + x) / p with he
    have hept : Real.exp (-p * e) = 1 + x := by
      have h : -p * e = Real.log (1 + x) := by rw [he]; field_simp
      rw [h, Real.exp_log htpos]
    have hlogne : Real.log (1 + x) ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one htpos (by intro h; apply hx0; linarith)
    have he0 : e ≠ 0 := by
      rw [he]; exact div_ne_zero (neg_ne_zero.mpr hlogne) hp0.ne'
    have heabs : |e| ≤ s * |x| := by
      rw [he, abs_div, abs_neg, abs_of_pos hp0, div_le_iff₀ hp0]
      have e1 : s * |x| * p = 2 * |x| + p * |x| := by rw [hs]; field_simp
      rw [e1]
      linarith [mul_nonneg hp0.le (abs_nonneg x)]
    have hdist := hδf (x := e) he0 (by
      rw [Real.dist_eq, sub_zero]; exact lt_of_le_of_lt heabs hxδ)
    rw [hept, Real.dist_eq] at hdist
    have h5 : 0 < |e| ^ m := pow_pos (abs_pos.mpr he0) m
    have hE : |e + Real.log (corrR (1 + x))| ≤ (|c| + 1) * |e| ^ m := by
      have h6 := abs_sub_abs_le_abs_sub ((e + Real.log (corrR (1 + x))) / e ^ m) c
      have h7 : |(e + Real.log (corrR (1 + x))) / e ^ m| < |c| + 1 := by linarith
      rw [abs_div, abs_pow, div_lt_iff₀ h5] at h7
      exact h7.le
    set L := Real.log (1 + x) - p * Real.log (corrR (1 + x)) with hL
    have hLe : L = -p * (e + Real.log (corrR (1 + x))) := by
      rw [hL, he]; field_simp; ring
    have hpow : |e| ^ m ≤ s ^ m * |x| ^ m := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg e) heabs m
    have hLabs : |L| ≤ K * |x| ^ m := by
      rw [hLe, abs_mul, abs_neg, abs_of_pos hp0, hK]
      have h8 := mul_le_mul_of_nonneg_left hE hp0.le
      have h9 : p * ((|c| + 1) * |e| ^ m) ≤ p * ((|c| + 1) * (s ^ m * |x| ^ m)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) hp0.le
      have e2 : p * (|c| + 1) * s ^ m * |x| ^ m = p * ((|c| + 1) * (s ^ m * |x| ^ m)) := by ring
      rw [e2]
      exact h8.trans h9
    have hx1 : |x| ^ m ≤ |x| := pow_le_of_le_one (abs_nonneg x) (by linarith) hm
    have hKx : K * |x| ≤ 1 := by
      rw [lt_div_iff₀ hKpos] at hxK
      linarith [mul_comm K |x|]
    have hL1 : |L| ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hx1 hKpos.le
      linarith
    have hexp : (1 + x) * Real.exp (-(p * Real.log (corrR (1 + x)))) = Real.exp L := by
      rw [hL, sub_eq_add_neg, Real.exp_add, Real.exp_log htpos]
    rw [hexp]
    have h10 := Real.abs_exp_sub_one_le hL1
    linarith [mul_assoc (2 : ℝ) K (|x| ^ m)]

/-- If a correction coincides on the positive axis with a real correction whose logarithmic error
has order `m`, its residual map has contact of order `m` at `1` in `ℂ`. -/
theorem order_of_real_limit (p : ℝ) (hp : 0 < p) (φ : ℂ → ℂ) (corrR : ℝ → ℝ) (m : ℕ) (hm : m ≠ 0)
    (c : ℝ) (hTd : ∀ t : ℂ, 0 < t.re → DifferentiableAt ℂ (Tmap p φ) t)
    (hreal : ∀ t : ℝ, 0 < t → φ (t : ℂ) = ((corrR t : ℝ) : ℂ))
    (hpos : ∀ t : ℝ, 0 < t → 0 < corrR t) (h1 : corrR 1 = 1)
    (hlim : Tendsto (fun e : ℝ => (e + Real.log (corrR (Real.exp (-p * e)))) / e ^ m) (𝓝[≠] 0)
      (𝓝 c)) :
    (fun t => Tmap p φ t - 1) =O[𝓝 1] fun t => (t - 1) ^ m := by
  set f : ℂ → ℂ := fun z => Tmap p φ (1 + z) - 1 with hf
  have hd : DifferentiableOn ℂ f (ball 0 1) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by simpa using hz
    have hre : 0 < (1 + z).re := by
      have h := Complex.abs_re_le_norm z
      have h2 := (abs_le.mp h).1
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have h1' : DifferentiableAt ℂ (fun z : ℂ => 1 + z) z :=
      (differentiableAt_const _).add differentiableAt_id
    exact (((hTd _ hre).comp z h1').sub_const 1).differentiableWithinAt
  have hana : AnalyticAt ℂ f 0 := hd.analyticAt (ball_mem_nhds 0 one_pos)
  obtain ⟨C, ρ, hρ, hρ2, hbound⟩ := real_residual_bound_gen p hp corrR m hm c h1 hlim
  have hrealb : ∀ᶠ x : ℝ in 𝓝 0, ‖f (x : ℂ)‖ ≤ C * |x| ^ m := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨ρ, hρ, fun x hx => ?_⟩
    have hx' : |x| < ρ := by simpa [Real.dist_eq] using hx
    have hpos' : 0 < 1 + x := by
      have := (abs_lt.mp (lt_of_lt_of_le hx' hρ2)).1
      linarith
    have e : (1 : ℂ) + (x : ℂ) = ((1 + x : ℝ) : ℂ) := by push_cast; rfl
    have hT : Tmap p φ ((1 + x : ℝ) : ℂ)
        = (((1 + x) * Real.exp (-(p * Real.log (corrR (1 + x)))) : ℝ) : ℂ) := by
      unfold Tmap
      rw [hreal _ hpos', ← Complex.ofReal_log (hpos _ hpos').le]
      push_cast
      rfl
    simp only [hf]
    rw [e, hT, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hbound x hx'
  have hfO := bigO_of_real_bound hana m C hrealb
  have htend : Tendsto (fun t : ℂ => t - 1) (𝓝 1) (𝓝 0) := by
    have hc : Continuous fun t : ℂ => t - 1 := continuous_id.sub continuous_const
    have h := hc.tendsto 1
    simpa using h
  have h := hfO.comp_tendsto htend
  refine h.congr (fun t => ?_) (fun t => rfl)
  simp [hf, Function.comp]

/-! ## The nested support on the positive axis -/

open LeanMath.Papers.NestedRadicalReal in
theorem wC_ofReal (t : ℝ) : wC (t : ℂ) = ((width t : ℝ) : ℂ) := by
  unfold wC width
  push_cast
  rfl

open LeanMath.Papers.NestedRadicalReal in
theorem innerRad_pos {p : ℝ} (hp : 2 < p) {w : ℝ} (hw : 0 ≤ w) : 0 < originalInnerRad p w := by
  obtain ⟨_, _, hB, _, hC, _⟩ := coeff_bounds hp
  unfold originalInnerRad
  positivity

open LeanMath.Papers.NestedRadicalReal in
theorem ρC_ofReal {p : ℝ} (hp : 2 < p) {t : ℝ} (ht : 0 < t) :
    ρC p (t : ℂ) = ((Real.sqrt (originalInnerRad p (width t)) : ℝ) : ℂ) := by
  have h2 : ρ2C p (t : ℂ) = ((originalInnerRad p (width t) : ℝ) : ℂ) := by
    unfold ρ2C DC originalInnerRad
    rw [wC_ofReal]
    push_cast
    rfl
  unfold ρC
  rw [h2, csqrt_ofReal (innerRad_pos hp (width_nonneg t ht))]

open LeanMath.Papers.NestedRadicalReal in
theorem qN_ofReal {p : ℝ} (hp : 2 < p) {t : ℝ} (ht : 0 < t) :
    qN p (t : ℂ) = ((support p t : ℝ) : ℂ) := by
  obtain ⟨hA, _, _, _, _, _⟩ := coeff_bounds hp
  have hw := width_nonneg t ht
  have hs : 0 < Real.sqrt (originalInnerRad p (width t)) :=
    Real.sqrt_pos.mpr (innerRad_pos hp hw)
  have hQ : QN p (t : ℂ)
      = ((t * (1 + originalA p * width t / Real.sqrt (originalInnerRad p (width t))) : ℝ) : ℂ) := by
    unfold QN innerC
    rw [wC_ofReal, ρC_ofReal hp ht]
    push_cast
    rfl
  have hpos : 0 < t * (1 + originalA p * width t / Real.sqrt (originalInnerRad p (width t))) := by
    positivity
  unfold qN
  rw [hQ, csqrt_ofReal hpos, ← originalSupport_eq p t hp ht]
  rfl

open LeanMath.Papers.NestedRadicalReal in
theorem φN_ofReal {p : ℝ} (hp : 2 < p) {t : ℝ} (ht : 0 < t) :
    φN p (t : ℂ) = ((correction p t : ℝ) : ℂ) := by
  unfold φN corr correction
  rw [qN_ofReal hp ht]
  push_cast
  rfl

open LeanMath.Papers.NestedRadicalReal in
theorem correction_pos {p : ℝ} (hp : 2 < p) {t : ℝ} (ht : 0 < t) : 0 < correction p t := by
  have hs := support_positive p t hp ht
  have h1 := mul_pos (by linarith : (0 : ℝ) < p - 1) hs
  unfold correction
  exact div_pos (by linarith) (by linarith)

open LeanMath.Papers.NestedRadicalReal in
theorem correction_one {p : ℝ} (hp : 2 < p) : correction p 1 = 1 := by
  have hs := support_positive p 1 hp one_pos
  have h1 := mul_pos (by linarith : (0 : ℝ) < p - 1) hs
  unfold correction
  exact div_self (by linarith)

theorem Tmap_differentiableAt {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 < t.re) :
    DifferentiableAt ℂ (Tmap p (φN p)) t := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at ht
    exact lt_irrefl _ ht
  have h1 := (φN_differentiableAt hp ht.le ht0).clog (φN_mem hp ht.le ht0)
  exact differentiableAt_id.mul ((h1.const_mul (p : ℂ)).neg.cexp)

/-- The residual map of the nested support has contact of order nine at `1`, in `ℂ`. -/
theorem nested_order {p : ℝ} (hp : 2 < p) :
    (fun t => Tmap p (φN p) t - 1) =O[𝓝 1] fun t => (t - 1) ^ 9 :=
  order_of_real_limit p (by linarith) (φN p) (NestedRadicalReal.correction p) 9 (by norm_num)
    (DegreesEfficiency.c9 p) (fun _ ht => Tmap_differentiableAt hp ht)
    (fun _ ht => φN_ofReal hp ht) (fun _ ht => correction_pos hp ht) (correction_one hp)
    (NestedOrderNine.order_nine p hp)

/-! ## The half-plane theorem, given the boundary inequality -/

theorem upper_of_arg {p : ℝ} (hp0 : 0 < p) {z : ℂ} (h0 : 0 ≤ Complex.arg z)
    (h1 : Complex.arg z ≤ Real.pi / p) : |Real.pi / 2 - p * Complex.arg z| ≤ Real.pi / 2 := by
  have h2 : p * Complex.arg z ≤ Real.pi := by
    have := mul_le_mul_of_nonneg_left h1 hp0.le
    rwa [mul_div_cancel₀ _ hp0.ne'] at this
  have h3 : 0 ≤ p * Complex.arg z := mul_nonneg hp0.le h0
  rw [abs_le]
  constructor <;> linarith

/-- **Half-plane theorem for the nested support**, with the boundary inequality as hypothesis:
if `0 ≤ arg φ (i y) ≤ π / p` for every `y > 0`, then for every `t` with `Re t > 0` the residual map
contracts the Cayley coordinate with exponent nine. -/
theorem nested_halfplane_contraction (p : ℝ) (hp : 2 < p)
    (hbdry : ∀ y : ℝ, 0 < y → 0 ≤ Complex.arg (φN p (Complex.I * y)) ∧
      Complex.arg (φN p (Complex.I * y)) ≤ Real.pi / p)
    (t : ℂ) (ht : 0 < t.re) :
    ‖(Tmap p (φN p) t - 1) / (Tmap p (φN p) t + 1)‖ ≤ ‖(t - 1) / (t + 1)‖ ^ 9 := by
  have hp0 : 0 < p := by linarith
  refine halfplane_contraction p 9 (φN p) (fun _ h h0 => φN_differentiableAt hp h h0)
    (fun _ h h0 => φN_mem hp h h0) (fun y hy => upper_of_arg hp0 (hbdry y hy).1 (hbdry y hy).2)
    ?_ (nested_order hp) t ht
  intro y hy
  obtain ⟨h0, h1⟩ := hbdry y hy
  have hre0 : (0 : ℝ) ≤ (Complex.I * (y : ℂ)).re := by simp
  have hne : Complex.I * (y : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hy.ne' this
  have hconj : -Complex.I * (y : ℂ) = (starRingEnd ℂ) (Complex.I * y) := by simp
  have hπp : Real.pi / p < Real.pi := by
    rw [div_lt_iff₀ hp0]
    nlinarith [Real.pi_pos]
  have hargne : Complex.arg (φN p (Complex.I * y)) ≠ Real.pi := by linarith
  rw [hconj, φN_conj hp hre0 hne, Complex.arg_conj, if_neg hargne]
  have h := upper_of_arg hp0 h0 h1
  rw [abs_le] at h ⊢
  constructor <;> nlinarith [h.1, h.2]

end LeanMath.Papers.NestedHalfPlane
