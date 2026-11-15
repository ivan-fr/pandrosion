import LeanMath.Papers.ComplexHalfPlane
import LeanMath.Papers.ArcOrderFive
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The half-plane theorem for the decentered arc

For every real `p > 2` and every `t` with `Re t > 0`, the residual map of the decentered arc,
with principal square root and principal logarithm, satisfies `|η (T t)| ≤ |η t| ^ 5`,
`η = (t - 1) / (t + 1)`. No hypothesis is left open: holomorphy, the boundary inequality and the
order of contact are proved here from `ComplexHalfPlane`, `ComplexRoots.arc_boundary_core` and
`ArcOrderFive.order_five`. -/

noncomputable section
namespace LeanMath.Papers.ArcHalfPlane

open Metric Filter Topology Asymptotics Set
open LeanMath.Papers.ComplexRoots LeanMath.Papers.ComplexHalfPlane

/-- `a = (p - 2) / (12 p)`. -/
def aR (p : ℝ) : ℝ := (p - 2) / (12 * p)

/-- The radicand `t + a (t - 1) ^ 2`. -/
def QC (p : ℝ) (t : ℂ) : ℂ := t + (aR p : ℂ) * (t - 1) ^ 2

/-- The support: principal square root of the radicand. -/
def qC (p : ℝ) (t : ℂ) : ℂ := Complex.exp (Complex.log (QC p t) / 2)

/-- The correction of the decentered arc. -/
def φC (p : ℝ) (t : ℂ) : ℂ := corr (p : ℂ) (qC p t) t

theorem aR_pos {p : ℝ} (hp : 2 < p) : 0 < aR p := div_pos (by linarith) (by linarith)

theorem aR_lt {p : ℝ} (hp : 2 < p) : aR p < 1 / 12 := by
  unfold aR
  rw [div_lt_iff₀ (by linarith)]
  linarith

theorem QC_re (p : ℝ) (t : ℂ) :
    (QC p t).re = t.re + aR p * ((t.re - 1) ^ 2 - t.im ^ 2) := by
  simp [QC, pow_two]

theorem QC_im (p : ℝ) (t : ℂ) :
    (QC p t).im = t.im * (1 - 2 * aR p + 2 * aR p * t.re) := by
  simp [QC, pow_two]
  ring

theorem QC_mem {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    QC p t ∈ Complex.slitPlane := by
  have ha := aR_pos hp
  have ha' := aR_lt hp
  rw [Complex.mem_slitPlane_iff, QC_re, QC_im]
  by_cases him : t.im = 0
  · left
    have hre : 0 < t.re := by
      rcases ht.lt_or_eq with h | h
      · exact h
      · exfalso
        apply ht0
        apply Complex.ext
        · simp [← h]
        · simp [him]
    rw [him]
    nlinarith [sq_nonneg (t.re - 1), mul_nonneg ha.le (sq_nonneg (t.re - 1))]
  · right
    have h1 : 0 < 1 - 2 * aR p + 2 * aR p * t.re := by
      have := mul_nonneg ha.le ht
      linarith
    exact mul_ne_zero him h1.ne'

theorem qC_sq {p : ℝ} {t : ℂ} (hQ : QC p t ≠ 0) : qC p t ^ 2 = QC p t := by
  unfold qC
  rw [← Complex.exp_nat_mul]
  have e : ((2 : ℕ) : ℂ) * (Complex.log (QC p t) / 2) = Complex.log (QC p t) := by
    push_cast; ring
  rw [e, Complex.exp_log hQ]

theorem qC_re_pos {p : ℝ} {t : ℂ} (hQ : QC p t ∈ Complex.slitPlane) : 0 < (qC p t).re := by
  unfold qC
  rw [Complex.exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have e : Complex.log (QC p t) / 2 = ((1 / 2 : ℝ) : ℂ) * Complex.log (QC p t) := by
    push_cast; ring
  rw [e, Complex.im_ofReal_mul, Complex.log_im]
  have h1 := Complex.neg_pi_lt_arg (QC p t)
  have h2 : Complex.arg (QC p t) < Real.pi :=
    lt_of_le_of_ne (Complex.arg_le_pi _) (Complex.mem_slitPlane_iff_arg.mp hQ).1
  constructor <;> linarith

theorem div_mem_slitPlane {N D : ℂ} (hN : 0 < N.re) (hD : 0 < D.re) :
    N / D ∈ Complex.slitPlane := by
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hD
    exact lt_irrefl _ hD
  have hns : 0 < Complex.normSq D := Complex.normSq_pos.mpr hD0
  rw [Complex.mem_slitPlane_iff, Complex.div_re, Complex.div_im]
  by_cases h : N.im * D.re - N.re * D.im = 0
  · left
    have h2 : (N.re * D.re + N.im * D.im) * D.re = N.re * (D.re ^ 2 + D.im ^ 2) := by
      linear_combination D.im * h
    have h3 : 0 < N.re * (D.re ^ 2 + D.im ^ 2) := mul_pos hN (by positivity)
    have h4 : 0 < N.re * D.re + N.im * D.im := by
      by_contra hneg
      have hneg' : N.re * D.re + N.im * D.im ≤ 0 := le_of_not_gt hneg
      have := mul_nonpos_of_nonpos_of_nonneg hneg' hD.le
      linarith
    rw [← add_div]
    exact div_pos h4 hns
  · right
    rw [← sub_div]
    exact div_ne_zero h hns.ne'

theorem cast_sub_one (p : ℝ) : ((p : ℂ) - 1) = ((p - 1 : ℝ) : ℂ) := by push_cast; ring

theorem num_re (p : ℝ) (q t : ℂ) : (t + ((p : ℂ) - 1) * q).re = t.re + (p - 1) * q.re := by
  rw [cast_sub_one, Complex.add_re, Complex.re_ofReal_mul]

theorem num_im (p : ℝ) (q t : ℂ) : (t + ((p : ℂ) - 1) * q).im = t.im + (p - 1) * q.im := by
  rw [cast_sub_one, Complex.add_im, Complex.im_ofReal_mul]

theorem den_re (p : ℝ) (q : ℂ) : (1 + ((p : ℂ) - 1) * q).re = 1 + (p - 1) * q.re := by
  rw [cast_sub_one, Complex.add_re, Complex.re_ofReal_mul, Complex.one_re]

theorem den_im (p : ℝ) (q : ℂ) : (1 + ((p : ℂ) - 1) * q).im = (p - 1) * q.im := by
  rw [cast_sub_one, Complex.add_im, Complex.im_ofReal_mul, Complex.one_im, zero_add]

theorem den_re_pos {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    0 < (1 + ((p : ℂ) - 1) * qC p t).re := by
  rw [den_re]
  have := mul_pos (by linarith : (0 : ℝ) < p - 1) (qC_re_pos (QC_mem hp ht ht0))
  linarith

theorem num_re_pos {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    0 < (t + ((p : ℂ) - 1) * qC p t).re := by
  rw [num_re]
  have := mul_pos (by linarith : (0 : ℝ) < p - 1) (qC_re_pos (QC_mem hp ht ht0))
  linarith

theorem den_ne_zero {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    1 + ((p : ℂ) - 1) * qC p t ≠ 0 := by
  intro h
  have h1 := den_re_pos hp ht ht0
  rw [h, Complex.zero_re] at h1
  exact lt_irrefl _ h1

theorem φC_mem {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    φC p t ∈ Complex.slitPlane :=
  div_mem_slitPlane (num_re_pos hp ht ht0) (den_re_pos hp ht ht0)

theorem qC_differentiableAt {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    DifferentiableAt ℂ (qC p) t := by
  have hQ : DifferentiableAt ℂ (QC p) t := by unfold QC; fun_prop
  exact ((hQ.clog (QC_mem hp ht ht0)).div_const 2).cexp

theorem φC_differentiableAt {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    DifferentiableAt ℂ (φC p) t := by
  have hq := qC_differentiableAt hp ht ht0
  exact (differentiableAt_id.add (hq.const_mul _)).div
    ((differentiableAt_const _).add (hq.const_mul _)) (den_ne_zero hp ht ht0)

/-! ## Conjugation symmetry -/

theorem QC_conj (p : ℝ) (t : ℂ) : QC p ((starRingEnd ℂ) t) = (starRingEnd ℂ) (QC p t) := by
  simp [QC]

theorem qC_conj {p : ℝ} {t : ℂ} (hQ : QC p t ∈ Complex.slitPlane) :
    qC p ((starRingEnd ℂ) t) = (starRingEnd ℂ) (qC p t) := by
  unfold qC
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := Complex.conj_eq_iff_real.mpr ⟨2, by norm_num⟩
  rw [QC_conj, Complex.log_conj _ (Complex.mem_slitPlane_iff_arg.mp hQ).1, ← Complex.exp_conj,
    map_div₀, h2]

theorem φC_conj {p : ℝ} {t : ℂ} (hQ : QC p t ∈ Complex.slitPlane) :
    φC p ((starRingEnd ℂ) t) = (starRingEnd ℂ) (φC p t) := by
  unfold φC corr
  rw [qC_conj hQ]
  simp

/-! ## The boundary inequality -/

set_option maxHeartbeats 1600000 in
theorem arc_boundary_arg {p : ℝ} (hp : 2 < p) {y : ℝ} (hy : 0 < y) :
    0 ≤ Complex.arg (φC p (Complex.I * y)) ∧
      Complex.arg (φC p (Complex.I * y)) ≤ Real.pi / p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hp2 : 0 < p - 2 := by linarith
  have ha := aR_pos hp
  have ha' := aR_lt hp
  set t : ℂ := Complex.I * y with ht
  have htre : t.re = 0 := by simp [ht]
  have htim : t.im = y := by simp [ht]
  have ht0 : t ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [htim, Complex.zero_im] at this
    exact hy.ne' this
  have htre' : 0 ≤ t.re := htre.ge
  have hQ := QC_mem hp htre' ht0
  have hQ0 : QC p t ≠ 0 := Complex.slitPlane_ne_zero hQ
  set q := qC p t with hq
  have hq1 : 0 < q.re := qC_re_pos hQ
  have hsq := qC_sq hQ0
  have hA : 1 - 2 * aR p = (5 * p + 2) / (6 * p) := by unfold aR; field_simp; ring
  have h1 : q.re ^ 2 - q.im ^ 2 = aR p * (1 - y ^ 2) := by
    have h := congrArg Complex.re hsq
    rw [QC_re, htre, htim] at h
    simp only [pow_two, Complex.mul_re] at h
    linear_combination h
  have h2 : 2 * q.re * q.im = y * (1 - 2 * aR p) := by
    have h := congrArg Complex.im hsq
    rw [QC_im, htre, htim] at h
    simp only [pow_two, Complex.mul_im] at h
    linear_combination h
  have hAp : 0 < 1 - 2 * aR p := by linarith
  have hq2 : 0 < q.im := by
    have h := mul_pos hy hAp
    by_contra hneg
    have hneg' : q.im ≤ 0 := le_of_not_gt hneg
    have := mul_nonpos_of_nonneg_of_nonpos hq1.le hneg'
    linarith
  -- the real quantities of `arc_boundary_core`
  set n2 := q.re ^ 2 + q.im ^ 2 with hn2
  have hn2pos : 0 < n2 := by positivity
  have hn2sq : n2 ^ 2 = (aR p * (1 - y ^ 2)) ^ 2 + (y * (1 - 2 * aR p)) ^ 2 := by
    rw [← h1, ← h2, hn2]; ring
  have hs : y * (1 - 2 * aR p) ≤ n2 := by
    by_contra hlt
    have hlt' : n2 < y * (1 - 2 * aR p) := lt_of_not_ge hlt
    have h6 := pow_lt_pow_left₀ hlt' hn2pos.le two_ne_zero
    linarith [sq_nonneg (aR p * (1 - y ^ 2))]
  have hay : aR p * (y ^ 2 + 1) ≤ n2 := by
    by_contra hlt
    have hlt' : n2 < aR p * (y ^ 2 + 1) := lt_of_not_ge hlt
    have h6 := pow_lt_pow_left₀ hlt' hn2pos.le two_ne_zero
    have h4a : 4 * aR p ^ 2 ≤ (1 - 2 * aR p) ^ 2 := by nlinarith
    have h7 := mul_le_mul_of_nonneg_left h4a (sq_nonneg y)
    have e7 : (aR p * (y ^ 2 + 1)) ^ 2 = (aR p * (1 - y ^ 2)) ^ 2 + y ^ 2 * (4 * aR p ^ 2) := by
      ring
    have e8 : (y * (1 - 2 * aR p)) ^ 2 = y ^ 2 * (1 - 2 * aR p) ^ 2 := by ring
    linarith
  have hRR : (q.re - q.im) * (y - 1) ≤ 0 := by
    have e : (q.re - q.im) * (y - 1) * (q.re + q.im) = -(aR p * (1 - y) ^ 2 * (1 + y)) := by
      have : (q.re - q.im) * (q.re + q.im) = aR p * (1 - y ^ 2) := by rw [← h1]; ring
      linear_combination (y - 1) * this
    have hpos : 0 ≤ aR p * (1 - y) ^ 2 * (1 + y) := by positivity
    by_contra hneg
    have hneg' : 0 < (q.re - q.im) * (y - 1) := lt_of_not_ge hneg
    have := mul_pos hneg' (by linarith : 0 < q.re + q.im)
    linarith
  set s := n2 / y with hsdef
  set R := q.re + q.im / y with hRdef
  set R' := q.im + q.re / y with hR'def
  have hs1 : (5 * p + 2) / (6 * p) ≤ s := by
    rw [← hA, hsdef, le_div_iff₀ hy]
    linarith
  have hR0 : 0 ≤ R := by positivity
  have hRR' : R ≤ R' := by
    have e : R' - R = -((q.re - q.im) * (y - 1)) / y := by
      rw [hRdef, hR'def]; field_simp; ring
    have : 0 ≤ R' - R := by rw [e]; exact div_nonneg (by linarith) hy.le
    linarith
  have hR2 : R ^ 2 ≤ 6 * p * s / (p - 2) := by
    have hprod : R * R' = (1 - 2 * aR p) * (y ^ 2 + 1) / (2 * y) + s := by
      have e : R * R' = (2 * q.re * q.im) * (y ^ 2 + 1) / (2 * y ^ 2) + n2 / y := by
        rw [hRdef, hR'def, hn2]; field_simp; ring
      rw [e, h2, hsdef]; field_simp
    have h8 : R ^ 2 ≤ R * R' := by
      rw [pow_two]; exact mul_le_mul_of_nonneg_left hRR' hR0
    have h9 : (1 - 2 * aR p) * (y ^ 2 + 1) / (2 * y) ≤ (1 - 2 * aR p) * s / (2 * aR p) := by
      have e9 : (1 - 2 * aR p) * (y ^ 2 + 1) / (2 * y)
          = (1 - 2 * aR p) * (aR p * (y ^ 2 + 1)) / (2 * aR p * y) := by field_simp
      have e10 : (1 - 2 * aR p) * s / (2 * aR p) = (1 - 2 * aR p) * n2 / (2 * aR p * y) := by
        rw [hsdef]; field_simp
      rw [e9, e10]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hay hAp.le) (by positivity)
    have h10 : (1 - 2 * aR p) * s / (2 * aR p) + s = 6 * p * s / (p - 2) := by
      unfold aR; field_simp; ring
    linarith
  have hτ : 3 / p ≤ Real.tan (Real.pi / p) := by
    have h3 : 3 / p ≤ Real.pi / p := div_le_div_of_nonneg_right Real.pi_gt_three.le hp0.le
    have h4 : Real.pi / p < Real.pi / 2 := by
      apply div_lt_div_of_pos_left Real.pi_pos (by norm_num) hp
    exact h3.trans (Real.le_tan (by positivity) h4)
  have hcore := arc_boundary_core p s R R' (Real.tan (Real.pi / p)) hp hτ hs1 hR0 hRR' hR2
  -- the correction on the boundary
  have hDre := den_re_pos hp htre' ht0
  have hNre := num_re_pos hp htre' ht0
  have hDne := den_ne_zero hp htre' ht0
  have hns : 0 < Complex.normSq (1 + ((p : ℂ) - 1) * q) := Complex.normSq_pos.mpr hDne
  have hφ : φC p t = (t + ((p : ℂ) - 1) * q) / (1 + ((p : ℂ) - 1) * q) := rfl
  set ImN := y + (p - 1) * (y * q.re) + (p - 1) * q.im with hImN
  set ReN := (p - 1) ^ 2 * n2 + (p - 1) * (y * q.im + q.re) with hReN
  have hImNpos : 0 < ImN := by positivity
  have hReNpos : 0 < ReN := by positivity
  have him : (φC p t).im = ImN / Complex.normSq (1 + ((p : ℂ) - 1) * q) := by
    rw [hφ, Complex.div_im, num_re p q t, num_im p q t, den_re p q, den_im p q, htre, htim,
      ← sub_div]
    congr 1
    rw [hImN]; ring
  have hre : (φC p t).re = ReN / Complex.normSq (1 + ((p : ℂ) - 1) * q) := by
    rw [hφ, Complex.div_re, num_re p q t, num_im p q t, den_re p q, den_im p q, htre, htim,
      ← add_div]
    congr 1
    rw [hReN, hn2]; ring
  have hle : ImN ≤ Real.tan (Real.pi / p) * ReN := by
    have e1 : ImN = y * (1 + (p - 1) * R) := by rw [hImN, hRdef]; field_simp; ring
    have e2 : ReN = y * ((p - 1) ^ 2 * s + (p - 1) * R') := by
      rw [hReN, hsdef, hR'def]; field_simp
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left hcore hy.le
    linarith [mul_left_comm y (Real.tan (Real.pi / p)) ((p - 1) ^ 2 * s + (p - 1) * R')]
  constructor
  · rw [Complex.arg_nonneg_iff, him]
    exact div_nonneg hImNpos.le hns.le
  · have hrepos : 0 < (φC p t).re := by rw [hre]; exact div_pos hReNpos hns
    have habs := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hrepos))
    have htan : Real.tan (Complex.arg (φC p t)) ≤ Real.tan (Real.pi / p) := by
      rw [Complex.tan_arg, him, hre, div_div_div_cancel_right₀ hns.ne', div_le_iff₀ hReNpos]
      exact hle
    by_contra hgt
    have hgt' : Real.pi / p < Complex.arg (φC p t) := lt_of_not_ge hgt
    have hπp : -(Real.pi / 2) < Real.pi / p := by
      have : 0 < Real.pi / p := by positivity
      linarith [Real.pi_pos]
    have := Real.tan_lt_tan_of_lt_of_lt_pi_div_two hπp habs.2 hgt'
    linarith

theorem arc_upper {p : ℝ} (hp : 2 < p) {y : ℝ} (hy : 0 < y) :
    |Real.pi / 2 - p * Complex.arg (φC p (Complex.I * y))| ≤ Real.pi / 2 := by
  have hp0 : 0 < p := by linarith
  obtain ⟨h0, h1⟩ := arc_boundary_arg hp hy
  have h2 : p * Complex.arg (φC p (Complex.I * y)) ≤ Real.pi := by
    have := mul_le_mul_of_nonneg_left h1 hp0.le
    rwa [mul_div_cancel₀ _ hp0.ne'] at this
  have h3 : 0 ≤ p * Complex.arg (φC p (Complex.I * y)) := mul_nonneg hp0.le h0
  rw [abs_le]
  constructor <;> linarith

theorem arc_lower {p : ℝ} (hp : 2 < p) {y : ℝ} (hy : 0 < y) :
    |-(Real.pi / 2) - p * Complex.arg (φC p (-Complex.I * y))| ≤ Real.pi / 2 := by
  have hp0 : 0 < p := by linarith
  obtain ⟨h0, h1⟩ := arc_boundary_arg hp hy
  have hre0 : (0 : ℝ) ≤ (Complex.I * (y : ℂ)).re := by simp
  have hne : Complex.I * (y : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hy.ne' this
  have hQ := QC_mem hp hre0 hne
  have hconj : -Complex.I * (y : ℂ) = (starRingEnd ℂ) (Complex.I * y) := by simp
  have hπp : Real.pi / p < Real.pi := by
    rw [div_lt_iff₀ hp0]
    nlinarith [Real.pi_pos]
  have hargne : Complex.arg (φC p (Complex.I * y)) ≠ Real.pi := by linarith
  rw [hconj, φC_conj hQ, Complex.arg_conj, if_neg hargne]
  have h := arc_upper hp hy
  rw [abs_le] at h ⊢
  constructor <;> nlinarith [h.1, h.2]

/-! ## Order of contact, from the real theorem `ArcOrderFive.order_five` -/

open LeanMath.Papers.DecenteredArcGlobal in
theorem QC_ofReal {p : ℝ} (hp : 2 < p) (t : ℝ) : QC p (t : ℂ) = ((rad p t : ℝ) : ℂ) := by
  have hp0 : p ≠ 0 := by linarith
  have hp0' : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
  unfold QC aR rad
  push_cast
  field_simp
  ring

theorem sqrt_eq_exp {r : ℝ} (hr : 0 < r) : Real.sqrt r = Real.exp (Real.log r / 2) := by
  have e : (Real.exp (Real.log r / 2)) ^ 2 = r := by
    rw [← Real.exp_nat_mul]
    have h : ((2 : ℕ) : ℝ) * (Real.log r / 2) = Real.log r := by push_cast; ring
    rw [h, Real.exp_log hr]
  calc Real.sqrt r = Real.sqrt ((Real.exp (Real.log r / 2)) ^ 2) := by rw [e]
    _ = Real.exp (Real.log r / 2) := Real.sqrt_sq (Real.exp_pos _).le

open LeanMath.Papers.DecenteredArcGlobal in
theorem qC_ofReal {p : ℝ} (hp : 2 < p) {t : ℝ} (ht : 0 < t) :
    qC p (t : ℂ) = ((support p t : ℝ) : ℂ) := by
  have hr := rad_positive p t hp ht
  unfold qC support
  rw [QC_ofReal hp, sqrt_eq_exp hr, Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_log hr.le]
  simp

open LeanMath.Papers.DecenteredArcGlobal in
theorem correction_pos {p : ℝ} (hp : 2 < p) {t : ℝ} (ht : 0 < t) : 0 < correction p t := by
  have hs : 0 < support p t := Real.sqrt_pos.mpr (rad_positive p t hp ht)
  have h1 := mul_pos (by linarith : (0 : ℝ) < p - 1) hs
  unfold correction
  exact div_pos (by linarith) (by linarith)

open LeanMath.Papers.DecenteredArcGlobal in
theorem φC_ofReal {p : ℝ} (hp : 2 < p) {t : ℝ} (ht : 0 < t) :
    φC p (t : ℂ) = ((correction p t : ℝ) : ℂ) := by
  unfold φC corr correction
  rw [qC_ofReal hp ht]
  push_cast
  rfl

open LeanMath.Papers.DecenteredArcGlobal in
theorem Tmap_ofReal {p : ℝ} (hp : 2 < p) {t : ℝ} (ht : 0 < t) :
    Tmap p (φC p) (t : ℂ)
      = ((t * Real.exp (-(p * Real.log (correction p t))) : ℝ) : ℂ) := by
  have hc := correction_pos hp ht
  unfold Tmap
  rw [φC_ofReal hp ht, ← Complex.ofReal_log hc.le]
  push_cast
  rfl

open LeanMath.Papers.DecenteredArcGlobal in
/-- Real form of the order-five contact of the residual map at `t = 1`. -/
theorem real_residual_bound (p : ℝ) (hp : 2 < p) :
    ∃ C ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ ∀ x : ℝ, |x| < ρ →
      |(1 + x) * Real.exp (-(p * Real.log (correction p (1 + x)))) - 1| ≤ C * |x| ^ 5 := by
  have hp0 : 0 < p := by linarith
  set c := (p - 2) * (p ^ 2 - 1) * (3 * p + 1) / 1440 with hc
  obtain ⟨δ, hδ, hδf⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp (ArcOrderFive.order_five p hp)) 1 one_pos
  set K := p * (|c| + 1) with hK
  have hKpos : 0 < K := by positivity
  refine ⟨2 * K, min (min (1 / 2) δ) (1 / K), by positivity, (min_le_left _ _).trans (min_le_left _ _), ?_⟩
  intro x hx
  have hx2 : |x| < 1 / 2 := lt_of_lt_of_le hx ((min_le_left _ _).trans (min_le_left _ _))
  have hxδ : |x| < δ := lt_of_lt_of_le hx ((min_le_left _ _).trans (min_le_right _ _))
  have hxK : |x| < 1 / K := lt_of_lt_of_le hx (min_le_right _ _)
  have hxb := abs_lt.mp hx2
  have htpos : 0 < 1 + x := by linarith
  by_cases hx0 : x = 0
  · subst hx0
    have h1 : correction p (1 + 0) = 1 := by
      rw [add_zero]
      have hs : 0 < support p 1 := Real.sqrt_pos.mpr (rad_positive p 1 hp one_pos)
      have h2 := mul_pos (by linarith : (0 : ℝ) < p - 1) hs
      unfold correction
      exact div_self (by linarith)
    rw [h1]
    simp
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
    have heabs : |e| ≤ |x| := by
      rw [he, abs_div, abs_neg, abs_of_pos hp0, div_le_iff₀ hp0]
      nlinarith [abs_nonneg x]
    have hdist := hδf (x := e) he0 (by
      rw [Real.dist_eq, sub_zero]; exact lt_of_le_of_lt heabs hxδ)
    rw [hept, Real.dist_eq] at hdist
    have h5 : 0 < |e| ^ 5 := pow_pos (abs_pos.mpr he0) 5
    have hE : |e + Real.log (correction p (1 + x))| ≤ (|c| + 1) * |e| ^ 5 := by
      have h6 := abs_sub_abs_le_abs_sub ((e + Real.log (correction p (1 + x))) / e ^ 5) c
      have h7 : |(e + Real.log (correction p (1 + x))) / e ^ 5| < |c| + 1 := by linarith
      rw [abs_div, abs_pow, div_lt_iff₀ h5] at h7
      exact h7.le
    set L := Real.log (1 + x) - p * Real.log (correction p (1 + x)) with hL
    have hLe : L = -p * (e + Real.log (correction p (1 + x))) := by
      rw [hL, he]; field_simp; ring
    have hpow : |e| ^ 5 ≤ |x| ^ 5 := pow_le_pow_left₀ (abs_nonneg e) heabs 5
    have hLabs : |L| ≤ K * |x| ^ 5 := by
      rw [hLe, abs_mul, abs_neg, abs_of_pos hp0, hK]
      have h8 := mul_le_mul_of_nonneg_left hE hp0.le
      have h9 : p * ((|c| + 1) * |e| ^ 5) ≤ p * ((|c| + 1) * |x| ^ 5) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) hp0.le
      linarith [mul_assoc p (|c| + 1) (|x| ^ 5)]
    have hx1 : |x| ^ 5 ≤ |x| := by
      have h0 := abs_nonneg x
      have h1 : |x| ≤ 1 := by linarith
      calc |x| ^ 5 = |x| * |x| ^ 4 := by ring
        _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1) h0
        _ = |x| := mul_one _
    have hKx : K * |x| ≤ 1 := by
      rw [lt_div_iff₀ hKpos] at hxK
      linarith [mul_comm K |x|]
    have hL1 : |L| ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hx1 hKpos.le
      linarith
    have hexp : (1 + x) * Real.exp (-(p * Real.log (correction p (1 + x)))) = Real.exp L := by
      rw [hL, sub_eq_add_neg, Real.exp_add, Real.exp_log htpos]
    rw [hexp]
    have h10 := Real.abs_exp_sub_one_le hL1
    linarith [mul_assoc (2 : ℝ) K (|x| ^ 5)]

theorem Tmap_differentiableAt {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 < t.re) :
    DifferentiableAt ℂ (Tmap p (φC p)) t := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at ht
    exact lt_irrefl _ ht
  have h1 := (φC_differentiableAt hp ht.le ht0).clog (φC_mem hp ht.le ht0)
  exact differentiableAt_id.mul ((h1.const_mul (p : ℂ)).neg.cexp)

/-- The residual map of the decentered arc has contact of order five at `1`, in `ℂ`. -/
theorem arc_order {p : ℝ} (hp : 2 < p) :
    (fun t => Tmap p (φC p) t - 1) =O[𝓝 1] fun t => (t - 1) ^ 5 := by
  set f : ℂ → ℂ := fun z => Tmap p (φC p) (1 + z) - 1 with hf
  have hd : DifferentiableOn ℂ f (ball 0 1) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := by simpa using hz
    have hre : 0 < (1 + z).re := by
      have h := Complex.abs_re_le_norm z
      have h2 := (abs_le.mp h).1
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have h1 : DifferentiableAt ℂ (fun z : ℂ => 1 + z) z :=
      (differentiableAt_const _).add differentiableAt_id
    exact (((Tmap_differentiableAt hp hre).comp z h1).sub_const 1).differentiableWithinAt
  have hana : AnalyticAt ℂ f 0 := hd.analyticAt (ball_mem_nhds 0 one_pos)
  obtain ⟨C, ρ, hρ, hρ2, hbound⟩ := real_residual_bound p hp
  have hreal : ∀ᶠ x : ℝ in 𝓝 0, ‖f (x : ℂ)‖ ≤ C * |x| ^ 5 := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨ρ, hρ, fun x hx => ?_⟩
    have hx' : |x| < ρ := by simpa [Real.dist_eq] using hx
    have hpos : 0 < 1 + x := by
      have := (abs_lt.mp (lt_of_lt_of_le hx' hρ2)).1
      linarith
    have e : (1 : ℂ) + (x : ℂ) = ((1 + x : ℝ) : ℂ) := by push_cast; rfl
    simp only [hf]
    rw [e, Tmap_ofReal hp hpos, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact hbound x hx'
  have hfO := bigO_of_real_bound hana 5 C hreal
  have htend : Tendsto (fun t : ℂ => t - 1) (𝓝 1) (𝓝 0) := by
    have hc : Continuous fun t : ℂ => t - 1 := continuous_id.sub continuous_const
    have h := hc.tendsto 1
    simpa using h
  have h := hfO.comp_tendsto htend
  refine h.congr (fun t => ?_) (fun t => rfl)
  simp [hf, Function.comp]

/-- **Half-plane theorem for the decentered arc.** For every real `p > 2` and every `t` with
`Re t > 0`, the residual map contracts the Cayley coordinate with exponent five. -/
theorem arc_halfplane_contraction (p : ℝ) (hp : 2 < p) (t : ℂ) (ht : 0 < t.re) :
    ‖(Tmap p (φC p) t - 1) / (Tmap p (φC p) t + 1)‖ ≤ ‖(t - 1) / (t + 1)‖ ^ 5 :=
  halfplane_contraction p 5 (φC p)
    (fun _ h h0 => φC_differentiableAt hp h h0) (fun _ h h0 => φC_mem hp h h0)
    (fun _ hy => arc_upper hp hy) (fun _ hy => arc_lower hp hy) (arc_order hp) t ht

/-- The residual map sends the open right half-plane into itself. -/
theorem arc_halfplane_invariant (p : ℝ) (hp : 2 < p) (t : ℂ) (ht : 0 < t.re) :
    0 < (Tmap p (φC p) t).re := by
  have h := arc_halfplane_contraction p hp t ht
  have h1 : ‖(t - 1) / (t + 1)‖ < 1 := cayley_norm_lt_one t ht
  have h2 : ‖(t - 1) / (t + 1)‖ ^ 5 < 1 := pow_lt_one₀ (norm_nonneg _) h1 (by norm_num)
  set w := Tmap p (φC p) t with hw
  have h3 : ‖(w - 1) / (w + 1)‖ < 1 := lt_of_le_of_lt h h2
  have hnn : 0 ≤ w.re :=
    (halfplane_core p (φC p) (fun _ h h0 => φC_differentiableAt hp h h0)
      (fun _ h h0 => φC_mem hp h h0) (fun _ hy => arc_upper hp hy)
      (fun _ hy => arc_lower hp hy)).2 t ht
  have hw1 : w + 1 ≠ 0 := by
    intro h0
    have h4 := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h4
    linarith
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hw1)] at h3
  by_contra hneg
  have hneg' : w.re ≤ 0 := le_of_not_gt hneg
  have h4 : ‖w + 1‖ ^ 2 ≤ ‖w - 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp
    nlinarith
  have h5 := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h4
  linarith

end LeanMath.Papers.ArcHalfPlane
