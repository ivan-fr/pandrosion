import LeanMath.Papers.ComplexRoots
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # The half-plane theorem: complex-analytic chain

General part of the proof of the half-plane theorem of *Complex Geometric Root Calculators*.

* `schwarz_bigO`: Schwarz lemma of order `m`, with the order stated as `F = O(z ^ m)`;
* `schwarz_halfplane`: the same on the right half-plane, in the Cayley coordinate;
* `strip_im_le`: a Phragmén–Lindelöf bound for the imaginary part on a horizontal strip;
* `bigO_of_real_bound`: an analytic function that is `O(|x| ^ m)` on the real axis is `O(z ^ m)`;
* `halfplane_contraction`: the abstract half-plane theorem for a correction `φ`.
-/

noncomputable section
namespace LeanMath.Papers.ComplexHalfPlane

open Metric Filter Topology Asymptotics Set
open LeanMath.Papers.ComplexRoots

/-! ## Schwarz lemma of order `m` from a bound at the origin -/

theorem schwarz_bigO (m : ℕ) (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball 0 1))
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖F z‖ ≤ 1) (hO : F =O[𝓝 0] fun z => z ^ m) :
    ∀ z ∈ ball (0 : ℂ) 1, ‖F z‖ ≤ ‖z‖ ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · intro z hz; simpa using hb z hz
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨δ, hδ, hδC⟩ := Metric.eventually_nhds_iff.mp hC
  have hF0 : F 0 = 0 := by
    have h := hδC (y := 0) (by simpa using hδ)
    rw [zero_pow hm.ne', norm_zero, mul_zero] at h
    exact norm_le_zero_iff.mp h
  set g₀ : ℂ → ℂ := fun z => F z / z ^ m with hg₀
  have hd : DifferentiableOn ℂ g₀ (ball 0 1 \ {0}) := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz.2
    exact ((hF z hz.1).mono diff_subset).div (differentiableWithinAt_id.pow m) (pow_ne_zero m hz0)
  have hbd : BddAbove (norm ∘ g₀ '' (ball 0 1 \ {0})) := by
    refine ⟨max C (1 / δ ^ m), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz0 : z ≠ 0 := by simpa using hz.2
    have hzpos : 0 < ‖z‖ ^ m := pow_pos (norm_pos_iff.mpr hz0) m
    simp only [Function.comp_apply, hg₀, norm_div, norm_pow]
    by_cases hzδ : ‖z‖ < δ
    · have h1 := hδC (y := z) (by simpa using hzδ)
      rw [norm_pow] at h1
      exact le_max_of_le_left ((div_le_iff₀ hzpos).mpr h1)
    · have hzδ' : δ ≤ ‖z‖ := le_of_not_gt hzδ
      have h2 : ‖F z‖ ≤ 1 := hb z hz.1
      have h3 : δ ^ m ≤ ‖z‖ ^ m := pow_le_pow_left₀ hδ.le hzδ' m
      refine le_max_of_le_right ?_
      calc ‖F z‖ / ‖z‖ ^ m ≤ 1 / ‖z‖ ^ m := div_le_div_of_nonneg_right h2 hzpos.le
        _ ≤ 1 / δ ^ m := one_div_le_one_div_of_le (pow_pos hδ m) h3
  have hG := Complex.differentiableOn_update_limUnder_of_bddAbove
    (ball_mem_nhds (0 : ℂ) one_pos) hd hbd
  refine schwarz_order m F _ hG ?_ hb
  intro z hz
  by_cases hz0 : z = 0
  · subst hz0; simp [hF0, zero_pow hm.ne']
  · rw [Function.update_of_ne hz0]
    simp only [hg₀]
    field_simp

/-! ## The right half-plane -/

theorem one_sub_ne_zero {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 1 - ζ ≠ 0 := by
  intro h
  have h1 : ζ = 1 := (sub_eq_zero.mp h).symm
  rw [h1, norm_one] at hζ
  exact lt_irrefl _ hζ

theorem cayley_norm_le_one (w : ℂ) (hw : 0 ≤ w.re) : ‖(w - 1) / (w + 1)‖ ≤ 1 := by
  have h1 : w + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [norm_div, div_le_one (norm_pos_iff.mpr h1)]
  have h2 : ‖w - 1‖ ^ 2 ≤ ‖w + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

theorem cayley_inv_re (ζ : ℂ) (hζ : ‖ζ‖ < 1) : 0 < ((1 + ζ) / (1 - ζ)).re := by
  have hns : 0 < Complex.normSq (1 - ζ) := Complex.normSq_pos.mpr (one_sub_ne_zero hζ)
  have h2 : ζ.re * ζ.re + ζ.im * ζ.im < 1 := by
    have h := Complex.sq_norm ζ
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg ζ]
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im, zero_add, zero_sub]
  have e : (1 + ζ.re) * (1 - ζ.re) / Complex.normSq (1 - ζ) + ζ.im * -ζ.im / Complex.normSq (1 - ζ)
      = (1 - (ζ.re * ζ.re + ζ.im * ζ.im)) / Complex.normSq (1 - ζ) := by ring
  rw [e]
  exact div_pos (by linarith) hns

/-- Schwarz lemma of order `m` on the right half-plane, in the coordinate `η = (t - 1) / (t + 1)`. -/
theorem schwarz_halfplane (m : ℕ) (T : ℂ → ℂ) (hT : DifferentiableOn ℂ T {t : ℂ | 0 < t.re})
    (hre : ∀ t : ℂ, 0 < t.re → 0 ≤ (T t).re)
    (hO : (fun t => T t - 1) =O[𝓝 1] fun t => (t - 1) ^ m) :
    ∀ t : ℂ, 0 < t.re → ‖(T t - 1) / (T t + 1)‖ ≤ ‖(t - 1) / (t + 1)‖ ^ m := by
  set cinv : ℂ → ℂ := fun ζ => (1 + ζ) / (1 - ζ) with hcinv
  set F : ℂ → ℂ := fun ζ => (T (cinv ζ) - 1) / (T (cinv ζ) + 1) with hFdef
  have hHopen : IsOpen {t : ℂ | 0 < t.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : ∀ ζ ∈ ball (0 : ℂ) 1, ‖ζ‖ < 1 := fun ζ hζ => by simpa using hζ
  have hcre : ∀ ζ ∈ ball (0 : ℂ) 1, 0 < (cinv ζ).re := fun ζ hζ => cayley_inv_re ζ (hmem ζ hζ)
  have hden : ∀ ζ ∈ ball (0 : ℂ) 1, T (cinv ζ) + 1 ≠ 0 := by
    intro ζ hζ h
    have h1 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h1
    linarith [hre _ (hcre ζ hζ)]
  have hFd : DifferentiableOn ℂ F (ball 0 1) := by
    intro ζ hζ
    have hc : DifferentiableAt ℂ cinv ζ :=
      (differentiableAt_const _ |>.add differentiableAt_id).div
        (differentiableAt_const _ |>.sub differentiableAt_id) (one_sub_ne_zero (hmem ζ hζ))
    have hTa : DifferentiableAt ℂ T (cinv ζ) :=
      (hT _ (hcre ζ hζ)).differentiableAt (hHopen.mem_nhds (hcre ζ hζ))
    have hcomp : DifferentiableAt ℂ (fun ζ => T (cinv ζ)) ζ := hTa.comp ζ hc
    exact ((hcomp.sub_const 1).div (hcomp.add_const 1) (hden ζ hζ)).differentiableWithinAt
  have hFb : ∀ ζ ∈ ball (0 : ℂ) 1, ‖F ζ‖ ≤ 1 :=
    fun ζ hζ => cayley_norm_le_one _ (hre _ (hcre ζ hζ))
  have hFO : F =O[𝓝 0] fun ζ => ζ ^ m := by
    have htend : Tendsto cinv (𝓝 0) (𝓝 1) := by
      have hc : ContinuousAt cinv 0 :=
        (continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id)
          (by simp)
      have h := hc.tendsto
      simpa [hcinv] using h
    have h1 : (fun ζ => T (cinv ζ) - 1) =O[𝓝 0] fun ζ => (cinv ζ - 1) ^ m :=
      hO.comp_tendsto htend
    have h2 : (fun ζ => (cinv ζ - 1) ^ m) =O[𝓝 0] fun ζ => ζ ^ m := by
      apply IsBigO.of_bound (4 ^ m)
      filter_upwards [ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with ζ hζ
      have hζn : ‖ζ‖ < 1 / 2 := by simpa using hζ
      have hne : 1 - ζ ≠ 0 := one_sub_ne_zero (by linarith)
      have e : cinv ζ - 1 = 2 * ζ / (1 - ζ) := by
        simp only [hcinv]; field_simp; ring
      have hlow : (1 / 2 : ℝ) ≤ ‖1 - ζ‖ := by
        have h := norm_sub_norm_le (1 : ℂ) ζ
        rw [norm_one] at h
        linarith
      have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [norm_pow, norm_pow, e, norm_div, norm_mul, h2n, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg ζ]
    have h3 : F =O[𝓝 0] fun ζ => T (cinv ζ) - 1 := by
      apply IsBigO.of_bound 1
      filter_upwards [ball_mem_nhds (0 : ℂ) one_pos] with ζ hζ
      rw [one_mul]
      simp only [hFdef, norm_div]
      apply div_le_self (norm_nonneg _)
      have hre1 : 1 ≤ (T (cinv ζ) + 1).re := by
        simp only [Complex.add_re, Complex.one_re]
        linarith [hre _ (hcre ζ hζ)]
      exact hre1.trans (Complex.re_le_norm _)
    exact h3.trans (h1.trans h2)
  intro t ht
  have ht1 : t + 1 ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at h1
    linarith
  have hη : (t - 1) / (t + 1) ∈ ball (0 : ℂ) 1 := by
    simpa using cayley_norm_lt_one t ht
  have e1 : 1 + (t - 1) / (t + 1) = 2 * t / (t + 1) := by field_simp; ring
  have e2 : 1 - (t - 1) / (t + 1) = 2 / (t + 1) := by field_simp; ring
  have hback : cinv ((t - 1) / (t + 1)) = t := by
    simp only [hcinv]; rw [e1, e2]; field_simp
  have h := schwarz_bigO m F hFd hFb hFO _ hη
  simp only [hFdef, hback] at h
  exact h

/-! ## A Phragmén–Lindelöf bound on a strip -/

theorem strip_im_le {Λ : ℂ → ℂ} {b B C : ℝ} (hb : 0 < b)
    (hd : DiffContOnCl ℂ Λ (Complex.im ⁻¹' Ioo (-b) b))
    (hB : ∀ x : ℂ, x.im ∈ Ioo (-b) b → (Λ x).im ≤ B)
    (h1 : ∀ x : ℂ, x.im = -b → (Λ x).im ≤ C) (h2 : ∀ x : ℂ, x.im = b → (Λ x).im ≤ C)
    (x : ℂ) (hx1 : -b ≤ x.im) (hx2 : x.im ≤ b) : (Λ x).im ≤ C := by
  set f : ℂ → ℂ := fun z => Complex.exp (-Complex.I * Λ z) with hf
  have hnorm : ∀ z, ‖f z‖ = Real.exp ((Λ z).im) := by
    intro z
    simp only [hf, Complex.norm_exp]
    congr 1
    simp
  have hfd : DiffContOnCl ℂ f (Complex.im ⁻¹' Ioo (-b) b) := by
    have hg : Differentiable ℂ fun w : ℂ => Complex.exp (-Complex.I * w) := by fun_prop
    exact hg.comp_diffContOnCl hd
  have key := PhragmenLindelof.horizontal_strip (C := Real.exp C) hfd ?_ ?_ ?_ hx1 hx2
  · rw [hnorm] at key
    exact Real.exp_le_exp.mp key
  · refine ⟨0, div_pos Real.pi_pos (by linarith), B, ?_⟩
    apply IsBigO.of_bound 1
    rw [eventually_inf_principal]
    filter_upwards with z hz
    rw [hnorm, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    simp only [zero_mul, Real.exp_zero, mul_one]
    exact Real.exp_le_exp.mpr (hB z hz)
  · intro z hz; rw [hnorm]; exact Real.exp_le_exp.mpr (h1 z hz)
  · intro z hz; rw [hnorm]; exact Real.exp_le_exp.mpr (h2 z hz)

/-! ## From a real bound to a complex order -/

theorem bigO_of_real_bound {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (m : ℕ) (C : ℝ)
    (hreal : ∀ᶠ x : ℝ in 𝓝 0, ‖f (x : ℂ)‖ ≤ C * |x| ^ m) : f =O[𝓝 0] fun z => z ^ m := by
  by_cases hz : ∀ᶠ z in 𝓝 (0 : ℂ), f z = 0
  · apply IsBigO.of_bound 0
    filter_upwards [hz] with z hz
    rw [hz, norm_zero, zero_mul]
  · obtain ⟨n, g, hg, hg0, hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz
    simp only [sub_zero, smul_eq_mul] at hfg
    have hofReal : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 0) (𝓝 0) := by
      have h := Complex.continuous_ofReal.tendsto 0
      simpa using h
    by_cases hnm : m ≤ n
    · have hgc : ∀ᶠ z in 𝓝 (0 : ℂ), ‖g z‖ < ‖g 0‖ + 1 :=
        hg.continuousAt.norm.tendsto.eventually (gt_mem_nhds (by linarith))
      apply IsBigO.of_bound (‖g 0‖ + 1)
      filter_upwards [hfg, hgc, ball_mem_nhds (0 : ℂ) one_pos] with z h1 h2 h3
      have hz1 : ‖z‖ ≤ 1 := by
        have h : ‖z‖ < 1 := by simpa using h3
        exact h.le
      rw [h1, norm_mul, norm_pow, norm_pow]
      have h4 : ‖z‖ ^ n ≤ ‖z‖ ^ m := pow_le_pow_of_le_one (norm_nonneg _) hz1 hnm
      calc ‖z‖ ^ n * ‖g z‖ ≤ ‖z‖ ^ m * (‖g 0‖ + 1) :=
            mul_le_mul h4 h2.le (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
        _ = (‖g 0‖ + 1) * ‖z‖ ^ m := by ring
    · have hnm' : n < m := lt_of_not_ge hnm
      exfalso
      have hcont : Tendsto (fun x : ℝ => ‖g (x : ℂ)‖) (𝓝[≠] 0) (𝓝 ‖g 0‖) :=
        (hg.continuousAt.norm.tendsto.comp hofReal).mono_left nhdsWithin_le_nhds
      have hfg' : ∀ᶠ x : ℝ in 𝓝 0, f (x : ℂ) = (x : ℂ) ^ n * g x := hofReal.eventually hfg
      have hbound : ∀ᶠ x : ℝ in 𝓝[≠] 0, ‖g (x : ℂ)‖ ≤ C * |x| ^ (m - n) := by
        filter_upwards [nhdsWithin_le_nhds hfg', nhdsWithin_le_nhds hreal,
          self_mem_nhdsWithin] with x h2 h3 hx
        have hx0 : x ≠ 0 := hx
        have hxpos : 0 < |x| ^ n := pow_pos (abs_pos.mpr hx0) n
        rw [h2, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] at h3
        have e : |x| ^ m = |x| ^ (m - n) * |x| ^ n := by
          rw [← pow_add, Nat.sub_add_cancel hnm'.le]
        rw [e] at h3
        have h5 : ‖g (x : ℂ)‖ * |x| ^ n ≤ C * |x| ^ (m - n) * |x| ^ n := by
          linarith [mul_comm (|x| ^ n) ‖g (x : ℂ)‖, mul_assoc C (|x| ^ (m - n)) (|x| ^ n)]
        exact le_of_mul_le_mul_right h5 hxpos
      have hlim0 : Tendsto (fun x : ℝ => C * |x| ^ (m - n)) (𝓝[≠] 0) (𝓝 0) := by
        have hc : Continuous fun x : ℝ => C * |x| ^ (m - n) := by fun_prop
        have h := hc.tendsto 0
        simp only [abs_zero] at h
        rw [zero_pow (Nat.sub_ne_zero_of_lt hnm'), mul_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      have h6 : ‖g 0‖ ≤ 0 := le_of_tendsto_of_tendsto hcont hlim0 hbound
      exact hg0 (norm_le_zero_iff.mp h6)

/-! ## The abstract half-plane theorem -/

/-- The residual map `t ↦ t * exp (-p * log (φ t))` of a correction `φ`, for a real degree `p`. -/
def Tmap (p : ℝ) (φ : ℂ → ℂ) (t : ℂ) : ℂ := t * Complex.exp (-(p * Complex.log (φ t)))

/-- Invariance of the closed right half-plane under the residual map, from the boundary values:
the map is holomorphic on the open half-plane and its real part is nonnegative there. -/
theorem halfplane_core (p : ℝ) (φ : ℂ → ℂ)
    (hφd : ∀ t : ℂ, 0 ≤ t.re → t ≠ 0 → DifferentiableAt ℂ φ t)
    (hφs : ∀ t : ℂ, 0 ≤ t.re → t ≠ 0 → φ t ∈ Complex.slitPlane)
    (hup : ∀ y : ℝ, 0 < y →
      |Real.pi / 2 - p * Complex.arg (φ (Complex.I * y))| ≤ Real.pi / 2)
    (hlo : ∀ y : ℝ, 0 < y →
      |-(Real.pi / 2) - p * Complex.arg (φ (-Complex.I * y))| ≤ Real.pi / 2) :
    DifferentiableOn ℂ (Tmap p φ) {t : ℂ | 0 < t.re} ∧
      ∀ t : ℂ, 0 < t.re → 0 ≤ (Tmap p φ t).re := by
  have hπ := Real.pi_pos
  set Λ : ℂ → ℂ := fun x => x - p * Complex.log (φ (Complex.exp x)) with hΛ
  have hexp_re : ∀ x : ℂ, x.im ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) → 0 ≤ (Complex.exp x).re := by
    intro x hx
    rw [Complex.exp_re]
    exact mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_mem_Icc hx)
  have hdiffAt : ∀ x : ℂ, x.im ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) → DifferentiableAt ℂ Λ x := by
    intro x hx
    have h1 : DifferentiableAt ℂ (fun x => φ (Complex.exp x)) x :=
      (hφd _ (hexp_re x hx) (Complex.exp_ne_zero x)).comp x Complex.differentiableAt_exp
    exact differentiableAt_id.sub
      ((h1.clog (hφs _ (hexp_re x hx) (Complex.exp_ne_zero x))).const_mul _)
  have hcl : closure (Complex.im ⁻¹' Ioo (-(Real.pi / 2)) (Real.pi / 2))
      ⊆ Complex.im ⁻¹' Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self)
      (isClosed_Icc.preimage Complex.continuous_im)
  have hd : DiffContOnCl ℂ Λ (Complex.im ⁻¹' Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    DifferentiableOn.diffContOnCl fun x hx => (hdiffAt x (hcl hx)).differentiableWithinAt
  have him : ∀ x : ℂ, (Λ x).im = x.im - p * Complex.arg (φ (Complex.exp x)) := by
    intro x
    simp [hΛ, Complex.log_im]
  have hbdd : ∀ x : ℂ, x.im ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) →
      |(Λ x).im| ≤ Real.pi / 2 + |p| * Real.pi := by
    intro x hx
    rw [him]
    have h1 : |x.im| ≤ Real.pi / 2 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
    have h2 : |p * Complex.arg (φ (Complex.exp x))| ≤ |p| * Real.pi := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi _) (abs_nonneg _)
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hexpI : ∀ x : ℂ, x.im = Real.pi / 2 →
      Complex.exp x = Complex.I * ((Real.exp x.re : ℝ) : ℂ) := by
    intro x hx
    apply Complex.ext
    · simp [Complex.exp_re, hx]
    · simp [Complex.exp_im, hx, Complex.exp_ofReal_re]
  have hexpI' : ∀ x : ℂ, x.im = -(Real.pi / 2) →
      Complex.exp x = -Complex.I * ((Real.exp x.re : ℝ) : ℂ) := by
    intro x hx
    apply Complex.ext
    · simp [Complex.exp_re, hx]
    · simp [Complex.exp_im, hx, Complex.exp_ofReal_re]
  have hupper : ∀ x : ℂ, x.im = Real.pi / 2 → |(Λ x).im| ≤ Real.pi / 2 := by
    intro x hx
    rw [him, hexpI x hx, hx]
    exact hup _ (Real.exp_pos _)
  have hlower : ∀ x : ℂ, x.im = -(Real.pi / 2) → |(Λ x).im| ≤ Real.pi / 2 := by
    intro x hx
    rw [him, hexpI' x hx, hx]
    exact hlo _ (Real.exp_pos _)
  have hπ2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hle : ∀ x : ℂ, x.im ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) → (Λ x).im ≤ Real.pi / 2 :=
    fun x hx => strip_im_le hπ2 hd (fun z hz => (le_abs_self _).trans (hbdd z hz))
      (fun z hz => (le_abs_self _).trans (hlower z hz))
      (fun z hz => (le_abs_self _).trans (hupper z hz)) x hx.1 hx.2
  have hge : ∀ x : ℂ, x.im ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) → -(Real.pi / 2) ≤ (Λ x).im := by
    intro x hx
    have hneg : Differentiable ℂ fun w : ℂ => -w := differentiable_neg
    have hd' : DiffContOnCl ℂ (fun z => -Λ z) (Complex.im ⁻¹' Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
      hneg.comp_diffContOnCl hd
    have h := strip_im_le (B := Real.pi / 2 + |p| * Real.pi) (C := Real.pi / 2) hπ2 hd'
      (fun z hz => by rw [Complex.neg_im]; exact (neg_le_abs _).trans (hbdd z hz))
      (fun z hz => by rw [Complex.neg_im]; exact (neg_le_abs _).trans (hlower z hz))
      (fun z hz => by rw [Complex.neg_im]; exact (neg_le_abs _).trans (hupper z hz)) x hx.1 hx.2
    rw [Complex.neg_im] at h
    linarith
  have hne0 : ∀ t : ℂ, 0 < t.re → t ≠ 0 := by
    intro t ht h
    rw [h, Complex.zero_re] at ht
    exact lt_irrefl _ ht
  have hTexp : ∀ t : ℂ, 0 < t.re → Tmap p φ t = Complex.exp (Λ (Complex.log t)) := by
    intro t ht
    simp only [Tmap, hΛ, Complex.exp_log (hne0 t ht)]
    rw [sub_eq_add_neg, Complex.exp_add, Complex.exp_log (hne0 t ht)]
  have hre : ∀ t : ℂ, 0 < t.re → 0 ≤ (Tmap p φ t).re := by
    intro t ht
    have harg : (Complex.log t).im ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [Complex.log_im]
      have h := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ht))
      exact ⟨h.1.le, h.2.le⟩
    rw [hTexp t ht, Complex.exp_re]
    exact mul_nonneg (Real.exp_pos _).le
      (Real.cos_nonneg_of_mem_Icc ⟨hge _ harg, hle _ harg⟩)
  have hTd : DifferentiableOn ℂ (Tmap p φ) {t : ℂ | 0 < t.re} := by
    intro t ht
    have ht' : (0 : ℝ) < t.re := ht
    have h1 := (hφd t ht'.le (hne0 t ht')).clog (hφs t ht'.le (hne0 t ht'))
    exact (differentiableAt_id.mul ((h1.const_mul (p : ℂ)).neg.cexp)).differentiableWithinAt
  exact ⟨hTd, hre⟩

/-- **Half-plane theorem, abstract form.** If the correction `φ` is holomorphic with values off the
negative axis on the closed right half-plane (origin removed), if on the two boundary rays the
imaginary part of `Λ = x - p log φ` stays in `[-π/2, π/2]`, and if the residual map has contact of
order `m` at `1`, then the residual map contracts the Cayley coordinate with exponent `m`. -/
theorem halfplane_contraction (p : ℝ) (m : ℕ) (φ : ℂ → ℂ)
    (hφd : ∀ t : ℂ, 0 ≤ t.re → t ≠ 0 → DifferentiableAt ℂ φ t)
    (hφs : ∀ t : ℂ, 0 ≤ t.re → t ≠ 0 → φ t ∈ Complex.slitPlane)
    (hup : ∀ y : ℝ, 0 < y →
      |Real.pi / 2 - p * Complex.arg (φ (Complex.I * y))| ≤ Real.pi / 2)
    (hlo : ∀ y : ℝ, 0 < y →
      |-(Real.pi / 2) - p * Complex.arg (φ (-Complex.I * y))| ≤ Real.pi / 2)
    (hO : (fun t => Tmap p φ t - 1) =O[𝓝 1] fun t => (t - 1) ^ m) :
    ∀ t : ℂ, 0 < t.re →
      ‖(Tmap p φ t - 1) / (Tmap p φ t + 1)‖ ≤ ‖(t - 1) / (t + 1)‖ ^ m :=
  have h := halfplane_core p φ hφd hφs hup hlo
  schwarz_halfplane m (Tmap p φ) h.1 h.2 hO

end LeanMath.Papers.ComplexHalfPlane
