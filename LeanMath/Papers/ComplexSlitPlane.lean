import LeanMath.Papers.ComplexHalfPlane

/-! # A half-plane theorem from the boundary of a quadrant

`ComplexHalfPlane.halfplane_contraction` asks the correction to be holomorphic across the boundary
of the half-plane. For a correction with branch points on the imaginary axis this fails. Here the
correction is only assumed holomorphic on the open right half-plane, continuous on the closed first
quadrant (origin removed), symmetric under conjugation and positive on the positive axis. The
Phragmén–Lindelöf argument is carried out on the quadrant, that is on the strip `0 < Im x < π / 2`
of the logarithmic chart, and the lower quadrant follows by conjugation.

In the application the variable is `z = sqrt t`, so the right half-plane in `z` is the slit plane
`ℂ ∖ (-∞, 0]` in the residual `t`. -/

noncomputable section
namespace LeanMath.Papers.ComplexSlitPlane

open Metric Filter Topology Asymptotics Set
open LeanMath.Papers.ComplexRoots LeanMath.Papers.ComplexHalfPlane

/-- Phragmén–Lindelöf bound on a strip `a < Im x < b`. -/
theorem strip_im_le_gen {Λ : ℂ → ℂ} {a b B C : ℝ} (hab : a < b)
    (hd : DiffContOnCl ℂ Λ (Complex.im ⁻¹' Ioo a b))
    (hB : ∀ x : ℂ, x.im ∈ Ioo a b → (Λ x).im ≤ B)
    (h1 : ∀ x : ℂ, x.im = a → (Λ x).im ≤ C) (h2 : ∀ x : ℂ, x.im = b → (Λ x).im ≤ C)
    (x : ℂ) (hx1 : a ≤ x.im) (hx2 : x.im ≤ b) : (Λ x).im ≤ C := by
  set f : ℂ → ℂ := fun z => Complex.exp (-Complex.I * Λ z) with hf
  have hnorm : ∀ z, ‖f z‖ = Real.exp ((Λ z).im) := by
    intro z
    simp only [hf, Complex.norm_exp]
    congr 1
    simp
  have hfd : DiffContOnCl ℂ f (Complex.im ⁻¹' Ioo a b) := by
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

/-- The closed first quadrant. -/
def Qc : Set ℂ := {w : ℂ | 0 ≤ w.re ∧ 0 ≤ w.im}

/-- Invariance of the closed right half-plane, on the open first quadrant, from the values of the
correction on the two boundary rays of the quadrant. -/
theorem quadrant_core (p : ℝ) (φ : ℂ → ℂ)
    (hφd : ∀ z : ℂ, 0 < z.re → 0 < z.im → DifferentiableAt ℂ φ z)
    (hφc : ∀ z : ℂ, z ∈ Qc → z ≠ 0 → ContinuousWithinAt φ Qc z)
    (hφs : ∀ z : ℂ, z ∈ Qc → z ≠ 0 → φ z ∈ Complex.slitPlane)
    (hreal : ∀ y : ℝ, 0 < y → Complex.arg (φ (y : ℂ)) = 0)
    (himag : ∀ y : ℝ, 0 < y →
      |Real.pi / 2 - p * Complex.arg (φ (Complex.I * y))| ≤ Real.pi / 2) :
    ∀ z : ℂ, 0 < z.re → 0 < z.im → 0 ≤ (Tmap p φ z).re := by
  have hπ := Real.pi_pos
  have hπ2 : (0 : ℝ) < Real.pi / 2 := by positivity
  set S : Set ℂ := Complex.im ⁻¹' Ioo 0 (Real.pi / 2) with hS
  set Λ : ℂ → ℂ := fun x => x - p * Complex.log (φ (Complex.exp x)) with hΛ
  have hexpQ : ∀ x : ℂ, x.im ∈ Icc 0 (Real.pi / 2) → Complex.exp x ∈ Qc := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [Complex.exp_re]
      exact mul_nonneg (Real.exp_pos _).le
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], hx.2⟩)
    · rw [Complex.exp_im]
      exact mul_nonneg (Real.exp_pos _).le
        (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2]))
  have hcl : closure S ⊆ Complex.im ⁻¹' Icc 0 (Real.pi / 2) :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self)
      (isClosed_Icc.preimage Complex.continuous_im)
  have hdiff : DifferentiableOn ℂ Λ S := by
    intro x hx
    have hx' : x.im ∈ Ioo 0 (Real.pi / 2) := hx
    have hre : 0 < (Complex.exp x).re := by
      rw [Complex.exp_re]
      exact mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx'.1], hx'.2⟩)
    have him : 0 < (Complex.exp x).im := by
      rw [Complex.exp_im]
      exact mul_pos (Real.exp_pos _)
        (Real.sin_pos_of_pos_of_lt_pi hx'.1 (by linarith [hx'.2]))
    have h1 : DifferentiableAt ℂ (fun x => φ (Complex.exp x)) x :=
      (hφd _ hre him).comp x Complex.differentiableAt_exp
    exact (differentiableAt_id.sub
      ((h1.clog (hφs _ ⟨hre.le, him.le⟩ (Complex.exp_ne_zero x))).const_mul _)).differentiableWithinAt
  have hcont : ContinuousOn Λ (closure S) := by
    intro x hx
    have hxI := hcl hx
    have hmaps : MapsTo Complex.exp (closure S) Qc := fun y hy => hexpQ y (hcl hy)
    have h1 : ContinuousWithinAt (fun x => φ (Complex.exp x)) (closure S) x :=
      (hφc _ (hexpQ x hxI) (Complex.exp_ne_zero x)).comp
        Complex.continuous_exp.continuousWithinAt hmaps
    have h2 : ContinuousWithinAt (fun x => Complex.log (φ (Complex.exp x))) (closure S) x :=
      h1.clog (hφs _ (hexpQ x hxI) (Complex.exp_ne_zero x))
    exact continuousWithinAt_id.sub (continuousWithinAt_const.mul h2)
  have hd : DiffContOnCl ℂ Λ S := ⟨hdiff, hcont⟩
  have him : ∀ x : ℂ, (Λ x).im = x.im - p * Complex.arg (φ (Complex.exp x)) := by
    intro x
    simp [hΛ, Complex.log_im]
  have hbdd : ∀ x : ℂ, x.im ∈ Ioo 0 (Real.pi / 2) →
      |(Λ x).im| ≤ Real.pi / 2 + |p| * Real.pi := by
    intro x hx
    rw [him]
    have h1 : |x.im| ≤ Real.pi / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2.le⟩
    have h2 : |p * Complex.arg (φ (Complex.exp x))| ≤ |p| * Real.pi := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi _) (abs_nonneg _)
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hexpR : ∀ x : ℂ, x.im = 0 → Complex.exp x = ((Real.exp x.re : ℝ) : ℂ) := by
    intro x hx
    apply Complex.ext
    · simp [Complex.exp_re, hx]
    · simp [Complex.exp_im, hx]
  have hexpI : ∀ x : ℂ, x.im = Real.pi / 2 →
      Complex.exp x = Complex.I * ((Real.exp x.re : ℝ) : ℂ) := by
    intro x hx
    apply Complex.ext
    · simp [Complex.exp_re, hx]
    · simp [Complex.exp_im, hx, Complex.exp_ofReal_re]
  have hlower : ∀ x : ℂ, x.im = 0 → |(Λ x).im| ≤ Real.pi / 2 := by
    intro x hx
    rw [him, hexpR x hx, hx, hreal _ (Real.exp_pos _)]
    simpa using hπ2.le
  have hupper : ∀ x : ℂ, x.im = Real.pi / 2 → |(Λ x).im| ≤ Real.pi / 2 := by
    intro x hx
    rw [him, hexpI x hx, hx]
    exact himag _ (Real.exp_pos _)
  have hle : ∀ x : ℂ, x.im ∈ Icc 0 (Real.pi / 2) → (Λ x).im ≤ Real.pi / 2 :=
    fun x hx => strip_im_le_gen hπ2 hd (fun z hz => (le_abs_self _).trans (hbdd z hz))
      (fun z hz => (le_abs_self _).trans (hlower z hz))
      (fun z hz => (le_abs_self _).trans (hupper z hz)) x hx.1 hx.2
  have hge : ∀ x : ℂ, x.im ∈ Icc 0 (Real.pi / 2) → -(Real.pi / 2) ≤ (Λ x).im := by
    intro x hx
    have hneg : Differentiable ℂ fun w : ℂ => -w := differentiable_neg
    have hd' : DiffContOnCl ℂ (fun z => -Λ z) S := hneg.comp_diffContOnCl hd
    have h := strip_im_le_gen (B := Real.pi / 2 + |p| * Real.pi) (C := Real.pi / 2) hπ2 hd'
      (fun z hz => by rw [Complex.neg_im]; exact (neg_le_abs _).trans (hbdd z hz))
      (fun z hz => by rw [Complex.neg_im]; exact (neg_le_abs _).trans (hlower z hz))
      (fun z hz => by rw [Complex.neg_im]; exact (neg_le_abs _).trans (hupper z hz)) x hx.1 hx.2
    rw [Complex.neg_im] at h
    linarith
  intro z hz1 hz2
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz1
    exact lt_irrefl _ hz1
  have hT : Tmap p φ z = Complex.exp (Λ (Complex.log z)) := by
    simp only [Tmap, hΛ, Complex.exp_log hz0]
    rw [sub_eq_add_neg, Complex.exp_add, Complex.exp_log hz0]
  have harg : (Complex.log z).im ∈ Icc 0 (Real.pi / 2) := by
    rw [Complex.log_im]
    exact ⟨Complex.arg_nonneg_iff.mpr hz2.le, Complex.arg_le_pi_div_two_iff.mpr (Or.inl hz1.le)⟩
  rw [hT, Complex.exp_re]
  exact mul_nonneg (Real.exp_pos _).le
    (Real.cos_nonneg_of_mem_Icc ⟨hge _ harg, hle _ harg⟩)

/-- Invariance of the closed right half-plane from the quadrant: the residual map is holomorphic on
the open right half-plane and its real part is nonnegative there. -/
theorem halfplane_core_of_quadrant (p : ℝ) (φ : ℂ → ℂ)
    (hφd : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ φ z)
    (hφc : ∀ z : ℂ, z ∈ Qc → z ≠ 0 → ContinuousWithinAt φ Qc z)
    (hφs : ∀ z : ℂ, 0 ≤ z.re → z ≠ 0 → φ z ∈ Complex.slitPlane)
    (hconj : ∀ z : ℂ, 0 < z.re → φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z))
    (hreal : ∀ y : ℝ, 0 < y → ∃ r : ℝ, 0 < r ∧ φ (y : ℂ) = (r : ℂ))
    (himag : ∀ y : ℝ, 0 < y →
      |Real.pi / 2 - p * Complex.arg (φ (Complex.I * y))| ≤ Real.pi / 2) :
    DifferentiableOn ℂ (Tmap p φ) {z : ℂ | 0 < z.re} ∧
      ∀ z : ℂ, 0 < z.re → 0 ≤ (Tmap p φ z).re := by
  have hne0 : ∀ z : ℂ, 0 < z.re → z ≠ 0 := by
    intro z hz h
    rw [h, Complex.zero_re] at hz
    exact lt_irrefl _ hz
  have hTd : DifferentiableOn ℂ (Tmap p φ) {z : ℂ | 0 < z.re} := by
    intro z hz
    have hz' : (0 : ℝ) < z.re := hz
    have h1 := (hφd z hz').clog (hφs z hz'.le (hne0 z hz'))
    exact (differentiableAt_id.mul ((h1.const_mul (p : ℂ)).neg.cexp)).differentiableWithinAt
  have harg0 : ∀ y : ℝ, 0 < y → Complex.arg (φ (y : ℂ)) = 0 := by
    intro y hy
    obtain ⟨r, hr, hφr⟩ := hreal y hy
    rw [hφr]
    exact Complex.arg_ofReal_of_nonneg hr.le
  have hq := quadrant_core p φ (fun z h1 _ => hφd z h1) hφc (fun z hz h0 => hφs z hz.1 h0)
    harg0 himag
  have hTconj : ∀ z : ℂ, 0 < z.re →
      Tmap p φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Tmap p φ z) := by
    intro z hz
    have hs := hφs z hz.le (hne0 z hz)
    have hargne : Complex.arg (φ z) ≠ Real.pi := (Complex.mem_slitPlane_iff_arg.mp hs).1
    simp only [Tmap]
    rw [hconj z hz, Complex.log_conj _ hargne, map_mul, ← Complex.exp_conj, map_neg, map_mul,
      Complex.conj_ofReal]
  refine ⟨hTd, ?_⟩
  intro z hz
  rcases lt_trichotomy z.im 0 with h | h | h
  · have hc : 0 < ((starRingEnd ℂ) z).im := by
      rw [Complex.conj_im]
      linarith
    have hc1 : 0 < ((starRingEnd ℂ) z).re := by
      rw [Complex.conj_re]
      exact hz
    have h2 := hq ((starRingEnd ℂ) z) hc1 hc
    rw [hTconj z hz, Complex.conj_re] at h2
    exact h2
  · have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext rfl (by simp [h])
    obtain ⟨r, hr, hφr⟩ := hreal z.re hz
    rw [← hzr] at hφr
    have hT : Tmap p φ z = ((z.re * Real.exp (-(p * Real.log r)) : ℝ) : ℂ) := by
      simp only [Tmap]
      rw [hφr, ← Complex.ofReal_log hr.le]
      push_cast
      rw [← hzr]
    rw [hT, Complex.ofReal_re]
    exact mul_nonneg hz.le (Real.exp_pos _).le
  · exact hq z hz h

/-- **Half-plane theorem from the quadrant.** Let the correction `φ` be holomorphic on the open
right half-plane with values off the negative axis, continuous on the closed first quadrant (origin
removed), symmetric under conjugation and positive on the positive axis. If on the positive
imaginary axis the imaginary part of `Λ = x - p log φ` stays in `[-π/2, π/2]`, and if the residual
map has contact of order `m` at `1`, then the residual map contracts the Cayley coordinate with
exponent `m` on the whole right half-plane. -/
theorem halfplane_contraction_of_quadrant (p : ℝ) (m : ℕ) (φ : ℂ → ℂ)
    (hφd : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ φ z)
    (hφc : ∀ z : ℂ, z ∈ Qc → z ≠ 0 → ContinuousWithinAt φ Qc z)
    (hφs : ∀ z : ℂ, 0 ≤ z.re → z ≠ 0 → φ z ∈ Complex.slitPlane)
    (hconj : ∀ z : ℂ, 0 < z.re → φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z))
    (hreal : ∀ y : ℝ, 0 < y → ∃ r : ℝ, 0 < r ∧ φ (y : ℂ) = (r : ℂ))
    (himag : ∀ y : ℝ, 0 < y →
      |Real.pi / 2 - p * Complex.arg (φ (Complex.I * y))| ≤ Real.pi / 2)
    (hO : (fun z => Tmap p φ z - 1) =O[𝓝 1] fun z => (z - 1) ^ m) :
    ∀ z : ℂ, 0 < z.re →
      ‖(Tmap p φ z - 1) / (Tmap p φ z + 1)‖ ≤ ‖(z - 1) / (z + 1)‖ ^ m :=
  have h := halfplane_core_of_quadrant p φ hφd hφc hφs hconj hreal himag
  schwarz_halfplane m (Tmap p φ) h.1 h.2 hO

end LeanMath.Papers.ComplexSlitPlane
