import LeanMath.Papers.ComplexSlitPlane
import LeanMath.Papers.NestedHalfPlane
import LeanMath.Papers.ThreeMeanOrderNine
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # The three-mean support on the slit plane

In the variable `z = sqrt t` the three-mean support of `ThreeMeanGlobal` is
`q = m (1 + z²) + g z - n R`, with `R² = z² + d (z² - 1)²`. The radicand factors as
`d (z² + e₁)(z² + e₂)` with `e₁ e₂ = 1`, and `R = sqrt d * sqrt (z² + e₁) * sqrt (z² + e₂)` with
principal roots is holomorphic on the right half-plane `Re z > 0`, that is on the slit plane
`t ∉ (-∞, 0]`, and continuous on the closed first quadrant.

Main result: for every real `p > 2` and every `z` with `Re z > 0`, the map
`S z = z * exp (-(p / 2) * log (φ z))`, which is `sqrt` of the residual update, satisfies
`‖(S z - 1) / (S z + 1)‖ ≤ ‖(z - 1) / (z + 1)‖ ^ 9`. -/

noncomputable section
namespace LeanMath.Papers.ThreeMeanSlitPlane

open Metric Filter Topology Asymptotics Set
open LeanMath.Papers.ComplexRoots LeanMath.Papers.ComplexHalfPlane LeanMath.Papers.ArcHalfPlane
open LeanMath.Papers.NestedHalfPlane LeanMath.Papers.ComplexSlitPlane
open LeanMath.Papers.ThreeMeanGlobal (mC gC nC dC)

/-! ## Principal square root with `sq 0 = 0` -/

/-- Principal square root, `v ^ (1/2)`, with value `0` at `0`. -/
def sq (v : ℂ) : ℂ := v ^ (((2 : ℕ) : ℂ)⁻¹)

theorem sq_sq (v : ℂ) : sq v ^ 2 = v := Complex.cpow_nat_inv_pow v two_ne_zero

theorem sq_zero : sq 0 = 0 := by
  have h := sq_sq 0
  exact pow_eq_zero_iff (two_ne_zero) |>.mp h

theorem sq_eq_csqrt {v : ℂ} (hv : v ≠ 0) : sq v = csqrt v := by
  unfold sq csqrt
  rw [Complex.cpow_def_of_ne_zero hv]
  simp [div_eq_mul_inv]

theorem sq_ofReal_nonneg {r : ℝ} (hr : 0 ≤ r) : sq (r : ℂ) = ((Real.sqrt r : ℝ) : ℂ) := by
  rcases hr.eq_or_lt with h | h
  · rw [← h]
    simp [sq_zero]
  · have hne : (r : ℂ) ≠ 0 := by exact_mod_cast h.ne'
    rw [sq_eq_csqrt hne, csqrt_ofReal h]

theorem sq_ofReal_neg {r : ℝ} (hr : 0 < r) :
    sq ((-r : ℝ) : ℂ) = Complex.I * ((Real.sqrt r : ℝ) : ℂ) := by
  have hne : ((-r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (neg_ne_zero.mpr hr.ne')
  rw [sq_eq_csqrt hne]
  unfold csqrt
  have harg : Complex.arg ((-r : ℝ) : ℂ) = Real.pi := Complex.arg_ofReal_of_neg (by linarith)
  have hlog : Complex.log ((-r : ℝ) : ℂ) = (Real.log r : ℂ) + Real.pi * Complex.I := by
    apply Complex.ext
    · rw [Complex.log_re]
      simp [abs_of_pos hr]
    · rw [Complex.log_im, harg]
      simp
  rw [hlog]
  have e : ((Real.log r : ℂ) + Real.pi * Complex.I) / 2
      = ((Real.log r / 2 : ℝ) : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hs : Real.exp (Real.log r / 2) = Real.sqrt r := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]
    congr 1
    ring
  rw [e, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two, ← Complex.ofReal_exp, hs]
  simp
  ring

theorem sq_differentiableAt {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z)
    (h : f z ∈ Complex.slitPlane) : DifferentiableAt ℂ (fun z => sq (f z)) z := by
  unfold sq
  exact hf.cpow (differentiableAt_const _) h

theorem sq_conj {v : ℂ} (hv : v ∈ Complex.slitPlane) :
    sq ((starRingEnd ℂ) v) = (starRingEnd ℂ) (sq v) := by
  have h0 : v ≠ 0 := Complex.slitPlane_ne_zero hv
  have h0' : (starRingEnd ℂ) v ≠ 0 := by
    intro h
    exact h0 ((map_eq_zero _).mp h)
  rw [sq_eq_csqrt h0, sq_eq_csqrt h0', csqrt_conj hv]

/-- The principal square root is continuous on the closed upper half-plane. -/
theorem sq_continuousWithinAt (v : ℂ) : ContinuousWithinAt sq {w : ℂ | 0 ≤ w.im} v := by
  by_cases h0 : v = 0
  · subst h0
    have h : ContinuousAt (fun x : ℂ => x ^ (((2 : ℕ) : ℂ)⁻¹)) 0 :=
      Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by simp)) (by norm_num)
    exact h.continuousWithinAt
  by_cases hs : v ∈ Complex.slitPlane
  · have h : ContinuousAt (fun x : ℂ => x ^ (((2 : ℕ) : ℂ)⁻¹)) v :=
      continuousAt_cpow_const hs
    exact h.continuousWithinAt
  · have hv : v.re ≤ 0 ∧ v.im = 0 := by
      rw [Complex.mem_slitPlane_iff] at hs
      push Not at hs
      exact hs
    have hre : v.re < 0 := by
      rcases hv.1.eq_or_lt with h | h
      · exact absurd (Complex.ext h hv.2) h0
      · exact h
    have hlog := Complex.continuousWithinAt_log_of_re_neg_of_im_zero hre hv.2
    have hc : ContinuousWithinAt (fun w : ℂ => Complex.exp (Complex.log w * (((2 : ℕ) : ℂ)⁻¹)))
        {w : ℂ | 0 ≤ w.im} v := (hlog.mul continuousWithinAt_const).cexp
    refine hc.congr_of_eventuallyEq ?_ (Complex.cpow_def_of_ne_zero h0 _)
    filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds h0)] with w hw
    exact Complex.cpow_def_of_ne_zero hw _

/-! ## Constants of the three-mean support -/

theorem d_bounds {p : ℝ} (hp : 2 < p) : 5 / 84 < dC p ∧ dC p < 1 / 14 := by
  have hp0 : 0 < p := by linarith
  unfold dC
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith

/-- `cK = m - n (2 d + 1/8)`, a rational lower bound of `m - n sqrt d`. -/
def cK (p : ℝ) : ℝ := mC p - nC p * (2 * dC p + 1 / 8)

theorem sd_sq (p : ℝ) : dC p ≤ (2 * dC p + 1 / 8) ^ 2 := by
  nlinarith [sq_nonneg (2 * dC p - 1 / 8)]

/-- Numerator of `cK`. -/
def PK (p : ℝ) : ℝ :=
      653*p^4 - 441*p^3  +  146*p^2 - 160

theorem PK_pos (p : ℝ) (hp : 2 ≤ p) : 0 < PK p := by
  obtain ⟨ε, rfl⟩ : ∃ ε, p = 2 + ε := ⟨p - 2, by ring⟩
  have hε : 0 ≤ ε := by linarith
  have e : PK (2 + ε) =
      7344 + 16188*ε + 13172*ε^2 + 4783*ε^3 + 653*ε^4 := by
    unfold PK
    ring
  rw [e]
  positivity

/-- Numerator of `(p - 1) (g - n) - 1`. -/
def PG (p : ℝ) : ℝ :=
      73*p^3  +  26*p^2 - 13*p  +  4

theorem PG_pos (p : ℝ) (hp : 2 ≤ p) : 0 < PG p := by
  obtain ⟨ε, rfl⟩ : ∃ ε, p = 2 + ε := ⟨p - 2, by ring⟩
  have hε : 0 ≤ ε := by linarith
  have e : PG (2 + ε) =
      666 + 967*ε + 464*ε^2 + 73*ε^3 := by
    unfold PG
    ring
  rw [e]
  positivity

/-- Bernstein numerator 0 of the middle-regime inequality. -/
def NB0 (p : ℝ) : ℝ :=
      172624*p^11 - 1513076*p^9  +  520792*p^7  +  129992*p^5  +  58784*p^3 - 25216*p

theorem NB0_pos (p : ℝ) (hp : 4 ≤ p) : 0 < NB0 p := by
  obtain ⟨ε, rfl⟩ : ∃ ε, p = 4 + ε := ⟨p - 4, by ring⟩
  have hε : 0 ≤ ε := by linarith
  have e : NB0 (4 + ε) =
      336063168000 + 1113756013440*ε + 1607713494912*ε^2 + 1350751439520*ε^3 + 739275689376*ε^4
      + 278034708296*ε^5 + 73546628512*ε^6 + 13712264536*ε^7 + 1768438704*ε^8 + 150396044*ε^9 +
      7595456*ε^10 + 172624*ε^11 := by
    unfold NB0
    ring
  rw [e]
  positivity

/-- Bernstein numerator 1 of the middle-regime inequality. -/
def NB1 (p : ℝ) : ℝ :=
      147928*p^11 - 1316782*p^9  +  28734*p^7  +  570404*p^5 - 73712*p^3 - 12672*p

theorem NB1_pos (p : ℝ) (hp : 4 ≤ p) : 0 < NB1 p := by
  obtain ⟨ε, rfl⟩ : ∃ ε, p = 4 + ε := ⟨p - 4, by ring⟩
  have hε : 0 ≤ ε := by linarith
  have e : NB1 (4 + ε) =
      276318604800 + 931132056960*ε + 1357126513344*ε^2 + 1146901917840*ε^3 + 629984567632*ε^4
      + 237467951492*ε^5 + 62904746184*ε^6 + 11738519742*ε^7 + 1514715528*ε^8 + 128859858*ε^9 +
      6508832*ε^10 + 147928*ε^11 := by
    unfold NB1
    ring
  rw [e]
  positivity

/-- Bernstein numerator 2 of the middle-regime inequality. -/
def NB2 (p : ℝ) : ℝ :=
      124800*p^11 - 990960*p^9 - 168540*p^7  +  463080*p^5 - 82560*p^3 - 1920*p

theorem NB2_pos (p : ℝ) (hp : 4 ≤ p) : 0 < NB2 p := by
  obtain ⟨ε, rfl⟩ : ∃ ε, p = 4 + ε := ⟨p - 4, by ring⟩
  have hε : 0 ≤ ε := by linarith
  have e : NB2 (4 + ε) =
      261382464000 + 850749540480*ε + 1211535521280*ε^2 + 1007127542400*ε^3 + 546532764960*ε^4
      + 204144957480*ε^5 + 53709262320*ε^6 + 9972142500*ε^7 + 1282213440*ε^8 + 108833040*ε^9 +
      5491200*ε^10 + 124800*ε^11 := by
    unfold NB2
    ring
  rw [e]
  positivity

/-- Bernstein numerator 3 of the middle-regime inequality. -/
def NB3 (p : ℝ) : ℝ :=
      41500*p^11 - 211475*p^9 - 395165*p^7 - 130240*p^5  +  32240*p^3  +  7040*p

theorem NB3_pos (p : ℝ) (hp : 4 ≤ p) : 0 < NB3 p := by
  obtain ⟨ε, rfl⟩ : ∃ ε, p = 4 + ε := ⟨p - 4, by ring⟩
  have hε : 0 ≤ ε := by linarith
  have e : NB3 (4 + ε) =
      112021056000 + 342446590080*ε + 465030054720*ε^2 + 372435341040*ε^3 + 196205755200*ε^4 +
      71578364720*ε^5 + 18485197780*ε^6 + 3383715235*ε^7 + 430626900*ε^8 + 36308525*ε^9 +
      1826000*ε^10 + 41500*ε^11 := by
    unfold NB3
    ring
  rw [e]
  positivity

/-- Numerator of the first outer-regime inequality. -/
def PO1 (p : ℝ) : ℝ :=
      460027*p^10 - 5169283*p^8 - 179352*p^6  +  2001488*p^4  +  647680*p^2 - 307200

theorem PO1_pos (p : ℝ) (hp : 4 ≤ p) : 0 < PO1 p := by
  obtain ⟨ε, rfl⟩ : ∃ ε, p = 4 + ε := ⟨p - 4, by ring⟩
  have hε : 0 ≤ ε := by linarith
  have e : PO1 (4 + ε) =
      143386951680 + 527800541184*ε + 763324176384*ε^2 + 607824973056*ε^3 + 303022229968*ε^4 +
      100178032576*ε^5 + 22415033384*ε^6 + 3367590304*ε^7 + 326050157*ε^8 + 18401080*ε^9 +
      460027*ε^10 := by
    unfold PO1
    ring
  rw [e]
  positivity

/-- Numerator of the second outer-regime inequality. -/
def PO2 (p : ℝ) : ℝ :=
      436765*p^12 - 4624114*p^10  +  2473133*p^8 - 3086952*p^6  +  1411024*p^4 - 80384*p^2 -
      28672

theorem PO2_pos (p : ℝ) (hp : 4 ≤ p) : 0 < PO2 p := by
  obtain ⟨ε, rfl⟩ : ∃ ε, p = 4 + ε := ⟨p - 4, by ring⟩
  have hε : 0 ≤ ε := by linarith
  have e : PO2 (4 + ε) =
      2628760780800 + 10166817669120*ε + 16861618658304*ε^2 + 16235483878656*ε^3 +
      10234897552464*ε^4 + 4483064798272*ε^5 + 1405538750552*ε^6 + 318785853856*ε^7 +
      52019971853*ε^8 + 5964686640*ε^9 + 456599726*ε^10 + 20964720*ε^11 + 436765*ε^12 := by
    unfold PO2
    ring
  rw [e]
  positivity

theorem denoms {p : ℝ} (hp : 2 < p) : p ≠ 0 ∧ 4 * p ^ 2 - 1 ≠ 0 ∧ 5 * p ^ 2 + 4 ≠ 0 ∧
    0 < 4 * p ^ 2 - 1 ∧ 0 < 5 * p ^ 2 + 4 := by
  have h1 : 0 < 4 * p ^ 2 - 1 := by nlinarith
  have h2 : 0 < 5 * p ^ 2 + 4 := by positivity
  exact ⟨by linarith, h1.ne', h2.ne', h1, h2⟩

theorem cK_eq {p : ℝ} (hp : 2 < p) :
    cK p = (p - 2) * PK p / (240 * p * (4 * p ^ 2 - 1) * (5 * p ^ 2 + 4)) := by
  obtain ⟨h0, h1, h2, -, -⟩ := denoms hp
  unfold cK mC nC dC PK
  generalize ha : 4 * p ^ 2 - 1 = a at h1 ⊢
  field_simp
  subst ha
  ring

theorem cK_pos {p : ℝ} (hp : 2 < p) : 0 < cK p := by
  obtain ⟨-, -, -, h1, h2⟩ := denoms hp
  rw [cK_eq hp]
  have hp0 : 0 < p := by linarith
  have := PK_pos p hp.le
  have h3 : 0 < p - 2 := by linarith
  positivity

theorem gn_gap {p : ℝ} (hp : 2 < p) : 1 < (p - 1) * (gC p - nC p) := by
  obtain ⟨h0, h1, h2, h1', h2'⟩ := denoms hp
  have e : (p - 1) * (gC p - nC p) - 1 = (p - 2) * PG p / (30 * p * (4 * p ^ 2 - 1)) := by
    unfold gC nC PG
    generalize ha : 4 * p ^ 2 - 1 = a at h1 ⊢
    field_simp
    subst ha
    ring
  have hp0 : 0 < p := by linarith
  have := PG_pos p hp.le
  have h3 : 0 < p - 2 := by linarith
  have h4 : 0 < (p - 2) * PG p / (30 * p * (4 * p ^ 2 - 1)) := by positivity
  linarith

/-! ## The boundary inequality, real form -/

set_option maxHeartbeats 1600000 in
theorem mid_F (p r : ℝ) (hp : 4 ≤ p) :
    6 * (((p - 1) * (gC p - nC p * r)) ^ 2
        + ((p - 1) ^ 2 * mC p ^ 2 + (p - 1) * mC p) * ((1 - r ^ 2) / dC p - 4) - 1)
      - p * ((p - 1) * (gC p - nC p * r)) * (1 + (1 - r ^ 2) / (4 * dC p))
    = (NB0 p * (1 - r) ^ 3 + 3 * NB1 p * r * (1 - r) ^ 2 + 3 * NB2 p * r ^ 2 * (1 - r)
        + NB3 p * r ^ 3) / (150 * p * (4 * p ^ 2 - 1) ^ 2 * (5 * p ^ 2 + 4) ^ 2) := by
  obtain ⟨h0, h1, h2, -, -⟩ := denoms (by linarith : (2 : ℝ) < p)
  unfold mC gC nC dC NB0 NB1 NB2 NB3
  generalize ha : 4 * p ^ 2 - 1 = a at h1 ⊢
  field_simp
  subst ha
  ring

/-- Middle regime of the boundary: `1 - d σ² = r² ≥ 0`. -/
theorem mid_core (p σ r : ℝ) (hp : 2 < p) (hσ : 2 ≤ σ) (hr0 : 0 ≤ r)
    (hr : r ^ 2 = 1 - dC p * σ ^ 2) :
    0 < ((p - 1) * (gC p - nC p * r)) ^ 2
        + ((p - 1) ^ 2 * mC p ^ 2 + (p - 1) * mC p) * (σ ^ 2 - 4) - 1 ∧
    (4 ≤ p → p * ((p - 1) * (gC p - nC p * r)) * σ ≤
      6 * (((p - 1) * (gC p - nC p * r)) ^ 2
        + ((p - 1) ^ 2 * mC p ^ 2 + (p - 1) * mC p) * (σ ^ 2 - 4) - 1)) := by
  obtain ⟨hm, hg, hn, hd⟩ := ThreeMeanGlobal.consts_pos p hp
  have hp1 : 0 < p - 1 := by linarith
  have hr1 : r ≤ 1 := by
    have h : r ^ 2 ≤ 1 := by
      rw [hr]
      nlinarith [mul_pos hd (by positivity : (0 : ℝ) < σ ^ 2)]
    nlinarith
  have hgap := gn_gap hp
  set A := (p - 1) * (gC p - nC p * r) with hA
  have hA1 : 1 < A := by
    have h : (p - 1) * (gC p - nC p) ≤ A := by
      rw [hA]
      apply mul_le_mul_of_nonneg_left _ hp1.le
      nlinarith
    linarith
  set K := (p - 1) ^ 2 * mC p ^ 2 + (p - 1) * mC p with hK
  have hK0 : 0 ≤ K := by positivity
  have hσ4 : 0 ≤ σ ^ 2 - 4 := by nlinarith
  have hKσ : 0 ≤ K * (σ ^ 2 - 4) := mul_nonneg hK0 hσ4
  refine ⟨by nlinarith, fun hp4 => ?_⟩
  have hσd : σ ^ 2 = (1 - r ^ 2) / dC p := by
    rw [hr]
    field_simp
    ring
  have hF := mid_F p r hp4
  rw [← hA, ← hK] at hF
  obtain ⟨-, -, -, h1', h2'⟩ := denoms hp
  have hp0 : 0 < p := by linarith
  have hN : 0 ≤ NB0 p * (1 - r) ^ 3 + 3 * NB1 p * r * (1 - r) ^ 2
      + 3 * NB2 p * r ^ 2 * (1 - r) + NB3 p * r ^ 3 := by
    have h0 := NB0_pos p hp4
    have h1 := NB1_pos p hp4
    have h2 := NB2_pos p hp4
    have h3 := NB3_pos p hp4
    have hr1' : 0 ≤ 1 - r := by linarith
    positivity
  have hFnn : 0 ≤ 6 * (A ^ 2 + K * (σ ^ 2 - 4) - 1) - p * A * (1 + σ ^ 2 / 4) := by
    have e : (1 : ℝ) + σ ^ 2 / 4 = 1 + (1 - r ^ 2) / (4 * dC p) := by
      rw [hσd]
      field_simp
    rw [e, hσd, hF]
    positivity
  have hσle : σ ≤ 1 + σ ^ 2 / 4 := by nlinarith [sq_nonneg (σ - 2)]
  have hpA : 0 ≤ p * A := by positivity
  have := mul_le_mul_of_nonneg_left hσle hpA
  linarith

theorem out_i (p : ℝ) (hp : 4 ≤ p) :
    p * ((p - 1) * gC p) ≤ 72 * ((p - 1) ^ 2 * cK p ^ 2 + (p - 1) * cK p) := by
  have hp2 : (2 : ℝ) < p := by linarith
  obtain ⟨h0, h1, h2, h1', h2'⟩ := denoms hp2
  have e : 72 * ((p - 1) ^ 2 * cK p ^ 2 + (p - 1) * cK p) - p * ((p - 1) * gC p)
      = (p - 1) * (p + 1) * PO1 p / (2400 * p ^ 2 * (4 * p ^ 2 - 1) ^ 2 * (5 * p ^ 2 + 4) ^ 2) := by
    rw [cK_eq hp2]
    unfold gC PK PO1
    generalize ha : 4 * p ^ 2 - 1 = a at h1 ⊢
    field_simp
    subst ha
    ring
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have := PO1_pos p hp
  have h4 : 0 ≤ (p - 1) * (p + 1) * PO1 p
      / (2400 * p ^ 2 * (4 * p ^ 2 - 1) ^ 2 * (5 * p ^ 2 + 4) ^ 2) := by positivity
  linarith

theorem out_ii (p : ℝ) (hp : 4 ≤ p) :
    3 * p * ((p - 1) * gC p) ≤ 6 * (((p - 1) * gC p) ^ 2 - 1)
      - 24 * ((p - 1) ^ 2 * cK p ^ 2 + (p - 1) * cK p) := by
  have hp2 : (2 : ℝ) < p := by linarith
  obtain ⟨h0, h1, h2, h1', h2'⟩ := denoms hp2
  have e : 6 * (((p - 1) * gC p) ^ 2 - 1) - 24 * ((p - 1) ^ 2 * cK p ^ 2 + (p - 1) * cK p)
        - 3 * p * ((p - 1) * gC p)
      = PO2 p / (800 * p ^ 2 * (4 * p ^ 2 - 1) ^ 2 * (5 * p ^ 2 + 4) ^ 2) := by
    rw [cK_eq hp2]
    unfold gC PK PO2
    generalize ha : 4 * p ^ 2 - 1 = a at h1 ⊢
    field_simp
    subst ha
    ring
  have hp0 : 0 < p := by linarith
  have := PO2_pos p hp
  have h4 : 0 ≤ PO2 p / (800 * p ^ 2 * (4 * p ^ 2 - 1) ^ 2 * (5 * p ^ 2 + 4) ^ 2) := by
    positivity
  linarith

/-- Outer regime of the boundary: `d σ² - 1 = ρ² ≥ 0`. -/
theorem out_core (p σ Δ ρ : ℝ) (hp : 2 < p) (hΔ0 : 0 ≤ Δ) (hρ0 : 0 ≤ ρ)
    (hΔ : Δ ^ 2 = σ ^ 2 - 4) (hρ : ρ ^ 2 = dC p * σ ^ 2 - 1) :
    0 ≤ (p - 1) * (mC p * Δ - nC p * ρ) ∧
    0 < ((p - 1) * gC p) ^ 2 - 1 + ((p - 1) * (mC p * Δ - nC p * ρ)) ^ 2
        + (p - 1) * (mC p * Δ - nC p * ρ) * Δ ∧
    (4 ≤ p → p * ((p - 1) * gC p) * σ ≤
      6 * (((p - 1) * gC p) ^ 2 - 1 + ((p - 1) * (mC p * Δ - nC p * ρ)) ^ 2
        + (p - 1) * (mC p * Δ - nC p * ρ) * Δ)) := by
  obtain ⟨hm, hg, hn, hd⟩ := ThreeMeanGlobal.consts_pos p hp
  obtain ⟨hd1, hd2⟩ := d_bounds hp
  have hp1 : 0 < p - 1 := by linarith
  have hk := cK_pos hp
  set sd := 2 * dC p + 1 / 8 with hsd
  have hsd0 : 0 < sd := by positivity
  have hρle : ρ ≤ sd * Δ := by
    have h1 : ρ ^ 2 ≤ (sd * Δ) ^ 2 := by
      rw [mul_pow, hρ, hΔ]
      have hsq : dC p ≤ sd ^ 2 := sd_sq p
      have h4 : 0 ≤ σ ^ 2 - 4 := by rw [← hΔ]; positivity
      have h5 := mul_le_mul_of_nonneg_right hsq h4
      linarith
    exact (pow_le_pow_iff_left₀ hρ0 (by positivity) two_ne_zero).mp h1
  set β := (p - 1) * (mC p * Δ - nC p * ρ) with hβ
  have hβge : (p - 1) * cK p * Δ ≤ β := by
    have h1 : cK p * Δ ≤ mC p * Δ - nC p * ρ := by
      have := mul_le_mul_of_nonneg_left hρle hn.le
      unfold cK
      rw [← hsd]
      nlinarith
    have := mul_le_mul_of_nonneg_left h1 hp1.le
    linarith [mul_assoc (p - 1) (cK p) Δ]
  have hkΔ : 0 ≤ (p - 1) * cK p * Δ := by positivity
  have hβ0 : 0 ≤ β := hkΔ.trans hβge
  have hgap := gn_gap hp
  have hcg : 1 < (p - 1) * gC p := by
    have : (p - 1) * (gC p - nC p) ≤ (p - 1) * gC p :=
      mul_le_mul_of_nonneg_left (by linarith) hp1.le
    linarith
  have hβΔ : 0 ≤ β * Δ := mul_nonneg hβ0 hΔ0
  refine ⟨hβ0, by nlinarith [sq_nonneg β], fun hp4 => ?_⟩
  set K2 := (p - 1) ^ 2 * cK p ^ 2 + (p - 1) * cK p with hK2
  have hi := out_i p hp4
  have hii := out_ii p hp4
  rw [← hK2] at hi hii
  have hβ2 : ((p - 1) * cK p * Δ) ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hkΔ hβge 2
  have hβΔ2 : (p - 1) * cK p * Δ * Δ ≤ β * Δ := mul_le_mul_of_nonneg_right hβge hΔ0
  have hlow : K2 * (σ ^ 2 - 4) ≤ β ^ 2 + β * Δ := by
    have e : K2 * (σ ^ 2 - 4) = ((p - 1) * cK p * Δ) ^ 2 + (p - 1) * cK p * Δ * Δ := by
      rw [hK2, ← hΔ]
      ring
    linarith
  have hσle : σ ≤ σ ^ 2 / 12 + 3 := by nlinarith [sq_nonneg (σ - 6)]
  have hpcg : 0 ≤ p * ((p - 1) * gC p) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hσle hpcg
  have h2 : p * ((p - 1) * gC p) * (σ ^ 2 / 12) ≤ 6 * K2 * σ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hi (by positivity : (0 : ℝ) ≤ σ ^ 2 / 12)
    linarith
  linarith

/-! ## Factorization of the radicand -/

/-- `sqrt (1 - 4 d)`. -/
def s4 (p : ℝ) : ℝ := Real.sqrt (1 - 4 * dC p)

/-- The larger root of `d Z² - (1 - 2 d) Z + d`. -/
def e1 (p : ℝ) : ℝ := ((1 - 2 * dC p) + s4 p) / (2 * dC p)

/-- The smaller root of `d Z² - (1 - 2 d) Z + d`. -/
def e2 (p : ℝ) : ℝ := ((1 - 2 * dC p) - s4 p) / (2 * dC p)

theorem e_facts {p : ℝ} (hp : 2 < p) :
    0 < e2 p ∧ e2 p ≤ 1 ∧ 1 ≤ e1 p ∧ e1 p * e2 p = 1 ∧
      dC p * (e1 p + e2 p) = 1 - 2 * dC p := by
  obtain ⟨hd1, hd2⟩ := d_bounds hp
  have hd : 0 < dC p := by linarith
  have hs0 : 0 ≤ s4 p := Real.sqrt_nonneg _
  have hs2 : s4 p ^ 2 = 1 - 4 * dC p := Real.sq_sqrt (by linarith)
  have hs1 : s4 p ≤ 1 := by nlinarith
  have hslt : s4 p < 1 - 2 * dC p := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold e2
    apply div_pos <;> linarith
  · unfold e2
    rw [div_le_one (by linarith)]
    nlinarith
  · unfold e1
    rw [le_div_iff₀ (by linarith)]
    linarith
  · unfold e1 e2
    field_simp
    nlinarith
  · unfold e1 e2
    field_simp
    ring

theorem rad_factor_real {p : ℝ} (hp : 2 < p) (T : ℝ) :
    dC p * (e1 p - T) * (e2 p - T) = dC p * (T + 1) ^ 2 - T := by
  obtain ⟨-, -, -, h1, h2⟩ := e_facts hp
  linear_combination dC p * h1 - T * h2

theorem rad_factor {p : ℝ} (hp : 2 < p) (Z : ℂ) :
    (dC p : ℂ) * (Z + (e1 p : ℂ)) * (Z + (e2 p : ℂ)) = Z + (dC p : ℂ) * (Z - 1) ^ 2 := by
  obtain ⟨-, -, -, h1, h2⟩ := e_facts hp
  have hc1 : (e1 p : ℂ) * (e2 p : ℂ) = 1 := by exact_mod_cast h1
  have hc2 : (dC p : ℂ) * ((e1 p : ℂ) + (e2 p : ℂ)) = 1 - 2 * (dC p : ℂ) := by exact_mod_cast h2
  linear_combination (dC p : ℂ) * hc1 + Z * hc2

/-! ## The support in the variable `z = sqrt t` -/

/-- The conic radical `R`, with `R² = z² + d (z² - 1)²`. -/
def RM (p : ℝ) (z : ℂ) : ℂ :=
  ((Real.sqrt (dC p) : ℝ) : ℂ) * sq (z ^ 2 + (e1 p : ℂ)) * sq (z ^ 2 + (e2 p : ℂ))

/-- The three-mean support in the variable `z`. -/
def qM (p : ℝ) (z : ℂ) : ℂ :=
  (mC p : ℂ) * (1 + z ^ 2) + (gC p : ℂ) * z - (nC p : ℂ) * RM p z

/-- The correction of the three-mean support, as a function of `z = sqrt t`. -/
def φM (p : ℝ) (z : ℂ) : ℂ := corr (p : ℂ) (qM p z) (z ^ 2)

theorem RM_sq {p : ℝ} (hp : 2 < p) (z : ℂ) :
    RM p z ^ 2 = z ^ 2 + (dC p : ℂ) * (z ^ 2 - 1) ^ 2 := by
  obtain ⟨hd1, -⟩ := d_bounds hp
  have hd : 0 ≤ dC p := by linarith
  have hsd : ((Real.sqrt (dC p) : ℝ) : ℂ) ^ 2 = (dC p : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hd]
  unfold RM
  rw [mul_pow, mul_pow, sq_sq, sq_sq, hsd]
  exact rad_factor hp (z ^ 2)

/-! ## Values off the negative axis -/

theorem qM_div_re {p : ℝ} (hp : 2 < p) {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    gC p - nC p ≤ (qM p z / z).re := by
  obtain ⟨hm, hg, hn, hd⟩ := ThreeMeanGlobal.consts_pos p hp
  have hk := cK_pos hp
  set s := RM p z / z with hs
  set u := z - z⁻¹ with hu
  have hs2 : s ^ 2 = 1 + (dC p : ℂ) * u ^ 2 := by
    rw [hs, hu, div_pow, RM_sq hp]
    field_simp
  have hre : (s ^ 2).re = s.re ^ 2 - s.im ^ 2 := by
    simp [pow_two]
  have hre' : (s ^ 2).re = 1 + dC p * (u.re ^ 2 - u.im ^ 2) := by
    rw [hs2]
    simp [pow_two]
  have hnorm : ‖s‖ ^ 2 ≤ 1 + dC p * (u.re ^ 2 + u.im ^ 2) := by
    have h : ‖s ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖(dC p : ℂ) * u ^ 2‖ := by
      rw [hs2]
      exact norm_add_le _ _
    rw [norm_pow, norm_one, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hd.le,
      Complex.sq_norm u, Complex.normSq_apply] at h
    linarith [pow_two u.re, pow_two u.im]
  have hns : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h1 : s.re ^ 2 ≤ 1 + dC p * u.re ^ 2 := by nlinarith
  set sd := 2 * dC p + 1 / 8 with hsd
  have hsd0 : 0 < sd := by positivity
  have hsq : dC p ≤ sd ^ 2 := sd_sq p
  have h2 : s.re ^ 2 ≤ (1 + sd * |u.re|) ^ 2 := by
    have h3 := mul_le_mul_of_nonneg_right hsq (sq_nonneg u.re)
    have h4 := mul_nonneg hsd0.le (abs_nonneg u.re)
    have h5 := sq_abs u.re
    nlinarith
  have hsre : s.re ≤ 1 + sd * |u.re| := (abs_le_of_sq_le_sq' h2 (by positivity)).2
  have hinv : 0 ≤ (z⁻¹).re := by
    rw [Complex.inv_re]
    exact div_nonneg hz (Complex.normSq_nonneg z)
  have hure : u.re = z.re - (z⁻¹).re := by
    rw [hu, Complex.sub_re]
  have habs : |u.re| ≤ z.re + (z⁻¹).re := by
    rw [hure, abs_le]
    constructor <;> linarith
  have e : qM p z / z = (mC p : ℂ) * (z⁻¹ + z) + (gC p : ℂ) - (nC p : ℂ) * s := by
    rw [hs]
    unfold qM
    field_simp
  have hRe : (qM p z / z).re = mC p * ((z⁻¹).re + z.re) + gC p - nC p * s.re := by
    rw [e]
    simp
  rw [hRe]
  have h6 := mul_le_mul_of_nonneg_left hsre hn.le
  have h7 := mul_le_mul_of_nonneg_left habs (mul_nonneg hn.le hsd0.le)
  have h8 : 0 ≤ cK p * (z.re + (z⁻¹).re) := mul_nonneg hk.le (by linarith)
  unfold cK at h8
  rw [← hsd] at h8
  nlinarith

theorem φM_eq (p : ℝ) {z : ℂ} (hz0 : z ≠ 0) :
    φM p z = (z + ((p : ℂ) - 1) * (qM p z / z)) / (z⁻¹ + ((p : ℂ) - 1) * (qM p z / z)) := by
  have h1 : z + ((p : ℂ) - 1) * (qM p z / z) = (z ^ 2 + ((p : ℂ) - 1) * qM p z) / z := by
    field_simp
  have h2 : z⁻¹ + ((p : ℂ) - 1) * (qM p z / z) = (1 + ((p : ℂ) - 1) * qM p z) / z := by
    field_simp
  rw [h1, h2, div_div_div_cancel_right₀ hz0]
  rfl

theorem parts_re_pos {p : ℝ} (hp : 2 < p) {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    0 < (z + ((p : ℂ) - 1) * (qM p z / z)).re ∧
      0 < (z⁻¹ + ((p : ℂ) - 1) * (qM p z / z)).re := by
  have hW := qM_div_re hp hz hz0
  have hgap := gn_gap hp
  have hp1 : 0 < p - 1 := by linarith
  have hgn : 0 < gC p - nC p := by
    by_contra h
    have h' : gC p - nC p ≤ 0 := le_of_not_gt h
    nlinarith
  have hinv : 0 ≤ (z⁻¹).re := by
    rw [Complex.inv_re]
    exact div_nonneg hz (Complex.normSq_nonneg z)
  have hpos : 0 < (p - 1) * (qM p z / z).re := mul_pos hp1 (lt_of_lt_of_le hgn hW)
  constructor
  · rw [num_re]
    linarith
  · rw [num_re]
    linarith

theorem φM_mem {p : ℝ} (hp : 2 < p) {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    φM p z ∈ Complex.slitPlane := by
  rw [φM_eq p hz0]
  obtain ⟨h1, h2⟩ := parts_re_pos hp hz hz0
  exact div_mem_slitPlane h1 h2

theorem den_ne {p : ℝ} (hp : 2 < p) {z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    1 + ((p : ℂ) - 1) * qM p z ≠ 0 := by
  obtain ⟨-, h2⟩ := parts_re_pos hp hz hz0
  have e : 1 + ((p : ℂ) - 1) * qM p z = z * (z⁻¹ + ((p : ℂ) - 1) * (qM p z / z)) := by
    field_simp
  rw [e]
  apply mul_ne_zero hz0
  intro h
  rw [h, Complex.zero_re] at h2
  exact lt_irrefl _ h2

/-! ## Holomorphy, continuity on the closed quadrant, conjugation -/

theorem arg_mem {z : ℂ} (hz : 0 < z.re) {e : ℝ} (he : 0 ≤ e) :
    z ^ 2 + (e : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  have hre : (z ^ 2 + (e : ℂ)).re = z.re ^ 2 - z.im ^ 2 + e := by
    simp [pow_two]
  have him : (z ^ 2 + (e : ℂ)).im = 2 * z.re * z.im := by
    simp [pow_two]
    ring
  by_cases h : z.im = 0
  · left
    rw [hre, h]
    have : 0 < z.re ^ 2 := by positivity
    linarith
  · right
    rw [him]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hz.ne') h

theorem RM_differentiableAt {p : ℝ} (hp : 2 < p) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (RM p) z := by
  obtain ⟨h2, -, h1, -, -⟩ := e_facts hp
  have hf : ∀ e : ℝ, DifferentiableAt ℂ (fun z : ℂ => z ^ 2 + (e : ℂ)) z := fun e =>
    (differentiableAt_id.pow 2).add (differentiableAt_const _)
  have ha := sq_differentiableAt (hf (e1 p)) (arg_mem hz (by linarith : (0 : ℝ) ≤ e1 p))
  have hb := sq_differentiableAt (hf (e2 p)) (arg_mem hz h2.le)
  exact ((differentiableAt_const _).mul ha).mul hb

theorem qM_differentiableAt {p : ℝ} (hp : 2 < p) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (qM p) z := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (mC p : ℂ) * (1 + z ^ 2)) z :=
    (differentiableAt_const _).mul ((differentiableAt_const _).add (differentiableAt_id.pow 2))
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (gC p : ℂ) * z) z :=
    (differentiableAt_const _).mul differentiableAt_id
  exact (h1.add h2).sub ((differentiableAt_const _).mul (RM_differentiableAt hp hz))

theorem φM_differentiableAt {p : ℝ} (hp : 2 < p) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (φM p) z := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz
    exact lt_irrefl _ hz
  have hq := qM_differentiableAt hp hz
  have hn : DifferentiableAt ℂ (fun z : ℂ => z ^ 2 + ((p : ℂ) - 1) * qM p z) z :=
    (differentiableAt_id.pow 2).add ((differentiableAt_const _).mul hq)
  have hd : DifferentiableAt ℂ (fun z : ℂ => 1 + ((p : ℂ) - 1) * qM p z) z :=
    (differentiableAt_const _).add ((differentiableAt_const _).mul hq)
  exact hn.div hd (den_ne hp hz.le hz0)

theorem sq_arg_continuousWithinAt (e : ℝ) (z : ℂ) :
    ContinuousWithinAt (fun z : ℂ => sq (z ^ 2 + (e : ℂ))) Qc z := by
  have hc : ContinuousWithinAt (fun z : ℂ => z ^ 2 + (e : ℂ)) Qc z :=
    ((continuous_pow 2).add continuous_const).continuousWithinAt
  have hmaps : MapsTo (fun z : ℂ => z ^ 2 + (e : ℂ)) Qc {w : ℂ | 0 ≤ w.im} := by
    intro w hw
    have him : (w ^ 2 + (e : ℂ)).im = 2 * w.re * w.im := by
      simp [pow_two]
      ring
    show 0 ≤ (w ^ 2 + (e : ℂ)).im
    rw [him]
    exact mul_nonneg (mul_nonneg (by norm_num) hw.1) hw.2
  exact (sq_continuousWithinAt _).comp hc hmaps

theorem qM_continuousWithinAt (p : ℝ) (z : ℂ) : ContinuousWithinAt (qM p) Qc z := by
  have h1 : ContinuousWithinAt (fun z : ℂ => (mC p : ℂ) * (1 + z ^ 2) + (gC p : ℂ) * z) Qc z :=
    ((continuous_const.mul (continuous_const.add (continuous_pow 2))).add
      (continuous_const.mul continuous_id)).continuousWithinAt
  have hR : ContinuousWithinAt (RM p) Qc z :=
    (continuousWithinAt_const.mul (sq_arg_continuousWithinAt (e1 p) z)).mul
      (sq_arg_continuousWithinAt (e2 p) z)
  exact h1.sub (continuousWithinAt_const.mul hR)

theorem φM_continuousWithinAt {p : ℝ} (hp : 2 < p) {z : ℂ} (hz : z ∈ Qc) (hz0 : z ≠ 0) :
    ContinuousWithinAt (φM p) Qc z := by
  have hq := qM_continuousWithinAt p z
  have hn : ContinuousWithinAt (fun z : ℂ => z ^ 2 + ((p : ℂ) - 1) * qM p z) Qc z :=
    ((continuous_pow 2).continuousWithinAt).add (continuousWithinAt_const.mul hq)
  have hd : ContinuousWithinAt (fun z : ℂ => 1 + ((p : ℂ) - 1) * qM p z) Qc z :=
    continuousWithinAt_const.add (continuousWithinAt_const.mul hq)
  exact hn.div hd (den_ne hp hz.1 hz0)

theorem RM_conj {p : ℝ} (hp : 2 < p) {z : ℂ} (hz : 0 < z.re) :
    RM p ((starRingEnd ℂ) z) = (starRingEnd ℂ) (RM p z) := by
  obtain ⟨h2, -, h1, -, -⟩ := e_facts hp
  have hc : ∀ e : ℝ, (starRingEnd ℂ) z ^ 2 + (e : ℂ) = (starRingEnd ℂ) (z ^ 2 + (e : ℂ)) := by
    intro e
    simp
  unfold RM
  rw [hc, hc, sq_conj (arg_mem hz (by linarith : (0 : ℝ) ≤ e1 p)), sq_conj (arg_mem hz h2.le)]
  simp

theorem φM_conj {p : ℝ} (hp : 2 < p) {z : ℂ} (hz : 0 < z.re) :
    φM p ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φM p z) := by
  have hq : qM p ((starRingEnd ℂ) z) = (starRingEnd ℂ) (qM p z) := by
    unfold qM
    rw [RM_conj hp hz]
    simp
  unfold φM corr
  rw [hq]
  simp

/-! ## The positive axis -/

open LeanMath.Papers.ThreeMeanGlobal in
theorem RM_ofReal {p : ℝ} (hp : 2 < p) {x : ℝ} (hx : 0 < x) :
    RM p (x : ℂ) = ((root p x : ℝ) : ℂ) := by
  obtain ⟨h2, -, h1, -, -⟩ := e_facts hp
  obtain ⟨hd1, -⟩ := d_bounds hp
  have hd : 0 ≤ dC p := by linarith
  have ha : 0 ≤ x ^ 2 + e1 p := by positivity
  have hb : 0 ≤ x ^ 2 + e2 p := by positivity
  have hc : ∀ e : ℝ, (x : ℂ) ^ 2 + (e : ℂ) = ((x ^ 2 + e : ℝ) : ℂ) := by
    intro e
    push_cast
    ring
  unfold RM root
  rw [hc, hc, sq_ofReal_nonneg ha, sq_ofReal_nonneg hb, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, ← Real.sqrt_mul hd, ← Real.sqrt_mul (mul_nonneg hd ha)]
  congr 2
  unfold rad
  have h := rad_factor_real hp (-(x ^ 2))
  linear_combination h

open LeanMath.Papers.ThreeMeanGlobal in
theorem φM_ofReal {p : ℝ} (hp : 2 < p) {x : ℝ} (hx : 0 < x) :
    φM p (x : ℂ) = ((correction p (x ^ 2) : ℝ) : ℂ) := by
  have hq : qM p (x : ℂ) = ((qx p x : ℝ) : ℂ) := by
    unfold qM qx lin
    rw [RM_ofReal hp hx]
    push_cast
    ring
  unfold φM corr correction support
  rw [hq, Real.sqrt_sq hx.le]
  push_cast
  ring

/-! ## Order nine -/

theorem Tmap_differentiableAt {p : ℝ} (hp : 2 < p) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ (Tmap (p / 2) (φM p)) z := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz
    exact lt_irrefl _ hz
  have h1 := (φM_differentiableAt hp hz).clog (φM_mem hp hz.le hz0)
  exact differentiableAt_id.mul ((h1.const_mul ((p / 2 : ℝ) : ℂ)).neg.cexp)

/-- The square root of the residual map has contact of order nine at `1`, in `ℂ`. -/
theorem slit_order {p : ℝ} (hp : 2 < p) :
    (fun z => Tmap (p / 2) (φM p) z - 1) =O[𝓝 1] fun z => (z - 1) ^ 9 := by
  have key : ∀ e : ℝ, Real.exp (-(p / 2) * e) ^ 2 = Real.exp (-p * e) := by
    intro e
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hlim := ThreeMeanOrderNine.order_nine p hp
  refine order_of_real_limit (p / 2) (by linarith) (φM p)
    (fun x => ThreeMeanGlobal.correction p (x ^ 2)) 9 (by norm_num) (ThreeMeanOrderNine.cM p)
    (fun _ ht => Tmap_differentiableAt hp ht) (fun _ ht => φM_ofReal hp ht)
    (fun t ht => ThreeMeanGlobal.correction_positive p (t ^ 2) hp (by positivity)) ?_ ?_
  · simp only [one_pow]
    exact ThreeMeanGlobal.correction_one p hp
  · simpa only [key] using hlim

/-! ## The boundary `z = i τ` -/

theorem I_mul_sq (τ : ℝ) : (Complex.I * (τ : ℂ)) ^ 2 = ((-(τ ^ 2) : ℝ) : ℂ) := by
  rw [mul_pow, Complex.I_sq]
  push_cast
  ring

/-- Values of the conic radical on the positive imaginary axis: purely imaginary between the two
branch points, real outside. -/
theorem boundary_R {p : ℝ} (hp : 2 < p) {τ : ℝ} (hτ : 0 < τ) :
    (∃ r : ℝ, 0 ≤ r ∧ r ^ 2 = 1 - dC p * (τ + 1 / τ) ^ 2 ∧
        RM p (Complex.I * τ) = (τ : ℂ) * (Complex.I * (r : ℂ))) ∨
    (∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ^ 2 = dC p * (τ + 1 / τ) ^ 2 - 1 ∧ τ ≤ 1 ∧
        RM p (Complex.I * τ) = (τ : ℂ) * (ρ : ℂ)) ∨
    (∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ^ 2 = dC p * (τ + 1 / τ) ^ 2 - 1 ∧ 1 ≤ τ ∧
        RM p (Complex.I * τ) = -((τ : ℂ) * (ρ : ℂ))) := by
  obtain ⟨he2, he2', he1, -, -⟩ := e_facts hp
  obtain ⟨hd1, -⟩ := d_bounds hp
  have hd : 0 < dC p := by linarith
  have hfac := rad_factor_real hp (τ ^ 2)
  have hc : ∀ e : ℝ, (Complex.I * (τ : ℂ)) ^ 2 + (e : ℂ) = ((e - τ ^ 2 : ℝ) : ℂ) := by
    intro e
    rw [I_mul_sq]
    push_cast
    ring
  have hR : RM p (Complex.I * τ) = ((Real.sqrt (dC p) : ℝ) : ℂ)
      * sq ((e1 p - τ ^ 2 : ℝ) : ℂ) * sq ((e2 p - τ ^ 2 : ℝ) : ℂ) := by
    unfold RM
    rw [hc, hc]
  set sd := Real.sqrt (dC p) with hsd
  have hsd2 : sd ^ 2 = dC p := Real.sq_sqrt hd.le
  have hsd0 : 0 ≤ sd := Real.sqrt_nonneg _
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ0
  have hσ : dC p * (τ + 1 / τ) ^ 2 - 1 = (dC p * (τ ^ 2 + 1) ^ 2 - τ ^ 2) / τ ^ 2 := by
    field_simp
  rcases le_or_gt (τ ^ 2) (e2 p) with hlow | hlow
  · right; left
    have ha : 0 ≤ e1 p - τ ^ 2 := by linarith
    have hb : 0 ≤ e2 p - τ ^ 2 := by linarith
    refine ⟨sd * Real.sqrt (e1 p - τ ^ 2) * Real.sqrt (e2 p - τ ^ 2) / τ, by positivity, ?_,
      le_of_not_gt (fun h => by nlinarith), ?_⟩
    · rw [hσ, div_pow, mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, hsd2, ← hfac]
    · rw [hR, sq_ofReal_nonneg ha, sq_ofReal_nonneg hb]
      push_cast
      field_simp
  · rcases le_or_gt (τ ^ 2) (e1 p) with hmid | hhigh
    · left
      have ha : 0 ≤ e1 p - τ ^ 2 := by linarith
      have hb : 0 < τ ^ 2 - e2 p := by linarith
      have hneg : ((e2 p - τ ^ 2 : ℝ) : ℂ) = ((-(τ ^ 2 - e2 p) : ℝ) : ℂ) := by
        push_cast
        ring
      refine ⟨sd * Real.sqrt (e1 p - τ ^ 2) * Real.sqrt (τ ^ 2 - e2 p) / τ, by positivity, ?_, ?_⟩
      · have e : 1 - dC p * (τ + 1 / τ) ^ 2 = -(dC p * (τ ^ 2 + 1) ^ 2 - τ ^ 2) / τ ^ 2 := by
          field_simp
          ring
        rw [e, div_pow, mul_pow, mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb.le, hsd2, ← hfac]
        ring
      · rw [hR, sq_ofReal_nonneg ha, hneg, sq_ofReal_neg hb]
        push_cast
        field_simp
    · right; right
      have ha : 0 < τ ^ 2 - e1 p := by linarith
      have hb : 0 < τ ^ 2 - e2 p := by linarith
      have hn1 : ((e1 p - τ ^ 2 : ℝ) : ℂ) = ((-(τ ^ 2 - e1 p) : ℝ) : ℂ) := by
        push_cast
        ring
      have hn2 : ((e2 p - τ ^ 2 : ℝ) : ℂ) = ((-(τ ^ 2 - e2 p) : ℝ) : ℂ) := by
        push_cast
        ring
      refine ⟨sd * Real.sqrt (τ ^ 2 - e1 p) * Real.sqrt (τ ^ 2 - e2 p) / τ, by positivity, ?_,
        le_of_not_gt (fun h => by nlinarith), ?_⟩
      · rw [hσ, div_pow, mul_pow, mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le, hsd2, ← hfac]
        ring
      · rw [hR, hn1, hn2, sq_ofReal_neg ha, sq_ofReal_neg hb]
        have hI : ∀ A B C : ℂ, A * (Complex.I * B) * (Complex.I * C) = -(A * B * C) := by
          intro A B C
          linear_combination (A * B * C) * Complex.I_sq
        rw [hI]
        push_cast
        field_simp

theorem re_parts (a b : ℝ) : ((a : ℂ) + Complex.I * (b : ℂ)).re = a := by simp

theorem im_parts (a b : ℝ) : ((a : ℂ) + Complex.I * (b : ℂ)).im = b := by simp

/-- From the real and imaginary parts of numerator and denominator to the argument. -/
theorem arg_bounds_of {p : ℝ} (hp : 2 < p) {τ X Y : ℝ} (hY : 0 < Y)
    (hR : 0 < (X - τ ^ 2) * (1 + X) + Y ^ 2)
    (h4 : 4 ≤ p → p * (Y * (1 + τ ^ 2)) ≤ 6 * ((X - τ ^ 2) * (1 + X) + Y ^ 2)) :
    0 ≤ Complex.arg ((((X - τ ^ 2 : ℝ) : ℂ) + Complex.I * (Y : ℂ))
        / (((1 + X : ℝ) : ℂ) + Complex.I * (Y : ℂ))) ∧
      Complex.arg ((((X - τ ^ 2 : ℝ) : ℂ) + Complex.I * (Y : ℂ))
        / (((1 + X : ℝ) : ℂ) + Complex.I * (Y : ℂ))) ≤ 2 * Real.pi / p := by
  set N : ℂ := ((X - τ ^ 2 : ℝ) : ℂ) + Complex.I * (Y : ℂ) with hN
  set D : ℂ := ((1 + X : ℝ) : ℂ) + Complex.I * (Y : ℂ) with hD
  have hNre : N.re = X - τ ^ 2 := re_parts _ _
  have hNim : N.im = Y := im_parts _ _
  have hDre : D.re = 1 + X := re_parts _ _
  have hDim : D.im = Y := im_parts _ _
  have hD0 : D ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [hDim, Complex.zero_im] at this
    exact hY.ne' this
  have hns : 0 < Complex.normSq D := Complex.normSq_pos.mpr hD0
  have hre : (N / D).re = ((X - τ ^ 2) * (1 + X) + Y ^ 2) / Complex.normSq D := by
    rw [Complex.div_re, hNre, hNim, hDre, hDim, ← add_div]
    congr 1
    ring
  have him : (N / D).im = (Y * (1 + τ ^ 2)) / Complex.normSq D := by
    rw [Complex.div_im, hNre, hNim, hDre, hDim, ← sub_div]
    congr 1
    ring
  have hrepos : 0 < (N / D).re := by
    rw [hre]
    exact div_pos hR hns
  have himpos : 0 ≤ (N / D).im := by
    rw [him]
    exact div_nonneg (by positivity) hns.le
  have hp0 : 0 < p := by linarith
  have hπ := Real.pi_pos
  refine ⟨Complex.arg_nonneg_iff.mpr himpos, ?_⟩
  have habs := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hrepos))
  rcases le_or_gt p 4 with hp4 | hp4
  · have h : Real.pi / 2 ≤ 2 * Real.pi / p := by
      rw [le_div_iff₀ hp0]
      nlinarith
    linarith [habs.2]
  · have h4' := h4 hp4.le
    have hx : 2 * Real.pi / p < Real.pi / 2 := by
      rw [div_lt_iff₀ hp0]
      nlinarith
    have hx0 : 0 ≤ 2 * Real.pi / p := by positivity
    have htan : Real.tan (Complex.arg (N / D)) ≤ Real.tan (2 * Real.pi / p) := by
      have h1 : Real.tan (Complex.arg (N / D)) ≤ 6 / p := by
        rw [Complex.tan_arg, him, hre, div_div_div_cancel_right₀ hns.ne', div_le_div_iff₀ hR hp0]
        linarith [mul_comm p (Y * (1 + τ ^ 2))]
      have h2 : 6 / p ≤ 2 * Real.pi / p :=
        div_le_div_of_nonneg_right (by linarith [Real.pi_gt_three]) hp0.le
      exact h1.trans (h2.trans (Real.le_tan hx0 hx))
    by_contra hgt
    have hgt' : 2 * Real.pi / p < Complex.arg (N / D) := lt_of_not_ge hgt
    have hneg : -(Real.pi / 2) < 2 * Real.pi / p := by linarith
    have := Real.tan_lt_tan_of_lt_of_lt_pi_div_two hneg habs.2 hgt'
    linarith

theorem φM_boundary_form (p : ℝ) {τ X₀ Y₀ : ℝ}
    (hq : qM p (Complex.I * τ) = (X₀ : ℂ) + Complex.I * (Y₀ : ℂ)) :
    φM p (Complex.I * τ)
      = ((((p - 1) * X₀ - τ ^ 2 : ℝ) : ℂ) + Complex.I * (((p - 1) * Y₀ : ℝ) : ℂ))
        / (((1 + (p - 1) * X₀ : ℝ) : ℂ) + Complex.I * (((p - 1) * Y₀ : ℝ) : ℂ)) := by
  unfold φM corr
  rw [I_mul_sq, hq]
  congr 1 <;> (push_cast; ring)

/-- **Boundary inequality on the cut.** On the positive imaginary axis of `z = sqrt t`, that is on
the upper edge of the negative axis of `t`, the argument of the correction lies in `[0, 2π/p]`. -/
theorem boundary_arg {p : ℝ} (hp : 2 < p) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ Complex.arg (φM p (Complex.I * τ)) ∧
      Complex.arg (φM p (Complex.I * τ)) ≤ 2 * Real.pi / p := by
  obtain ⟨hm, hg, hn, hd⟩ := ThreeMeanGlobal.consts_pos p hp
  have hp1 : 0 < p - 1 := by linarith
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hgap := gn_gap hp
  have hgn : 0 < gC p - nC p := by
    by_contra h
    have h' : gC p - nC p ≤ 0 := le_of_not_gt h
    nlinarith
  have hσ2 : 2 ≤ τ + 1 / τ := by
    have e : τ + 1 / τ - 2 = (τ - 1) ^ 2 / τ := by
      field_simp
      ring
    have : 0 ≤ (τ - 1) ^ 2 / τ := by positivity
    linarith
  have hqgen : qM p (Complex.I * τ) = (mC p : ℂ) * (1 + ((-(τ ^ 2) : ℝ) : ℂ))
      + (gC p : ℂ) * (Complex.I * τ) - (nC p : ℂ) * RM p (Complex.I * τ) := by
    unfold qM
    rw [I_mul_sq]
  rcases boundary_R hp hτ with ⟨r, hr0, hr, hR⟩ | ⟨ρ, hρ0, hρ, hτ1, hR⟩ | ⟨ρ, hρ0, hρ, hτ1, hR⟩
  · -- between the branch points
    have hq : qM p (Complex.I * τ) = ((mC p * (1 - τ ^ 2) : ℝ) : ℂ)
        + Complex.I * ((τ * (gC p - nC p * r) : ℝ) : ℂ) := by
      rw [hqgen, hR]
      push_cast
      ring
    rw [φM_boundary_form p hq]
    obtain ⟨hpos, h4⟩ := mid_core p (τ + 1 / τ) r hp hσ2 hr0 hr
    have hr1 : r ≤ 1 := by
      have h : r ^ 2 ≤ 1 := by
        rw [hr]
        nlinarith [mul_pos hd (by positivity : (0 : ℝ) < (τ + 1 / τ) ^ 2)]
      nlinarith
    have hgr : 0 < gC p - nC p * r := by nlinarith
    have e : ((p - 1) * (mC p * (1 - τ ^ 2)) - τ ^ 2) * (1 + (p - 1) * (mC p * (1 - τ ^ 2)))
          + ((p - 1) * (τ * (gC p - nC p * r))) ^ 2
        = τ ^ 2 * (((p - 1) * (gC p - nC p * r)) ^ 2
          + ((p - 1) ^ 2 * mC p ^ 2 + (p - 1) * mC p) * ((τ + 1 / τ) ^ 2 - 4) - 1) := by
      field_simp
      ring
    have e2 : (p - 1) * (τ * (gC p - nC p * r)) * (1 + τ ^ 2)
        = τ ^ 2 * (((p - 1) * (gC p - nC p * r)) * (τ + 1 / τ)) := by
      field_simp
      ring
    apply arg_bounds_of hp (by positivity)
    · rw [e]
      exact mul_pos (by positivity) hpos
    · intro hp4
      rw [e, e2]
      have := mul_le_mul_of_nonneg_left (h4 hp4) (sq_nonneg τ)
      linarith
  · -- below the lower branch point
    have hq : qM p (Complex.I * τ) = ((mC p * (1 - τ ^ 2) - nC p * (τ * ρ) : ℝ) : ℂ)
        + Complex.I * ((τ * gC p : ℝ) : ℂ) := by
      rw [hqgen, hR]
      push_cast
      ring
    rw [φM_boundary_form p hq]
    have hΔ0 : 0 ≤ (1 - τ ^ 2) / τ := div_nonneg (by nlinarith) hτ.le
    have hΔ : ((1 - τ ^ 2) / τ) ^ 2 = (τ + 1 / τ) ^ 2 - 4 := by
      field_simp
      ring
    obtain ⟨-, hpos, h4⟩ := out_core p (τ + 1 / τ) ((1 - τ ^ 2) / τ) ρ hp hΔ0 hρ0 hΔ hρ
    have e : ((p - 1) * (mC p * (1 - τ ^ 2) - nC p * (τ * ρ)) - τ ^ 2)
          * (1 + (p - 1) * (mC p * (1 - τ ^ 2) - nC p * (τ * ρ)))
          + ((p - 1) * (τ * gC p)) ^ 2
        = τ ^ 2 * (((p - 1) * gC p) ^ 2 - 1
          + ((p - 1) * (mC p * ((1 - τ ^ 2) / τ) - nC p * ρ)) ^ 2
          + (p - 1) * (mC p * ((1 - τ ^ 2) / τ) - nC p * ρ) * ((1 - τ ^ 2) / τ)) := by
      field_simp
      ring
    have e2 : (p - 1) * (τ * gC p) * (1 + τ ^ 2)
        = τ ^ 2 * (((p - 1) * gC p) * (τ + 1 / τ)) := by
      field_simp
      ring
    apply arg_bounds_of hp (by positivity)
    · rw [e]
      exact mul_pos (by positivity) hpos
    · intro hp4
      rw [e, e2]
      have := mul_le_mul_of_nonneg_left (h4 hp4) (sq_nonneg τ)
      linarith
  · -- above the upper branch point
    have hq : qM p (Complex.I * τ) = ((mC p * (1 - τ ^ 2) + nC p * (τ * ρ) : ℝ) : ℂ)
        + Complex.I * ((τ * gC p : ℝ) : ℂ) := by
      rw [hqgen, hR]
      push_cast
      ring
    rw [φM_boundary_form p hq]
    have hΔ0 : 0 ≤ (τ ^ 2 - 1) / τ := div_nonneg (by nlinarith) hτ.le
    have hΔ : ((τ ^ 2 - 1) / τ) ^ 2 = (τ + 1 / τ) ^ 2 - 4 := by
      field_simp
      ring
    obtain ⟨-, hpos, h4⟩ := out_core p (τ + 1 / τ) ((τ ^ 2 - 1) / τ) ρ hp hΔ0 hρ0 hΔ hρ
    have e : ((p - 1) * (mC p * (1 - τ ^ 2) + nC p * (τ * ρ)) - τ ^ 2)
          * (1 + (p - 1) * (mC p * (1 - τ ^ 2) + nC p * (τ * ρ)))
          + ((p - 1) * (τ * gC p)) ^ 2
        = τ ^ 2 * (((p - 1) * gC p) ^ 2 - 1
          + ((p - 1) * (mC p * ((τ ^ 2 - 1) / τ) - nC p * ρ)) ^ 2
          + (p - 1) * (mC p * ((τ ^ 2 - 1) / τ) - nC p * ρ) * ((τ ^ 2 - 1) / τ)) := by
      field_simp
      ring
    have e2 : (p - 1) * (τ * gC p) * (1 + τ ^ 2)
        = τ ^ 2 * (((p - 1) * gC p) * (τ + 1 / τ)) := by
      field_simp
      ring
    apply arg_bounds_of hp (by positivity)
    · rw [e]
      exact mul_pos (by positivity) hpos
    · intro hp4
      rw [e, e2]
      have := mul_le_mul_of_nonneg_left (h4 hp4) (sq_nonneg τ)
      linarith

/-! ## The slit-plane theorem -/

/-- **Slit-plane theorem for the three-mean support.** For every real `p > 2` and every `z` with
`Re z > 0`, the map `S z = z * exp (-(p / 2) * log (φ z))` contracts the Cayley coordinate with
exponent nine. With `z = sqrt t`, `S z` is the square root of the updated residual, and the
statement covers every residual `t` off the negative axis. -/
theorem three_mean_slit_contraction (p : ℝ) (hp : 2 < p) (z : ℂ) (hz : 0 < z.re) :
    ‖(Tmap (p / 2) (φM p) z - 1) / (Tmap (p / 2) (φM p) z + 1)‖ ≤ ‖(z - 1) / (z + 1)‖ ^ 9 := by
  have hp2 : 0 < p / 2 := by linarith
  refine halfplane_contraction_of_quadrant (p / 2) 9 (φM p)
    (fun _ h => φM_differentiableAt hp h) (fun _ h h0 => φM_continuousWithinAt hp h h0)
    (fun _ h h0 => φM_mem hp h h0) (fun _ h => φM_conj hp h) ?_ ?_ (slit_order hp) z hz
  · intro y hy
    exact ⟨ThreeMeanGlobal.correction p (y ^ 2),
      ThreeMeanGlobal.correction_positive p (y ^ 2) hp (by positivity), φM_ofReal hp hy⟩
  · intro y hy
    obtain ⟨h0, h1⟩ := boundary_arg hp hy
    apply upper_of_arg hp2 h0
    have e : Real.pi / (p / 2) = 2 * Real.pi / p := by
      field_simp
    rw [e]
    exact h1

/-- The right half-plane is invariant under `S`. -/
theorem three_mean_slit_invariant (p : ℝ) (hp : 2 < p) (z : ℂ) (hz : 0 < z.re) :
    0 < (Tmap (p / 2) (φM p) z).re := by
  have hp2 : 0 < p / 2 := by linarith
  have hcore := (halfplane_core_of_quadrant (p / 2) (φM p)
    (fun _ h => φM_differentiableAt hp h) (fun _ h h0 => φM_continuousWithinAt hp h h0)
    (fun _ h h0 => φM_mem hp h h0) (fun _ h => φM_conj hp h)
    (fun y hy => ⟨ThreeMeanGlobal.correction p (y ^ 2),
      ThreeMeanGlobal.correction_positive p (y ^ 2) hp (by positivity), φM_ofReal hp hy⟩)
    (fun y hy => by
      obtain ⟨h0, h1⟩ := boundary_arg hp hy
      apply upper_of_arg hp2 h0
      have e : Real.pi / (p / 2) = 2 * Real.pi / p := by field_simp
      rw [e]
      exact h1)).2 z hz
  have h := three_mean_slit_contraction p hp z hz
  have hlt : ‖(z - 1) / (z + 1)‖ ^ 9 < 1 :=
    pow_lt_one₀ (norm_nonneg _) (cayley_norm_lt_one z hz) (by norm_num)
  set S := Tmap (p / 2) (φM p) z with hS
  have hn : ‖(S - 1) / (S + 1)‖ < 1 := lt_of_le_of_lt h hlt
  rcases hcore.eq_or_lt with h0 | h0
  · exfalso
    have h1 : S + 1 ≠ 0 := by
      intro h1
      have := congrArg Complex.re h1
      simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at this
      linarith
    rw [norm_div, div_lt_one (norm_pos_iff.mpr h1)] at hn
    have h2 : ‖S + 1‖ ^ 2 = ‖S - 1‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im, Complex.one_re,
        Complex.one_im]
      rw [← h0]
      ring
    have h3 := pow_lt_pow_left₀ hn (norm_nonneg _) two_ne_zero
    linarith
  · exact h0

/-- The square of `S` is the residual update `t ↦ t exp (-p log φ)` with `t = z²`. -/
theorem slit_residual (p : ℝ) (φ : ℂ → ℂ) (z : ℂ) :
    Tmap (p / 2) φ z ^ 2 = z ^ 2 * Complex.exp (-((p : ℂ) * Complex.log (φ z))) := by
  unfold Tmap
  rw [mul_pow, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-! ## The half-plane `Re t > 0`, given the boundary inequality on the imaginary axis -/

/-- The correction as a function of the residual `t`, with `z = sqrt t` principal. -/
def φT (p : ℝ) (t : ℂ) : ℂ := φM p (csqrt t)

theorem mem_slit_of_re {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) : t ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases h : t.im = 0
  · left
    rcases ht.eq_or_lt with h0 | h0
    · exact absurd (Complex.ext h0.symm h) ht0
    · exact h0
  · exact Or.inr h

theorem φT_differentiableAt {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    DifferentiableAt ℂ (φT p) t := by
  have hs := mem_slit_of_re ht ht0
  have h1 : DifferentiableAt ℂ (fun t : ℂ => csqrt t) t :=
    csqrt_differentiableAt differentiableAt_id hs
  exact (φM_differentiableAt hp (csqrt_re_pos hs)).comp t h1

theorem φT_mem {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    φT p t ∈ Complex.slitPlane := by
  have hs := mem_slit_of_re ht ht0
  have hz := csqrt_re_pos hs
  have hz0 : csqrt t ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz
    exact lt_irrefl _ hz
  exact φM_mem hp hz.le hz0

theorem φT_conj {p : ℝ} (hp : 2 < p) {t : ℂ} (ht : 0 ≤ t.re) (ht0 : t ≠ 0) :
    φT p ((starRingEnd ℂ) t) = (starRingEnd ℂ) (φT p t) := by
  have hs := mem_slit_of_re ht ht0
  unfold φT
  rw [csqrt_conj hs, φM_conj hp (csqrt_re_pos hs)]

theorem φT_ofReal {p : ℝ} (hp : 2 < p) {t : ℝ} (ht : 0 < t) :
    φT p (t : ℂ) = ((ThreeMeanGlobal.correction p t : ℝ) : ℂ) := by
  unfold φT
  rw [csqrt_ofReal ht, φM_ofReal hp (Real.sqrt_pos.mpr ht), Real.sq_sqrt ht.le]

/-- The residual map of the three-mean support has contact of order nine at `1`, in `ℂ`. -/
theorem three_mean_order {p : ℝ} (hp : 2 < p) :
    (fun t => Tmap p (φT p) t - 1) =O[𝓝 1] fun t => (t - 1) ^ 9 := by
  refine order_of_real_limit p (by linarith) (φT p) (ThreeMeanGlobal.correction p) 9 (by norm_num)
    (ThreeMeanOrderNine.cM p) ?_ (fun _ ht => φT_ofReal hp ht)
    (fun t ht => ThreeMeanGlobal.correction_positive p t hp ht)
    (ThreeMeanGlobal.correction_one p hp) (ThreeMeanOrderNine.order_nine p hp)
  intro t ht
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at ht
    exact lt_irrefl _ ht
  have h1 := (φT_differentiableAt hp ht.le ht0).clog (φT_mem hp ht.le ht0)
  exact differentiableAt_id.mul ((h1.const_mul (p : ℂ)).neg.cexp)

/-- **Half-plane theorem for the three-mean support**, with the boundary inequality as hypothesis:
if `0 ≤ arg φ (i y) ≤ π / p` for every `y > 0`, then for every `t` with `Re t > 0` the residual map
contracts the Cayley coordinate with exponent nine. -/
theorem three_mean_halfplane_contraction (p : ℝ) (hp : 2 < p)
    (hbdry : ∀ y : ℝ, 0 < y → 0 ≤ Complex.arg (φT p (Complex.I * y)) ∧
      Complex.arg (φT p (Complex.I * y)) ≤ Real.pi / p)
    (t : ℂ) (ht : 0 < t.re) :
    ‖(Tmap p (φT p) t - 1) / (Tmap p (φT p) t + 1)‖ ≤ ‖(t - 1) / (t + 1)‖ ^ 9 := by
  have hp0 : 0 < p := by linarith
  refine halfplane_contraction p 9 (φT p) (fun _ h h0 => φT_differentiableAt hp h h0)
    (fun _ h h0 => φT_mem hp h h0) (fun y hy => upper_of_arg hp0 (hbdry y hy).1 (hbdry y hy).2)
    ?_ (three_mean_order hp) t ht
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
  have hargne : Complex.arg (φT p (Complex.I * y)) ≠ Real.pi := by linarith
  rw [hconj, φT_conj hp hre0 hne, Complex.arg_conj, if_neg hargne]
  have h := upper_of_arg hp0 h0 h1
  rw [abs_le] at h ⊢
  constructor <;> nlinarith [h.1, h.2]

end LeanMath.Papers.ThreeMeanSlitPlane
