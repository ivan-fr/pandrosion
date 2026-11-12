import LeanMath.Papers.MonotoneIteration
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
The nested-radical cubic Pandrosion update.  The global statements concern
every positive input and positive initial estimate, in exact real arithmetic.
They make no assertion about the general real-degree family or drawing costs.
-/
noncomputable section
namespace LeanMath.Papers.NestedRadicalCubic
open Real Filter Function
open scoped Topology
set_option maxHeartbeats 1000000

def numerator (t : ℝ) : ℝ := t^2 + 52*t + 1
def denominator (t : ℝ) : ℝ := t^2 + 4*t + 1
def inner (t : ℝ) : ℝ := Real.sqrt (numerator t / denominator t)
def radicand (t : ℝ) : ℝ := t + (t-1)^2/108 * inner t
def support (t : ℝ) : ℝ := Real.sqrt (radicand t)
def correction (t : ℝ) : ℝ := (t+2*support t)/(1+2*support t)
def step (X u : ℝ) : ℝ := u * correction (X/u^3)

def certificate (v : ℝ) : ℝ :=
  v^8+10*v^7+55*v^6+268*v^5+466*v^4+268*v^3+55*v^2+10*v+1

theorem numerator_pos (t : ℝ) (ht : 0 < t) : 0 < numerator t := by
  unfold numerator; positivity

theorem denominator_pos (t : ℝ) (ht : 0 < t) : 0 < denominator t := by
  unfold denominator; positivity

theorem inner_pos (t : ℝ) (ht : 0 < t) : 0 < inner t := by
  exact Real.sqrt_pos.2 (div_pos (numerator_pos t ht) (denominator_pos t ht))

theorem inner_square (t : ℝ) (ht : 0 < t) :
    inner t ^ 2 * denominator t = numerator t := by
  have hs := Real.sq_sqrt (div_pos (numerator_pos t ht) (denominator_pos t ht)).le
  change inner t ^ 2 = numerator t / denominator t at hs
  rw [hs]
  exact div_mul_cancel₀ _ (denominator_pos t ht).ne'

theorem radicand_pos (t : ℝ) (ht : 0 < t) : 0 < radicand t := by
  have hk := inner_pos t ht
  unfold radicand
  positivity

theorem support_pos (t : ℝ) (ht : 0 < t) : 0 < support t := by
  exact Real.sqrt_pos.2 (radicand_pos t ht)

theorem support_square (t : ℝ) (ht : 0 < t) : support t ^ 2 = radicand t := by
  exact Real.sq_sqrt (radicand_pos t ht).le

theorem certificate_pos (v : ℝ) (hv : 0 < v) : 0 < certificate v := by
  unfold certificate
  positivity

/-- The positive-polynomial certificate, checked by the kernel via `ring`. -/
theorem polynomial_identity (v : ℝ) :
    (v^2+v+1)^4*numerator (v^3) - 729*v^4*denominator (v^3) =
      (v-1)^6*certificate v := by
  unfold numerator denominator certificate
  ring

theorem inner_comparison (v : ℝ) (hv : 0 < v) (hne : v ≠ 1) :
    27*v^2 < (v^2+v+1)^2 * inner (v^3) := by
  have ht : 0 < v^3 := pow_pos hv _
  have hd := denominator_pos (v^3) ht
  have hk := inner_pos (v^3) ht
  have hs := inner_square (v^3) ht
  have hi :
      (((v^2+v+1)^2*inner (v^3))^2 - (27*v^2)^2) * denominator (v^3) =
        (v-1)^6*certificate v := by
    calc
      _ = (v^2+v+1)^4*(inner (v^3)^2*denominator (v^3)) -
          729*v^4*denominator (v^3) := by ring
      _ = _ := by rw [hs]; exact polynomial_identity v
  have hn : 0 < (v-1)^6 := by
    simpa only [← pow_mul] using pow_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)) 3
  have hp : 0 < (((v^2+v+1)^2*inner (v^3))^2 - (27*v^2)^2) * denominator (v^3) := by
    rw [hi]
    exact mul_pos hn (certificate_pos v hv)
  have hsq : (27*v^2)^2 < ((v^2+v+1)^2*inner (v^3))^2 := by
    exact sub_pos.mp ((mul_pos_iff_of_pos_right hd).mp hp)
  exact (sq_lt_sq₀ (by positivity) (by positivity)).mp hsq

/-- The support lies strictly above the support giving an exact cube root. -/
theorem support_above_ideal (v : ℝ) (hv : 0 < v) (hne : v ≠ 1) :
    (v^2+v)/2 < support (v^3) := by
  have hk := inner_comparison v hv hne
  have hi : radicand (v^3) - ((v^2+v)/2)^2 =
      (v-1)^2/108 * ((v^2+v+1)^2*inner (v^3)-27*v^2) := by
    unfold radicand
    ring
  have hn : 0 < (v-1)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  have hr : ((v^2+v)/2)^2 < radicand (v^3) := by
    apply sub_pos.mp
    rw [hi]
    exact mul_pos (div_pos hn (by norm_num)) (sub_pos.mpr hk)
  exact Real.lt_sqrt_of_sq_lt hr

theorem correction_pos (t : ℝ) (ht : 0 < t) : 0 < correction t := by
  have hq := support_pos t ht
  unfold correction
  positivity

theorem correction_one : correction 1 = 1 := by
  norm_num [correction, support, radicand, inner, numerator, denominator]

theorem correction_above_one (v : ℝ) (hv : 1 < v) :
    1 < correction (v^3) ∧ correction (v^3) < v := by
  have hv0 : 0 < v := by linarith
  have ht : 0 < v^3 := pow_pos hv0 _
  have hq := support_pos (v^3) ht
  have hqi := support_above_ideal v hv0 (ne_of_gt hv)
  have hd : 0 < 1+2*support (v^3) := by positivity
  have hv3 : 1 < v^3 := by nlinarith [sq_nonneg (v-1), mul_pos (by linarith : 0 < v-1) (by positivity : 0 < v^2+v+1)]
  have hi : v*(1+2*support (v^3))-(v^3+2*support (v^3)) =
      (v-1)*(2*support (v^3)-v^2-v) := by ring
  have hi0 : 0 < v*(1+2*support (v^3))-(v^3+2*support (v^3)) := by
    rw [hi]
    exact mul_pos (by linarith) (by linarith)
  constructor
  · exact (lt_div_iff₀ hd).2 (by linarith)
  · exact (div_lt_iff₀ hd).2 (by linarith)

theorem correction_below_one (v : ℝ) (hv : 0 < v) (hv1 : v < 1) :
    v < correction (v^3) ∧ correction (v^3) < 1 := by
  have ht : 0 < v^3 := pow_pos hv _
  have hq := support_pos (v^3) ht
  have hqi := support_above_ideal v hv (ne_of_lt hv1)
  have hd : 0 < 1+2*support (v^3) := by positivity
  have hv3 : v^3 < 1 := by nlinarith [mul_pos (by linarith : 0 < 1-v) (by positivity : 0 < v^2+v+1)]
  have hi : (v^3+2*support (v^3))-v*(1+2*support (v^3)) =
      (1-v)*(2*support (v^3)-v^2-v) := by ring
  have hi0 : 0 < (v^3+2*support (v^3))-v*(1+2*support (v^3)) := by
    rw [hi]
    exact mul_pos (by linarith) (by linarith)
  constructor
  · exact (lt_div_iff₀ hd).2 (by linarith)
  · exact (div_lt_iff₀ hd).2 (by linarith)

theorem continuousAt_inner (t : ℝ) (ht : 0 < t) : ContinuousAt inner t := by
  have hn : ContinuousAt numerator t := by unfold numerator; fun_prop
  have hd : ContinuousAt denominator t := by unfold denominator; fun_prop
  exact (hn.div hd (denominator_pos t ht).ne').sqrt

theorem continuousAt_support (t : ℝ) (ht : 0 < t) : ContinuousAt support t := by
  have hi := continuousAt_inner t ht
  have hr : ContinuousAt radicand t := by unfold radicand; fun_prop
  exact hr.sqrt

theorem continuousAt_correction (t : ℝ) (ht : 0 < t) :
    ContinuousAt correction t := by
  have hq := continuousAt_support t ht
  have hd : 1+2*support t ≠ 0 := by have := support_pos t ht; positivity
  unfold correction
  fun_prop

theorem continuousAt_step (X u : ℝ) (hX : 0 < X) (hu : 0 < u) :
    ContinuousAt (step X) u := by
  have ht : 0 < X/u^3 := div_pos hX (pow_pos hu _)
  have hc := continuousAt_correction (X/u^3) ht
  have hr : ContinuousAt (fun v : ℝ => X/v^3) u := by
    fun_prop (disch := positivity)
  change ContinuousAt (fun v : ℝ => v * correction (X/v^3)) u
  apply ContinuousAt.mul continuousAt_id
  exact ContinuousAt.comp (f := fun v : ℝ => X/v^3) (g := correction) hc hr

theorem step_pos (X u : ℝ) (hX : 0 < X) (hu : 0 < u) : 0 < step X u := by
  exact mul_pos hu (correction_pos _ (div_pos hX (pow_pos hu _)))

theorem step_fixed (X r : ℝ) (hr : 0 < r) (hroot : r^3 = X) :
    step X r = r := by
  have ht : X/r^3=1 := by rw [← hroot]; exact div_self (pow_ne_zero _ hr.ne')
  simp [step, ht, correction_one]

/-- Every point below the root moves strictly upward without crossing it. -/
theorem step_below_root (X r u : ℝ) (hr : 0 < r) (hu : 0 < u)
    (hroot : r^3 = X) (hur : u < r) : u < step X u ∧ step X u < r := by
  have hv : 1 < r/u := (one_lt_div hu).2 hur
  have hc := correction_above_one (r/u) hv
  have ht : X/u^3=(r/u)^3 := by rw [div_pow, hroot]
  have hm : u*(r/u)=r := by field_simp
  unfold step
  rw [ht]
  constructor
  · simpa using mul_lt_mul_of_pos_left hc.1 hu
  · simpa only [hm] using mul_lt_mul_of_pos_left hc.2 hu

/-- Every point above the root moves strictly downward without crossing it. -/
theorem step_above_root (X r u : ℝ) (hr : 0 < r) (hu : 0 < u)
    (hroot : r^3 = X) (hru : r < u) : r < step X u ∧ step X u < u := by
  have hv : 0 < r/u := div_pos hr hu
  have hv1 : r/u < 1 := (div_lt_one hu).2 hru
  have hc := correction_below_one (r/u) hv hv1
  have ht : X/u^3=(r/u)^3 := by rw [div_pow, hroot]
  have hm : u*(r/u)=r := by field_simp
  unfold step
  rw [ht]
  constructor
  · simpa only [hm] using mul_lt_mul_of_pos_left hc.1 hu
  · simpa using mul_lt_mul_of_pos_left hc.2 hu

/-- Global convergence in exact reals, for every positive cubic target and start. -/
theorem global_convergence_to_root (X r u : ℝ) (hr : 0 < r) (hu : 0 < u)
    (hroot : r^3 = X) :
    Tendsto (fun n : ℕ => (step X)^[n] u) atTop (𝓝 r) := by
  have hX : 0 < X := hroot ▸ pow_pos hr _
  apply LeanMath.Papers.Iteration.converge (step X) r u hr hu
  · exact fun t ht => continuousAt_step X t hX ht
  · exact step_fixed X r hr hroot
  · intro t ht htr
    exact step_below_root X r t hr ht hroot htr
  · intro t hrt
    exact step_above_root X r t hr (hr.trans hrt) hroot hrt

/-- Explicit form of the positive-root limit: X^(1/3). -/
theorem global_convergence (X u : ℝ) (hX : 0 < X) (hu : 0 < u) :
    Tendsto (fun n : ℕ => (step X)^[n] u) atTop (𝓝 (X ^ ((3:ℝ)⁻¹))) := by
  apply global_convergence_to_root X (X ^ ((3:ℝ)⁻¹)) u
  · exact Real.rpow_pos_of_pos hX _
  · exact hu
  · exact Real.rpow_inv_natCast_pow hX.le (by norm_num : (3:ℕ) ≠ 0)

theorem cube_root_two (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n : ℕ => (step 2)^[n] u) atTop (𝓝 ((2:ℝ) ^ ((3:ℝ)⁻¹))) := by
  exact global_convergence 2 u (by norm_num) hu

/-! The same certificate gives an exact ninth-order error factorization. -/

def ideal (v : ℝ) : ℝ := (v^2+v)/2
def transfer (v : ℝ) : ℝ := (v^2+v+1)^2 * inner (v^3)
def gapDen (v : ℝ) : ℝ :=
  108 * denominator (v^3) * (transfer v+27*v^2) * (support (v^3)+ideal v)
def errorFactor (v : ℝ) : ℝ :=
  2*v^8*certificate v / ((1+2*support (v^3))*gapDen v)

theorem inner_gap_identity (v : ℝ) (hv : 0 < v) :
    (transfer v ^ 2 - (27*v^2)^2) * denominator (v^3) =
      (v-1)^6*certificate v := by
  have hs := inner_square (v^3) (pow_pos hv _)
  unfold transfer
  calc
    _ = (v^2+v+1)^4*(inner (v^3)^2*denominator (v^3)) -
        729*v^4*denominator (v^3) := by ring
    _ = _ := by rw [hs]; exact polynomial_identity v

theorem support_gap_identity (v : ℝ) (hv : 0 < v) :
    support (v^3)^2 - ideal v ^ 2 =
      (v-1)^2/108 * (transfer v-27*v^2) := by
  rw [support_square (v^3) (pow_pos hv _)]
  unfold radicand ideal transfer
  ring

theorem gapDen_pos (v : ℝ) (hv : 0 < v) : 0 < gapDen v := by
  have ht := pow_pos hv 3
  have hd := denominator_pos (v^3) ht
  have hq := support_pos (v^3) ht
  have hk := inner_pos (v^3) ht
  unfold gapDen transfer ideal
  positivity

theorem gap_factor_identity (v : ℝ) (hv : 0 < v) :
    gapDen v * (support (v^3)-ideal v) = (v-1)^8*certificate v := by
  calc
    _ = 108*denominator (v^3)*(transfer v+27*v^2)*
        (support (v^3)^2-ideal v^2) := by unfold gapDen; ring
    _ = (v-1)^2 * ((transfer v^2-(27*v^2)^2)*denominator (v^3)) := by
      rw [support_gap_identity v hv]
      ring
    _ = _ := by rw [inner_gap_identity v hv]; ring

theorem gap_factor (v : ℝ) (hv : 0 < v) :
    support (v^3)-ideal v = (v-1)^8*certificate v / gapDen v := by
  apply (eq_div_iff (gapDen_pos v hv).ne').2
  simpa only [mul_comm] using gap_factor_identity v hv

/-- Exact error factor, not an interpolated Taylor coefficient. -/
theorem normalized_error_factor (v : ℝ) (hv : 0 < v) :
    correction (v^3)/v-1 = (1/v-1)^9 * errorFactor v := by
  have hd : 1+2*support (v^3) ≠ 0 := by
    have := support_pos (v^3) (pow_pos hv _)
    positivity
  have hg := (gapDen_pos v hv).ne'
  have he : correction (v^3)/v-1 =
      -2*(v-1)*(support (v^3)-ideal v)/(v*(1+2*support (v^3))) := by
    unfold correction ideal
    field_simp
    ring
  rw [he, gap_factor v hv]
  unfold errorFactor
  field_simp [hv.ne', hd, hg]
  ring

theorem relative_error_factor (w : ℝ) (hw : 0 < w) :
    step 1 w-1 = (w-1)^9 * errorFactor (1/w) := by
  have h := normalized_error_factor (1/w) (one_div_pos.mpr hw)
  simpa [step, div_pow, div_eq_mul_inv, mul_comm] using h

theorem errorFactor_one : errorFactor 1 = 7/648 := by
  norm_num [errorFactor, gapDen, transfer, ideal, support, radicand, inner,
    numerator, denominator, certificate]

theorem continuousAt_errorFactor_one : ContinuousAt errorFactor 1 := by
  have hq : ContinuousAt (fun v : ℝ => support (v^3)) 1 := by
    exact ContinuousAt.comp_of_eq (f := fun v : ℝ => v^3) (x := 1) (g := support)
      (continuousAt_support 1 (by norm_num)) (continuousAt_id.pow 3) (by norm_num)
  have hk : ContinuousAt (fun v : ℝ => inner (v^3)) 1 := by
    exact ContinuousAt.comp_of_eq (f := fun v : ℝ => v^3) (x := 1) (g := inner)
      (continuousAt_inner 1 (by norm_num)) (continuousAt_id.pow 3) (by norm_num)
  have hd : ContinuousAt gapDen 1 := by
    unfold gapDen denominator transfer ideal
    fun_prop
  have hn : ContinuousAt (fun v : ℝ => 2*v^8*certificate v) 1 := by
    unfold certificate
    fun_prop
  exact hn.div (by fun_prop) (by
    have h1 : 0 < 1+2*support ((1:ℝ)^3) := by
      have := support_pos 1 (by norm_num)
      norm_num at *
      positivity
    exact (mul_pos h1 (gapDen_pos 1 (by norm_num))).ne')

/-- Exact local order nine, in relative root error. -/
theorem exact_order_nine :
    Tendsto (fun w : ℝ => (step 1 w-1)/(w-1)^9) (𝓝[≠] 1) (𝓝 (7/648)) := by
  have hf : ContinuousAt (fun w : ℝ => errorFactor (1/w)) 1 := by
    exact ContinuousAt.comp_of_eq (f := fun w : ℝ => 1/w) (x := 1) (g := errorFactor)
      continuousAt_errorFactor_one (continuousAt_const.div continuousAt_id (by norm_num))
      (by norm_num)
  have hlimit : Tendsto (fun w : ℝ => errorFactor (1/w)) (𝓝[≠] 1) (𝓝 (7/648)) := by
    simpa [errorFactor_one] using hf.tendsto.mono_left nhdsWithin_le_nhds
  apply hlimit.congr'
  have hpositive : ∀ᶠ w : ℝ in 𝓝[≠] 1, 0 < w :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hpositive, self_mem_nhdsWithin] with w hw hne
  rw [relative_error_factor w hw]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.mpr hne))).symm

/-- Scaling the target and estimate preserves the normalized iteration. -/
theorem scale_step (r w : ℝ) (hr : 0 < r) (hw : 0 < w) :
    step (r^3) (r*w) = r * step 1 w := by
  have ht : r^3/(r*w)^3=1/w^3 := by
    field_simp [hr.ne', hw.ne']
  unfold step
  rw [ht]
  ring

/-- The relative-error order is nine at every positive cubic root. -/
theorem exact_order_nine_at_root (r : ℝ) (hr : 0 < r) :
    Tendsto (fun w : ℝ => (step (r^3) (r*w)/r-1)/(w-1)^9)
      (𝓝[≠] 1) (𝓝 (7/648)) := by
  apply exact_order_nine.congr'
  have hpositive : ∀ᶠ w : ℝ in 𝓝[≠] 1, 0 < w :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_gt_nhds (by norm_num : (0:ℝ) < 1))
  filter_upwards [hpositive] with w hw
  rw [scale_step r w hr hw]
  field_simp [hr.ne']

end LeanMath.Papers.NestedRadicalCubic
