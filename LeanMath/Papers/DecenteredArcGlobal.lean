import LeanMath.Papers.MonotoneIteration
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # Global convergence of the decentered-arc iteration (Theorem 3.1)

The decentered-arc update is written in the direct state `u = 1 / s`:
`u₊ = u * (t + (p-1) q) / (1 + (p-1) q)` with `t = X / u ^ p` and
`q = sqrt (((p-2)(t²+1) + (10p+4) t) / (12 p))`. It is the inverse of the reciprocal-state map of the
paper. For every real `p > 2`, `X > 0` and `u₀ > 0` the iteration converges to `X ^ (1 / p)`,
moving strictly toward the root without crossing it. -/

noncomputable section
namespace LeanMath.Papers.DecenteredArcGlobal
open Real Filter Function Set
open scoped Topology

def rad (p t : ℝ) := ((p-2)*(t^2+1)+(10*p+4)*t)/(12*p)
def radPrime (p t : ℝ) := ((p-2)*(2*t)+(10*p+4))/(12*p)
def N1 (p t : ℝ) := (p-1)*(t^2+1)+(10*p+2)*t
def N2 (p t : ℝ) := (t+1)*(6*p*t-(t-1)^2)
def N3 (p t : ℝ) := (p^2-5*p-2)*(t-1)^2+12*p*(3*p+1)*t
def support (p t : ℝ) := Real.sqrt (rad p t)
def supportPrime (p t : ℝ) := radPrime p t/(2*support p t)
def correction (p t : ℝ) := (t+(p-1)*support p t)/(1+(p-1)*support p t)
def step (p X u : ℝ) := u*correction p (X/u^p)

theorem rad_positive (p t : ℝ) (hp : 2<p) (ht : 0<t) : 0<rad p t := by
  have hp0 : 0<p := by linarith
  have hp2 : 0<p-2 := by linarith
  unfold rad
  positivity

theorem support_positive (p t : ℝ) (hp : 2<p) (ht : 0<t) : 0<support p t :=
  Real.sqrt_pos.mpr (rad_positive p t hp ht)

theorem support_square (p t : ℝ) (hp : 2<p) (ht : 0<t) : support p t^2=rad p t :=
  Real.sq_sqrt (rad_positive p t hp ht).le

theorem N1_positive (p t : ℝ) (hp : 2<p) (ht : 0<t) : 0<N1 p t := by
  have hp0 : 0<p := by linarith
  have hp1 : 0<p-1 := by linarith
  unfold N1
  positivity

/-- Identity (3.4) of the paper. -/
theorem square_identity (p t : ℝ) (hp : 2<p) :
    rad p t*N1 p t^2-N2 p t^2=(p+1)/(12*p)*(t-1)^4*N3 p t := by
  have hp0 : p≠0 := by linarith
  unfold rad N1 N2 N3
  field_simp
  ring

theorem N3_positive (p t : ℝ) (hp : 2<p) (ht : 0<t) (h2 : 0<N2 p t) : 0<N3 p t := by
  have hp0 : 0<p := by linarith
  have hsmall : (t-1)^2<6*p*t := by
    unfold N2 at h2
    have ht1 : 0<t+1 := by linarith
    have := (mul_pos_iff_of_pos_left ht1).mp h2
    linarith
  rcases le_or_gt 0 (p^2-5*p-2) with hc | hc
  · unfold N3
    have h1 : 0≤(p^2-5*p-2)*(t-1)^2 := mul_nonneg hc (sq_nonneg _)
    have h3 : 0<12*p*(3*p+1)*t := by positivity
    linarith
  · have e : N3 p t=6*p^2*(p+1)*t+(p^2-5*p-2)*((t-1)^2-6*p*t) := by unfold N3; ring
    rw [e]
    have h1 : 0<6*p^2*(p+1)*t := by positivity
    have h3 : 0<(p^2-5*p-2)*((t-1)^2-6*p*t) := mul_pos_of_neg_of_neg hc (by linarith)
    linarith

/-- The sign that controls monotonicity: `q N1 > N2` away from `t = 1`. -/
theorem support_barrier (p t : ℝ) (hp : 2<p) (ht : 0<t) (hne : t≠1) :
    0<support p t*N1 p t-N2 p t := by
  have hp0 : 0<p := by linarith
  have hq := support_positive p t hp ht
  have hN1 := N1_positive p t hp ht
  have hqN : 0<support p t*N1 p t := mul_pos hq hN1
  rcases le_or_gt (N2 p t) 0 with h2 | h2
  · linarith
  · have hN3 := N3_positive p t hp ht h2
    have ht4 : 0<(t-1)^4 := by
      have : t-1≠0 := sub_ne_zero.mpr hne
      positivity
    have hsq : N2 p t^2<(support p t*N1 p t)^2 := by
      have hid := square_identity p t hp
      have hpos : 0<(p+1)/(12*p)*(t-1)^4*N3 p t := by positivity
      rw [mul_pow, support_square p t hp ht]
      linarith
    by_contra hcon
    have hle : support p t*N1 p t≤N2 p t := by linarith
    have := mul_le_mul hle hle hqN.le h2.le
    nlinarith

theorem hasDerivAt_rad (p t : ℝ) : HasDerivAt (rad p) (radPrime p t) t := by
  have h1 : HasDerivAt (fun x : ℝ => (p-2)*(x^2+1)+(10*p+4)*x) ((p-2)*(2*t)+(10*p+4)) t := by
    have ha := ((hasDerivAt_pow 2 t).add_const (1:ℝ)).const_mul (p-2)
    have hb := (hasDerivAt_id t).const_mul (10*p+4)
    exact (ha.add hb).congr_deriv (by norm_num)
  exact h1.div_const (12*p)

theorem hasDerivAt_support (p t : ℝ) (hp : 2<p) (ht : 0<t) :
    HasDerivAt (support p) (supportPrime p t) t :=
  (hasDerivAt_rad p t).sqrt (rad_positive p t hp ht).ne'

def logGap (p t : ℝ) :=
  Real.log (t+(p-1)*support p t)-Real.log (1+(p-1)*support p t)-Real.log t/p
def logSlope (p t : ℝ) :=
  (1+(p-1)*supportPrime p t)/(t+(p-1)*support p t)-
    (p-1)*supportPrime p t/(1+(p-1)*support p t)-(1/t)/p

theorem hasDerivAt_logGap (p t : ℝ) (hp : 2<p) (ht : 0<t) :
    HasDerivAt (logGap p) (logSlope p t) t := by
  have hq := support_positive p t hp ht
  have hp1 : 0<p-1 := by linarith
  have hn : 0<t+(p-1)*support p t := by positivity
  have hd : 0<1+(p-1)*support p t := by positivity
  have hder := hasDerivAt_support p t hp ht
  have hh := ((((hasDerivAt_id t).add (hder.const_mul (p-1))).log hn.ne').sub
    (((hasDerivAt_const t (1:ℝ)).add (hder.const_mul (p-1))).log hd.ne')).sub
    ((hasDerivAt_log ht.ne').div_const p)
  convert! hh using 1
  simp [logSlope, id_eq]

/-- Pure algebra: elimination of the radical with `q ^ 2 = R`. -/
theorem numerator_elimination (p t q R R' : ℝ) (h : q^2=R) :
    2*q*(1+(p-1)*q)*((p-1)*t-(p-1)*q)+p*t*(1-t)*(p-1)*R'
      =(p-1)*(q*(2*t-2*(p-1)*R)+((2*(p-1)*t-2)*R+p*t*(1-t)*R')) := by
  linear_combination ((p-1)*(-2+2*(p-1)*t-2*(p-1)*q))*h

theorem coefficient_one (p t : ℝ) (hp : 2<p) :
    2*t-2*(p-1)*rad p t=-((p-2)*N1 p t)/(6*p) := by
  have hp0 : p≠0 := by linarith
  unfold rad N1
  field_simp
  ring

theorem coefficient_two (p t : ℝ) (hp : 2<p) :
    (2*(p-1)*t-2)*rad p t+p*t*(1-t)*radPrime p t=(p-2)*N2 p t/(6*p) := by
  have hp0 : p≠0 := by linarith
  unfold rad radPrime N2
  field_simp
  ring

/-- Identity (3.3) of the paper, in the direct state. -/
theorem slope_identity (p t : ℝ) (hp : 2<p) (ht : 0<t) :
    logSlope p t=
      -((p-1)*(p-2)*(support p t*N1 p t-N2 p t))/
        (12*p^2*t*support p t*(t+(p-1)*support p t)*(1+(p-1)*support p t)) := by
  have hp0 : 0<p := by linarith
  have hp1 : 0<p-1 := by linarith
  have hq := support_positive p t hp ht
  have hn : 0<t+(p-1)*support p t := by positivity
  have hd : 0<1+(p-1)*support p t := by positivity
  have helim := numerator_elimination p t (support p t) (rad p t) (radPrime p t)
    (support_square p t hp ht)
  rw [coefficient_one p t hp] at helim
  have hc2 := coefficient_two p t hp
  have key : 2*support p t*(1+(p-1)*support p t)*((p-1)*t-(p-1)*support p t)
      +p*t*(1-t)*(p-1)*radPrime p t
      =-((p-1)*(p-2)*(support p t*N1 p t-N2 p t))/(6*p) := by
    rw [helim, hc2]
    field_simp
    ring
  have hsp : supportPrime p t=radPrime p t/(2*support p t) := rfl
  rw [eq_div_iff (by positivity)]
  have key2 : radPrime p t=2*support p t*supportPrime p t := by
    rw [hsp]
    field_simp
  rw [key2] at key
  unfold logSlope
  field_simp
  field_simp at key
  linear_combination (p-1)*key

theorem slope_negative (p t : ℝ) (hp : 2<p) (ht : 0<t) (hne : t≠1) :
    logSlope p t<0 := by
  rw [slope_identity p t hp ht]
  have hp0 : 0<p := by linarith
  have hp1 : 0<p-1 := by linarith
  have hp2 : 0<p-2 := by linarith
  have hq := support_positive p t hp ht
  have hb := support_barrier p t hp ht hne
  apply div_neg_of_neg_of_pos
  · exact neg_neg_of_pos (mul_pos (mul_pos hp1 hp2) hb)
  · positivity

theorem support_one (p : ℝ) (hp : 2<p) : support p 1=1 := by
  have hp0 : p≠0 := by linarith
  have h : rad p 1=1 := by
    unfold rad
    field_simp
    ring
  rw [support, h, Real.sqrt_one]

theorem logGap_one (p : ℝ) (hp : 2<p) : logGap p 1=0 := by
  simp [logGap, support_one p hp]

theorem gap_negative_above_one (p t : ℝ) (hp : 2<p) (ht : 1<t) : logGap p t<0 := by
  have hm : StrictAntiOn (logGap p) (Icc 1 t) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 1 t)
    · intro x hx
      exact (hasDerivAt_logGap p x hp (by linarith [hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0<x := by linarith [hx.1]
      rw [(hasDerivAt_logGap p x hp hx0).deriv]
      exact slope_negative p x hp hx0 (by linarith [hx.1])
  simpa only [logGap_one p hp] using hm ⟨le_rfl,ht.le⟩ ⟨ht.le,le_rfl⟩ ht

theorem gap_positive_below_one (p t : ℝ) (hp : 2<p) (ht : 0<t) (ht1 : t<1) :
    0<logGap p t := by
  have hm : StrictAntiOn (logGap p) (Icc t 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc t 1)
    · intro x hx
      exact (hasDerivAt_logGap p x hp (ht.trans_le hx.1)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 := ht.trans hx.1
      rw [(hasDerivAt_logGap p x hp hx0).deriv]
      exact slope_negative p x hp hx0 (by linarith [hx.2])
  simpa only [logGap_one p hp] using hm ⟨le_rfl,ht1.le⟩ ⟨ht1.le,le_rfl⟩ ht1

theorem correction_positive (p t : ℝ) (hp : 2<p) (ht : 0<t) : 0<correction p t := by
  have hq := support_positive p t hp ht
  have hp1 : 0<p-1 := by linarith
  unfold correction
  positivity

theorem logGap_eq (p t : ℝ) (hp : 2<p) (ht : 0<t) :
    logGap p t=Real.log (correction p t)-Real.log t/p := by
  have hq := support_positive p t hp ht
  have hp1 : 0<p-1 := by linarith
  have hn : 0<t+(p-1)*support p t := by positivity
  have hd : 0<1+(p-1)*support p t := by positivity
  unfold logGap correction
  rw [Real.log_div hn.ne' hd.ne']

/-- For `t > 1` the correction lies strictly between `1` and the exact factor `t ^ (1 / p)`. -/
theorem correction_above_one (p t : ℝ) (hp : 2<p) (ht : 1<t) :
    1<correction p t ∧ correction p t<t^(1/p) := by
  have ht0 : 0<t := by linarith
  have hq := support_positive p t hp ht0
  have hp1 : 0<p-1 := by linarith
  have hd : 0<1+(p-1)*support p t := by positivity
  have hc := correction_positive p t hp ht0
  have hg := gap_negative_above_one p t hp ht
  rw [logGap_eq p t hp ht0] at hg
  constructor
  · exact (lt_div_iff₀ hd).2 (by linarith)
  · apply (Real.log_lt_log_iff hc (Real.rpow_pos_of_pos ht0 _)).mp
    rw [Real.log_rpow ht0]
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using sub_neg.mp hg

/-- For `0 < t < 1` the correction lies strictly between `t ^ (1 / p)` and `1`. -/
theorem correction_below_one (p t : ℝ) (hp : 2<p) (ht : 0<t) (ht1 : t<1) :
    t^(1/p)<correction p t ∧ correction p t<1 := by
  have hq := support_positive p t hp ht
  have hp1 : 0<p-1 := by linarith
  have hd : 0<1+(p-1)*support p t := by positivity
  have hc := correction_positive p t hp ht
  have hg := gap_positive_below_one p t hp ht ht1
  rw [logGap_eq p t hp ht] at hg
  constructor
  · apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos ht _) hc).mp
    rw [Real.log_rpow ht]
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using sub_pos.mp hg
  · exact (div_lt_iff₀ hd).2 (by linarith)

theorem correction_one (p : ℝ) (hp : 2<p) : correction p 1=1 := by
  have hp0 : p≠0 := by linarith
  simp [correction, support_one p hp, hp0]

theorem continuousAt_correction (p t : ℝ) (hp : 2<p) (ht : 0<t) :
    ContinuousAt (correction p) t := by
  have hq := support_positive p t hp ht
  have hp1 : 0<p-1 := by linarith
  have hd : 1+(p-1)*support p t≠0 := by positivity
  have hcont := (hasDerivAt_support p t hp ht).continuousAt
  unfold correction
  fun_prop

theorem continuousAt_step (p X u : ℝ) (hp : 2<p) (hX : 0<X) (hu : 0<u) :
    ContinuousAt (step p X) u := by
  have hpow := Real.rpow_pos_of_pos hu p
  have hr : ContinuousAt (fun u : ℝ => X/u^p) u :=
    continuousAt_const.div (continuousAt_id.rpow_const (Or.inr (by linarith))) hpow.ne'
  have hc := continuousAt_correction p (X/u^p) hp (div_pos hX hpow)
  exact continuousAt_id.mul (hc.comp (f := fun v : ℝ => X/v^p) hr)

theorem step_below_root (p X r u : ℝ) (hp : 2<p) (hr : 0<r)
    (hx : r^p=X) (hu : 0<u) (hur : u<r) : u<step p X u ∧ step p X u<r := by
  have hp0 : 0<p := by linarith
  have hru : 1<r/u := (one_lt_div hu).2 hur
  have hres : X/u^p=(r/u)^p := by rw [Real.div_rpow hr.le hu.le,hx]
  have hroot : ((r/u)^p)^(1/p)=r/u := by
    rw [one_div,Real.rpow_rpow_inv (div_pos hr hu).le hp0.ne']
  have hc := correction_above_one p ((r/u)^p) hp (Real.one_lt_rpow hru hp0)
  rw [hroot] at hc
  have hm : u*(r/u)=r := by field_simp
  unfold step
  rw [hres]
  exact ⟨by simpa using mul_lt_mul_of_pos_left hc.1 hu,
    by simpa only [hm] using mul_lt_mul_of_pos_left hc.2 hu⟩

theorem step_above_root (p X r u : ℝ) (hp : 2<p) (hr : 0<r)
    (hx : r^p=X) (hru : r<u) : r<step p X u ∧ step p X u<u := by
  have hp0 : 0<p := by linarith
  have hu := hr.trans hru
  have hq : r/u<1 := (div_lt_one hu).2 hru
  have hq0 := div_pos hr hu
  have hres : X/u^p=(r/u)^p := by rw [Real.div_rpow hr.le hu.le,hx]
  have hroot : ((r/u)^p)^(1/p)=r/u := by
    rw [one_div,Real.rpow_rpow_inv hq0.le hp0.ne']
  have hc := correction_below_one p ((r/u)^p) hp
    (Real.rpow_pos_of_pos hq0 _) (Real.rpow_lt_one hq0.le hq hp0)
  rw [hroot] at hc
  have hm : u*(r/u)=r := by field_simp
  unfold step
  rw [hres]
  exact ⟨by simpa only [hm] using mul_lt_mul_of_pos_left hc.1 hu,
    by simpa using mul_lt_mul_of_pos_left hc.2 hu⟩

/-- Theorem 3.1: global monotone convergence of the decentered-arc iteration for every real
`p > 2`, `X > 0` and `u₀ > 0`. -/
theorem global_convergence (p X u : ℝ) (hp : 2<p) (hX : 0<X) (hu : 0<u) :
    Tendsto (fun n : ℕ => (step p X)^[n] u) atTop (𝓝 (X^(1/p))) := by
  let r := X^(1/p)
  have hr : 0<r := Real.rpow_pos_of_pos hX _
  have hx : r^p=X := by
    dsimp [r]
    rw [one_div,Real.rpow_inv_rpow hX.le (by linarith : p≠0)]
  apply LeanMath.Papers.Iteration.converge (step p X) r u hr hu
  · exact fun t ht => continuousAt_step p X t hp hX ht
  · unfold step
    rw [←hx,div_self (Real.rpow_pos_of_pos hr p).ne',correction_one p hp,mul_one]
  · exact fun t ht htr => step_below_root p X r t hp hr hx ht htr
  · exact fun t htr => step_above_root p X r t hp hr hx htr

/-- The reciprocal state `s = 1 / u` follows the map of the paper,
`s₊ = s (1 + g) / (t + g)` with `t = X s ^ p`. -/
theorem reciprocal_form (p X u : ℝ) (hp : 2<p) (hX : 0<X) (hu : 0<u) :
    1/step p X u=(1/u)*((1+(p-1)*support p (X/u^p))/(X/u^p+(p-1)*support p (X/u^p))) := by
  have ht : 0<X/u^p := div_pos hX (Real.rpow_pos_of_pos hu p)
  have hq := support_positive p (X/u^p) hp ht
  have hp1 : 0<p-1 := by linarith
  have hn : 0<X/u^p+(p-1)*support p (X/u^p) := by positivity
  have hd : 0<1+(p-1)*support p (X/u^p) := by positivity
  unfold step correction
  field_simp

end LeanMath.Papers.DecenteredArcGlobal
