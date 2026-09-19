import LeanMath.Papers.RectangleFixedCircle
import LeanMath.Papers.RectangleFastPower
import Mathlib.Topology.Order.MonotoneConvergence

/-! A polynomial residual gate and a safeguarded fixed-circle/AD iteration.
The global convergence theorem does not assume convergence of the candidate.
Geometric incidence, scalar convergence, and inherited local order are separate.
-/
noncomputable section
namespace LeanMath.Papers.RectangleCircleSafeguard
open Filter Set Function
open scoped Topology
open RectangleReports
attribute [local instance] Classical.propDecidable

/-- Three order comparisons after constructing u² and t*u². -/
def Gate (t u : ℝ) : Prop :=
  (t ≤ 1 ∧ t ≤ u^2 ∧ t*u^2 ≤ 1) ∨
  (1 ≤ t ∧ u^2 ≤ t ∧ 1 ≤ t*u^2)

theorem gate_log_bound (t u : ℝ) (ht : 0<t) (hu : 0<u) (hg : Gate t u) :
    |Real.log u| ≤ |Real.log t|/2 := by
  have hu2 : 0<u^2 := sq_pos_of_pos hu
  have hprod : 0<t*u^2 := mul_pos ht hu2
  have hlogprod : Real.log (t*u^2)=Real.log t+2*Real.log u := by
    rw [Real.log_mul ht.ne' hu2.ne', Real.log_pow]; norm_num
  rcases hg with ⟨ht1,hlo,hhi⟩ | ⟨ht1,hhi,hlo⟩
  · have hl := Real.log_le_log ht hlo
    have hh := Real.log_le_log hprod hhi
    rw [Real.log_pow] at hl
    rw [hlogprod, Real.log_one] at hh
    have hlt : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
    rw [abs_of_nonpos hlt]
    apply abs_le.mpr
    constructor <;> norm_num at hl <;> linarith
  · have hh := Real.log_le_log hu2 hhi
    have hl := Real.log_le_log (by norm_num : (0:ℝ)<1) hlo
    rw [Real.log_pow] at hh
    rw [hlogprod, Real.log_one] at hl
    have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1
    rw [abs_of_nonneg hlt]
    apply abs_le.mpr
    constructor <;> norm_num at hh <;> linarith

theorem gate_of_log_bound (t u : ℝ) (ht : 0<t) (hu : 0<u)
    (hg : |Real.log u| ≤ |Real.log t|/2) : Gate t u := by
  have hu2 : 0<u^2 := sq_pos_of_pos hu
  have hprod : 0<t*u^2 := mul_pos ht hu2
  have hlogprod : Real.log (t*u^2)=Real.log t+2*Real.log u := by
    rw [Real.log_mul ht.ne' hu2.ne', Real.log_pow]; norm_num
  by_cases h : t ≤ 1
  · rw [abs_of_nonpos (Real.log_nonpos ht.le h)] at hg
    obtain ⟨hl,hh⟩ := abs_le.mp hg
    left; refine ⟨h,?_,?_⟩
    · apply (Real.log_le_log_iff ht hu2).mp
      rw [Real.log_pow]; norm_num; linarith
    · apply (Real.log_le_log_iff hprod (by norm_num)).mp
      rw [hlogprod,Real.log_one]; linarith
  · have h' : 1 ≤ t := le_of_not_ge h
    rw [abs_of_nonneg (Real.log_nonneg h')] at hg
    obtain ⟨hl,hh⟩ := abs_le.mp hg
    right; refine ⟨h',?_,?_⟩
    · apply (Real.log_le_log_iff hu2 ht).mp
      rw [Real.log_pow]; norm_num; linarith
    · apply (Real.log_le_log_iff (by norm_num) hprod).mp
      rw [hlogprod,Real.log_one]; linarith

theorem gate_iff_log (t u : ℝ) (ht : 0<t) (hu : 0<u) :
    Gate t u ↔ |Real.log u| ≤ |Real.log t|/2 :=
  ⟨gate_log_bound t u ht hu,gate_of_log_bound t u ht hu⟩

/-- A general switching theorem. Accepted moves halve a nonnegative error;
all other moves use a globally convergent fallback that never increases it. -/
theorem switching_error_converges (f b E : ℝ → ℝ) (s₀ : ℝ) (hs₀ : 0<s₀)
    (hfpos : ∀ s, 0<s → 0<f s)
    (hEnonneg : ∀ s, 0<s → 0≤E s)
    (hbdown : ∀ s, 0<s → E (b s) ≤ E s)
    (hbconv : ∀ s, 0<s → Tendsto (fun n : ℕ => E (b^[n] s)) atTop (𝓝 0))
    (hchoice : ∀ s, 0<s → f s=b s ∨ E (f s) ≤ E s/2) :
    Tendsto (fun n : ℕ => E (f^[n] s₀)) atTop (𝓝 0) := by
  let x : ℕ → ℝ := fun n => f^[n] s₀
  have hx : ∀ n, 0<x n := by
    intro n; induction n with
    | zero => exact hs₀
    | succ n ih =>
      change 0 < f^[n+1] s₀
      rw [iterate_succ_apply']
      exact hfpos _ ih
  have hstep : ∀ n, x (n+1)=f (x n) := fun n => iterate_succ_apply' f n s₀
  have hm : Antitone (fun n => E (x n)) := by
    apply antitone_nat_of_succ_le
    intro n; rw [hstep]
    rcases hchoice _ (hx n) with hh | hh
    · rw [hh]; exact hbdown _ (hx n)
    · linarith [hEnonneg _ (hx n)]
  have hb : BddBelow (range (fun n => E (x n))) := ⟨0,by
    rintro _ ⟨n,rfl⟩; exact hEnonneg _ (hx n)⟩
  let ell := ⨅ n, E (x n)
  have ht : Tendsto (fun n => E (x n)) atTop (𝓝 ell) := tendsto_atTop_ciInf hm hb
  have hlow : ∀ n, ell ≤ E (x n) := fun n => ciInf_le hb n
  have hl0 : 0≤ell := le_ciInf (fun n => hEnonneg _ (hx n))
  have heq : ell=0 := by
    by_contra hn
    have hl : 0<ell := lt_of_le_of_ne hl0 (Ne.symm hn)
    have hev : ∀ᶠ n in atTop, E (x n)<3*ell/2 :=
      ht.eventually (Iio_mem_nhds (by linarith : ell<3*ell/2))
    obtain ⟨N,hN⟩ := eventually_atTop.mp hev
    have tail : ∀ n, N≤n → f (x n)=b (x n) := by
      intro n hn
      rcases hchoice _ (hx n) with h | h
      · exact h
      · have hh := hlow (n+1)
        rw [hstep] at hh
        have hu := hN n hn
        linarith
    have orbit : ∀ n, x (n+N)=b^[n] (x N) := by
      intro n; induction n with
      | zero => simp
      | succ n ih =>
        rw [show n+1+N=(n+N)+1 by omega,hstep,tail (n+N) (by omega),ih,
          iterate_succ_apply']
    have hz : Tendsto (fun n => E (x (n+N))) atTop (𝓝 0) := by
      simpa only [orbit] using hbconv (x N) (hx N)
    exact hn (tendsto_nhds_unique (ht.comp (tendsto_add_atTop_nat N)) hz)
  simpa only [heq] using ht

def residual (p : ℕ) (X s : ℝ) := X*s^p
def error (p : ℕ) (X s : ℝ) := |Real.log (residual p X s)|

theorem residual_pos (p : ℕ) (X s : ℝ) (hX : 0<X) (hs : 0<s) :
    0<residual p X s := mul_pos hX (pow_pos hs _)

theorem residual_mono (p : ℕ) (X s z : ℝ) (hX : 0<X) (hs : 0≤s) (hz : s≤z) :
    residual p X s ≤ residual p X z :=
  mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs hz p) hX.le

theorem ad_monotone (p : ℕ) (X : ℝ) (hp : 2≤p) (hX : 0<X) :
    MonotoneOn (ad p X) (Ioi 0) := by
  have hd : ∀ s ∈ Ioi (0:ℝ), HasDerivAt (ad p X)
      (((p:ℝ)^2-1)*(X*s^p-1)^2/((p:ℝ)-1+((p:ℝ)+1)*X*s^p)^2) s := by
    intro s hs
    exact RectangleDynamics.hasDerivAt_ad p X s hp (denominators_pos p X s hp hX hs).2.ne'
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro s hs; exact (hd s hs).continuousAt.continuousWithinAt
  · intro s hs; exact (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
  · intro s hs; rw [(hd s (interior_subset hs)).deriv]
    have hp' : (2:ℝ)≤p := by exact_mod_cast hp
    apply div_nonneg _ (sq_nonneg _)
    apply mul_nonneg _ (sq_nonneg _)
    nlinarith

theorem ad_at_root (p : ℕ) (X a : ℝ) (hp : 2≤p) (hr : residual p X a=1) :
    ad p X a=a := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  change X*a^p=1 at hr
  unfold ad
  rw [show ((p:ℝ)-1)*X*a^p=((p:ℝ)-1)*(X*a^p) by ring,
      show ((p:ℝ)+1)*X*a^p=((p:ℝ)+1)*(X*a^p) by ring,hr]
  have hn : (p:ℝ)-1+((p:ℝ)+1)*1≠0 := by linarith
  apply (div_eq_iff hn).mpr; ring

theorem ad_between (p : ℕ) (X a s : ℝ) (hp : 2≤p) (hX : 0<X)
    (ha : 0<a) (hs : 0<s) (hr : residual p X a=1) :
    min s a ≤ ad p X s ∧ ad p X s ≤ max s a := by
  have hd := (denominators_pos p X s hp hX hs).2
  have hm := ad_monotone p X hp hX
  have hf := ad_at_root p X a hp hr
  by_cases hsa : s≤a
  · have ht : X*s^p≤1 := (residual_mono p X s a hX hs.le hsa).trans_eq hr
    rw [min_eq_left hsa,max_eq_right hsa]
    constructor
    · apply (le_div_iff₀ hd).mpr
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr ht)]
    · simpa only [hf] using hm hs ha hsa
  · have has : a≤s := le_of_not_ge hsa
    have ht : 1≤X*s^p := by
      have hh := residual_mono p X a s hX ha.le has
      rw [hr] at hh; exact hh
    rw [min_eq_right has,max_eq_left has]
    constructor
    · simpa only [hf] using hm ha hs has
    · apply (div_le_iff₀ hd).mpr
      nlinarith [mul_nonneg hs.le (sub_nonneg.mpr ht)]

theorem log_abs_between (t u : ℝ) (ht : 0<t) (hu : 0<u)
    (hb : min t 1≤u ∧ u≤max t 1) : |Real.log u|≤|Real.log t| := by
  by_cases h : t≤1
  · rw [min_eq_left h,max_eq_right h] at hb
    have hlt := Real.log_nonpos ht.le h
    have hlu := Real.log_nonpos hu.le hb.2
    have hh := Real.log_le_log ht hb.1
    rw [abs_of_nonpos hlt,abs_of_nonpos hlu]; linarith
  · have h' : 1≤t := le_of_not_ge h
    rw [min_eq_right h',max_eq_left h'] at hb
    rw [abs_of_nonneg (Real.log_nonneg h'),abs_of_nonneg (Real.log_nonneg hb.1)]
    exact Real.log_le_log hu hb.2

def root (p : ℕ) (X : ℝ) := X⁻¹ ^ (1/(p:ℝ))

theorem root_pos (p : ℕ) (X : ℝ) (hX : 0<X) : 0<root p X :=
  Real.rpow_pos_of_pos (inv_pos.mpr hX) _

theorem residual_root (p : ℕ) (X : ℝ) (hp : 2≤p) (hX : 0<X) :
    residual p X (root p X)=1 := by
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  unfold residual root
  rw [← Real.rpow_natCast,one_div,Real.rpow_inv_rpow (inv_nonneg.mpr hX.le) hp0,
    mul_inv_cancel₀ hX.ne']

theorem ad_error_nonincrease (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    error p X (ad p X s) ≤ error p X s := by
  let a := root p X
  have ha : 0<a := root_pos p X hX
  have hr : residual p X a=1 := residual_root p X hp hX
  have hb := ad_between p X a s hp hX ha hs hr
  have had := RectangleDynamics.ad_pos p X s hp hX hs
  apply log_abs_between _ _ (residual_pos p X s hX hs) (residual_pos p X _ hX had)
  by_cases h : s≤a
  · rw [min_eq_left h,max_eq_right h] at hb
    have ht := (residual_mono p X s a hX hs.le h).trans_eq hr
    rw [min_eq_left ht,max_eq_right ht]
    exact ⟨residual_mono p X s _ hX hs.le hb.1,
      (residual_mono p X _ a hX had.le hb.2).trans_eq hr⟩
  · have h' : a≤s := le_of_not_ge h
    rw [min_eq_right h',max_eq_left h'] at hb
    have ht : 1≤residual p X s := by simpa [hr] using residual_mono p X a s hX ha.le h'
    rw [min_eq_right ht,max_eq_left ht]
    exact ⟨by simpa [hr] using residual_mono p X a _ hX ha.le hb.1,
      residual_mono p X _ s hX had.le hb.2⟩

theorem error_continuous (p : ℕ) (X s : ℝ) (hX : 0<X) (hs : 0<s) :
    ContinuousAt (error p X) s := by
  apply ContinuousAt.abs
  apply ContinuousAt.log
  · unfold residual; fun_prop
  · exact (residual_pos p X s hX hs).ne'

theorem ad_error_converges (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => error p X ((ad p X)^[n] s)) atTop (𝓝 0) := by
  have ht := (error_continuous p X (root p X) hX (root_pos p X hX)).tendsto.comp
    (RectangleDynamics.ad_global_convergence p X s hp hX hs)
  simpa only [Function.comp_def,error,residual_root p X hp hX,Real.log_one,abs_zero] using ht

/-- Invalid charts may return any number: nonpositive or failed-gate outputs
are discarded. This keeps the global theorem independent of a candidate oracle. -/
def Accept (p : ℕ) (X : ℝ) (candidate : ℝ → ℝ) (s : ℝ) : Prop :=
  0<candidate s ∧ Gate (residual p X s) (residual p X (candidate s))

def hybrid (p : ℕ) (X : ℝ) (candidate : ℝ → ℝ) (s : ℝ) :=
  if Accept p X candidate s then candidate s else ad p X s

theorem hybrid_pos (p : ℕ) (X : ℝ) (candidate : ℝ → ℝ) (s : ℝ)
    (hp : 2≤p) (hX : 0<X) (hs : 0<s) : 0<hybrid p X candidate s := by
  unfold hybrid; split_ifs with h
  · exact h.1
  · exact RectangleDynamics.ad_pos p X s hp hX hs

theorem accepted_halves_error (p : ℕ) (X : ℝ) (candidate : ℝ → ℝ) (s : ℝ)
    (hX : 0<X) (hs : 0<s) (h : Accept p X candidate s) :
    error p X (candidate s) ≤ error p X s/2 :=
  gate_log_bound _ _ (residual_pos p X s hX hs)
    (residual_pos p X _ hX h.1) h.2

theorem hybrid_error_converges (p : ℕ) (X : ℝ) (candidate : ℝ → ℝ) (s : ℝ)
    (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => error p X ((hybrid p X candidate)^[n] s)) atTop (𝓝 0) := by
  apply switching_error_converges (hybrid p X candidate) (ad p X) (error p X) s hs
  · exact fun z hz => hybrid_pos p X candidate z hp hX hz
  · exact fun z _ => abs_nonneg _
  · exact fun z hz => ad_error_nonincrease p X z hp hX hz
  · exact fun z hz => ad_error_converges p X z hp hX hz
  · intro z hz
    unfold hybrid; split_ifs with h
    · exact Or.inr (accepted_halves_error p X candidate z hX hz h)
    · exact Or.inl rfl

theorem state_from_residual (p : ℕ) (X a s : ℝ) (hp : 2≤p) (hX : 0<X)
    (ha : 0<a) (hs : 0<s) (hr : residual p X a=1) :
    a*Real.exp (Real.log (residual p X s)/(p:ℝ))=s := by
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  have hl (z : ℝ) (hz : 0<z) :
      Real.log (residual p X z)=Real.log X+(p:ℝ)*Real.log z := by
    unfold residual; rw [Real.log_mul hX.ne' (pow_pos hz p).ne',Real.log_pow]
  have hla := hl a ha
  rw [hr,Real.log_one] at hla
  have hls := hl s hs
  have he : Real.log (residual p X s)/(p:ℝ)=Real.log (s/a) := by
    rw [Real.log_div hs.ne' ha.ne']
    apply (div_eq_iff hp0).mpr; nlinarith
  rw [he,Real.exp_log (div_pos hs ha)]
  field_simp

/-- Global convergence for every positive start, regardless of how often the
candidate is unavailable, rejected, discontinuous, or inaccurate. -/
theorem hybrid_global_convergence (p : ℕ) (X : ℝ) (candidate : ℝ → ℝ) (s : ℝ)
    (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => (hybrid p X candidate)^[n] s) atTop (𝓝 (root p X)) := by
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  have hx : ∀ n : ℕ, 0<(hybrid p X candidate)^[n] s := by
    intro n; induction n with
    | zero => exact hs
    | succ n ih => rw [iterate_succ_apply']; exact hybrid_pos p X candidate _ hp hX ih
  have he := hybrid_error_converges p X candidate s hp hX hs
  have hl : Tendsto (fun n : ℕ => Real.log (residual p X ((hybrid p X candidate)^[n] s)))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => le_rfl)
    simpa only [error,Real.norm_eq_abs] using he
  have ht' : Tendsto (fun n : ℕ => root p X * Real.exp
      (Real.log (residual p X ((hybrid p X candidate)^[n] s))/(p:ℝ)))
      atTop (𝓝 (root p X)) := by
    simpa only [Function.comp_def,zero_div,Real.exp_zero,mul_one] using
      ((Real.continuous_exp.continuousAt.tendsto.comp (hl.div_const (p:ℝ))).const_mul (root p X))
  simpa only [state_from_residual p X (root p X) _ hp hX (root_pos p X hX)
    (hx _) (residual_root p X hp hX)] using ht'

/-- The actual inverse-circle branch is totalized by zero outside its real
transverse domain. A chart predicate can reject a geometrically singular output. -/
def circleFactor (p t : ℝ) :=
  if t ≤ 1 then (RectangleFixedCircle.A p-t*RectangleFixedCircle.C p) /
    (RectangleFixedCircle.B p*(1-t)+Real.sqrt (RectangleFixedCircle.delta p t))
  else (Real.sqrt (RectangleFixedCircle.delta p t)-RectangleFixedCircle.B p*(1-t)) /
    (t*RectangleFixedCircle.A p-RectangleFixedCircle.C p)

def circleCandidate (p : ℕ) (X : ℝ) (chart : ℝ → Prop) (s : ℝ) :=
  if 0<RectangleFixedCircle.delta p (residual p X s) ∧ chart s then
    s*circleFactor p (residual p X s) else 0

theorem guarded_circle_global (p : ℕ) (X s : ℝ) (chart : ℝ → Prop)
    (hp : 3≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => (hybrid p X (circleCandidate p X chart))^[n] s)
      atTop (𝓝 (root p X)) :=
  hybrid_global_convergence p X _ s (by omega) hX hs

/-- Order on the vertical number rail is reversed, without a distance or root oracle. -/
theorem rail_order (W H a b : ℝ) (hH : 0<H) :
    (RectangleFastPower.R W H a).2 ≤ (RectangleFastPower.R W H b).2 ↔ b≤a := by
  dsimp [RectangleFastPower.R]
  constructor <;> intro h <;> nlinarith

def railGate (W H : ℝ) (T U : RectangleGeometry.Point) : Prop :=
  let S := RectangleFastPower.geometricMul W H U U
  let V := RectangleFastPower.geometricMul W H T S
  let One := RectangleFastPower.R W H 1
  (One.2≤T.2 ∧ S.2≤T.2 ∧ One.2≤V.2) ∨
  (T.2≤One.2 ∧ T.2≤S.2 ∧ V.2≤One.2)

/-- The geometric gate uses two product constructions and three rail comparisons. -/
theorem geometric_gate_correct (W H t u : ℝ) (hH : 0<H) :
    railGate W H (RectangleFastPower.R W H t) (RectangleFastPower.R W H u) ↔
      Gate t u := by
  dsimp [railGate]
  rw [RectangleFastPower.geometricMul_R W H u u hH.ne',
    RectangleFastPower.geometricMul_R W H t (u*u) hH.ne']
  simp only [rail_order W H _ _ hH,← pow_two]
  rfl

/-- This composes the already checked binary-power incidences with multiplication
by the fixed input X; no p-th root is used to place the residual point. -/
theorem geometric_residual (W H X s : ℝ) (p : ℕ) (hH : H≠0) :
    RectangleFastPower.geometricMul W H (RectangleFastPower.R W H X)
      (RectangleFastPower.geometricPower W H s p) =
      RectangleFastPower.R W H (residual p X s) := by
  rw [RectangleFastPower.geometricPower_eq W H s p hH,
    RectangleFastPower.geometricMul_R W H X (s^p) hH]
  rfl

/-- Any locally superlinear candidate eventually passes the gate on non-root states.
For the inverse circle, its local fifth-order theorem supplies this analytic premise;
the closed-form inverse-function assembly remains a written argument in the paper. -/
theorem eventual_selection (p : ℕ) (X : ℝ) (candidate : ℝ → ℝ) (l : Filter ℝ)
    (hX : 0<X)
    (hpos : ∀ᶠ s in l, 0<s ∧ 0<error p X s ∧ 0<candidate s)
    (hratio : Tendsto (fun s => error p X (candidate s)/error p X s) l (𝓝 0)) :
    ∀ᶠ s in l, hybrid p X candidate s=candidate s := by
  have hh := hratio.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [hpos,hh] with s hs hb
  have he : error p X (candidate s) ≤ error p X s/2 := by
    have hm := (div_lt_iff₀ hs.2.1).mp hb
    linarith
  have hg := gate_of_log_bound _ _ (residual_pos p X s hX hs.1)
    (residual_pos p X _ hX hs.2.2) he
  exact if_pos ⟨hs.2.2,hg⟩

theorem local_order_inherited (p q : ℕ) (X a c : ℝ) (candidate : ℝ → ℝ)
    (heq : ∀ᶠ s in 𝓝[≠] a, hybrid p X candidate s=candidate s)
    (horder : Tendsto (fun s => (candidate s-a)/(s-a)^q) (𝓝[≠] a) (𝓝 c)) :
    Tendsto (fun s => (hybrid p X candidate s-a)/(s-a)^q) (𝓝[≠] a) (𝓝 c) := by
  apply horder.congr'
  filter_upwards [heq] with s hs
  rw [hs]

open RectangleGeometry RectanglePencils

def toLeft (W H f : ℝ) (P : Point) := meet (join (hub W H f) P) (vertical 0)
def toRight (W H f : ℝ) (P : Point) := meet (join (hub W H f) P) (vertical W)

theorem toLeft_right (W H f q : ℝ) (hW : W≠0) (hf : f-1≠0) :
    toLeft W H f (right W H q)=left H (q*f) := by
  apply multiply_unique W H q f hW hf
  apply meet_on
  rw [multiply_det W H q f hf]
  exact div_ne_zero hW hf

theorem toRight_left (W H f q : ℝ) (hW : W≠0) (hf : f-1≠0) (hf0 : f≠0) :
    toRight W H f (left H q)=right W H (q/f) := by
  apply divide_unique W H q f hW hf hf0
  apply meet_on
  dsimp [RectangleGeometry.join,hub,left,vertical]
  simpa using div_ne_zero (mul_ne_zero hW hf0) hf

def rulerMul (W H : ℝ) (P Q : Point) :=
  if Q=(W,0) then P else
    let V := meet (join (0,0) Q) (horizontal H)
    let L := toLeft W H (1/2) P
    let Z := meet (join V L) (vertical W)
    toRight W H (1/4) (toLeft W H (1/2) Z)

/-- Five joins when b≠1; the exact identity b=1 reuses the input point.
The two fixed centers have factors 1/2 and 1/4. -/
theorem rulerMul_correct (W H a b : ℝ) (hW : W≠0) (hH : H≠0) (hb : 0<b) :
    rulerMul W H (right W H a) (right W H b)=right W H (a*b) := by
  by_cases hb1 : b=1
  · subst b; simp [rulerMul,right]
  have hn : right W H b≠(W,0) := by
    intro h; have hh := congrArg Prod.snd h
    dsimp [right] at hh
    exact hb1 (by rcases mul_eq_zero.mp hh with h | h; exact False.elim (hH h); linarith)
  have hi : 1/b-1≠0 := by
    intro h; apply hb1
    have : 1/b=1 := by linarith
    have hh := (div_eq_iff hb.ne').mp this
    linarith
  have hv : meet (join (0,0) (right W H b)) (horizontal H)=hub W H (1/b) := by
    apply intersection_unique _ _ _ _ _ (meet_on _ _ _) ?_
    · simpa [RectangleGeometry.join,right,horizontal] using
        neg_ne_zero.mpr (mul_ne_zero hH (sub_ne_zero.mpr (Ne.symm hb1)))
    · simpa [RectangleGeometry.join,right,horizontal] using
        neg_ne_zero.mpr (mul_ne_zero hH (sub_ne_zero.mpr (Ne.symm hb1)))
    · exact ⟨by simpa [left] using chain_center W H b hb.ne' hb1,hub_on_top W H (1/b)⟩
  unfold rulerMul
  rw [if_neg hn,hv,toLeft_right W H (1/2) a hW (by norm_num)]
  change toRight W H (1/4) (toLeft W H (1/2)
    (toRight W H (1/b) (left H (a*(1/2)))))=right W H (a*b)
  rw [toRight_left W H (1/b) _ hW hi (one_div_ne_zero hb.ne'),
    toLeft_right W H (1/2) _ hW (by norm_num),
    toRight_left W H (1/4) _ hW (by norm_num) (by norm_num)]
  congr 1
  field_simp; ring

/-- A positive prepared scale is two joins, with both centers finite. -/
def rulerScale (W H c : ℝ) (P : Point) :=
  toRight W H (1/(2*(1+c))) (toLeft W H (c/(2*(1+c))) P)

theorem rulerScale_correct (W H c q : ℝ) (hW : W≠0) (hc : 0<c) :
    rulerScale W H c (right W H q)=right W H (c*q) := by
  have hd : 0<2*(1+c) := by positivity
  have hf : c/(2*(1+c))-1≠0 := by
    have : c/(2*(1+c))<1 := (div_lt_one hd).mpr (by linarith)
    linarith
  have hg : 1/(2*(1+c))-1≠0 := by
    have : 1/(2*(1+c))<1 := (div_lt_one hd).mpr (by linarith)
    linarith
  unfold rulerScale
  rw [toLeft_right W H _ q hW hf,toRight_left W H _ _ hW hg (one_div_ne_zero hd.ne')]
  congr 1
  field_simp

/-- Binary powers made entirely of ruler-only product gadgets. -/
def rulerPower (W H s : ℝ) (n : ℕ) : Point :=
  if n=0 then right W H 1 else if n=1 then right W H s else
    let Q := rulerPower W H s (n/2)
    let Q₂ := rulerMul W H Q Q
    if n%2=0 then Q₂ else rulerMul W H (right W H s) Q₂
termination_by n

theorem rulerPower_correct (W H s : ℝ) (n : ℕ) (hW : W≠0) (hH : H≠0) (hs : 0<s) :
    rulerPower W H s n=right W H (s^n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [rulerPower]
    by_cases h0 : n=0
    · simp [h0]
    rw [if_neg h0]
    by_cases h1 : n=1
    · simp [h1]
    rw [if_neg h1,ih (n/2) (Nat.div_lt_self (by omega) (by omega))]
    dsimp only
    rw [rulerMul_correct W H _ _ hW hH (pow_pos hs _)]
    have hmod := Nat.mod_lt n (by norm_num : 0<2)
    split_ifs with he
    · congr 1; rw [← pow_add]; congr 1; omega
    · rw [rulerMul_correct W H _ _ hW hH (mul_pos (pow_pos hs _) (pow_pos hs _)),
        ← pow_add,← pow_succ']
      congr 2; omega

theorem ruler_residual_correct (W H X s : ℝ) (p : ℕ)
    (hW : W≠0) (hH : H≠0) (hX : 0<X) (hs : 0<s) :
    rulerScale W H X (rulerPower W H s p)=right W H (residual p X s) := by
  rw [rulerPower_correct W H s p hW hH hs,rulerScale_correct W H X _ hW hX]
  rfl

def rulerRailGate (W H : ℝ) (T U : Point) : Prop :=
  let S := rulerMul W H U U
  let V := rulerMul W H T S
  let One := right W H 1
  (One.2≤T.2 ∧ S.2≤T.2 ∧ One.2≤V.2) ∨
  (T.2≤One.2 ∧ T.2≤S.2 ∧ V.2≤One.2)

/-- At most ten moving joins and three rail-order comparisons certify the gate,
after the two residual points are available. Product identity tests are separate. -/
theorem ruler_gate_correct (W H t u : ℝ) (hW : W≠0) (hH : 0<H) (hu : 0<u) :
    rulerRailGate W H (right W H t) (right W H u) ↔ Gate t u := by
  dsimp [rulerRailGate]
  rw [rulerMul_correct W H u u hW hH.ne' hu,
    rulerMul_correct W H t (u*u) hW hH.ne' (mul_pos hu hu)]
  have order (a b : ℝ) : (right W H a).2≤(right W H b).2 ↔ b≤a := rail_order W H a b hH
  simp only [order,←pow_two]
  rfl

def preparedRho (p : ℕ) : ℝ := if p=4 then 1/3 else 1/2
def preparedH (p : ℕ) : ℝ := if p=4 then 13502/7167 else RectangleFixedCircle.centerX p
def preparedJ (p : ℕ) : ℝ := if p=4 then 3328/2389 else RectangleFixedCircle.centerY p

def finiteChart (p : ℕ) (X s : ℝ) : Prop :=
  let v := circleFactor p (residual p X s)
  v≠preparedRho p ∧
    RectangleFixedCircle.dotDir 2 4 (preparedRho p) (preparedH p) (preparedJ p) v≠0

def guardedCircleStep (p : ℕ) (X : ℝ) :=
  hybrid p X (circleCandidate p X (finiteChart p X))

/-- Closed specialization to the prepared circle, including its affine exclusions. -/
theorem fixed_circle_AD_global (p : ℕ) (X s : ℝ) (hp : 3≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => (guardedCircleStep p X)^[n] s) atTop (𝓝 (root p X)) :=
  guarded_circle_global p X s (finiteChart p X) hp hX hs

theorem circleFactor_one (p : ℝ) (hp : 0<p) : circleFactor p 1=1 := by
  have hd : RectangleFixedCircle.delta p 1=(6*p)^2 := by
    unfold RectangleFixedCircle.delta; ring
  have hs : Real.sqrt (RectangleFixedCircle.delta p 1)=6*p := by
    rw [hd,Real.sqrt_sq (by positivity)]
  unfold circleFactor
  rw [if_pos (by norm_num),hs]
  have hh : RectangleFixedCircle.A p-1*RectangleFixedCircle.C p=6*p := by
    unfold RectangleFixedCircle.A RectangleFixedCircle.C; ring
  rw [hh]
  simp only [sub_self,mul_zero,zero_add]
  exact div_self (by positivity)

theorem prepared_readout_regular (p : ℕ) (hp : 3≤p) :
    (1:ℝ)≠preparedRho p ∧
    RectangleFixedCircle.dotDir 2 4 (preparedRho p) (preparedH p) (preparedJ p) 1≠0 := by
  by_cases h4 : p=4
  · subst p
    norm_num [preparedRho,preparedH,preparedJ,RectangleFixedCircle.dotDir]
  have hp' : (3:ℝ)≤p := by exact_mod_cast hp
  have hp0 : (0:ℝ)<p := by linarith
  have hL := (RectangleFixedCircle.positive_preparation_scale p hp').1
  have hd : ((p:ℝ)-1)*RectangleFixedCircle.polyL p≠0 :=
    mul_ne_zero (by linarith) hL.ne'
  have hid : RectangleFixedCircle.dotDir 2 4 (1/2)
      (RectangleFixedCircle.centerX p) (RectangleFixedCircle.centerY p) 1 =
      48*(p:ℝ)*((p:ℝ)+4)*((p:ℝ)+1)/(((p:ℝ)-1)*RectangleFixedCircle.polyL p) := by
    unfold RectangleFixedCircle.dotDir RectangleFixedCircle.centerX RectangleFixedCircle.centerY
    field_simp; ring
  simp only [preparedRho,preparedH,preparedJ,if_neg h4]
  constructor
  · norm_num
  · rw [hid]
    exact (div_pos (by positivity) (mul_pos (by linarith) hL)).ne'

theorem finiteChart_at_root (p : ℕ) (X : ℝ) (hp : 3≤p) (hX : 0<X) :
    finiteChart p X (root p X) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  unfold finiteChart
  rw [residual_root p X (by omega) hX,circleFactor_one p hp0]
  exact prepared_readout_regular p hp

/-- The controller can be expressed entirely by the two ruler-product gadgets. -/
theorem ruler_accept_iff (p : ℕ) (W H X s c : ℝ)
    (hW : W≠0) (hH : 0<H) (hX : 0<X) (hc : 0<c) :
    rulerRailGate W H (right W H (residual p X s)) (right W H (residual p X c)) ↔
      Gate (residual p X s) (residual p X c) :=
  ruler_gate_correct W H _ _ hW hH (residual_pos p X c hX hc)

/-- An executable incidence description of the gate, with both residuals formed
by the ruler-only binary program. The returned state is the candidate or AD. -/
def rulerControlledStep (p : ℕ) (X : ℝ) (candidate : ℝ → ℝ) (s : ℝ) :=
  if 0<candidate s ∧ rulerRailGate 2 4
      (rulerScale 2 4 X (rulerPower 2 4 s p))
      (rulerScale 2 4 X (rulerPower 2 4 (candidate s) p))
  then candidate s else ad p X s

theorem rulerControlledStep_eq (p : ℕ) (X s : ℝ) (candidate : ℝ → ℝ)
    (hX : 0<X) (hs : 0<s) :
    rulerControlledStep p X candidate s=hybrid p X candidate s := by
  by_cases hc : 0<candidate s
  · unfold rulerControlledStep hybrid Accept
    rw [ruler_residual_correct 2 4 X s p (by norm_num) (by norm_num) hX hs,
      ruler_residual_correct 2 4 X (candidate s) p (by norm_num) (by norm_num) hX hc]
    simp only [ruler_accept_iff p 2 4 X s (candidate s) (by norm_num) (by norm_num) hX hc]
    split_ifs <;> rfl
  · simp [rulerControlledStep,hybrid,Accept,hc]

theorem ruler_controlled_global (p : ℕ) (X s : ℝ) (candidate : ℝ → ℝ)
    (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => (rulerControlledStep p X candidate)^[n] s)
      atTop (𝓝 (root p X)) := by
  have hid : ∀ n : ℕ, (rulerControlledStep p X candidate)^[n] s=
      (hybrid p X candidate)^[n] s ∧ 0<(hybrid p X candidate)^[n] s := by
    intro n; induction n with
    | zero => exact ⟨rfl,hs⟩
    | succ n ih =>
      rw [iterate_succ_apply',iterate_succ_apply',ih.1]
      exact ⟨rulerControlledStep_eq p X _ candidate hX ih.2,
        hybrid_pos p X candidate _ hp hX ih.2⟩
  simpa only [(hid _).1] using hybrid_global_convergence p X candidate s hp hX hs

theorem ruler_circle_AD_global (p : ℕ) (X s : ℝ) (hp : 3≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ =>
      (rulerControlledStep p X (circleCandidate p X (finiteChart p X)))^[n] s)
      atTop (𝓝 (root p X)) :=
  ruler_controlled_global p X s _ (by omega) hX hs

end LeanMath.Papers.RectangleCircleSafeguard
