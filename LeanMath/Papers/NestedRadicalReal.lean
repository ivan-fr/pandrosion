import LeanMath.Papers.NestedRadicalRealCertificate
import LeanMath.Papers.MonotoneIteration
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue

/-! The unguarded nested-radical update for every real degree p>2. -/
noncomputable section
namespace LeanMath.Papers.NestedRadicalReal
open Real Filter Function Set
open scoped Topology
open LeanMath.Papers.NestedRadicalRealCertificate
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def a (p : ℝ) := (p-2)/(12*p)
def ell (p w : ℝ) := Real.sqrt (U p w/V p w)
def radial (p w : ℝ) := 1+a p*w*ell p w
def radialPrime (p w : ℝ) :=
  a p*ell p w*(1-base p*(dPoly p-cPoly p)*w/(2*U p w*V p w))
def abar (p w : ℝ) := 1+(p-1)*w*ell p w/(12*p)
def bbar (p w : ℝ) := 1-J p w*w*ell p w/(24*p*U p w*V p w)
def width (t : ℝ) := (t-1)^2/t
def support (p t : ℝ) := Real.sqrt (t*radial p (width t))
def correction (p t : ℝ) := (t+(p-1)*support p t)/(1+(p-1)*support p t)
def step (p X u : ℝ) := u*correction p (X/u^p)

theorem ell_positive (p w : ℝ) (hp : 2<p) (hw : 0≤w) : 0<ell p w := by
  exact Real.sqrt_pos.2 (div_pos (U_positive p w hp hw) (V_positive p w hp hw))

theorem ell_square (p w : ℝ) (hp : 2<p) (hw : 0≤w) :
    ell p w^2*V p w=U p w := by
  have h := Real.sq_sqrt (div_pos (U_positive p w hp hw) (V_positive p w hp hw)).le
  change ell p w^2=U p w/V p w at h
  rw [h]
  exact div_mul_cancel₀ _ (V_positive p w hp hw).ne'

theorem radial_positive (p w : ℝ) (hp : 2<p) (hw : 0≤w) : 0<radial p w := by
  have hl := ell_positive p w hp hw
  have hp0 : 0<p := by linarith
  have hpa : 0<p-2 := by linarith
  unfold radial a
  positivity

theorem abar_positive (p w : ℝ) (hp : 2<p) (hw : 0≤w) : 0<abar p w := by
  have hl := ell_positive p w hp hw
  have hp0 : 0<p := by linarith
  have hp1 : 0<p-1 := by linarith
  unfold abar
  positivity

theorem width_nonneg (t : ℝ) (ht : 0<t) : 0≤width t := by unfold width; positivity
theorem width_positive (t : ℝ) (ht : 0<t) (hne : t≠1) : 0<width t := by
  exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)) ht

theorem support_positive (p t : ℝ) (hp : 2<p) (ht : 0<t) : 0<support p t := by
  exact Real.sqrt_pos.2 (mul_pos ht (radial_positive p (width t) hp (width_nonneg t ht)))

theorem support_square (p t : ℝ) (hp : 2<p) (ht : 0<t) :
    support p t^2=t*radial p (width t) := by
  exact Real.sq_sqrt (mul_pos ht (radial_positive p (width t) hp (width_nonneg t ht))).le

theorem small_squaring (p w : ℝ) (hp : 2<p) (hw : 0<w) (hsmall : w≤30*p) :
    0<K p w+ell p w*V p w^2*M p w := by
  have hu := U_positive p w hp hw.le
  have hv := V_positive p w hp hw.le
  have hl := ell_positive p w hp hw.le
  have hm := M_positive p w hp hw.le
  have hs := ell_square p w hp hw.le
  have hg := squared_positive_small p w hp hw hsmall
  have hi : ((ell p w*V p w^2*M p w)^2-K p w^2)*V p w =
      (V p w^2*M p w)^2*U p w-K p w^2*V p w := by
    calc
      _ = (ell p w^2*V p w)*(V p w^2*M p w)^2-K p w^2*V p w := by ring
      _ = _ := by rw [hs]; ring
  have hsq : K p w^2<(ell p w*V p w^2*M p w)^2 := by
    apply sub_pos.mp
    apply (mul_pos_iff_of_pos_right hv).mp
    rw [hi]
    exact hg
  have hr : 0<ell p w*V p w^2*M p w := by positivity
  have hb : -K p w<ell p w*V p w^2*M p w := by
    by_cases hk : 0≤-K p w
    · apply (sq_lt_sq₀ hk hr.le).mp
      simpa using hsq
    · exact (lt_of_not_ge hk).trans hr
  linarith

theorem core_polynomial_identity (p w : ℝ) (hp : 2<p) (hw : 0≤w) :
    4*U p w^2*V p w^3*(12*p+(p-2)*w*ell p w)*(12*p+(p-1)*w*ell p w)^2-
      3*p*V p w*(4+w)*(24*p*U p w*V p w-J p w*w*ell p w)^2 =
    U p w*w*(K p w+ell p w*V p w^2*M p w) := by
  have hs := ell_square p w hp hw
  unfold K M
  linear_combination
    (48*p*U p w^2*V p w^2*(p-1)*(3*p-5)*w^2-
      3*p*J p w^2*(4+w)*w^2+
      4*U p w^2*V p w^2*(p-2)*(p-1)^2*w^3*ell p w)*hs

theorem normalized_identity (p w : ℝ) (hp : 2<p) (hw : 0≤w) :
    (6912*p^3*U p w^2*V p w^3)*
      (radial p w*abar p w^2-(1+w/4)*bbar p w^2) =
    4*U p w^2*V p w^3*(12*p+(p-2)*w*ell p w)*(12*p+(p-1)*w*ell p w)^2-
      3*p*V p w*(4+w)*(24*p*U p w*V p w-J p w*w*ell p w)^2 := by
  have hp0 : p≠0 := by linarith
  have hu := (U_positive p w hp hw).ne'
  have hv := (V_positive p w hp hw).ne'
  unfold radial a abar bbar
  field_simp
  ring

theorem small_barrier (p w : ℝ) (hp : 2<p) (hw : 0<w) (hsmall : w≤30*p) :
    (1+w/4)*bbar p w^2<radial p w*abar p w^2 := by
  have hi := normalized_identity p w hp hw.le
  rw [core_polynomial_identity p w hp hw.le] at hi
  have hu := U_positive p w hp hw.le
  have hv := V_positive p w hp hw.le
  have hp0 : 0<p := by linarith
  have hr := small_squaring p w hp hw hsmall
  apply sub_pos.mp
  apply (mul_pos_iff_of_pos_left (by positivity : 0<6912*p^3*U p w^2*V p w^3)).mp
  rw [hi]
  positivity

theorem large_barrier (p w : ℝ) (hp : 2<p) (hw : 30*p≤w) : bbar p w<0 := by
  have hp0 : 0<p := by linarith
  have hw0 : 0<w := by linarith
  have hu := U_positive p w hp hw0.le
  have hv := V_positive p w hp hw0.le
  have hl := ell_positive p w hp hw0.le
  have hj := J_positive_large p w hp hw
  have ht := tail_positive_large p w hp hw
  have hs := ell_square p w hp hw0.le
  have hi : ((J p w*w*ell p w)^2-(24*p*U p w*V p w)^2)*V p w =
      U p w*(w^2*J p w^2-576*p^2*U p w*V p w^3) := by
    calc
      _ = (ell p w^2*V p w)*J p w^2*w^2-
          576*p^2*U p w^2*V p w^3 := by ring
      _ = _ := by rw [hs]; ring
  have hsq : (24*p*U p w*V p w)^2<(J p w*w*ell p w)^2 := by
    apply sub_pos.mp
    apply (mul_pos_iff_of_pos_right hv).mp
    rw [hi]
    exact mul_pos hu ht
  have hden : 0<24*p*U p w*V p w := by positivity
  have hnum : 0<J p w*w*ell p w := by positivity
  have hlt := (sq_lt_sq₀ hden.le hnum.le).mp hsq
  have hdiv : 1<J p w*w*ell p w/(24*p*U p w*V p w) := by
    exact (lt_div_iff₀ hden).2 (by simpa using hlt)
  unfold bbar
  linarith

theorem support_barrier (p t : ℝ) (hp : 2<p) (ht : 0<t) (hne : t≠1) :
    0<2*support p t*abar p (width t)-(t+1)*bbar p (width t) := by
  have hw := width_positive t ht hne
  have hq := support_positive p t hp ht
  have ha := abar_positive p (width t) hp hw.le
  by_cases hsmall : width t≤30*p
  · have hb := small_barrier p (width t) hp hw hsmall
    have hs := support_square p t hp ht
    have hwidth : t*width t=(t-1)^2 := by unfold width; field_simp
    have hi : (2*support p t*abar p (width t))^2-((t+1)*bbar p (width t))^2 =
        4*t*(radial p (width t)*abar p (width t)^2-
          (1+width t/4)*bbar p (width t)^2) := by
      linear_combination 4*abar p (width t)^2*hs+bbar p (width t)^2*hwidth
    have hsq : ((t+1)*bbar p (width t))^2<(2*support p t*abar p (width t))^2 := by
      apply sub_pos.mp
      rw [hi]
      positivity
    have hr : 0<2*support p t*abar p (width t) := by positivity
    have hlt : (t+1)*bbar p (width t)<2*support p t*abar p (width t) := by
      by_cases hleft : 0≤(t+1)*bbar p (width t)
      · exact (sq_lt_sq₀ hleft hr.le).mp hsq
      · exact (lt_of_not_ge hleft).trans hr
    linarith
  · have hb := large_barrier p (width t) hp (le_of_not_ge hsmall)
    have hn : (t+1)*bbar p (width t)<0 := mul_neg_of_pos_of_neg (by linarith) hb
    have hr : 0<2*support p t*abar p (width t) := by positivity
    linarith

theorem hasDerivAt_ell (p w : ℝ) (hp : 2<p) (hw : 0≤w) :
    HasDerivAt (ell p) (-base p*(dPoly p-cPoly p)*ell p w/(2*U p w*V p w)) w := by
  have hu := U_positive p w hp hw
  have hv := V_positive p w hp hw
  have hl := ell_positive p w hp hw
  have hs := ell_square p w hp hw
  have hU : HasDerivAt (U p) (cPoly p) w := by
    convert! (hasDerivAt_const w (base p)).add ((hasDerivAt_id w).const_mul (cPoly p)) using 1
    simp
  have hV : HasDerivAt (V p) (dPoly p) w := by
    convert! (hasDerivAt_const w (base p)).add ((hasDerivAt_id w).const_mul (dPoly p)) using 1
    simp
  have hh := (hU.div hV hv.ne').sqrt (div_pos hu hv).ne'
  have hcross : cPoly p*V p w-U p w*dPoly p = -base p*(dPoly p-cPoly p) := by
    unfold U V
    ring
  change HasDerivAt (ell p)
    (((cPoly p*V p w-U p w*dPoly p)/V p w^2)/(2*ell p w)) w at hh
  rw [hcross] at hh
  convert hh using 1
  rw [←hs]
  field_simp [hl.ne', hv.ne']

theorem hasDerivAt_radial (p w : ℝ) (hp : 2<p) (hw : 0≤w) :
    HasDerivAt (radial p) (radialPrime p w) w := by
  have hl := hasDerivAt_ell p w hp hw
  have hu := (U_positive p w hp hw).ne'
  have hv := (V_positive p w hp hw).ne'
  have hh := (hasDerivAt_const w (1:ℝ)).add (((hasDerivAt_id w).const_mul (a p)).mul hl)
  simp only [id_eq] at hh
  change HasDerivAt (radial p) _ w at hh
  convert hh using 1
  unfold radialPrime
  field_simp
  ring

theorem hasDerivAt_width (t : ℝ) (ht : 0<t) :
    HasDerivAt width ((t^2-1)/t^2) t := by
  have hh := (((hasDerivAt_id t).sub_const 1).pow 2).div (hasDerivAt_id t) ht.ne'
  simp only [id_eq, Pi.pow_apply] at hh
  change HasDerivAt width _ t at hh
  convert hh using 1
  field_simp
  ring

def supportPrime (p t : ℝ) :=
  (radial p (width t)+t*radialPrime p (width t)*((t^2-1)/t^2))/(2*support p t)

theorem hasDerivAt_support (p t : ℝ) (hp : 2<p) (ht : 0<t) :
    HasDerivAt (support p) (supportPrime p t) t := by
  have hw := hasDerivAt_width t ht
  have hr := (hasDerivAt_radial p (width t) hp (width_nonneg t ht)).comp t hw
  have hrad : 0<t*radial p (width t) := mul_pos ht (radial_positive p (width t) hp (width_nonneg t ht))
  have hh := ((hasDerivAt_id t).mul hr).sqrt hrad.ne'
  convert! hh using 1
  simp [support, supportPrime, mul_assoc]

theorem abar_relation (p w : ℝ) (hp : 2<p) :
    (p-1)*radial p w-1=(p-2)*abar p w := by
  have hp0 : p≠0 := by linarith
  unfold radial a abar
  field_simp
  ring

theorem bbar_relation (p w : ℝ) (hp : 2<p) (hw : 0≤w) :
    (p-2)*radial p w-p*w*radialPrime p w=(p-2)*bbar p w := by
  have hp0 : p≠0 := by linarith
  have hu := (U_positive p w hp hw).ne'
  have hv := (V_positive p w hp hw).ne'
  unfold radial radialPrime a bbar J
  field_simp
  ring

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

theorem slope_identity (p t : ℝ) (hp : 2<p) (ht : 0<t) :
    logSlope p t = -(p-1)*(p-2)*
      (2*support p t*abar p (width t)-(t+1)*bbar p (width t))/
      (2*p*support p t*(t+(p-1)*support p t)*(1+(p-1)*support p t)) := by
  have hp0 : p≠0 := by linarith
  have hp1 : 0<p-1 := by linarith
  have hq := support_positive p t hp ht
  have hn : 0<t+(p-1)*support p t := by positivity
  have hd : 0<1+(p-1)*support p t := by positivity
  have hh : logSlope p t -
      (-(p-1)*(2*support p t*((p-1)*radial p (width t)-1)-
        (t+1)*((p-2)*radial p (width t)-p*width t*radialPrime p (width t)))/
        (2*p*support p t*(t+(p-1)*support p t)*(1+(p-1)*support p t))) =
      -(p-1)*(support p t^2-t*radial p (width t))*
        (p*support p t-p*t-support p t+t+1)/
        (p*support p t*t*(1+(p-1)*support p t)*(t+(p-1)*support p t)) := by
    unfold logSlope supportPrime width
    field_simp
    ring
  rw [support_square p t hp ht, sub_self, mul_zero, zero_mul, zero_div] at hh
  rw [abar_relation p (width t) hp, bbar_relation p (width t) hp (width_nonneg t ht)] at hh
  have he : logSlope p t =
      -(p-1)*(2*support p t*((p-2)*abar p (width t))-
        (t+1)*((p-2)*bbar p (width t)))/
        (2*p*support p t*(t+(p-1)*support p t)*(1+(p-1)*support p t)) := by linarith
  rw [he]
  ring

theorem slope_negative (p t : ℝ) (hp : 2<p) (ht : 0<t) (hne : t≠1) :
    logSlope p t<0 := by
  rw [slope_identity p t hp ht]
  have hp0 : 0<p := by linarith
  have hp1 : 0<p-1 := by linarith
  have hp2 : 0<p-2 := by linarith
  have hq := support_positive p t hp ht
  have hb := support_barrier p t hp ht hne
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hp1) hp2) hb
  · positivity

theorem logGap_one (p : ℝ) : logGap p 1=0 := by simp [logGap]

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
  simpa only [logGap_one] using hm ⟨le_rfl,ht.le⟩ ⟨ht.le,le_rfl⟩ ht

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
  simpa only [logGap_one] using hm ⟨le_rfl,ht1.le⟩ ⟨ht1.le,le_rfl⟩ ht1

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

theorem support_one (p : ℝ) : support p 1=1 := by
  norm_num [support, width, radial]

theorem correction_one (p : ℝ) (hp : 2<p) : correction p 1=1 := by
  have hp0 : p≠0 := by linarith
  simp [correction, support_one, hp0]

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

/-- Global unguarded convergence for every real p>2, X>0, and u0>0. -/
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

def originalA (p : ℝ) := (1-2/p)/12
def originalB (p : ℝ) := (1/p+1)*(1/p+3)/30
def originalC (p : ℝ) := (121-185/p-67/p^2-1/p^3)/(840*(1/p+3))
def originalInnerRad (p w : ℝ) := 1+originalB p*w/(1+originalC p*w)
def originalSupport (p t : ℝ) :=
  Real.sqrt (t*(1+originalA p*width t/Real.sqrt (originalInnerRad p (width t))))

theorem originalA_eq (p : ℝ) (hp : 2<p) : originalA p=a p := by
  have hp0 : p≠0 := by linarith
  unfold originalA a
  field_simp

theorem originalB_eq (p : ℝ) (hp : 2<p) : originalB p=(dPoly p-cPoly p)/base p := by
  have hp0 : p≠0 := by linarith
  have hp3 : 3*p+1≠0 := by linarith
  unfold originalB dPoly cPoly base
  field_simp
  ring

theorem originalC_eq (p : ℝ) (hp : 2<p) : originalC p=cPoly p/base p := by
  have hp0 : p≠0 := by linarith
  have hp3 : 3*p+1≠0 := by linarith
  have hpc : 1/p+3≠0 := by
    have hp0pos : 0<p := by linarith
    positivity
  unfold originalC cPoly base
  field_simp
  ring

theorem originalInnerRad_eq (p w : ℝ) (hp : 2<p) (hw : 0≤w) :
    originalInnerRad p w=V p w/U p w := by
  have hp0 : 0<p := by linarith
  have he : 0<base p := by unfold base; positivity
  have hc := cPoly_positive p hp
  have hd : 0<1+cPoly p/base p*w := by positivity
  unfold originalInnerRad
  rw [originalB_eq p hp,originalC_eq p hp]
  unfold U V
  field_simp [he.ne',hd.ne']
  ring

/-- This normalized proof concerns exactly the original two-radical formula. -/
theorem originalSupport_eq (p t : ℝ) (hp : 2<p) (ht : 0<t) :
    originalSupport p t=support p t := by
  have hw := width_nonneg t ht
  have hu := U_positive p (width t) hp hw
  have hv := V_positive p (width t) hp hw
  have hi : V p (width t)/U p (width t)=(U p (width t)/V p (width t))⁻¹ := by
    field_simp
  unfold originalSupport
  rw [originalA_eq p hp,originalInnerRad_eq p (width t) hp hw,hi,Real.sqrt_inv]
  simp only [div_inv_eq_mul]
  rfl

/-- The unrestricted original radical is not real for all positive degrees. -/
theorem counterexample_three_halves :
    originalInnerRad (3/2) (width 100) = -15947/25 := by
  norm_num [originalInnerRad, originalB, originalC, width]

theorem no_real_inner_root_three_halves :
    ¬∃ k : ℝ, k^2=originalInnerRad (3/2) (width 100) := by
  rw [counterexample_three_halves]
  rintro ⟨k,hk⟩
  nlinarith [sq_nonneg k]

end LeanMath.Papers.NestedRadicalReal
