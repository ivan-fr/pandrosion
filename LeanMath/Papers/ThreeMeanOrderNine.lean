import LeanMath.Papers.ThreeMeanGlobal
import LeanMath.Papers.NestedOrderNine

/-! # Local order nine of the three-mean iteration

For every real `p > 2` the logarithmic error of the three-mean iteration satisfies
`ê₊ / ê ^ 9 → c_M p = (p²-1)(p²-4)(4p²-1)(17p²+8) / 203212800`.

The proof works in the variable `y = (log t) / 2`, so that `sqrt t = exp y`. The conic radical is
`exp y * sqrt (1 + d w)` with `w = (t-1)² / t`; it is replaced by its quartic Taylor polynomial in
`w` at an algebraic cost `O (w ^ 5)`. What remains is an exponential sum in `exp y` and
`exp (2 h y)`, `h = 1 / p`, with ten vanishing moments. Lemma 2.1 (`contact_limit`) converts contact
of order eight into order nine. -/

noncomputable section
namespace LeanMath.Papers.ThreeMeanOrderNine
open Filter Asymptotics
open scoped Topology
open LeanMath.Papers.ContactLimit
open LeanMath.Papers.NestedOrderNine (monoSum toExp monoSum_eq qStar exp_scaled_ne)
open LeanMath.Papers.ThreeMeanGlobal
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-! ## The coefficients in `h = 1 / p` -/

def mH (h : ℝ) : ℝ := (1-2*h)*(4*h^2+21*h+47)/(60*(4-h^2))
def gH (h : ℝ) : ℝ := 16*(1+h)*(4-h^2)/(15*(4*h^2+5))
def nH (h : ℝ) : ℝ := 49*(1+h)*(1-4*h^2)/(10*(4-h^2)*(4*h^2+5))
def dH (h : ℝ) : ℝ := (4*h^2+5)/84
/-- The first unmatched coefficient: `q_M / sqrt t - q_* / sqrt t = DH h * w ^ 4 + ...`. -/
def DH (h : ℝ) : ℝ := (2-h)*(1+h)*(2+h)*(1-2*h)*(1+2*h)*(8*h^2+17)/203212800

theorem h_bounds (p : ℝ) (hp : 2<p) : 0<1/p ∧ 1/p<1/2 := by
  have hp0 : 0<p := by linarith
  exact ⟨by positivity, one_div_lt_one_div_of_lt (by norm_num) hp⟩

theorem four_sub (p : ℝ) (hp : 2<p) : (4:ℝ)-(1/p)^2=(4*p^2-1)/p^2 := by
  have hp0 : p≠0 := by linarith
  field_simp

theorem mC_h (p : ℝ) (hp : 2<p) : mC p=mH (1/p) := by
  have hp0 : p≠0 := by linarith
  have h4 : 4*p^2-1≠0 := by nlinarith
  unfold mC mH
  rw [four_sub p hp]
  generalize ha : 4*p^2-1=a at h4 ⊢
  field_simp
  ring

theorem gC_h (p : ℝ) (hp : 2<p) : gC p=gH (1/p) := by
  have hp0 : p≠0 := by linarith
  have h4 : 4*p^2-1≠0 := by nlinarith
  unfold gC gH
  rw [four_sub p hp]
  generalize ha : 4*p^2-1=a at h4 ⊢
  field_simp
  ring

theorem nC_h (p : ℝ) (hp : 2<p) : nC p=nH (1/p) := by
  have hp0 : p≠0 := by linarith
  have h4 : 4*p^2-1≠0 := by nlinarith
  unfold nC nH
  rw [four_sub p hp]
  generalize ha : 4*p^2-1=a at h4 ⊢
  field_simp
  ring

theorem dC_h (p : ℝ) (hp : 2<p) : dC p=dH (1/p) := by
  have hp0 : p≠0 := by linarith
  unfold dC dH
  field_simp
  ring

/-! ## Quartic expansion of `sqrt (1 + d w)` -/

def R4 (d w : ℝ) : ℝ := 1+d/2*w-d^2/8*w^2+d^3/16*w^3-5*d^4/128*w^4
def G4 (d w : ℝ) : ℝ := 7*d^5/128-7*d^6/512*w+5*d^7/1024*w^2-25*d^8/16384*w^3

/-- `R4` is the square root of `1 + d w` up to `w ^ 5`. -/
theorem R4_sq (d w : ℝ) : 1+d*w-R4 d w^2=w^5*G4 d w := by
  unfold R4 G4
  ring

/-- The width `w = (t - 1)² / t` at `t = E²`. -/
def wE (E : ℝ) : ℝ := (E^2-1)^2/E^2

theorem root_remainder (p E : ℝ) (hp : 2<p) (hE : 0<E) :
    (root p E-E*R4 (dC p) (wE E))*(root p E+E*R4 (dC p) (wE E))
      =E^2*(wE E^5*G4 (dC p) (wE E)) := by
  have hs := root_sq p E hp hE
  have hr : rad p E=E^2*(1+dC p*wE E) := by
    have hE0 : E≠0 := hE.ne'
    unfold rad wE
    field_simp
  have h5 := R4_sq (dC p) (wE E)
  linear_combination hs+hr+E^2*h5

/-! ## The exponential sum -/

def KH (h : ℝ) : ℝ := 60*(4-h^2)*(4*h^2+5)
def Km (h : ℝ) : ℝ := (1-2*h)*(4*h^2+21*h+47)*(4*h^2+5)
def Kg (h : ℝ) : ℝ := 64*(1+h)*(4-h^2)^2
def Kn (h : ℝ) : ℝ := 294*(1+h)*(1-4*h^2)
/-- `E ^ 9 * R4 d ((E² - 1)² / E²)`, a polynomial in `E`. -/
def E9R4 (d E : ℝ) : ℝ :=
  E^9+d/2*E^7*(E^2-1)^2-d^2/8*E^5*(E^2-1)^4+d^3/16*E^3*(E^2-1)^6-5*d^4/128*E*(E^2-1)^8

/-- The numerator, a polynomial in `E = exp y` and `T = exp (2 h y)`. -/
def NPh (h E T : ℝ) : ℝ :=
  (1-h)*(T-1)*(Km h*(E^8+E^10)+Kg h*E^9-Kn h*E9R4 (dH h) E-KH h*DH h*(E*(E^2-1)^8))
    -KH h*h*E^8*(E^2-T)

/-- Coefficients of `NPh h (exp y) (exp (2 h y))` as an exponential sum. -/
def LM (h : ℝ) : List (ℝ × ℕ × ℕ) :=
  [
    ((h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(192*h^6 + 1072*h^4 + 1108*h^2 - 797)/15482880, 17, 1),
    (-(h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(192*h^6 + 1072*h^4 + 1108*h^2 - 797)/15482880, 17, 0),
    (-(h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(192*h^6 + 2032*h^4 + 3508*h^2 + 703)/1935360, 15, 1),
    ((h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(192*h^6 + 2032*h^4 + 3508*h^2 + 703)/1935360, 15, 0),
    ((h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(1344*h^6 + 19024*h^4 + 117196*h^2 + 113221)/3870720, 13, 1),
    (-(h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(1344*h^6 + 19024*h^4 + 117196*h^2 + 113221)/3870720, 13, 0),
    (-(h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(1344*h^6 + 21904*h^4 + 205036*h^2 + 3605401)/1935360, 11, 1),
    ((h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(1344*h^6 + 21904*h^4 + 205036*h^2 + 3605401)/1935360, 11, 0),
    ((h - 1)*(2*h - 1)*(4*h^2 + 5)*(4*h^2 + 21*h + 47), 10, 1),
    (-(h + 1)*(2*h + 1)*(4*h^2 + 5)*(4*h^2 - 21*h + 47), 10, 0),
    ((h - 1)*(h + 1)*(4*h^2 + 5)*(5376*h^8 + 90112*h^6 + 935904*h^4 - 2294904*h^2 - 231729397)/1548288, 9, 1),
    (-(h - 1)*(h + 1)*(4*h^2 + 5)*(5376*h^8 + 90112*h^6 + 935904*h^4 - 2294904*h^2 - 231729397)/1548288, 9, 0),
    ((h + 1)*(2*h + 1)*(4*h^2 + 5)*(4*h^2 - 21*h + 47), 8, 1),
    (-(h - 1)*(2*h - 1)*(4*h^2 + 5)*(4*h^2 + 21*h + 47), 8, 0),
    (-(h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(1344*h^6 + 21904*h^4 + 205036*h^2 + 3605401)/1935360, 7, 1),
    ((h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(1344*h^6 + 21904*h^4 + 205036*h^2 + 3605401)/1935360, 7, 0),
    ((h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(1344*h^6 + 19024*h^4 + 117196*h^2 + 113221)/3870720, 5, 1),
    (-(h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(1344*h^6 + 19024*h^4 + 117196*h^2 + 113221)/3870720, 5, 0),
    (-(h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(192*h^6 + 2032*h^4 + 3508*h^2 + 703)/1935360, 3, 1),
    ((h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(192*h^6 + 2032*h^4 + 3508*h^2 + 703)/1935360, 3, 0),
    ((h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(192*h^6 + 1072*h^4 + 1108*h^2 - 797)/15482880, 1, 1),
    (-(h - 1)*(h + 1)*(2*h - 1)*(2*h + 1)*(4*h^2 + 5)*(192*h^6 + 1072*h^4 + 1108*h^2 - 797)/15482880, 1, 0)]

theorem LM_poly (h y : ℝ) :
    monoSum (2*h) (LM h) y=NPh h (Real.exp y) (Real.exp (2*h*y)) := by
  simp only [monoSum, LM, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, NPh, Km, Kg,
    Kn, KH, E9R4, dH, DH]
  ring

theorem LM_moments (h : ℝ) : ∀ n < 10, moment (toExp (2*h) (LM h)) n=0 := by
  intro n hn
  interval_cases n <;>
    simp only [moment, toExp, LM, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;>
    push_cast <;> ring

/-- Pure algebra: the polynomial part of `q_M - q_*`, minus its leading term, over the common
denominator. -/
theorem bracket_h (h E T : ℝ) (h4 : 4-h^2≠0) (h1 : 1-h≠0) (hE : E≠0) (hT : T-1≠0) :
    mH h*(1+E^2)+gH h*E-nH h*(E*R4 (dH h) (wE E))-DH h*E*wE E^4-h*(E^2-T)/((1-h)*(T-1))
      =NPh h E T/(KH h*(1-h)*(T-1)*E^8) := by
  unfold NPh Km Kg Kn KH E9R4 mH gH nH R4 wE
  generalize ha : 4-h^2=a at h4 ⊢
  field_simp
  subst ha
  ring

/-! ## Limits at `y = 0` -/

theorem exp_two (y : ℝ) : Real.exp (2*y)=Real.exp y^2 := by
  rw [two_mul, Real.exp_add, sq]

theorem exp_ne_one (c y : ℝ) (hc : c≠0) (hy : y≠0) : Real.exp (c*y)-1≠0 := by
  intro h0
  have : Real.exp (c*y)=Real.exp 0 := by rw [Real.exp_zero]; linarith
  rcases mul_eq_zero.mp (Real.exp_injective this) with h' | h'
  · exact hc h'
  · exact hy h'

theorem tendsto_exp_nhds : Tendsto (fun y : ℝ => Real.exp y) (𝓝[≠] 0) (𝓝 1) := by
  simpa using tendsto_exp_one 1

def W (y : ℝ) : ℝ := wE (Real.exp y)

theorem tendsto_W : Tendsto W (𝓝[≠] 0) (𝓝 0) := by
  have hc : Continuous fun y : ℝ => (Real.exp y^2-1)^2/Real.exp y^2 :=
    (((Real.continuous_exp.pow 2).sub continuous_const).pow 2).div (Real.continuous_exp.pow 2)
      (fun y => pow_ne_zero 2 (Real.exp_pos y).ne')
  have h2 : Tendsto (fun y : ℝ => (Real.exp y^2-1)^2/Real.exp y^2) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  exact h2

theorem tendsto_W_div : Tendsto (fun y : ℝ => W y/y^2) (𝓝[≠] 0) (𝓝 4) := by
  have h := ((tendsto_exp_scaled 2).pow 2).div (tendsto_exp_nhds.pow 2) (by norm_num)
  have e : (2:ℝ)^2/1^2=4 := by norm_num
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : y≠0 := hy
  have hE : Real.exp y≠0 := (Real.exp_pos y).ne'
  show ((Real.exp (2*y)-1)/y)^2/Real.exp y^2=W y/y^2
  rw [exp_two]
  unfold W wE
  field_simp

/-- The polynomial part of `q_M - q_*` minus its leading term, at `t = exp (2 y)`. -/
def brH (h y : ℝ) : ℝ :=
  mH h*(1+Real.exp y^2)+gH h*Real.exp y-nH h*(Real.exp y*R4 (dH h) (W y))
    -DH h*Real.exp y*W y^4
    -h*(Real.exp y^2-Real.exp (2*h*y))/((1-h)*(Real.exp (2*h*y)-1))

theorem bracket_limit (h : ℝ) (hh0 : 0<h) (hh2 : h<1/2) :
    Tendsto (fun y : ℝ => brH h y/y^8) (𝓝[≠] 0) (𝓝 0) := by
  have h4p : 0<4-h^2 := by nlinarith
  have h1p : 0<1-h := by linarith
  have hK : KH h≠0 := by unfold KH; positivity
  have hH := expSum_tendsto_zero (toExp (2*h) (LM h)) 10 9 (by norm_num) (LM_moments h)
  have hden := ((tendsto_const_nhds (x := KH h*(1-h))).mul (tendsto_exp_scaled (2*h))).mul
    (tendsto_exp_nhds.pow 8)
  have hne : KH h*(1-h)*(2*h)*1^8≠0 := by positivity
  have hq := hH.div hden hne
  rw [zero_div] at hq
  refine hq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : y≠0 := hy
  have hEne : Real.exp y≠0 := (Real.exp_pos y).ne'
  have hTne : Real.exp (2*h*y)-1≠0 := exp_ne_one (2*h) y (by positivity) hy0
  have hb : brH h y=NPh h (Real.exp y) (Real.exp (2*h*y))
      /(KH h*(1-h)*(Real.exp (2*h*y)-1)*Real.exp y^8) :=
    bracket_h h (Real.exp y) (Real.exp (2*h*y)) h4p.ne' h1p.ne' hEne hTne
  show expSum (toExp (2*h) (LM h)) y/y^9
      /(KH h*(1-h)*((Real.exp (2*h*y)-1)/y)*Real.exp y^8)=brH h y/y^8
  rw [hb, ← LM_poly, monoSum_eq]
  field_simp

theorem root_limit (p : ℝ) (hp : 2<p) :
    Tendsto (fun y : ℝ => (root p (Real.exp y)-Real.exp y*R4 (dC p) (W y))/y^8) (𝓝[≠] 0)
      (𝓝 0) := by
  have hE := tendsto_exp_nhds
  have hW := tendsto_W
  have hroot : Tendsto (fun y : ℝ => root p (Real.exp y)) (𝓝[≠] 0) (𝓝 1) := by
    have hc : ContinuousAt (root p) 1 := (hasDerivAt_root p 1 hp one_pos).continuousAt
    have := hc.tendsto.comp hE
    rwa [root_one] at this
  have hR4 : Tendsto (fun y : ℝ => R4 (dC p) (W y)) (𝓝[≠] 0) (𝓝 1) := by
    have hc : ContinuousAt (R4 (dC p)) 0 := by
      have : Continuous (R4 (dC p)) := by unfold R4; fun_prop
      exact this.continuousAt
    have e : R4 (dC p) 0=1 := by unfold R4; ring
    have := hc.tendsto.comp hW
    rwa [e] at this
  have hG : Tendsto (fun y : ℝ => G4 (dC p) (W y)) (𝓝[≠] 0) (𝓝 (G4 (dC p) 0)) := by
    have hc : ContinuousAt (G4 (dC p)) 0 := by
      have : Continuous (G4 (dC p)) := by unfold G4; fun_prop
      exact this.continuousAt
    exact hc.tendsto.comp hW
  have hsum := hroot.add (hE.mul hR4)
  have hmain := ((((hE.pow 2).mul (tendsto_W_div.pow 4)).mul hW).mul hG).div hsum (by norm_num)
  have e : (1:ℝ)^2*4^4*0*G4 (dC p) 0/(1+1*1)=0 := by ring
  rw [e] at hmain
  refine hmain.congr' ?_
  have hsne : ∀ᶠ y in 𝓝[≠] 0, root p (Real.exp y)+Real.exp y*R4 (dC p) (W y)≠0 :=
    hsum.eventually_ne (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hsne] with y hy hs
  have hy0 : y≠0 := hy
  have hrem : (root p (Real.exp y)-Real.exp y*R4 (dC p) (W y))
      *(root p (Real.exp y)+Real.exp y*R4 (dC p) (W y))
      =Real.exp y^2*(W y^5*G4 (dC p) (W y)) := root_remainder p (Real.exp y) hp (Real.exp_pos y)
  show Real.exp y^2*(W y/y^2)^4*W y*G4 (dC p) (W y)
      /(root p (Real.exp y)+Real.exp y*R4 (dC p) (W y))
    =(root p (Real.exp y)-Real.exp y*R4 (dC p) (W y))/y^8
  rw [div_eq_div_iff hs (pow_ne_zero 8 hy0), hrem]
  field_simp

/-! ## Contact of order eight -/

theorem support_exp (p y : ℝ) :
    support p (Real.exp (2*y))=lin p (Real.exp y)-nC p*root p (Real.exp y) := by
  unfold support qx
  rw [exp_two, Real.sqrt_sq (Real.exp_pos y).le]

theorem qStar_two (p y : ℝ) (hp : 2<p) (hT : Real.exp (2*(1/p)*y)-1≠0) :
    qStar p (2*y)=(1/p)*(Real.exp y^2-Real.exp (2*(1/p)*y))
      /((1-1/p)*(Real.exp (2*(1/p)*y)-1)) := by
  have hp0 : p≠0 := by linarith
  have hp1 : 0<p-1 := by linarith
  have e : 1/p*(2*y)=2*(1/p)*y := by ring
  unfold qStar
  rw [e, exp_two]
  generalize Real.exp (2*(1/p)*y)=T at hT ⊢
  field_simp

/-- Contact in the variable `y`: `(q_M - q_*) / y ^ 8 → 256 DH`. -/
theorem contact_y (p : ℝ) (hp : 2<p) :
    Tendsto (fun y : ℝ => (support p (Real.exp (2*y))-qStar p (2*y))/y^8) (𝓝[≠] 0)
      (𝓝 (256*DH (1/p))) := by
  have hp0 : 0<p := by linarith
  have hp1 : 0<p-1 := by linarith
  obtain ⟨hh0, hh2⟩ := h_bounds p hp
  have hmain := ((bracket_limit (1/p) hh0 hh2).add
    (((tendsto_const_nhds (x := DH (1/p))).mul tendsto_exp_nhds).mul (tendsto_W_div.pow 4))).sub
    ((root_limit p hp).const_mul (nC p))
  have e : 0+DH (1/p)*1*4^4-nC p*0=256*DH (1/p) := by ring
  rw [e] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : y≠0 := hy
  have hTne : Real.exp (2*(1/p)*y)-1≠0 := exp_ne_one (2*(1/p)) y (by positivity) hy0
  show brH (1/p) y/y^8+DH (1/p)*Real.exp y*(W y/y^2)^4
      -nC p*((root p (Real.exp y)-Real.exp y*R4 (dC p) (W y))/y^8)
    =(support p (Real.exp (2*y))-qStar p (2*y))/y^8
  rw [support_exp, qStar_two p y hp hTne]
  unfold brH lin
  rw [mC_h p hp, gC_h p hp, nC_h p hp, dC_h p hp]
  field_simp
  ring

def kappaM (p x : ℝ) : ℝ := 1+(p-1)*support p (Real.exp x)

/-- The three-mean support has contact of order eight with the exact support. -/
theorem contact_eight (p : ℝ) (hp : 2<p) :
    Tendsto (fun x : ℝ => (kappaM p x-kappaStarX p x)/x^8) (𝓝[≠] 0)
      (𝓝 ((p-1)*DH (1/p))) := by
  have hp0 : 0<p := by linarith
  have hp1 : 0<p-1 := by linarith
  have hhalf : Tendsto (fun x : ℝ => x/2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Continuous fun x : ℝ => x/2 := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x≠0 := hx
      exact div_ne_zero hx0 (by norm_num)
  have h := ((contact_y p hp).comp hhalf).const_mul ((p-1)/256)
  have e : (p-1)/256*(256*DH (1/p))=(p-1)*DH (1/p) := by ring
  rw [e] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x≠0 := hx
  have hT := exp_scaled_ne p x hp0 hx0
  have hstar : kappaStarX p x=1+(p-1)*qStar p x := by
    have e1 : x/p=1/p*x := by ring
    unfold kappaStarX qStar
    rw [e1]
    generalize Real.exp (1/p*x)=T at hT ⊢
    field_simp
    ring
  have e2 : 2*(x/2)=x := by ring
  simp only [Function.comp]
  rw [e2, hstar]
  unfold kappaM
  field_simp
  ring

/-! ## Order nine -/

/-- The error constant of the three-mean iteration. -/
def cM (p : ℝ) : ℝ := (p^2-1)*(p^2-4)*(4*p^2-1)*(17*p^2+8)/203212800

theorem cM_pos (p : ℝ) (hp : 2<p) : 0<cM p := by
  have h1 : 0<p^2-1 := by nlinarith
  have h2 : 0<p^2-4 := by nlinarith
  have h3 : 0<4*p^2-1 := by nlinarith
  unfold cM
  positivity

theorem cM_three : cM 3=23/20736 := by
  norm_num [cM]

theorem cM_eq (p : ℝ) (hp : 2<p) : (-p)^9*(-((p-1)*DH (1/p))/p^2)=cM p := by
  have hp0 : p≠0 := by linarith
  unfold DH cM
  field_simp
  ring

theorem correction_eq_kappa (p x : ℝ) :
    correction p (Real.exp x)=(kappaM p x-1+Real.exp x)/kappaM p x := by
  have : kappaM p x-1+Real.exp x=Real.exp x+(p-1)*support p (Real.exp x) := by
    unfold kappaM
    ring
  rw [this]
  rfl

/-- Order nine in the variable `x = log t`. -/
theorem order_nine_x (p : ℝ) (hp : 2<p) :
    Tendsto (fun x : ℝ => (Real.log (correction p (Real.exp x))-x/p)/x^9) (𝓝[≠] 0)
      (𝓝 (-((p-1)*DH (1/p))/p^2)) := by
  have h := contact_limit (kappaM p) p (by linarith) 8 (by norm_num) _ (contact_eight p hp)
  refine h.congr fun x => ?_
  rw [correction_eq_kappa]

/-- **Order nine.** For every real `p > 2`, the logarithmic error `ê = log (u / r)` of the
three-mean iteration satisfies `ê₊ / ê ^ 9 → cM p`, where `ê₊ = ê + log (correction p t)` and
`t = exp (-p ê)`. -/
theorem order_nine (p : ℝ) (hp : 2<p) :
    Tendsto (fun e : ℝ => (e+Real.log (correction p (Real.exp (-p*e))))/e^9) (𝓝[≠] 0)
      (𝓝 (cM p)) := by
  have hp0 : p≠0 := by linarith
  have hx := order_nine_x p hp
  have hsub : Tendsto (fun e : ℝ => -p*e) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Continuous fun e : ℝ => -p*e := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    · filter_upwards [self_mem_nhdsWithin] with e he
      have he0 : e≠0 := he
      exact mul_ne_zero (neg_ne_zero.mpr hp0) he0
  have h := (hx.comp hsub).const_mul ((-p)^9)
  rw [cM_eq p hp] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  have he0 : e≠0 := he
  simp only [Function.comp]
  field_simp
  ring

/-- The quantity in `order_nine` is the logarithmic error of one step of the iteration. -/
theorem log_error_step (p X r e : ℝ) (hp : 2<p) (hr : 0<r) (hX : r^p=X) :
    Real.log (step p X (r*Real.exp e)/r)=e+Real.log (correction p (Real.exp (-p*e))) := by
  have hXpos : 0<X := by rw [← hX]; exact Real.rpow_pos_of_pos hr p
  have ht : X/(r*Real.exp e)^p=Real.exp (-p*e) := by
    rw [Real.mul_rpow hr.le (Real.exp_pos e).le, hX, ← Real.exp_mul, div_mul_eq_div_div,
      div_self hXpos.ne', one_div, ← Real.exp_neg]
    congr 1
    ring
  have hc := correction_positive p (Real.exp (-p*e)) hp (Real.exp_pos _)
  unfold step
  rw [ht]
  have : r*Real.exp e*correction p (Real.exp (-p*e))/r
      =Real.exp e*correction p (Real.exp (-p*e)) := by
    field_simp
  rw [this, Real.log_mul (Real.exp_pos e).ne' hc.ne', Real.log_exp]

end LeanMath.Papers.ThreeMeanOrderNine
