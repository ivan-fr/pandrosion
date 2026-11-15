import LeanMath.Papers.MonotoneIteration
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # Global convergence of the three-mean iteration

The three-mean support combines the arithmetic mean, the geometric mean and one conic mean of
`1` and `t`:
`q(t) = m (1 + t) + g sqrt t - n sqrt (t + d (t - 1)²)`,
with coefficients `m, g, n, d` rational in the degree `p`. The update is written in the direct
state `u = 1 / s`: `u₊ = u * (t + (p-1) q) / (1 + (p-1) q)` with `t = X / u ^ p`.
For every real `p > 2`, `X > 0` and `u₀ > 0` the iteration converges to `X ^ (1 / p)`, moving
strictly toward the root without crossing it.

The analysis is done in the variable `x = sqrt t`, in which the support has a single radical. -/

noncomputable section
namespace LeanMath.Papers.ThreeMeanGlobal
open Real Filter Function Set
open scoped Topology

/-! ## Coefficients -/

def mC (p : ℝ) := (p-2)*(47*p^2+21*p+4)/(60*p*(4*p^2-1))
def gC (p : ℝ) := 16*(p+1)*(4*p^2-1)/(15*p*(5*p^2+4))
def nC (p : ℝ) := 49*p*(p+1)*(p^2-4)/(10*(4*p^2-1)*(5*p^2+4))
def dC (p : ℝ) := (5*p^2+4)/(84*p^2)

/-- The cube-root coefficients `7/90`, `64/63`, `6/35`, `7/108`. -/
theorem consts_cubic : mC 3=7/90 ∧ gC 3=64/63 ∧ nC 3=6/35 ∧ dC 3=7/108 := by
  refine ⟨?_,?_,?_,?_⟩ <;> norm_num [mC,gC,nC,dC]

theorem consts_pos (p : ℝ) (hp : 2<p) : 0<mC p ∧ 0<gC p ∧ 0<nC p ∧ 0<dC p := by
  have hp0 : 0<p := by linarith
  have hp2 : 0<p-2 := by linarith
  have h4 : 0<4*p^2-1 := by nlinarith
  have hq : 0<p^2-4 := by nlinarith
  refine ⟨?_,?_,?_,?_⟩
  · unfold mC; positivity
  · unfold gC; positivity
  · unfold nC; positivity
  · unfold dC; positivity

/-- The weights of the three means sum to one: `2 m + g - n = 1`. -/
theorem weights_sum (p : ℝ) (hp : 2<p) : 2*mC p+gC p-nC p=1 := by
  have hp0 : p≠0 := by linarith
  have h4 : 4*p^2-1≠0 := by nlinarith
  have h5 : 5*p^2+4≠0 := by nlinarith
  unfold mC gC nC
  generalize ha : 4*p^2-1=a at h4 ⊢
  field_simp
  subst ha
  ring

/-! ## The support in the variable `x = sqrt t` -/

def rad (p x : ℝ) := x^2+dC p*(x^2-1)^2
def radPrime (p x : ℝ) := 2*x+dC p*(4*x*(x^2-1))
def root (p x : ℝ) := Real.sqrt (rad p x)
def lin (p x : ℝ) := mC p*(1+x^2)+gC p*x
def linPrime (p x : ℝ) := 2*mC p*x+gC p
def qx (p x : ℝ) := lin p x-nC p*root p x
def qxPrime (p x : ℝ) := linPrime p x-nC p*(radPrime p x/(2*root p x))

theorem rad_pos (p x : ℝ) (hp : 2<p) (hx : 0<x) : 0<rad p x := by
  have hd := (consts_pos p hp).2.2.2
  unfold rad
  positivity

theorem root_pos (p x : ℝ) (hp : 2<p) (hx : 0<x) : 0<root p x :=
  Real.sqrt_pos.mpr (rad_pos p x hp hx)

theorem root_sq (p x : ℝ) (hp : 2<p) (hx : 0<x) : root p x^2=rad p x :=
  Real.sq_sqrt (rad_pos p x hp hx).le

theorem lin_pos (p x : ℝ) (hp : 2<p) (hx : 0<x) : 0<lin p x := by
  obtain ⟨hm,hg,-,-⟩ := consts_pos p hp
  unfold lin
  positivity

/-! ## Positivity of the support -/

def Q0 (p : ℝ) := 626*p^6 - 2273*p^5 + 1708*p^4 + 244*p^3 + 1168*p^2 - 608*p - 64
def Q1 (p : ℝ) := 8520*p^6 - 12420*p^5 - 8880*p^4 - 4080*p^3 + 7200*p^2 - 960*p
def Q2 (p : ℝ) := 26820*p^6 + 8820*p^5 - 25380*p^4 - 35280*p^3 - 3600*p^2

theorem Q0_nonneg (p : ℝ) (hp : 2<p) : 0≤Q0 p := by
  have hr : 0<p-2 := by linarith
  have e : Q0 p=12024*(p-2)^2+23148*(p-2)^3+16538*(p-2)^4+5239*(p-2)^5+626*(p-2)^6 := by
    unfold Q0; ring
  rw [e]; positivity

theorem Q1_pos (p : ℝ) (hp : 2<p) : 0<Q1 p := by
  have hr : 0<p-2 := by linarith
  have e : Q1 p=336960*(p-2)+820800*(p-2)^2+791280*(p-2)^3+378120*(p-2)^4+89820*(p-2)^5
      +8520*(p-2)^6 := by
    unfold Q1; ring
  rw [e]; positivity

theorem Q2_pos (p : ℝ) (hp : 2<p) : 0<Q2 p := by
  have hr : 0<p-2 := by linarith
  have e : Q2 p=1296000+4605120*(p-2)+6318000*(p-2)^2+4405680*(p-2)^3+1672020*(p-2)^4
      +330660*(p-2)^5+26820*(p-2)^6 := by
    unfold Q2; ring
  rw [e]; positivity

/-- `lin² - n² rad` is a positive combination of `(x-1)⁴`, `x (x-1)²` and `x²`. -/
theorem lin_sq_identity (p x : ℝ) (hp : 2<p) :
    lin p x^2-nC p^2*rad p x=
      (Q0 p*(x-1)^4+Q1 p*x*(x-1)^2+Q2 p*x^2)/(900*p^2*(4*p^2-1)*(5*p^2+4)) := by
  have hp0 : p≠0 := by linarith
  have h4 : 4*p^2-1≠0 := by nlinarith
  have h5 : 5*p^2+4≠0 := by nlinarith
  unfold lin rad mC gC nC dC Q0 Q1 Q2
  generalize ha : 4*p^2-1=a at h4 ⊢
  field_simp
  subst ha
  ring

theorem qx_pos (p x : ℝ) (hp : 2<p) (hx : 0<x) : 0<qx p x := by
  obtain ⟨-,-,hn,-⟩ := consts_pos p hp
  have hp0 : 0<p := by linarith
  have h4 : 0<4*p^2-1 := by nlinarith
  have hl := lin_pos p x hp hx
  have hr := root_pos p x hp hx
  have h0 := Q0_nonneg p hp
  have h1 := Q1_pos p hp
  have h2 := Q2_pos p hp
  have hpos : 0<(Q0 p*(x-1)^4+Q1 p*x*(x-1)^2+Q2 p*x^2)/(900*p^2*(4*p^2-1)*(5*p^2+4)) := by
    apply div_pos
    · have a1 : 0≤Q0 p*(x-1)^4 := by positivity
      have a2 : 0≤Q1 p*x*(x-1)^2 := by positivity
      have a3 : 0<Q2 p*x^2 := by positivity
      linarith
    · positivity
  have hid := lin_sq_identity p x hp
  have hsq : (nC p*root p x)^2<lin p x^2 := by
    rw [mul_pow, root_sq p x hp hx]
    linarith
  have hnr : 0<nC p*root p x := by positivity
  have hlt : nC p*root p x<lin p x := by
    by_contra hcon
    have hle : lin p x≤nC p*root p x := not_lt.mp hcon
    have := mul_le_mul hle hle hl.le hnr.le
    nlinarith
  unfold qx
  linarith

/-! ## Derivatives -/

theorem hasDerivAt_sq (x : ℝ) : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
  simpa using hasDerivAt_pow 2 x

theorem hasDerivAt_rad (p x : ℝ) : HasDerivAt (rad p) (radPrime p x) x := by
  have h1 := hasDerivAt_sq x
  have h2 : HasDerivAt (fun y : ℝ => (y^2-1)^2) (4*x*(x^2-1)) x := by
    have h := (h1.sub_const (1:ℝ)).pow 2
    refine h.congr_deriv ?_
    norm_num
    ring
  have h3 : HasDerivAt (fun y : ℝ => y^2+dC p*(y^2-1)^2) (radPrime p x) x :=
    (h1.add (h2.const_mul (dC p))).congr_deriv (by unfold radPrime; ring)
  exact h3

theorem hasDerivAt_root (p x : ℝ) (hp : 2<p) (hx : 0<x) :
    HasDerivAt (root p) (radPrime p x/(2*root p x)) x :=
  (hasDerivAt_rad p x).sqrt (rad_pos p x hp hx).ne'

theorem hasDerivAt_lin (p x : ℝ) : HasDerivAt (lin p) (linPrime p x) x := by
  have h1 := hasDerivAt_sq x
  have h : HasDerivAt (fun y : ℝ => mC p*(1+y^2)+gC p*y) (linPrime p x) x :=
    (((h1.const_add (1:ℝ)).const_mul (mC p)).add
      ((hasDerivAt_id x).const_mul (gC p))).congr_deriv (by unfold linPrime; ring)
  exact h

theorem hasDerivAt_qx (p x : ℝ) (hp : 2<p) (hx : 0<x) :
    HasDerivAt (qx p) (qxPrime p x) x :=
  (hasDerivAt_lin p x).sub ((hasDerivAt_root p x hp hx).const_mul (nC p))

/-! ## The logarithmic gap and its slope -/

def gap (p x : ℝ) :=
  Real.log (x^2+(p-1)*qx p x)-Real.log (1+(p-1)*qx p x)-2*Real.log x/p
def slope (p x : ℝ) :=
  (2*x+(p-1)*qxPrime p x)/(x^2+(p-1)*qx p x)-
    (p-1)*qxPrime p x/(1+(p-1)*qx p x)-2*(1/x)/p

theorem hasDerivAt_gap (p x : ℝ) (hp : 2<p) (hx : 0<x) :
    HasDerivAt (gap p) (slope p x) x := by
  have hq := qx_pos p x hp hx
  have hp1 : 0<p-1 := by linarith
  have hn : 0<x^2+(p-1)*qx p x := by positivity
  have hd : 0<1+(p-1)*qx p x := by positivity
  have hder := hasDerivAt_qx p x hp hx
  have hh := ((((hasDerivAt_sq x).add (hder.const_mul (p-1))).log hn.ne').sub
    (((hasDerivAt_const x (1:ℝ)).add (hder.const_mul (p-1))).log hd.ne')).sub
    (((hasDerivAt_log hx.ne').const_mul 2).div_const p)
  convert! hh using 1
  simp [slope]

/-! ## Elimination of the radical -/

def Agen (m g n d c h x : ℝ) := c^2*(4*d*g*h*n*x^5-8*d*g*h*n*x^3+4*d*g*h*n*x
    +4*d*h*m*n*x^6-4*d*h*m*n*x^4-4*d*h*m*n*x^2+4*d*h*m*n+4*g*h*n*x^3+4*h*m*n*x^4+4*h*m*n*x^2)
    +c*(2*d*h*n*x^6-2*d*h*n*x^4-2*d*h*n*x^2+2*d*h*n+2*h*n*x^4+2*h*n*x^2-n*x^4-n*x^2)
def Bgen (m g n d c h x : ℝ) := c^2*(-2*d*h*n^2*x^4
    +4*d*h*n^2*x^2-2*d*h*n^2-2*g^2*h*x^2-4*g*h*m*x^3-4*g*h*m*x-2*h*m^2*x^4-4*h*m^2*x^2-2*h*m^2-2*h*n^2*x^2)
    +c*(-2*g*h*x^3-2*g*h*x+g*x^3+g*x-2*h*m*x^4-4*h*m*x^2-2*h*m+4*m*x^2)-2*h*x^2+2*x^2

/-- Pure algebra: with `ρ² = x² + d (x²-1)²`, the numerator of the slope is `A + B ρ`. -/
theorem numerator_elimination (m g n d c h x ρ : ℝ) (hρ : ρ^2=x^2+d*(x^2-1)^2) :
    2*x^2*(1+c*(m*(1+x^2)+g*x-n*ρ))*ρ
      +c*x*((2*m*x+g)*ρ-n*(2*x+d*(4*x*(x^2-1)))/2)*(1-x^2)
      -2*h*(x^2+c*(m*(1+x^2)+g*x-n*ρ))*(1+c*(m*(1+x^2)+g*x-n*ρ))*ρ
      =Agen m g n d c h x+Bgen m g n d c h x*ρ := by
  unfold Agen Bgen
  linear_combination (-2*c^2*h*n^2*ρ+(2*c*n*(2*c*g*h*x+2*c*h*m*x^2+2*c*h*m+h*x^2+h-x^2)))*hρ

/-- Pure algebra: the slope over a common denominator. -/
theorem slope_algebra (p c x ρ q l n D : ℝ) (hp : p≠0) (hx : x≠0) (hρ : ρ≠0)
    (h1 : x^2+c*q≠0) (h2 : 1+c*q≠0) :
    (2*x+c*(l-n*(D/(2*ρ))))/(x^2+c*q)-c*(l-n*(D/(2*ρ)))/(1+c*q)-2*(1/x)/p
      =(2*x^2*(1+c*q)*ρ+c*x*(l*ρ-n*D/2)*(1-x^2)-2*(1/p)*(x^2+c*q)*(1+c*q)*ρ)/
        (x*ρ*(x^2+c*q)*(1+c*q)) := by
  field_simp
  ring

def kap (p : ℝ) := (p^2-4)*(p^2-1)
def Qden (p : ℝ) := p^3*(4*p^2-1)^2*(5*p^2+4)^2
def PA (p x : ℝ) := (1175*p^8+2755*p^6+2352*p^4+880*p^2+128)*(x^6+1)+(5120*p^8-3584*p^6-3264*p^4
    +1984*p^2-256)*(x^5+x)+(-6635*p^8+13877*p^6+17808*p^4+1808*p^2-128)*(x^4+x^2)
    +(75776*p^8-121856*p^6+54912*p^4-9344*p^2+512)*x^3
def B0 (p : ℝ) := 30185*p^8 + 32563*p^6 + 16572*p^4 + 8032*p^2 + 128
def B1 (p : ℝ) := 54180*p^8 + 100044*p^6 + 85680*p^4 + 32256*p^2
def B2 (p : ℝ) := 262836*p^8 - 335160*p^6 + 310464*p^4
def PB (p x : ℝ) := B0 p*(x-1)^4+B1 p*x*(x-1)^2+B2 p*x^2
def E0 (p : ℝ) := 489845*p^8 + 647956*p^6 + 361344*p^4 + 123904*p^2 - 1024
def E1 (p : ℝ) := 804380*p^8 + 1583824*p^6 + 2050176*p^4 + 1033216*p^2 - 4096
def E2 (p : ℝ) := 3829896*p^8 - 3081456*p^6 + 2225664*p^4 + 2128896*p^2
def PE (p x : ℝ) := E0 p*(x-1)^4+E1 p*x*(x-1)^2+E2 p*x^2

theorem Agen_special (p x : ℝ) (hp : 2<p) :
    Agen (mC p) (gC p) (nC p) (dC p) (p-1) (1/p) x=7*kap p*PA p x/(1800*Qden p) := by
  have hp0 : p≠0 := by linarith
  have h4 : 4*p^2-1≠0 := by nlinarith
  have h5 : 5*p^2+4≠0 := by nlinarith
  unfold Agen mC gC nC dC kap Qden PA
  generalize ha : 4*p^2-1=a at h4 ⊢
  field_simp
  subst ha
  ring

theorem Bgen_special (p x : ℝ) (hp : 2<p) :
    Bgen (mC p) (gC p) (nC p) (dC p) (p-1) (1/p) x=-(kap p*PB p x)/(900*Qden p) := by
  have hp0 : p≠0 := by linarith
  have h4 : 4*p^2-1≠0 := by nlinarith
  have h5 : 5*p^2+4≠0 := by nlinarith
  unfold Bgen mC gC nC dC kap Qden PB B0 B1 B2
  generalize ha : 4*p^2-1=a at h4 ⊢
  field_simp
  subst ha
  ring

theorem kap_pos (p : ℝ) (hp : 2<p) : 0<kap p := by
  have h1 : 0<p^2-4 := by nlinarith
  have h2 : 0<p^2-1 := by nlinarith
  unfold kap
  positivity

theorem Qden_pos (p : ℝ) (hp : 2<p) : 0<Qden p := by
  have hp0 : 0<p := by linarith
  have h4 : 0<4*p^2-1 := by nlinarith
  unfold Qden
  positivity

/-- The slope identity: `d gap / dx = -κ (2 PB ρ - 7 PA) / (positive)`. -/
theorem slope_identity (p x : ℝ) (hp : 2<p) (hx : 0<x) :
    slope p x=-(kap p*(2*PB p x*root p x-7*PA p x))/
      (1800*Qden p*(x*root p x*(x^2+(p-1)*qx p x)*(1+(p-1)*qx p x))) := by
  have hp0 : 0<p := by linarith
  have hp1 : 0<p-1 := by linarith
  have hρ := root_pos p x hp hx
  have hq := qx_pos p x hp hx
  have hn : 0<x^2+(p-1)*qx p x := by positivity
  have hd : 0<1+(p-1)*qx p x := by positivity
  have hQ := Qden_pos p hp
  have hnum : 2*x^2*(1+(p-1)*qx p x)*root p x
      +(p-1)*x*(linPrime p x*root p x-nC p*radPrime p x/2)*(1-x^2)
      -2*(1/p)*(x^2+(p-1)*qx p x)*(1+(p-1)*qx p x)*root p x
      =7*kap p*PA p x/(1800*Qden p)+-(kap p*PB p x)/(900*Qden p)*root p x := by
    rw [←Agen_special p x hp, ←Bgen_special p x hp]
    exact numerator_elimination (mC p) (gC p) (nC p) (dC p) (p-1) (1/p) x (root p x)
      (root_sq p x hp hx)
  have hs : slope p x=(2*x^2*(1+(p-1)*qx p x)*root p x
      +(p-1)*x*(linPrime p x*root p x-nC p*radPrime p x/2)*(1-x^2)
      -2*(1/p)*(x^2+(p-1)*qx p x)*(1+(p-1)*qx p x)*root p x)/
        (x*root p x*(x^2+(p-1)*qx p x)*(1+(p-1)*qx p x)) :=
    slope_algebra p (p-1) x (root p x) (qx p x) (linPrime p x) (nC p) (radPrime p x)
      hp0.ne' hx.ne' hρ.ne' hn.ne' hd.ne'
  rw [hs, hnum]
  field_simp
  ring

/-! ## The sign of the slope -/

theorem B0_pos (p : ℝ) (hp : 2<p) : 0<B0 p := by
  have hr : 0<p-2 := by linarith
  have e : B0 p=10108800+37723968*(p-2)+62312400*(p-2)^2+59434176*(p-2)^3+35777552*(p-2)^4
      +13913636*(p-2)^5+3413283*(p-2)^6+482960*(p-2)^7+30185*(p-2)^8 := by
    unfold B0; ring
  rw [e]; positivity

theorem B1_pos (p : ℝ) (hp : 2<p) : 0<B1 p := by
  have hr : 0<p-2 := by linarith
  have e : B1 p=21772800+77559552*(p-2)+123189696*(p-2)^2+113783040*(p-2)^3+66769920*(p-2)^4
      +25473168*(p-2)^5+6168204*(p-2)^6+866880*(p-2)^7+54180*(p-2)^8 := by
    unfold B1; ring
  rw [e]; positivity

theorem B2_pos (p : ℝ) (hp : 2<p) : 0<B2 p := by
  have hr : 0<p-2 := by linarith
  have e : B2 p=50803200+214728192*(p-2)+398014848*(p-2)^2+419860224*(p-2)^3+274577184*(p-2)^4
      +113728608*(p-2)^5+29102472*(p-2)^6+4205376*(p-2)^7+262836*(p-2)^8 := by
    unfold B2; ring
  rw [e]; positivity

theorem E0_pos (p : ℝ) (hp : 2<p) : 0<E0 p := by
  have hr : 0<p-2 := by linarith
  have e : E0 p=173145600+638067456*(p-2)+1042107840*(p-2)^2+984365952*(p-2)^3+587865104*(p-2)^4
      +227226032*(p-2)^5+55510596*(p-2)^6+7837520*(p-2)^7+489845*(p-2)^8 := by
    unfold E0; ring
  rw [e]; positivity

theorem E1_pos (p : ℝ) (hp : 2<p) : 0<E1 p := by
  have hr : 0<p-2 := by linarith
  have e : E1 p=344217600+1197517824*(p-2)+1871804160*(p-2)^2+1711262208*(p-2)^3
      +997985216*(p-2)^4+379368128*(p-2)^5+91674384*(p-2)^6+12870080*(p-2)^7
      +804380*(p-2)^8 := by
    unfold E1; ring
  rw [e]; positivity

theorem E2_pos (p : ℝ) (hp : 2<p) : 0<E2 p := by
  have hr : 0<p-2 := by linarith
  have e : E2 p=827366400+3409910784*(p-2)+6179169024*(p-2)^2+6387945984*(p-2)^3
      +4106821824*(p-2)^4+1678815936*(p-2)^5+425866896*(p-2)^6+61278336*(p-2)^7
      +3829896*(p-2)^8 := by
    unfold E2; ring
  rw [e]; positivity

theorem PB_pos (p x : ℝ) (hp : 2<p) (hx : 0<x) : 0<PB p x := by
  have h0 := B0_pos p hp
  have h1 := B1_pos p hp
  have h2 := B2_pos p hp
  have a1 : 0≤B0 p*(x-1)^4 := by positivity
  have a2 : 0≤B1 p*x*(x-1)^2 := by positivity
  have a3 : 0<B2 p*x^2 := by positivity
  unfold PB
  linarith

theorem PE_pos (p x : ℝ) (hp : 2<p) (hx : 0<x) : 0<PE p x := by
  have h0 := E0_pos p hp
  have h1 := E1_pos p hp
  have h2 := E2_pos p hp
  have a1 : 0≤E0 p*(x-1)^4 := by positivity
  have a2 : 0≤E1 p*x*(x-1)^2 := by positivity
  have a3 : 0<E2 p*x^2 := by positivity
  unfold PE
  linarith

/-- Rationalization: `(2 PB ρ)² - (7 PA)²` is `(x-1)⁸` times a positive polynomial. -/
theorem square_identity (p x : ℝ) (hp : 2<p) :
    4*PB p x^2*rad p x-49*PA p x^2=
      4*(4*p^2-1)^3*(5*p^2+4)^2*(x-1)^8*PE p x/(21*p^2) := by
  have hp0 : p≠0 := by linarith
  unfold PB PE PA rad dC B0 B1 B2 E0 E1 E2
  field_simp
  ring

/-- The sign that controls monotonicity: `2 PB ρ > 7 PA` away from `x = 1`. -/
theorem barrier (p x : ℝ) (hp : 2<p) (hx : 0<x) (hne : x≠1) :
    0<2*PB p x*root p x-7*PA p x := by
  have hB := PB_pos p x hp hx
  have hρ := root_pos p x hp hx
  have hpos : 0<2*PB p x*root p x := by positivity
  rcases le_or_gt (PA p x) 0 with hA | hA
  · linarith
  · have hE := PE_pos p x hp hx
    have hp0 : 0<p := by linarith
    have h4 : 0<4*p^2-1 := by nlinarith
    have hx8 : 0<(x-1)^8 := by
      have : x-1≠0 := sub_ne_zero.mpr hne
      positivity
    have hR : 0<4*(4*p^2-1)^3*(5*p^2+4)^2*(x-1)^8*PE p x/(21*p^2) := by positivity
    have hid := square_identity p x hp
    have hsq : (7*PA p x)^2<(2*PB p x*root p x)^2 := by
      have e : (2*PB p x*root p x)^2=4*PB p x^2*rad p x := by
        rw [mul_pow, mul_pow, root_sq p x hp hx]; ring
      rw [e]
      nlinarith
    by_contra hcon
    have hle : 2*PB p x*root p x≤7*PA p x := by linarith
    have := mul_le_mul hle hle hpos.le (by positivity : (0:ℝ)≤7*PA p x)
    nlinarith

theorem slope_negative (p x : ℝ) (hp : 2<p) (hx : 0<x) (hne : x≠1) : slope p x<0 := by
  rw [slope_identity p x hp hx]
  have hp1 : 0<p-1 := by linarith
  have hk := kap_pos p hp
  have hQ := Qden_pos p hp
  have hρ := root_pos p x hp hx
  have hq := qx_pos p x hp hx
  have hb := barrier p x hp hx hne
  apply div_neg_of_neg_of_pos
  · exact neg_neg_of_pos (mul_pos hk hb)
  · positivity

/-! ## The gap has the sign of `1 - x` -/

theorem root_one (p : ℝ) : root p 1=1 := by
  have h : rad p 1=1 := by unfold rad; ring
  rw [root, h, Real.sqrt_one]

theorem qx_one (p : ℝ) (hp : 2<p) : qx p 1=1 := by
  have h := weights_sum p hp
  unfold qx lin
  rw [root_one]
  linarith

theorem gap_one (p : ℝ) (hp : 2<p) : gap p 1=0 := by
  simp [gap, qx_one p hp]

theorem gap_negative_above_one (p x : ℝ) (hp : 2<p) (hx : 1<x) : gap p x<0 := by
  have hm : StrictAntiOn (gap p) (Icc 1 x) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 1 x)
    · intro y hy
      exact (hasDerivAt_gap p y hp (by linarith [hy.1])).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hy0 : 0<y := by linarith [hy.1]
      rw [(hasDerivAt_gap p y hp hy0).deriv]
      exact slope_negative p y hp hy0 (by linarith [hy.1])
  simpa only [gap_one p hp] using hm ⟨le_rfl,hx.le⟩ ⟨hx.le,le_rfl⟩ hx

theorem gap_positive_below_one (p x : ℝ) (hp : 2<p) (hx : 0<x) (hx1 : x<1) : 0<gap p x := by
  have hm : StrictAntiOn (gap p) (Icc x 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc x 1)
    · intro y hy
      exact (hasDerivAt_gap p y hp (hx.trans_le hy.1)).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hy0 := hx.trans hy.1
      rw [(hasDerivAt_gap p y hp hy0).deriv]
      exact slope_negative p y hp hy0 (by linarith [hy.2])
  simpa only [gap_one p hp] using hm ⟨le_rfl,hx1.le⟩ ⟨hx1.le,le_rfl⟩ hx1

/-! ## The support and the correction in the residual `t` -/

def support (p t : ℝ) := qx p (Real.sqrt t)
def correction (p t : ℝ) := (t+(p-1)*support p t)/(1+(p-1)*support p t)
def step (p X u : ℝ) := u*correction p (X/u^p)

/-- The support as it is written in the paper. -/
theorem support_formula (p t : ℝ) (ht : 0≤t) :
    support p t=mC p*(1+t)+gC p*Real.sqrt t-nC p*Real.sqrt (t+dC p*(t-1)^2) := by
  unfold support qx lin root rad
  rw [Real.sq_sqrt ht]

theorem support_positive (p t : ℝ) (hp : 2<p) (ht : 0<t) : 0<support p t :=
  qx_pos p _ hp (Real.sqrt_pos.mpr ht)

theorem support_one (p : ℝ) (hp : 2<p) : support p 1=1 := by
  rw [support, Real.sqrt_one, qx_one p hp]

theorem correction_positive (p t : ℝ) (hp : 2<p) (ht : 0<t) : 0<correction p t := by
  have hq := support_positive p t hp ht
  have hp1 : 0<p-1 := by linarith
  unfold correction
  positivity

theorem gap_eq (p t : ℝ) (hp : 2<p) (ht : 0<t) :
    gap p (Real.sqrt t)=Real.log (correction p t)-Real.log t/p := by
  have hq := support_positive p t hp ht
  have hp1 : 0<p-1 := by linarith
  have hn : 0<t+(p-1)*support p t := by positivity
  have hd : 0<1+(p-1)*support p t := by positivity
  unfold gap correction
  rw [Real.log_div hn.ne' hd.ne', Real.sq_sqrt ht.le, Real.log_sqrt ht.le]
  unfold support
  ring

/-- For `t > 1` the correction lies strictly between `1` and the exact factor `t ^ (1 / p)`. -/
theorem correction_above_one (p t : ℝ) (hp : 2<p) (ht : 1<t) :
    1<correction p t ∧ correction p t<t^(1/p) := by
  have ht0 : 0<t := by linarith
  have hq := support_positive p t hp ht0
  have hp1 : 0<p-1 := by linarith
  have hd : 0<1+(p-1)*support p t := by positivity
  have hc := correction_positive p t hp ht0
  have hs : 1<Real.sqrt t := by
    have := Real.sqrt_lt_sqrt zero_le_one ht
    rwa [Real.sqrt_one] at this
  have hg := gap_negative_above_one p (Real.sqrt t) hp hs
  rw [gap_eq p t hp ht0] at hg
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
  have hs : Real.sqrt t<1 := by
    have := Real.sqrt_lt_sqrt ht.le ht1
    rwa [Real.sqrt_one] at this
  have hg := gap_positive_below_one p (Real.sqrt t) hp (Real.sqrt_pos.mpr ht) hs
  rw [gap_eq p t hp ht] at hg
  constructor
  · apply (Real.log_lt_log_iff (Real.rpow_pos_of_pos ht _) hc).mp
    rw [Real.log_rpow ht]
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using sub_pos.mp hg
  · exact (div_lt_iff₀ hd).2 (by linarith)

theorem correction_one (p : ℝ) (hp : 2<p) : correction p 1=1 := by
  have hp0 : p≠0 := by linarith
  simp [correction, support_one p hp, hp0]

theorem continuous_support (p : ℝ) : Continuous (support p) := by
  have h : support p=fun t => mC p*(1+Real.sqrt t^2)+gC p*Real.sqrt t
      -nC p*Real.sqrt (Real.sqrt t^2+dC p*(Real.sqrt t^2-1)^2) := rfl
  rw [h]
  fun_prop

theorem continuousAt_correction (p t : ℝ) (hp : 2<p) (ht : 0<t) :
    ContinuousAt (correction p) t := by
  have hq := support_positive p t hp ht
  have hp1 : 0<p-1 := by linarith
  have hd : 1+(p-1)*support p t≠0 := by positivity
  have hcont : ContinuousAt (support p) t := (continuous_support p).continuousAt
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

/-- Global monotone convergence of the three-mean iteration for every real `p > 2`, `X > 0`
and `u₀ > 0`. -/
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

/-- Every step moves strictly toward the root and never crosses it. -/
theorem no_crossing (p X u : ℝ) (hp : 2<p) (hX : 0<X) (hu : 0<u) (hne : u≠X^(1/p)) :
    (u<step p X u ∧ step p X u<X^(1/p)) ∨ (X^(1/p)<step p X u ∧ step p X u<u) := by
  have hr : 0<X^(1/p) := Real.rpow_pos_of_pos hX _
  have hx : (X^(1/p))^p=X := by
    rw [one_div,Real.rpow_inv_rpow hX.le (by linarith : p≠0)]
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inl (step_below_root p X _ u hp hr hx hu h)
  · exact Or.inr (step_above_root p X _ u hp hr hx h)

/-- The reciprocal state `s = 1 / u` follows the rectangle update
`s₊ = s (1 + g) / (t + g)` with `t = X s ^ p` and `g = (p-1) q`. -/
theorem reciprocal_form (p X u : ℝ) (hp : 2<p) (hX : 0<X) (hu : 0<u) :
    1/step p X u=(1/u)*((1+(p-1)*support p (X/u^p))/(X/u^p+(p-1)*support p (X/u^p))) := by
  have ht : 0<X/u^p := div_pos hX (Real.rpow_pos_of_pos hu p)
  have hq := support_positive p (X/u^p) hp ht
  have hp1 : 0<p-1 := by linarith
  have hn : 0<X/u^p+(p-1)*support p (X/u^p) := by positivity
  have hd : 0<1+(p-1)*support p (X/u^p) := by positivity
  unfold step correction
  field_simp

end LeanMath.Papers.ThreeMeanGlobal
