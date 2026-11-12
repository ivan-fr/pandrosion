import LeanMath.Papers.NestedRadicalReal
import LeanMath.Papers.ContactLimit
import LeanMath.Papers.DegreesEfficiency

/-! # Local order nine of the nested-radical iteration (Theorem 4.1)

For every real `p > 2` the logarithmic error of the nested-radical iteration satisfies
`ê₊ / ê ^ 9 → c9 p`. The proof follows the paper: the exact quantity `Y = q_* ^ 2 / t` agrees with a
quartic polynomial in `w` up to `o (w ^ 4)` (an exponential sum with twelve vanishing moments), the
nested radical is expanded algebraically, and Lemma 2.1 converts contact of order eight into order
nine. -/

noncomputable section
namespace LeanMath.Papers.NestedOrderNine
open Filter Asymptotics
open scoped Topology
open LeanMath.Papers.ContactLimit LeanMath.Papers.NestedRadicalReal
open LeanMath.Papers.NestedRadicalRealCertificate
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-! ## Sums of monomials in `exp x` and `exp (h x)` -/

def monoSum (h : ℝ) (l : List (ℝ × ℕ × ℕ)) (x : ℝ) : ℝ :=
  (l.map fun c => c.1 * (Real.exp x ^ c.2.1 * Real.exp (h * x) ^ c.2.2)).sum

def toExp (h : ℝ) (l : List (ℝ × ℕ × ℕ)) : List (ℝ × ℝ) :=
  l.map fun c => (c.1, (c.2.1 : ℝ) + c.2.2 * h)

theorem exp_monomial (h x : ℝ) (m e : ℕ) :
    Real.exp x ^ m * Real.exp (h * x) ^ e = Real.exp (((m : ℝ) + e * h) * x) := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

theorem monoSum_eq (h : ℝ) (l : List (ℝ × ℕ × ℕ)) (x : ℝ) :
    monoSum h l x = expSum (toExp h l) x := by
  unfold monoSum expSum toExp
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, exp_monomial]

/-! ## The exact quantity `Y` and its quartic approximation in `w` -/

def aH (h : ℝ) : ℝ := (1 - 2 * h) / 12
def A2H (h : ℝ) : ℝ := (h + 1) * (h + 3) * (2 * h - 1) / 720
def A3H (h : ℝ) : ℝ := -(h + 1) * (2 * h - 1) * (2 * h ^ 3 + 8 * h ^ 2 + 13 * h + 31) / 60480
def A4H (h : ℝ) : ℝ :=
  (h + 1) * (2 * h - 1) * (3 * h ^ 5 + 15 * h ^ 4 + 34 * h ^ 3 + 104 * h ^ 2 + 131 * h + 289) / 3628800

/-- The quartic Taylor polynomial of `Y` in the variable `w`. -/
def P4 (h w : ℝ) : ℝ := 1 + aH h * w + A2H h * w ^ 2 + A3H h * w ^ 3 + A4H h * w ^ 4

/-- `t ^ 4 * P4 h ((t - 1) ^ 2 / t)`, a polynomial in `t`. -/
def Q9 (h t : ℝ) : ℝ :=
  t ^ 4 + aH h * (t - 1) ^ 2 * t ^ 3 + A2H h * (t - 1) ^ 4 * t ^ 2 + A3H h * (t - 1) ^ 6 * t
    + A4H h * (t - 1) ^ 8

/-- `Y = q_* ^ 2 / t` with `t = exp x`, `θ = exp (h x)` and `p - 1 = (1 - h) / h`. -/
def Yx (h x : ℝ) : ℝ :=
  h ^ 2 * (Real.exp x - Real.exp (h * x)) ^ 2
    / ((1 - h) ^ 2 * (Real.exp (h * x) - 1) ^ 2 * Real.exp x)

/-- The width `w = (t - 1) ^ 2 / t` at `t = exp x`. -/
def wx (x : ℝ) : ℝ := width (Real.exp x)

/-- Coefficients of the exponential sum `h² t⁴ (t - θ)² - (1 - h)² t (θ - 1)² Q9 h t`. -/
def L9 (h : ℝ) : List (ℝ × ℕ × ℕ) :=
  [(-(h - 1)^2*(h + 1)*(2*h - 1)*(3*h^5 + 15*h^4 + 34*h^3 + 104*h^2 + 131*h + 289)/3628800, 9, 2),
    ((h - 1)^2*(h + 1)*(2*h - 1)*(3*h^5 + 15*h^4 + 34*h^3 + 104*h^2 + 131*h + 289)/1814400, 9, 1),
    (-(h - 1)^2*(h + 1)*(2*h - 1)*(3*h^5 + 15*h^4 + 34*h^3 + 104*h^2 + 131*h + 289)/3628800, 9, 0),
    ((h - 1)^2*(h + 1)*(2*h - 1)*(6*h^5 + 30*h^4 + 98*h^3 + 328*h^2 + 457*h + 1043)/907200, 8, 2),
    (-(h - 1)^2*(h + 1)*(2*h - 1)*(6*h^5 + 30*h^4 + 98*h^3 + 328*h^2 + 457*h + 1043)/453600, 8, 1),
    ((h - 1)^2*(h + 1)*(2*h - 1)*(6*h^5 + 30*h^4 + 98*h^3 + 328*h^2 + 457*h + 1043)/907200, 8, 0),
    (-(h - 1)^2*(h + 1)*(2*h - 1)*(21*h^5 + 105*h^4 + 418*h^3 + 1448*h^2 + 3347*h + 8593)/907200, 7, 2),
    ((h - 1)^2*(h + 1)*(2*h - 1)*(21*h^5 + 105*h^4 + 418*h^3 + 1448*h^2 + 3347*h + 8593)/453600, 7, 1),
    (-(h - 1)^2*(h + 1)*(2*h - 1)*(21*h^5 + 105*h^4 + 418*h^3 + 1448*h^2 + 3347*h + 8593)/907200, 7, 0),
    ((h - 1)^2*(2*h - 1)*(42*h^6 + 252*h^5 + 1136*h^4 + 4182*h^3 + 13055*h^2 + 35940*h + 101741)/907200, 6, 2),
    (-(h - 1)^2*(2*h - 1)*(42*h^6 + 252*h^5 + 1136*h^4 + 4182*h^3 + 13055*h^2 + 35940*h + 101741)/453600, 6, 1),
    ((h + 1)*(84*h^8 + 210*h^7 + 970*h^6 + 2680*h^5 + 6812*h^4 + 15385*h^3 + 56435*h^2 + 472765*h - 101741)/907200, 6, 0),
    (-(h - 1)^2*(42*h^7 + 231*h^6 + 1040*h^5 + 3749*h^4 + 12212*h^3 + 33443*h^2 + 130274*h + 287585)/362880, 5, 2),
    ((2*h - 1)*(21*h^8 + 84*h^7 + 352*h^6 + 1126*h^5 + 3440*h^4 + 8104*h^3 + 41852*h^2 - 130274*h - 287585)/181440, 5, 1),
    (-(h - 1)^2*(42*h^7 + 231*h^6 + 1040*h^5 + 3749*h^4 + 12212*h^3 + 33443*h^2 + 130274*h + 287585)/362880, 5, 0),
    ((h + 1)*(84*h^8 + 210*h^7 + 970*h^6 + 2680*h^5 + 6812*h^4 + 15385*h^3 + 56435*h^2 + 472765*h - 101741)/907200, 4, 2),
    (-(h - 1)^2*(2*h - 1)*(42*h^6 + 252*h^5 + 1136*h^4 + 4182*h^3 + 13055*h^2 + 35940*h + 101741)/453600, 4, 1),
    ((h - 1)^2*(2*h - 1)*(42*h^6 + 252*h^5 + 1136*h^4 + 4182*h^3 + 13055*h^2 + 35940*h + 101741)/907200, 4, 0),
    (-(h - 1)^2*(h + 1)*(2*h - 1)*(21*h^5 + 105*h^4 + 418*h^3 + 1448*h^2 + 3347*h + 8593)/907200, 3, 2),
    ((h - 1)^2*(h + 1)*(2*h - 1)*(21*h^5 + 105*h^4 + 418*h^3 + 1448*h^2 + 3347*h + 8593)/453600, 3, 1),
    (-(h - 1)^2*(h + 1)*(2*h - 1)*(21*h^5 + 105*h^4 + 418*h^3 + 1448*h^2 + 3347*h + 8593)/907200, 3, 0),
    ((h - 1)^2*(h + 1)*(2*h - 1)*(6*h^5 + 30*h^4 + 98*h^3 + 328*h^2 + 457*h + 1043)/907200, 2, 2),
    (-(h - 1)^2*(h + 1)*(2*h - 1)*(6*h^5 + 30*h^4 + 98*h^3 + 328*h^2 + 457*h + 1043)/453600, 2, 1),
    ((h - 1)^2*(h + 1)*(2*h - 1)*(6*h^5 + 30*h^4 + 98*h^3 + 328*h^2 + 457*h + 1043)/907200, 2, 0),
    (-(h - 1)^2*(h + 1)*(2*h - 1)*(3*h^5 + 15*h^4 + 34*h^3 + 104*h^2 + 131*h + 289)/3628800, 1, 2),
    ((h - 1)^2*(h + 1)*(2*h - 1)*(3*h^5 + 15*h^4 + 34*h^3 + 104*h^2 + 131*h + 289)/1814400, 1, 1),
    (-(h - 1)^2*(h + 1)*(2*h - 1)*(3*h^5 + 15*h^4 + 34*h^3 + 104*h^2 + 131*h + 289)/3628800, 1, 0)]

theorem L9_poly (h x : ℝ) :
    monoSum h (L9 h) x
      = h ^ 2 * Real.exp x ^ 4 * (Real.exp x - Real.exp (h * x)) ^ 2
        - (1 - h) ^ 2 * Real.exp x * (Real.exp (h * x) - 1) ^ 2 * Q9 h (Real.exp x) := by
  simp only [monoSum, L9, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Q9, aH, A2H,
    A3H, A4H]
  ring

theorem L9_moments (h : ℝ) : ∀ n < 12, moment (toExp h (L9 h)) n = 0 := by
  intro n hn
  interval_cases n <;>
    simp only [moment, toExp, L9, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;>
    push_cast <;> ring

theorem Y_sub_P4 (h x : ℝ) (hh1 : h ≠ 1) (hx : x ≠ 0) (hh0 : h ≠ 0) :
    Yx h x - P4 h (wx x)
      = monoSum h (L9 h) x
        / ((1 - h) ^ 2 * (Real.exp (h * x) - 1) ^ 2 * Real.exp x ^ 5) := by
  have hE : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have h1 : (1 - h) ≠ 0 := sub_ne_zero.mpr (Ne.symm hh1)
  have hT : Real.exp (h * x) - 1 ≠ 0 := by
    intro h0
    have : Real.exp (h * x) = Real.exp 0 := by rw [Real.exp_zero]; linarith
    have := Real.exp_injective this
    rcases mul_eq_zero.mp this with h' | h'
    · exact hh0 h'
    · exact hx h'
  rw [L9_poly]
  unfold Yx P4 Q9 wx width
  field_simp

/-- `Y - P4 (w) = o (w ^ 4)`. -/
theorem Y_limit (h : ℝ) (hh0 : 0 < h) (hh1 : h < 1) :
    Tendsto (fun x : ℝ => (Yx h x - P4 h (wx x)) / wx x ^ 4) (𝓝[≠] 0) (𝓝 0) := by
  have hH := expSum_tendsto_zero (toExp h (L9 h)) 12 10 (by norm_num) (L9_moments h)
  have hT := tendsto_exp_scaled h
  have hE := tendsto_exp_sub_one_div
  have hE1 : Tendsto (fun x : ℝ => Real.exp x) (𝓝[≠] 0) (𝓝 1) := by
    simpa using tendsto_exp_one 1
  have hden := ((tendsto_const_nhds (x := (1 - h) ^ 2)).mul (hT.pow 2)).mul hE1 |>.mul (hE.pow 8)
  have hne : (1 - h) ^ 2 * h ^ 2 * 1 * 1 ^ 8 ≠ 0 := by
    have : (1 - h) ≠ 0 := by linarith
    positivity
  have hq := hH.div hden hne
  rw [zero_div] at hq
  refine hq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx
  have hEne : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hE1ne : Real.exp x - 1 ≠ 0 := by
    intro h0
    have : Real.exp x = Real.exp 0 := by rw [Real.exp_zero]; linarith
    exact hx0 (Real.exp_injective this)
  have hTne : Real.exp (h * x) - 1 ≠ 0 := by
    intro h0
    have : Real.exp (h * x) = Real.exp 0 := by rw [Real.exp_zero]; linarith
    have := Real.exp_injective this
    rcases mul_eq_zero.mp this with h' | h'
    · exact hh0.ne' h'
    · exact hx0 h'
  have h1 : (1 - h) ≠ 0 := by linarith
  rw [Y_sub_P4 h x hh1.ne hx0 hh0.ne']
  simp only [Pi.div_apply, wx, width]
  rw [← monoSum_eq]
  field_simp

/-! ## Algebraic expansion of the inner radical -/

def pi1 (p : ℝ) : ℝ := -(p + 1) * (3 * p + 1) / (60 * p ^ 2)
def pi2 (p : ℝ) : ℝ := (p + 1) * (31 * p ^ 3 + 13 * p ^ 2 + 8 * p + 2) / (5040 * p ^ 4)
def piPoly (p w : ℝ) : ℝ := 1 + pi1 p * w + pi2 p * w ^ 2
def rho (p w : ℝ) : ℝ :=
  ((-(p + 1)^2*(31*p^3 + 13*p^2 + 8*p + 2)^2*(373*p^3 + 235*p^2 + 129*p + 27))*w^2 + (168*p^2*(p + 1)^2*(3*p + 1)*(31*p^3 + 13*p^2 + 8*p + 2)*(218*p^3 + 170*p^2 + 89*p + 17))*w + (-1008*p^4*(p + 1)*(100069*p^6 + 93830*p^5 + 83699*p^4 + 44372*p^3 + 15471*p^2 + 3886*p + 449))) / (25401600 * p ^ 8)
def beta (p : ℝ) : ℝ := rho p 0 / (V p 0 * 2)
def D4p (p : ℝ) : ℝ := a p * beta p - A4H (1 / p)

theorem ell_identity (p w : ℝ) (hp : 2 < p) :
    U p w - piPoly p w ^ 2 * V p w = w ^ 3 * rho p w := by
  have hp0 : p ≠ 0 := by linarith
  unfold U V base cPoly dPoly piPoly pi1 pi2 rho
  field_simp
  ring

theorem D4p_eq (p : ℝ) (hp : 2 < p) : D4p p = DegreesEfficiency.D4 (1 / p) := by
  have hp0 : p ≠ 0 := by linarith
  have h3 : 3 * p + 1 ≠ 0 := by linarith
  have h4 : 1 / p + 3 ≠ 0 := by
    have : 0 < 1 / p := by positivity
    linarith
  unfold D4p beta rho V base dPoly a A4H DegreesEfficiency.D4
  field_simp
  ring

theorem ell_zero (p : ℝ) (hp : 2 < p) : ell p 0 = 1 := by
  have hb : base p ≠ 0 := by
    have hp0 : 0 < p := by linarith
    unfold base
    positivity
  simp [ell, U, V, div_self hb]

theorem wx_pos (x : ℝ) (hx : x ≠ 0) : 0 < wx x := by
  apply width_positive (Real.exp x) (Real.exp_pos x)
  intro h1
  have : Real.exp x = Real.exp 0 := by rw [Real.exp_zero, h1]
  exact hx (Real.exp_injective this)

theorem tendsto_wx : Tendsto wx (𝓝[≠] 0) (𝓝 0) := by
  have hc : Continuous fun x : ℝ => (Real.exp x - 1) ^ 2 / Real.exp x :=
    ((Real.continuous_exp.sub continuous_const).pow 2).div Real.continuous_exp
      (fun x => (Real.exp_pos x).ne')
  have h2 : Tendsto (fun x : ℝ => (Real.exp x - 1) ^ 2 / Real.exp x) (𝓝[≠] 0) (𝓝 0) := by
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  exact h2

theorem ell_limit (p : ℝ) (hp : 2 < p) :
    Tendsto (fun x : ℝ => (ell p (wx x) - piPoly p (wx x)) / wx x ^ 3) (𝓝[≠] 0)
      (𝓝 (beta p)) := by
  have hw := tendsto_wx
  have hellc : ContinuousAt (ell p) 0 := (hasDerivAt_ell p 0 hp le_rfl).continuousAt
  have hell : Tendsto (fun x : ℝ => ell p (wx x)) (𝓝[≠] 0) (𝓝 1) := by
    have := hellc.tendsto.comp hw
    rwa [ell_zero p hp] at this
  have hpi : Tendsto (fun x : ℝ => piPoly p (wx x)) (𝓝[≠] 0) (𝓝 1) := by
    have hc : Continuous (piPoly p) := by unfold piPoly; fun_prop
    have h2 : Tendsto (piPoly p ∘ wx) (𝓝[≠] 0) (𝓝 (piPoly p 0)) := (hc.tendsto 0).comp hw
    have e0 : piPoly p 0 = 1 := by simp [piPoly]
    rw [e0] at h2
    exact h2
  have hrho : Tendsto (fun x : ℝ => rho p (wx x)) (𝓝[≠] 0) (𝓝 (rho p 0)) := by
    have hc : Continuous (rho p) := by unfold rho; fun_prop
    exact (hc.tendsto 0).comp hw
  have hV : Tendsto (fun x : ℝ => V p (wx x)) (𝓝[≠] 0) (𝓝 (V p 0)) := by
    have hc : Continuous (V p) := by unfold V; fun_prop
    exact (hc.tendsto 0).comp hw
  have hV0 : V p 0 ≠ 0 := (V_positive p 0 hp le_rfl).ne'
  have hsum := hell.add hpi
  have hq := hrho.div (hV.mul hsum) (mul_ne_zero hV0 (by norm_num))
  have e : rho p 0 / (V p 0 * (1 + 1)) = beta p := by unfold beta; norm_num
  rw [e] at hq
  refine hq.congr' ?_
  have hsne : ∀ᶠ x in 𝓝[≠] 0, ell p (wx x) + piPoly p (wx x) ≠ 0 :=
    hsum.eventually_ne (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hsne] with x hx hs
  have hx0 : x ≠ 0 := hx
  have hwpos := wx_pos x hx0
  have hVp := V_positive p (wx x) hp hwpos.le
  have hsq := ell_square p (wx x) hp hwpos.le
  have hid := ell_identity p (wx x) hp
  try simp only [Pi.div_apply, Pi.mul_apply, Pi.add_apply]
  rw [div_eq_div_iff (mul_ne_zero hVp.ne' hs) (pow_ne_zero 3 hwpos.ne')]
  linear_combination (-1 : ℝ) * hid - hsq

theorem radial_sub_P4 (p w : ℝ) (hp : 2 < p) :
    radial p w - P4 (1 / p) w = a p * w * (ell p w - piPoly p w) - A4H (1 / p) * w ^ 4 := by
  have hp0 : p ≠ 0 := by linarith
  unfold radial P4 piPoly pi1 pi2 a aH A2H A3H
  field_simp
  ring

theorem radial_limit (p : ℝ) (hp : 2 < p) :
    Tendsto (fun x : ℝ => (radial p (wx x) - P4 (1 / p) (wx x)) / wx x ^ 4) (𝓝[≠] 0)
      (𝓝 (D4p p)) := by
  have h1 := ((ell_limit p hp).const_mul (a p)).sub_const (A4H (1 / p))
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hw := (wx_pos x hx).ne'
  rw [radial_sub_P4 p (wx x) hp]
  field_simp

/-- The nested radical and the exact quantity differ by `D4 w ^ 4 + o (w ^ 4)`: equation (4.9). -/
theorem radial_Y_limit (p : ℝ) (hp : 2 < p) :
    Tendsto (fun x : ℝ => (radial p (wx x) - Yx (1 / p) x) / wx x ^ 4) (𝓝[≠] 0)
      (𝓝 (D4p p)) := by
  have hp0 : 0 < p := by linarith
  have hh0 : (0 : ℝ) < 1 / p := by positivity
  have hh1 : (1 : ℝ) / p < 1 := by
    rw [div_lt_one hp0]
    linarith
  have h := (radial_limit p hp).sub (Y_limit (1 / p) hh0 hh1)
  rw [sub_zero] at h
  refine h.congr fun x => ?_
  ring

/-! ## Contact of order eight and order nine -/

def kappa9 (p x : ℝ) : ℝ := 1 + (p - 1) * support p (Real.exp x)
def qStar (p x : ℝ) : ℝ :=
  (Real.exp x - Real.exp (1 / p * x)) / ((p - 1) * (Real.exp (1 / p * x) - 1))

theorem exp_scaled_ne (p x : ℝ) (hp : 0 < p) (hx : x ≠ 0) : Real.exp (1 / p * x) - 1 ≠ 0 := by
  intro h0
  have : Real.exp (1 / p * x) = Real.exp 0 := by rw [Real.exp_zero]; linarith
  have := Real.exp_injective this
  rcases mul_eq_zero.mp this with h' | h'
  · exact (by positivity : (1 / p : ℝ) ≠ 0) h'
  · exact hx h'

/-- The nested-radical support has contact of order eight with the exact support. -/
theorem contact_nine (p : ℝ) (hp : 2 < p) :
    Tendsto (fun x : ℝ => (kappa9 p x - kappaStarX p x) / x ^ 8) (𝓝[≠] 0)
      (𝓝 ((p - 1) * D4p p / 2)) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hRY := radial_Y_limit p hp
  have hE1 : Tendsto (fun x : ℝ => Real.exp x) (𝓝[≠] 0) (𝓝 1) := by
    simpa using tendsto_exp_one 1
  have hs : Tendsto (fun x : ℝ => support p (Real.exp x)) (𝓝[≠] 0) (𝓝 1) := by
    have hc : ContinuousAt (support p) 1 := (hasDerivAt_support p 1 hp one_pos).continuousAt
    have := hc.tendsto.comp hE1
    rwa [support_one] at this
  have hks := tendsto_kappaStarX p hp0
  have hstar : ∀ x : ℝ, x ≠ 0 → kappaStarX p x = 1 + (p - 1) * qStar p x := by
    intro x hx
    have hT := exp_scaled_ne p x hp0 hx
    have e : x / p = 1 / p * x := by ring
    unfold kappaStarX qStar
    rw [e]
    generalize Real.exp (1 / p * x) = T at hT ⊢
    field_simp
    ring
  have hq : Tendsto (qStar p) (𝓝[≠] 0) (𝓝 1) := by
    have := (hks.sub_const 1).div_const (p - 1)
    rw [div_self hp1.ne'] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [hstar x hx]
    field_simp
    ring
  have hwx : Tendsto (fun x : ℝ => wx x / x ^ 2) (𝓝[≠] 0) (𝓝 1) := by
    have := (tendsto_exp_sub_one_div.pow 2).div hE1 one_ne_zero
    simp only [one_pow, div_one] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    have hE := (Real.exp_pos x).ne'
    try simp only [Pi.div_apply, Pi.pow_apply]
    simp only [wx, width]
    field_simp
  have hmain := (((hE1.const_mul (p - 1)).mul hRY).mul (hwx.pow 4)).div (hs.add hq)
    (by norm_num)
  have e : (p - 1) * 1 * D4p p * 1 ^ 4 / (1 + 1) = (p - 1) * D4p p / 2 := by ring
  rw [e] at hmain
  refine hmain.congr' ?_
  have hsne : ∀ᶠ x in 𝓝[≠] 0, support p (Real.exp x) + qStar p x ≠ 0 :=
    (hs.add hq).eventually_ne (by norm_num)
  filter_upwards [self_mem_nhdsWithin, hsne] with x hx hsq
  have hx0 : x ≠ 0 := hx
  have hEpos := Real.exp_pos x
  have hwpos := wx_pos x hx0
  have hT := exp_scaled_ne p x hp0 hx0
  have hs2 := support_square p (Real.exp x) hp hEpos
  have hpp : (1 : ℝ) - 1 / p ≠ 0 := by
    have : (1 : ℝ) / p < 1 := by rw [div_lt_one hp0]; linarith
    linarith
  have hq2 : qStar p x ^ 2 = Real.exp x * Yx (1 / p) x := by
    unfold qStar Yx
    field_simp
  have key : (support p (Real.exp x) - qStar p x) * (support p (Real.exp x) + qStar p x)
      = Real.exp x * (radial p (wx x) - Yx (1 / p) x) := by
    have hw : wx x = width (Real.exp x) := rfl
    rw [hw]
    linear_combination hs2 - hq2
  try simp only [Pi.div_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply]
  rw [hstar x hx0]
  unfold kappa9
  have h1 : (p - 1) * Real.exp x * ((radial p (wx x) - Yx (1 / p) x) / wx x ^ 4)
      * (wx x / x ^ 2) ^ 4
      = (p - 1) * ((support p (Real.exp x) - qStar p x)
          * (support p (Real.exp x) + qStar p x)) / x ^ 8 := by
    rw [key]
    field_simp
  rw [h1]
  field_simp
  ring

theorem correction_eq_kappa (p x : ℝ) :
    correction p (Real.exp x) = (kappa9 p x - 1 + Real.exp x) / kappa9 p x := by
  have : kappa9 p x - 1 + Real.exp x = Real.exp x + (p - 1) * support p (Real.exp x) := by
    unfold kappa9
    ring
  rw [this]
  rfl

/-- Order nine in the variable `x = log t`. -/
theorem order_nine_x (p : ℝ) (hp : 2 < p) :
    Tendsto (fun x : ℝ => (Real.log (correction p (Real.exp x)) - x / p) / x ^ 9) (𝓝[≠] 0)
      (𝓝 (-((p - 1) * D4p p / 2) / p ^ 2)) := by
  have h := contact_limit (kappa9 p) p (by linarith) 8 (by norm_num) _ (contact_nine p hp)
  refine h.congr fun x => ?_
  rw [correction_eq_kappa]

/-- **Theorem 4.1.** For every real `p > 2`, the logarithmic error `ê = log (u / r)` of the
nested-radical iteration satisfies `ê₊ / ê ^ 9 → c9 p`, where `ê₊ = ê + log (correction p t)` and
`t = exp (-p ê)`. -/
theorem order_nine (p : ℝ) (hp : 2 < p) :
    Tendsto (fun e : ℝ => (e + Real.log (correction p (Real.exp (-p * e)))) / e ^ 9) (𝓝[≠] 0)
      (𝓝 (DegreesEfficiency.c9 p)) := by
  have hp0 : p ≠ 0 := by linarith
  have hx := order_nine_x p hp
  have hsub : Tendsto (fun e : ℝ => -p * e) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : Continuous fun e : ℝ => -p * e := by fun_prop
      simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    · filter_upwards [self_mem_nhdsWithin] with e he
      have he0 : e ≠ 0 := he
      exact mul_ne_zero (neg_ne_zero.mpr hp0) he0
  have h := (hx.comp hsub).const_mul ((-p) ^ 9)
  have e9 : (-p) ^ 9 * (-((p - 1) * D4p p / 2) / p ^ 2) = DegreesEfficiency.c9 p := by
    rw [DegreesEfficiency.c9_eq_D4 hp, D4p_eq p hp]
    field_simp
  rw [e9] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with e he
  have he0 : e ≠ 0 := he
  simp only [Function.comp]
  field_simp
  ring

/-- The quantity in `order_nine` is the logarithmic error of one step of the iteration. -/
theorem log_error_step (p X r e : ℝ) (hp : 2 < p) (hr : 0 < r) (hX : r ^ p = X) :
    Real.log (step p X (r * Real.exp e) / r)
      = e + Real.log (correction p (Real.exp (-p * e))) := by
  have hXpos : 0 < X := by rw [← hX]; exact Real.rpow_pos_of_pos hr p
  have ht : X / (r * Real.exp e) ^ p = Real.exp (-p * e) := by
    rw [Real.mul_rpow hr.le (Real.exp_pos e).le, hX, ← Real.exp_mul, div_mul_eq_div_div,
      div_self hXpos.ne', one_div, ← Real.exp_neg]
    congr 1
    ring
  have hc := correction_positive p (Real.exp (-p * e)) hp (Real.exp_pos _)
  unfold step
  rw [ht]
  have : r * Real.exp e * correction p (Real.exp (-p * e)) / r
      = Real.exp e * correction p (Real.exp (-p * e)) := by
    field_simp
  rw [this, Real.log_mul (Real.exp_pos e).ne' hc.ne', Real.log_exp]

end LeanMath.Papers.NestedOrderNine
