import LeanMath.Papers.RectangleFixedCircle
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Whole-branch strict contraction of the fixed-circle inverse [2/2] correction.

V20 stated as conjecture (29) that on the whole transverse real branch
`τ₋ < t < τ₊`, `t ≠ 1`, the fixed-circle update strictly decreases the
logarithmic error: `|log t / p + log v(t)| < |log t| / p`.
This module proves it for every integer degree `p ≥ 3`.

Reduction. With `t = N(v)/D(v)` on the descending branch `Q(v) < 0`
(equivalently `v₋ < v < v₊`), the inequality is equivalent to
`log v · h(v) < 0` where `h(v) = p log v + 2 log N(v) − 2 log D(v)`.
The derivative certificate `pND + v(N'D − ND') = pAC(v−1)⁴` gives
`h'(v) = p S(v) / (v N D)` with the quartic `S = 2AC(v−1)⁴ − ND`,
and `S(1+u)/u²` is strictly increasing on `u > 0`, so `S` changes sign at most
once on `(1, v₊)`. Hence `h < 0` on `(1, v₊)` as soon as `h(v₊) < 0`, i.e.
`v₊ᵖ N(v₊)² < D(v₊)²`, which is checked by rational bounds for `3 ≤ p ≤ 9`
and by an exponential bound for `p ≥ 10`. Reciprocity transfers the result
to `(v₋, 1)`. -/
noncomputable section
namespace LeanMath.Papers.RectangleFixedCircleBranch
open LeanMath.Papers.RectangleFixedCircle
open Set

/-- Sign polynomial of the contraction functional. -/
def S (p v : ℝ) := 2*A p*C p*(v-1)^4 - N p v*D p v
/-- Branch quadratic; the selected descending branch `R'(v) < 0` is `Q < 0`. -/
def Q (p v : ℝ) := (p^2-4)*(v^2+1) - 2*(p^2+2)*v
/-- Contraction functional `h(v) = p log v + 2 log t`, `t = N/D`. -/
def h (p v : ℝ) := p*Real.log v + 2*Real.log (N p v) - 2*Real.log (D p v)
/-- `r = √(12(p²−1))`. -/
def r (p : ℝ) := Real.sqrt (12*(p^2-1))
/-- Upper branch endpoint offset `u₊ = v₊ − 1 = (6 + r)/(p²−4)`. -/
def uplus (p : ℝ) := (6 + r p)/(p^2-4)
def vplus (p : ℝ) := 1 + uplus p
/-- Certificate polynomial for the monotonicity of `S(1+u)/u²`. -/
def slopeCert (p u₁ u₂ : ℝ) :=
  A p*C p*u₁^2*u₂^2*(u₁+u₂) + 12*(p^2-4)*u₁^2*u₂^2 + 288*u₁*u₂ + 144*(u₁+u₂)
/-- `N` and `D` at a point of the branch boundary, using `(p²−4)u² = 12(u+1)`. -/
def Nred (p u : ℝ) := 6*(2*(2*p+1) - (p^2-2*p-2)*u)/(p+2)
def Dred (p u : ℝ) := 6*(2*(2*p-1) + (p^2+2*p-2)*u)/(p-2)

/-! ### Polynomial identities -/

theorem branch_derivative (p v : ℝ) :
    (2*C p*v-2*B p)*D p v - N p v*(2*A p*v-2*B p) = 12*p*Q p v := by
  unfold N D A B C Q; ring

theorem S_expand (p u : ℝ) :
    S p (1+u) = A p*C p*u^4 + 12*(p^2-4)*u^3 + 12*(p^2-16)*u^2 - 288*u - 144 := by
  unfold S N D A B C; ring

theorem S_slope (p u₁ u₂ : ℝ) :
    u₂^2*S p (1+u₁) - u₁^2*S p (1+u₂) = -(u₂-u₁)*slopeCert p u₁ u₂ := by
  unfold slopeCert S N D A B C; ring

theorem Q_shift (p u : ℝ) : Q p (1+u) = (p^2-4)*u^2 - 12*u - 12 := by
  unfold Q; ring

theorem ND_branch (p v : ℝ) : N p v*D p v - A p*C p*(v-1)^4 + 12*v*Q p v = 0 := by
  unfold N D A B C Q; ring

theorem Q_reciprocal (p v : ℝ) (hv : v ≠ 0) : Q p (1/v)*v^2 = Q p v := by
  unfold Q; field_simp; ring

theorem AC_pos (p : ℝ) (hp : 2 < p) : 0 < A p*C p := by
  unfold A C
  have h1 : 0 < p-1 := by linarith
  have h2 : 0 < p-2 := by linarith
  have h3 : 0 < p+1 := by linarith
  have h4 : 0 < p+2 := by linarith
  positivity

/-! ### One sign change of `S` on the positive axis -/

theorem slopeCert_pos (p u₁ u₂ : ℝ) (hp : 2 < p) (h1 : 0 < u₁) (h2 : 0 < u₂) :
    0 < slopeCert p u₁ u₂ := by
  unfold slopeCert
  have hac := AC_pos p hp
  have hp4 : 0 < p^2-4 := by nlinarith
  have e1 : 0 < A p*C p*u₁^2*u₂^2*(u₁+u₂) := by
    have : 0 < u₁^2*u₂^2*(u₁+u₂) := by positivity
    nlinarith
  have e2 : 0 < 12*(p^2-4)*u₁^2*u₂^2 := by
    have : 0 < u₁^2*u₂^2 := by positivity
    nlinarith
  nlinarith [mul_pos h1 h2]

theorem S_neg_before (p u₁ u₂ : ℝ) (hp : 2 < p) (h1 : 0 < u₁) (h12 : u₁ < u₂)
    (hS : S p (1+u₂) ≤ 0) : S p (1+u₁) < 0 := by
  have h2 : 0 < u₂ := by linarith
  have hc := slopeCert_pos p u₁ u₂ hp h1 h2
  have hs := S_slope p u₁ u₂
  have ha : u₁^2*S p (1+u₂) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg u₁) hS
  have hb : 0 < (u₂-u₁)*slopeCert p u₁ u₂ := mul_pos (by linarith) hc
  by_contra hcon
  have hcon' : 0 ≤ S p (1+u₁) := not_lt.mp hcon
  nlinarith [mul_nonneg (sq_nonneg u₂) hcon']

theorem S_pos_after (p u₁ u₂ : ℝ) (hp : 2 < p) (h1 : 0 < u₁) (h12 : u₁ < u₂)
    (hS : 0 ≤ S p (1+u₁)) : 0 < S p (1+u₂) := by
  have h2 : 0 < u₂ := by linarith
  have hc := slopeCert_pos p u₁ u₂ hp h1 h2
  have hs := S_slope p u₁ u₂
  have ha : 0 ≤ u₂^2*S p (1+u₁) := mul_nonneg (sq_nonneg u₂) hS
  have hb : 0 < (u₂-u₁)*slopeCert p u₁ u₂ := mul_pos (by linarith) hc
  by_contra hcon
  have hcon' : S p (1+u₂) ≤ 0 := not_lt.mp hcon
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg u₁) hcon']

/-! ### The derivative of `h` -/

theorem N_hasDerivAt (p v : ℝ) : HasDerivAt (fun v => N p v) (2*C p*v-2*B p) v := by
  convert! ((((hasDerivAt_id v).pow 2).const_mul (C p)).sub
    ((hasDerivAt_id v).const_mul (2*B p))).add_const (A p) using 1
  dsimp [N]
  ring

theorem D_hasDerivAt (p v : ℝ) : HasDerivAt (fun v => D p v) (2*A p*v-2*B p) v := by
  convert! ((((hasDerivAt_id v).pow 2).const_mul (A p)).sub
    ((hasDerivAt_id v).const_mul (2*B p))).add_const (C p) using 1
  dsimp [D]
  ring

theorem h_hasDerivAt (p v : ℝ) (hp : 2 < p) (hv : 0 < v) :
    HasDerivAt (h p) (p*S p v/(v*N p v*D p v)) v := by
  have hN := (positive_quadratics p v hp).1
  have hD := (positive_quadratics p v hp).2
  have hl := (Real.hasDerivAt_log hv.ne').const_mul p
  have hn := ((N_hasDerivAt p v).log hN.ne').const_mul 2
  have hd := ((D_hasDerivAt p v).log hD.ne').const_mul 2
  have hh := (hl.add hn).sub hd
  convert! hh using 1
  have hv0 := hv.ne'
  have hN0 := hN.ne'
  have hD0 := hD.ne'
  unfold S
  field_simp
  linear_combination (-2:ℝ)*derivative_certificate p v

theorem h_one (p : ℝ) : h p 1 = 0 := by
  simp [h, (at_one p).1, (at_one p).2]

theorem h_anti (p a b : ℝ) (hp : 2 < p) (ha : 0 < a) (hab : a < b)
    (hS : ∀ v ∈ Ioo a b, S p v < 0) : h p b < h p a := by
  have hcont : ContinuousOn (h p) (Icc a b) := fun v hv =>
    (h_hasDerivAt p v hp (by linarith [hv.1])).continuousAt.continuousWithinAt
  have hderiv : ∀ v ∈ interior (Icc a b), deriv (h p) v < 0 := by
    intro v hv
    rw [interior_Icc] at hv
    have hv0 : 0 < v := by linarith [hv.1]
    rw [(h_hasDerivAt p v hp hv0).deriv]
    have hN := (positive_quadratics p v hp).1
    have hD := (positive_quadratics p v hp).2
    have hs := hS v hv
    apply div_neg_of_neg_of_pos
    · nlinarith
    · exact mul_pos (mul_pos hv0 hN) hD
  exact strictAntiOn_of_deriv_neg (convex_Icc a b) hcont hderiv
    (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab

theorem h_mono (p a b : ℝ) (hp : 2 < p) (ha : 0 < a) (hab : a < b)
    (hS : ∀ v ∈ Ioo a b, 0 < S p v) : h p a < h p b := by
  have hcont : ContinuousOn (h p) (Icc a b) := fun v hv =>
    (h_hasDerivAt p v hp (by linarith [hv.1])).continuousAt.continuousWithinAt
  have hderiv : ∀ v ∈ interior (Icc a b), 0 < deriv (h p) v := by
    intro v hv
    rw [interior_Icc] at hv
    have hv0 : 0 < v := by linarith [hv.1]
    rw [(h_hasDerivAt p v hp hv0).deriv]
    have hN := (positive_quadratics p v hp).1
    have hD := (positive_quadratics p v hp).2
    have hs := hS v hv
    apply div_pos
    · nlinarith
    · exact mul_pos (mul_pos hv0 hN) hD
  exact strictMonoOn_of_deriv_pos (convex_Icc a b) hcont hderiv
    (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab

/-! ### The branch endpoint -/

theorem r_sq (p : ℝ) (hp : 1 ≤ p) : r p^2 = 12*(p^2-1) :=
  Real.sq_sqrt (by nlinarith)

theorem r_nonneg (p : ℝ) : 0 ≤ r p := Real.sqrt_nonneg _

theorem uplus_rel (p : ℝ) (hp : 2 < p) : (p^2-4)*uplus p^2 = 12*(uplus p+1) := by
  have hp4 : p^2-4 ≠ 0 := by nlinarith
  have hr := r_sq p (by linarith)
  unfold uplus
  field_simp
  linear_combination hr

theorem uplus_pos (p : ℝ) (hp : 2 < p) : 0 < uplus p := by
  unfold uplus
  have hp4 : 0 < p^2-4 := by nlinarith
  have := r_nonneg p
  positivity

theorem Q_vplus (p : ℝ) (hp : 2 < p) : Q p (vplus p) = 0 := by
  unfold vplus
  rw [Q_shift]
  linear_combination uplus_rel p hp

/-- On the descending branch, points above one lie below the endpoint. -/
theorem lt_uplus_of_branch (p u : ℝ) (hp : 2 < p) (hu : 0 < u) (hQ : Q p (1+u) < 0) :
    u < uplus p := by
  rw [Q_shift] at hQ
  have hrel := uplus_rel p hp
  have hp4 : 0 < p^2-4 := by nlinarith
  have hu6 : 6 ≤ (p^2-4)*uplus p := by
    unfold uplus
    rw [mul_div_cancel₀ _ hp4.ne']
    linarith [r_nonneg p]
  by_contra hcon
  have hcon' : uplus p ≤ u := not_lt.mp hcon
  have key : (p^2-4)*u^2 - 12*u - 12 - ((p^2-4)*uplus p^2 - 12*uplus p - 12)
      = (u-uplus p)*((p^2-4)*(u+uplus p) - 12) := by ring
  have hz : (p^2-4)*uplus p^2 - 12*uplus p - 12 = 0 := by linarith
  have hpos : 0 ≤ (u-uplus p)*((p^2-4)*(u+uplus p) - 12) := by
    apply mul_nonneg (by linarith)
    nlinarith [uplus_pos p hp]
  linarith

theorem N_reduced (p u : ℝ) (hp : 2 < p) (hu : (p^2-4)*u^2 = 12*(u+1)) :
    N p (1+u) = Nred p u := by
  unfold N Nred A B C
  have : p+2 ≠ 0 := by linarith
  field_simp
  linear_combination (p-1)*hu

theorem D_reduced (p u : ℝ) (hp : 2 < p) (hu : (p^2-4)*u^2 = 12*(u+1)) :
    D p (1+u) = Dred p u := by
  unfold D Dred A B C
  have : p-2 ≠ 0 := by linarith
  field_simp
  linear_combination (p+1)*hu

/-- Endpoint inequality from rational bounds on `r`; used for `3 ≤ p ≤ 9`. -/
theorem endpoint_of_bounds (n : ℕ) (hn : 3 ≤ n) (rlo rhi : ℝ) (h0 : 0 ≤ rlo) (h0' : 0 ≤ rhi)
    (hlo : rlo^2 ≤ 12*((n:ℝ)^2-1)) (hhi : 12*((n:ℝ)^2-1) ≤ rhi^2)
    (hnum : (1+(6+rhi)/((n:ℝ)^2-4))^n * Nred n ((6+rlo)/((n:ℝ)^2-4))^2
      < Dred n ((6+rlo)/((n:ℝ)^2-4))^2) :
    vplus n^n * N n (vplus n)^2 < D n (vplus n)^2 := by
  set p : ℝ := (n:ℝ) with hpdef
  have hp3 : 3 ≤ p := by rw [hpdef]; exact_mod_cast hn
  have hp : 2 < p := by linarith
  have hp4 : 0 < p^2-4 := by nlinarith
  have hrlo : rlo ≤ r p := Real.le_sqrt_of_sq_le hlo
  have hrhi : r p ≤ rhi := (Real.sqrt_le_left h0').mpr hhi
  set u := uplus p with hu
  set ulo := (6+rlo)/(p^2-4) with hulo
  set uhi := (6+rhi)/(p^2-4) with huhi
  have hu_lo : ulo ≤ u := by
    rw [hulo, hu]; unfold uplus
    exact div_le_div_of_nonneg_right (by linarith) hp4.le
  have hu_hi : u ≤ uhi := by
    rw [huhi, hu]; unfold uplus
    exact div_le_div_of_nonneg_right (by linarith) hp4.le
  have hulo0 : 0 ≤ ulo := by rw [hulo]; positivity
  have hrel := uplus_rel p hp
  have hvp : vplus p = 1+u := by rw [hu]; rfl
  rw [hvp, N_reduced p u hp hrel, D_reduced p u hp hrel]
  have hNpos : 0 < Nred p u := by
    rw [← N_reduced p u hp hrel]; exact (positive_quadratics p (1+u) hp).1
  have hp2 : 0 < p+2 := by linarith
  have hpm2 : 0 < p-2 := by linarith
  have hNle : Nred p u ≤ Nred p ulo := by
    unfold Nred
    apply div_le_div_of_nonneg_right _ hp2.le
    have : 0 ≤ p^2-2*p-2 := by nlinarith
    nlinarith
  have hDle : Dred p ulo ≤ Dred p u := by
    unfold Dred
    apply div_le_div_of_nonneg_right _ hpm2.le
    have : 0 ≤ p^2+2*p-2 := by nlinarith
    nlinarith
  have hDlo_pos : 0 < Dred p ulo := by
    unfold Dred
    apply div_pos _ hpm2
    have : 0 ≤ p^2+2*p-2 := by nlinarith
    nlinarith
  have hpow : (1+u)^n ≤ (1+uhi)^n :=
    pow_le_pow_left₀ (by linarith [uplus_pos p hp]) (by linarith) n
  have hN2 : Nred p u^2 ≤ Nred p ulo^2 := pow_le_pow_left₀ hNpos.le hNle 2
  have hD2 : Dred p ulo^2 ≤ Dred p u^2 := pow_le_pow_left₀ hDlo_pos.le hDle 2
  calc (1+u)^n * Nred p u^2 ≤ (1+uhi)^n * Nred p ulo^2 :=
        mul_le_mul hpow hN2 (by positivity) (by positivity)
    _ < Dred p ulo^2 := hnum
    _ ≤ Dred p u^2 := hD2

theorem endpoint_small (n : ℕ) (hn : 3 ≤ n) (hn' : n ≤ 9) :
    vplus n^n * N n (vplus n)^2 < D n (vplus n)^2 := by
  interval_cases n
  · exact endpoint_of_bounds 3 (by norm_num) (979/100) (49/5) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [Nred, Dred])
  · exact endpoint_of_bounds 4 (by norm_num) (1341/100) (671/50) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [Nred, Dred])
  · exact endpoint_of_bounds 5 (by norm_num) (1697/100) (849/50) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [Nred, Dred])
  · exact endpoint_of_bounds 6 (by norm_num) (2049/100) (41/2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [Nred, Dred])
  · exact endpoint_of_bounds 7 (by norm_num) 24 (2401/100) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [Nred, Dred])
  · exact endpoint_of_bounds 8 (by norm_num) (2749/100) (55/2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [Nred, Dred])
  · exact endpoint_of_bounds 9 (by norm_num) (1549/50) (3099/100) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num [Nred, Dred])

/-- Endpoint inequality for `p ≥ 10`, by `(1+u)^p ≤ e^{pu} ≤ e^5` and `D ≥ 12.3 N`. -/
theorem endpoint_large (n : ℕ) (hn : 10 ≤ n) :
    vplus n^n * N n (vplus n)^2 < D n (vplus n)^2 := by
  set p : ℝ := (n:ℝ) with hpdef
  have hp10 : 10 ≤ p := by rw [hpdef]; exact_mod_cast hn
  have hp : 2 < p := by linarith
  have hp4 : 0 < p^2-4 := by nlinarith
  -- bounds on r
  have hrhi : r p ≤ 347/100*p := by
    apply (Real.sqrt_le_left (by linarith)).mpr
    nlinarith
  have hrlo : 346/100*p-1 ≤ r p := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  set u := uplus p with hu
  have hrel := uplus_rel p hp
  have hvp : vplus p = 1+u := by rw [hu]; rfl
  have hupos : 0 < u := uplus_pos p hp
  have hu_hi : u*(p^2-4) ≤ 6+347/100*p := by
    rw [hu]; unfold uplus; rw [div_mul_cancel₀ _ hp4.ne']; linarith
  have hu_lo : 346/100*p+5 ≤ u*(p^2-4) := by
    rw [hu]; unfold uplus; rw [div_mul_cancel₀ _ hp4.ne']; linarith
  -- p·u ≤ 5
  have hpu : p*u ≤ 5 := by
    have h1 : p*(u*(p^2-4)) ≤ p*(6+347/100*p) := mul_le_mul_of_nonneg_left hu_hi (by linarith)
    have h2 : p*(6+347/100*p) ≤ 5*(p^2-4) := by nlinarith
    have h3 : p*u*(p^2-4) ≤ 5*(p^2-4) := by nlinarith
    exact le_of_mul_le_mul_right h3 hp4
  -- (1+u)^n < 148.42
  have hexp : (1+u)^n < 14842/100 := by
    have e1 : (1+u)^n ≤ Real.exp u^n :=
      pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp u]) n
    have e2 : Real.exp u^n = Real.exp (p*u) := by
      rw [← Real.exp_nat_mul]
    have e3 : Real.exp (p*u) ≤ Real.exp 5 := Real.exp_le_exp.mpr hpu
    have e4 : Real.exp 5 = Real.exp 1^5 := by
      rw [Real.exp_one_pow]; norm_num
    have e5 : Real.exp 1^5 < (27182818286/10000000000:ℝ)^5 := by
      have := Real.exp_one_lt_d9
      have h0 := (Real.exp_pos 1).le
      gcongr
      norm_num at this ⊢
      linarith
    have e6 : (27182818286/10000000000:ℝ)^5 < 14842/100 := by norm_num
    linarith
  -- D ≥ 12.3 N at the endpoint
  rw [hvp, N_reduced p u hp hrel, D_reduced p u hp hrel]
  have hNpos : 0 < Nred p u := by
    rw [← N_reduced p u hp hrel]; exact (positive_quadratics p (1+u) hp).1
  have hp2 : 0 < p+2 := by linarith
  have hpm2 : 0 < p-2 := by linarith
  have hpoly : 0 ≤ 409*p^4 - 5046*p^3 + 46018*p^2 - 14904*p + 22600 := by
    have hq : 0 ≤ p-10 := by linarith
    nlinarith [pow_nonneg hq 4, pow_nonneg hq 3, pow_nonneg hq 2]
  have hkey : 123/10*Nred p u ≤ Dred p u := by
    unfold Nred Dred
    rw [← mul_div_assoc, div_le_div_iff₀ hp2 hpm2]
    -- linear in u with positive coefficient; true at the lower bound of u
    have hc : 0 < (p+2)*(p^2+2*p-2) + 123/10*(p-2)*(p^2-2*p-2) := by nlinarith
    have hlin : (346/100*p+5)*((p+2)*(p^2+2*p-2) + 123/10*(p-2)*(p^2-2*p-2))
        ≥ (p^2-4)*(123/10*(p-2)*2*(2*p+1) - (p+2)*2*(2*p-1)) := by
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hu_lo hc.le]
  have hN2 : (123/10)^2*Nred p u^2 ≤ Dred p u^2 := by
    have := pow_le_pow_left₀ (by linarith) hkey 2
    nlinarith
  have hN2pos : 0 < Nred p u^2 := by positivity
  nlinarith

theorem endpoint (n : ℕ) (hn : 3 ≤ n) :
    vplus n^n * N n (vplus n)^2 < D n (vplus n)^2 := by
  by_cases h9 : n ≤ 9
  · exact endpoint_small n hn h9
  · exact endpoint_large n (by omega)

theorem h_vplus_neg (n : ℕ) (hn : 3 ≤ n) : h n (vplus n) < 0 := by
  set p : ℝ := (n:ℝ) with hpdef
  have hp : 2 < p := by
    have : (3:ℝ) ≤ p := by rw [hpdef]; exact_mod_cast hn
    linarith
  have hv : 0 < vplus p := by unfold vplus; linarith [uplus_pos p hp]
  have hN := (positive_quadratics p (vplus p) hp).1
  have hD := (positive_quadratics p (vplus p) hp).2
  have he := endpoint n hn
  have hlog := Real.log_lt_log (by positivity) he
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  unfold h
  push_cast at hlog
  linarith

/-! ### Main theorem -/

/-- `h < 0` above one on the descending branch. -/
theorem h_neg_of_branch (n : ℕ) (hn : 3 ≤ n) (v : ℝ) (hv : 1 < v) (hQ : Q n v < 0) :
    h n v < 0 := by
  set p : ℝ := (n:ℝ) with hpdef
  have hp : 2 < p := by
    have : (3:ℝ) ≤ p := by rw [hpdef]; exact_mod_cast hn
    linarith
  have hu : v = 1+(v-1) := by ring
  have hvlt : v < vplus p := by
    have := lt_uplus_of_branch p (v-1) hp (by linarith) (by rw [← hu]; exact hQ)
    unfold vplus; linarith
  by_cases hS : S p v ≤ 0
  · have hall : ∀ w ∈ Ioo 1 v, S p w < 0 := by
      intro w hw
      have := S_neg_before p (w-1) (v-1) hp (by linarith [hw.1]) (by linarith [hw.2])
        (by rw [← hu]; exact hS)
      have e : 1+(w-1) = w := by ring
      rwa [e] at this
    have := h_anti p 1 v hp one_pos hv hall
    rwa [h_one] at this
  · rw [not_le] at hS
    have hall : ∀ w ∈ Ioo v (vplus p), 0 < S p w := by
      intro w hw
      have := S_pos_after p (v-1) (w-1) hp (by linarith) (by linarith [hw.1])
        (by rw [← hu]; exact hS.le)
      have e : 1+(w-1) = w := by ring
      rwa [e] at this
    have h1 := h_mono p v (vplus p) hp (by linarith) hvlt hall
    have h2 := h_vplus_neg n hn
    linarith

theorem h_reciprocal (p v : ℝ) (hp : 2 < p) (hv : 0 < v) : h p (1/v) = -h p v := by
  have hN := (positive_quadratics p v hp).1
  have hD := (positive_quadratics p v hp).2
  have hr := reciprocity p v hv.ne'
  have e1 : N p (1/v) = D p v/v^2 := by
    rw [← hr.1]; field_simp
  have e2 : D p (1/v) = N p v/v^2 := by
    rw [← hr.2]; field_simp
  unfold h
  rw [e1, e2, Real.log_div hD.ne' (by positivity), Real.log_div hN.ne' (by positivity),
    Real.log_pow, one_div, Real.log_inv]
  push_cast
  ring

/-- `h > 0` below one on the descending branch. -/
theorem h_pos_of_branch (n : ℕ) (hn : 3 ≤ n) (v : ℝ) (hv0 : 0 < v) (hv : v < 1)
    (hQ : Q n v < 0) : 0 < h n v := by
  set p : ℝ := (n:ℝ) with hpdef
  have hp : 2 < p := by
    have : (3:ℝ) ≤ p := by rw [hpdef]; exact_mod_cast hn
    linarith
  have hw : 1 < 1/v := by rw [lt_div_iff₀ hv0]; linarith
  have hQ' : Q p (1/v) < 0 := by
    have := Q_reciprocal p v hv0.ne'
    have hv2 : 0 < v^2 := by positivity
    nlinarith
  have := h_neg_of_branch n hn (1/v) hw hQ'
  rw [h_reciprocal p v hp hv0] at this
  linarith

/-- **Whole-branch strict contraction** (V20 conjecture (29)).
For every integer degree `p ≥ 3` and every point `v ≠ 1` of the selected
descending branch `Q(v) < 0` (that is `v₋ < v < v₊`), with `t = N(v)/D(v)`
the residual, the fixed-circle update `s⁺ = s v` satisfies
`|log t / p + log v| < |log t| / p`: the logarithmic error strictly decreases. -/
theorem whole_branch_contraction (n : ℕ) (hn : 3 ≤ n) (v : ℝ) (hv0 : 0 < v) (hv1 : v ≠ 1)
    (hQ : Q n v < 0) :
    |Real.log (N n v/D n v)/n + Real.log v| < |Real.log (N n v/D n v)/n| := by
  set p : ℝ := (n:ℝ) with hpdef
  have hp : 2 < p := by
    have : (3:ℝ) ≤ p := by rw [hpdef]; exact_mod_cast hn
    linarith
  have hp0 : p ≠ 0 := by linarith
  have hN := (positive_quadratics p v hp).1
  have hD := (positive_quadratics p v hp).2
  set e := Real.log (N p v/D p v)/p with he
  set l := Real.log v with hl
  have hh : h p v = p*(l+2*e) := by
    unfold h
    rw [he, hl, Real.log_div hN.ne' hD.ne']
    field_simp
    ring
  have hlh : l*h p v < 0 := by
    rcases lt_or_gt_of_ne hv1 with hlt | hgt
    · have := h_pos_of_branch n hn v hv0 hlt hQ
      have hl0 : l < 0 := Real.log_neg hv0 hlt
      exact mul_neg_of_neg_of_pos hl0 this
    · have := h_neg_of_branch n hn v hgt hQ
      have hl0 : 0 < l := Real.log_pos hgt
      exact mul_neg_of_pos_of_neg hl0 this
  have hsq : (e+l)^2 < e^2 := by
    have : (e+l)^2 - e^2 = l*(l+2*e) := by ring
    have hpp : 0 < p := by linarith
    have : l*(l+2*e) < 0 := by
      rw [hh] at hlh
      nlinarith
    linarith
  exact sq_lt_sq.mp hsq

end LeanMath.Papers.RectangleFixedCircleBranch
