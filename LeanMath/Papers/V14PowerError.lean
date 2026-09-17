import LeanMath.Papers.V14RationalCertificate
import LeanMath.Papers.V14PolynomialGate

/-! Differential comparison for the small diagonal degrees of Proposition 13.5. -/
noncomputable section
namespace LeanMath.Papers.V14PowerError
open Real Set Polynomial
open LeanMath.Papers.V14RationalCertificate LeanMath.Papers.Cayley

def primitive (n : ℕ) (k x : ℝ) : ℝ := k*x^(n+1)/(n+1)

theorem primitive_deriv (n : ℕ) (k x : ℝ) :
    HasDerivAt (primitive n k) (k*x^n) x := by
  have hn : (n:ℝ)+1≠0 := by positivity
  convert! (((hasDerivAt_id x).pow (n+1)).const_mul k).div_const ((n:ℝ)+1) using 1
  <;> simp only [id_eq,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,mul_one]
  <;> field_simp

theorem derivative_compare (f g : ℝ → ℝ) (rho lo hi : ℝ) (n : ℕ)
    (hr : 0≤rho) (hzero : f 0=0)
    (hd : ∀ x ∈ Icc 0 rho, HasDerivAt f (g x) x)
    (hb : ∀ x ∈ Icc 0 rho, lo*x^n≤g x ∧ g x≤hi*x^n)
    (y : ℝ) (hy : y ∈ Icc 0 rho) :
    primitive n lo y≤f y ∧ f y≤primitive n hi y := by
  have hlow : MonotoneOn (fun x => f x-primitive n lo x) (Icc 0 rho) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 rho)
    · intro x hx; exact ((hd x hx).sub (primitive_deriv n lo x)).continuousAt.continuousWithinAt
    · intro x hx; exact ((hd x (interior_subset hx)).sub (primitive_deriv n lo x)).differentiableAt.differentiableWithinAt
    · intro x hx
      change 0≤deriv (f-primitive n lo) x
      rw [((hd x (interior_subset hx)).sub (primitive_deriv n lo x)).deriv]
      exact sub_nonneg.mpr (hb x (interior_subset hx)).1
  have hupp : MonotoneOn (fun x => primitive n hi x-f x) (Icc 0 rho) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 rho)
    · intro x hx; exact ((primitive_deriv n hi x).sub (hd x hx)).continuousAt.continuousWithinAt
    · intro x hx; exact ((primitive_deriv n hi x).sub (hd x (interior_subset hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      change 0≤deriv (primitive n hi-f) x
      rw [((primitive_deriv n hi x).sub (hd x (interior_subset hx))).deriv]
      exact sub_nonneg.mpr (hb x (interior_subset hx)).2
  have hl := hlow ⟨le_rfl,hr⟩ hy hy.1
  have hu := hupp ⟨le_rfl,hr⟩ hy hy.1
  simp only [primitive,zero_pow (Nat.succ_ne_zero n),mul_zero,zero_div,hzero,sub_zero,zero_sub,neg_zero] at hl hu ⊢
  constructor <;> linarith

/-- A lower bound on the magnitude of a negative logarithmic error excludes a candidate. -/
theorem relative_lower (v eta : ℝ) (hv : 0<v) (he : 0≤eta) (hlog : log v≤-eta) :
    eta/(1+eta)≤|v-1| := by
  have hp : 0<1+eta := by positivity
  have hvu : v≤exp (-eta) := by rw [← exp_log hv]; exact exp_le_exp.mpr hlog
  have hexp : 1+eta≤exp eta := by linarith [add_one_le_exp eta]
  have hdiv : exp (-eta)≤1/(1+eta) := by
    rw [exp_neg,← one_div]
    exact div_le_div_of_nonneg_left (by norm_num) hp hexp
  have hv1 : v≤1 := (hvu.trans hdiv).trans ((div_le_one hp).mpr (by linarith))
  rw [abs_of_nonpos (by linarith : v-1≤0)]
  have hid : eta/(1+eta)=1-1/(1+eta) := by field_simp; ring
  rw [hid]
  linarith

theorem positive_log_bounds (A : ℝ[X]) (p rho c L U : ℝ) (n : ℕ)
    (hp : 0<p) (hr0 : 0≤rho) (hr1 : rho<1) (hc : 0≤c) (hL : 0<L) (hU : 0<U)
    (hpos : ∀ x, |x|≤rho → 0<A.eval x)
    (hN : numerator A (A.comp (-X)) p = -(C c : ℝ[X])*X^n)
    (hD : ∀ x, |x|≤rho → L≤(denominator A (A.comp (-X)) p).eval x ∧
      (denominator A (A.comp (-X)) p).eval x≤U)
    (y : ℝ) (hy : y ∈ Icc 0 rho) :
    primitive n (c/U) y≤-error A (A.comp (-X)) p y ∧
      -error A (A.comp (-X)) p y≤primitive n (c/L) y := by
  let D := denominator A (A.comp (-X)) p
  have hd : ∀ x ∈ Icc 0 rho, HasDerivAt (fun t => -error A (A.comp (-X)) p t)
      (c*x^n/D.eval x) x := by
    intro x hx
    have hxr : |x|≤rho := by simpa [abs_of_nonneg hx.1] using hx.2
    have hxmem : x ∈ Ioo (-1) 1 := abs_lt.mp (hxr.trans_lt hr1)
    have hZ : 0<(A.comp (-X)).eval x := by simpa using hpos (-x) (by simpa using hxr)
    have hh := (hasDerivAt_error A (A.comp (-X)) p x hp.ne' hxmem (hpos x hxr).ne' hZ.ne').neg
    change HasDerivAt (-error A (A.comp (-X)) p) _ x
    simpa [hN,D,neg_div] using hh
  apply derivative_compare _ _ rho (c/U) (c/L) n hr0 (by simp [error_zero]) hd _ y hy
  intro x hx
  have hxr : |x|≤rho := by simpa [abs_of_nonneg hx.1] using hx.2
  have hh := hD x hxr
  have hdx : 0<D.eval x := lt_of_lt_of_le hL hh.1
  have hcx : 0≤c*x^n := mul_nonneg hc (pow_nonneg hx.1 n)
  constructor
  · simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_left hcx hdx hh.2
  · simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_left hcx hL hh.1

/-- Absolute coefficient mass bounds a polynomial around its constant term. -/
theorem constant_mass_bounds (a : ℚ) (cs : List ℚ) (rho : ℚ) (hr : 0≤rho)
    (y : ℝ) (hy : |y|≤(rho:ℝ)) :
    (a-rho*LeanMath.Papers.V14PolynomialGate.mass cs rho:ℚ)≤
      (LeanMath.Papers.V14PolynomialGate.ofCoeffs (a::cs)).eval y ∧
    (LeanMath.Papers.V14PolynomialGate.ofCoeffs (a::cs)).eval y≤
      (a+rho*LeanMath.Papers.V14PolynomialGate.mass cs rho:ℚ) := by
  have hb := LeanMath.Papers.V14PolynomialGate.eval_abs_bound cs rho hr y hy
  have hm : (0:ℝ)≤LeanMath.Papers.V14PolynomialGate.mass cs rho := by
    exact_mod_cast LeanMath.Papers.V14PolynomialGate.mass_nonneg cs rho hr
  have hh : |y*(LeanMath.Papers.V14PolynomialGate.ofCoeffs cs).eval y|≤
      (rho:ℝ)*LeanMath.Papers.V14PolynomialGate.mass cs rho := by
    rw [abs_mul]
    exact mul_le_mul hy hb (abs_nonneg _) (by exact_mod_cast hr)
  simp only [LeanMath.Papers.V14PolynomialGate.ofCoeffs,eval_add,eval_mul,eval_C,eval_X,Rat.cast_add,Rat.cast_sub,Rat.cast_mul]
  exact ⟨by linarith [(abs_le.mp hh).1],by linarith [(abs_le.mp hh).2]⟩

structure Certificate (A : ℝ[X]) (p rho : ℝ) (n : ℕ) where
  c : ℝ
  L : ℝ
  U : ℝ
  hp : 0<p
  hr0 : 0≤rho
  hr1 : rho<1
  hc : 0≤c
  hL : 0<L
  hU : 0<U
  hpos : ∀ x, |x|≤rho → 0<A.eval x
  hN : numerator A (A.comp (-X)) p = -(C c : ℝ[X])*X^n
  hD : ∀ x, |x|≤rho → L≤(denominator A (A.comp (-X)) p).eval x ∧
    (denominator A (A.comp (-X)) p).eval x≤U

def etaUpper {A : ℝ[X]} {p rho : ℝ} {n : ℕ} (s : Certificate A p rho n) := primitive n (s.c/s.L) rho
def etaLower {A : ℝ[X]} {p rho : ℝ} {n : ℕ} (s : Certificate A p rho n) := primitive n (s.c/s.U) rho

theorem uniform_bound {A : ℝ[X]} {p rho : ℝ} {n : ℕ} (s : Certificate A p rho n) (he : etaUpper s<1)
    (y : ℝ) (hy : |y|≤rho) :
    |(A.eval y/A.eval (-y))/(unchi y)^(1/p)-1|≤etaUpper s/(1-etaUpper s) := by
  have hhalf : ∀ t ∈ Icc 0 rho, |error A (A.comp (-X)) p t|≤etaUpper s := by
    intro t ht
    have hh := positive_log_bounds A p rho s.c s.L s.U n s.hp s.hr0 s.hr1 s.hc s.hL s.hU s.hpos s.hN s.hD t ht
    have hlo : 0≤primitive n (s.c/s.U) t := by
      exact div_nonneg (mul_nonneg (div_nonneg s.hc s.hU.le) (pow_nonneg ht.1 _)) (by positivity)
    have hu : primitive n (s.c/s.L) t≤etaUpper s := by
      unfold primitive etaUpper
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht.1 ht.2 _) (div_nonneg s.hc s.hL.le)) (by positivity)
    rw [abs_of_nonpos (by linarith [hh.1])]
    exact hh.2.trans hu
  have hmem : y ∈ Ioo (-1) 1 := abs_lt.mp (hy.trans_lt s.hr1)
  have herr : |error A (A.comp (-X)) p y|≤etaUpper s := by
    by_cases h : 0≤y
    · exact hhalf y ⟨h,by simpa [abs_of_nonneg h] using hy⟩
    · have hh := hhalf (-y) ⟨by linarith,by simpa [abs_of_neg (lt_of_not_ge h)] using hy⟩
      rwa [error_odd A p y hmem,abs_neg] at hh
  have hA := s.hpos y hy
  have hZ : 0<(A.comp (-X)).eval y := by simpa using s.hpos (-y) (by simpa using hy)
  rw [error_eq_log_ratio A (A.comp (-X)) p y hmem hA hZ] at herr
  have hv := div_pos (div_pos hA hZ) (rpow_pos_of_pos (unchi_pos y hmem) (1/p))
  have he0 : 0≤etaUpper s := by
    exact div_nonneg (mul_nonneg (div_nonneg s.hc s.hL.le) (pow_nonneg s.hr0 _)) (by positivity)
  simpa using LeanMath.Papers.V14Halley.relative_of_log_bound _ _ hv he0 he herr

theorem endpoint_bound {A : ℝ[X]} {p rho : ℝ} {n : ℕ} (s : Certificate A p rho n) :
    etaLower s/(1+etaLower s)≤|(A.eval rho/A.eval (-rho))/(unchi rho)^(1/p)-1| := by
  have hh := (positive_log_bounds A p rho s.c s.L s.U n s.hp s.hr0 s.hr1 s.hc s.hL s.hU
    s.hpos s.hN s.hD rho ⟨s.hr0,le_rfl⟩).1
  have hy : |rho|≤rho := by simp [abs_of_nonneg s.hr0]
  have hmem : rho ∈ Ioo (-1) 1 := abs_lt.mp (hy.trans_lt s.hr1)
  have hA := s.hpos rho hy
  have hZ : 0<(A.comp (-X)).eval rho := by simpa using s.hpos (-rho) (by simpa using hy)
  rw [error_eq_log_ratio A (A.comp (-X)) p rho hmem hA hZ] at hh
  have hv := div_pos (div_pos hA hZ) (rpow_pos_of_pos (unchi_pos rho hmem) (1/p))
  have he0 : 0≤etaLower s := by
    exact div_nonneg (mul_nonneg (div_nonneg s.hc s.hU.le) (pow_nonneg s.hr0 _)) (by positivity)
  have hlog : log ((A.eval rho/(A.comp (-X)).eval rho)/(unchi rho)^(1/p))≤-etaLower s := by
    change etaLower s≤-_ at hh
    linarith
  simpa using relative_lower _ _ hv he0 hlog

end LeanMath.Papers.V14PowerError
