import LeanMath.Papers.V14SeriesContact

/-! An odd analytic error with a known leading limit has a two-order Taylor remainder. -/
noncomputable section
namespace LeanMath.Papers.V14OddRemainder
open Filter Asymptotics Polynomial
open scoped Topology
open LeanMath.Papers.V14ScalarSeries

theorem polynomial_littleO_divisible (P : ℝ[X]) (n : ℕ)
    (hO : (fun x : ℝ => P.eval x) =o[𝓝 0] (fun x => x^n)) : X^(n+1) ∣ P := by
  obtain ⟨Q,hQ⟩ := V14AnalyticUniqueness.polynomial_contact_divisible P n hO.isBigO
  have hz := hO.tendsto_div_nhds_zero.mono_left
    (show 𝓝[≠] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have he : (fun x : ℝ => P.eval x/x^n) =ᶠ[𝓝[≠] 0] (fun x => Q.eval x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    rw [hQ,eval_mul,eval_pow,eval_X]
    field_simp
  have hc := (Q.continuous.tendsto 0).mono_left
    (show 𝓝[≠] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hQ0 : Q.eval 0=0 := tendsto_nhds_unique hc (hz.congr' he)
  have hd : X ∣ Q := by simpa using dvd_iff_isRoot.mpr hQ0
  obtain ⟨W,hW⟩ := hd
  refine ⟨W,?_⟩
  rw [hQ,hW,pow_succ,mul_assoc]

theorem analytic_littleO_vanishing (F : PowerSeries ℝ) (f : ℝ → ℝ) (hf : Represents F f)
    (n : ℕ) (hO : f =o[𝓝 0] (fun y : ℝ => y^n)) : PowerSeries.X^(n+1) ∣ F := by
  have hr := (V14SeriesContact.truncation_remainder F f hf (n+1)).trans_isLittleO
    (isLittleO_pow_pow (by omega : n<n+1))
  have hh := hO.sub hr
  have hT : (fun y : ℝ => (PowerSeries.trunc (n+1) F).eval y) =o[𝓝 0] (fun y => y^n) := by
    convert! hh using 1
    funext y; ring
  have hd := polynomial_littleO_divisible _ n hT
  have hz : PowerSeries.trunc (n+1) F=0 := by
    by_contra hn
    have hb := natDegree_le_of_dvd hd hn
    simp only [natDegree_X_pow] at hb
    have hlt := PowerSeries.natDegree_trunc_lt F n
    omega
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro k hk
  have hc := congrArg (fun P : ℝ[X] => P.coeff k) hz
  simpa [PowerSeries.coeff_trunc,hk] using hc

theorem reflect_represents (F : PowerSeries ℝ) (f : ℝ → ℝ) (hf : Represents F f) :
    Represents (PowerSeries.rescale (-1) F) (fun y => f (-y)) := by
  rw [represents_iff] at hf ⊢
  have ht : Tendsto (fun y : ℝ => -y) (𝓝 0) (𝓝 0) := by simpa using continuous_neg.tendsto (0:ℝ)
  filter_upwards [ht.eventually hf] with y hy
  convert! hy using 1
  funext n
  rw [PowerSeries.coeff_rescale,neg_pow]
  ring

/-- Oddness removes the next even coefficient after an odd leading order. -/
theorem odd_analytic_remainder (f : ℝ → ℝ) (n : ℕ) (hn : Odd n)
    (ha : AnalyticAt ℝ f 0) (hodd : ∀ x, f (-x)= -f x)
    (hO : f =o[𝓝 0] (fun x : ℝ => x^n)) : f =O[𝓝 0] (fun x : ℝ => x^(n+2)) := by
  obtain ⟨F,hF⟩ := exists_series f ha
  have hd := analytic_littleO_vanishing F f hF n hO
  have hneg : Represents (-F) (fun y => -f y) := by
    simpa using V14ScalarSeries.sub _ _ _ _ (V14ScalarSeries.const (0:ℝ)) hF
  have href : PowerSeries.rescale (-1) F = -F :=
    unique _ _ _ _ (reflect_represents F f hF) hneg (Filter.Eventually.of_forall hodd)
  have hnext : PowerSeries.coeff (n+1) F=0 := by
    have hh := congrArg (PowerSeries.coeff (n+1)) href
    simp only [PowerSeries.coeff_rescale,map_neg,pow_succ,hn.neg_one_pow] at hh
    norm_num at hh
    linarith
  have hz : PowerSeries.trunc (n+2) F=0 := by
    apply Polynomial.ext
    intro k
    rw [PowerSeries.coeff_trunc,Polynomial.coeff_zero]
    by_cases hk : k<n+2
    · rw [if_pos hk]
      by_cases hk' : k<n+1
      · exact PowerSeries.X_pow_dvd_iff.mp hd k hk'
      · have he : k=n+1 := by omega
        simpa only [he] using hnext
    · rw [if_neg hk]
  have hr := V14SeriesContact.truncation_remainder F f hF (n+2)
  simpa only [hz,Polynomial.eval_zero,sub_zero] using hr

/-- Convert the punctured leading-limit statement into a genuine little-o remainder. -/
theorem leading_limit_littleO (f : ℝ → ℝ) (n : ℕ) (c : ℝ) (hn : 0<n) (hf0 : f 0=0)
    (ht : Tendsto (fun x : ℝ => f x/x^n) (𝓝[≠] 0) (𝓝 c)) :
    (fun x : ℝ => f x-c*x^n) =o[𝓝 0] (fun x => x^n) := by
  have hp : Tendsto (fun x : ℝ => (f x-c*x^n)/x^n) (𝓝[≠] 0) (𝓝 0) := by
    have hh := ht.sub_const c
    simp only [sub_self] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    field_simp
  have hfull : Tendsto (fun x : ℝ => (f x-c*x^n)/x^n) (𝓝 0) (𝓝 0) := by
    conv_lhs => rw [← nhdsNE_sup_pure (0:ℝ)]
    apply hp.sup
    simpa [zero_pow (Nat.ne_of_gt hn)] using
      tendsto_pure_nhds (fun x : ℝ => (f x-c*x^n)/x^n) 0
  apply (isLittleO_iff_tendsto (fun x hx => ?_)).mpr hfull
  have hx0 : x=0 := (pow_eq_zero_iff (Nat.ne_of_gt hn)).mp hx
  simp [hx0,hf0,Nat.ne_of_gt hn]

/-- Exact leading coefficient plus odd analyticity yields the printed O(e^(m+2)) form. -/
theorem odd_leading_remainder (f : ℝ → ℝ) (n : ℕ) (c : ℝ) (hn : Odd n)
    (ha : AnalyticAt ℝ f 0) (hodd : ∀ x, f (-x)= -f x) (hf0 : f 0=0)
    (ht : Tendsto (fun x : ℝ => f x/x^n) (𝓝[≠] 0) (𝓝 c)) :
    (fun x : ℝ => f x-c*x^n) =O[𝓝 0] (fun x => x^(n+2)) := by
  apply odd_analytic_remainder _ n hn
  · exact ha.sub (analyticAt_const.mul (analyticAt_id.pow n))
  · intro x
    rw [hodd,hn.neg_pow]
    ring
  · exact leading_limit_littleO f n c hn.pos hf0 ht

end LeanMath.Papers.V14OddRemainder
