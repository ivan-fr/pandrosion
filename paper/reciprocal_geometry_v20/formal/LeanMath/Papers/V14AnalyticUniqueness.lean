import LeanMath.Papers.V14PadeContact

/-! Uniqueness of diagonal rational contact in the original residual variable. -/
noncomputable section
namespace LeanMath.Papers.V14AnalyticUniqueness
open Polynomial Filter Asymptotics
open scoped Topology

/-- A polynomial with order-n analytic vanishing is divisible by X^n. -/
theorem polynomial_contact_divisible (P : ℝ[X]) (n : ℕ)
    (hO : (fun x : ℝ => P.eval x) =O[𝓝 0] (fun x => x^n)) : X^n ∣ P := by
  have hstep : ∀ k ≤ n, X^k ∣ P := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨Q,hQ⟩ := ih (by omega)
      have hlo := hO.trans_isLittleO (isLittleO_pow_pow (by omega : k < n))
      have hzero := hlo.tendsto_div_nhds_zero.mono_left
        (show 𝓝[≠] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
      have heq : (fun x : ℝ => P.eval x/x^k) =ᶠ[𝓝[≠] 0] (fun x => Q.eval x) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        have hx0 : x ≠ 0 := hx
        rw [hQ,eval_mul,eval_pow,eval_X]
        field_simp
      have hlim := hzero.congr' heq
      have hQc := (Q.continuous.tendsto 0).mono_left
        (show 𝓝[≠] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
      have hQ0 : Q.eval 0=0 := tendsto_nhds_unique hQc hlim
      have hX : X ∣ Q := by simpa using (dvd_iff_isRoot.mpr hQ0)
      obtain ⟨W,hW⟩ := hX
      refine ⟨W,?_⟩
      rw [hQ,hW,pow_succ,mul_assoc]
  exact hstep n le_rfl

theorem polynomial_contact_zero (P : ℝ[X]) (n : ℕ) (hdeg : P.natDegree < n)
    (hO : (fun x : ℝ => P.eval x) =O[𝓝 0] (fun x => x^n)) : P=0 := by
  by_contra hn
  have h := natDegree_le_of_dvd (polynomial_contact_divisible P n hO) hn
  simp only [natDegree_X_pow] at h
  omega

/-- Local contact of order 2d+1 uniquely determines a rational function of type (d,d). -/
theorem rational_unique (A B C D : ℝ[X]) (d : ℕ) (f : ℝ → ℝ)
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d)
    (hC : C.natDegree ≤ d) (hD : D.natDegree ≤ d)
    (hB1 : B.eval 1 ≠ 0) (hD1 : D.eval 1 ≠ 0)
    (hfirst : (fun h : ℝ => A.eval (1+h)/B.eval (1+h)-f (1+h)) =O[𝓝 0] (fun h => h^(2*d+1)))
    (hsecond : (fun h : ℝ => C.eval (1+h)/D.eval (1+h)-f (1+h)) =O[𝓝 0] (fun h => h^(2*d+1))) :
    A*D=C*B := by
  have hb : ContinuousAt (fun h : ℝ => B.eval (1+h)) 0 := by fun_prop
  have hd : ContinuousAt (fun h : ℝ => D.eval (1+h)) 0 := by fun_prop
  have hbound := ((hb.mul hd).tendsto).isBigO_one ℝ
  have hh := (hfirst.sub hsecond).mul hbound
  simp only [mul_one] at hh
  have hbne : ∀ᶠ h : ℝ in 𝓝 0, B.eval (1+h) ≠ 0 := by
    exact hb.tendsto.eventually (eventually_ne_nhds (by simpa using hB1))
  have hdne : ∀ᶠ h : ℝ in 𝓝 0, D.eval (1+h) ≠ 0 := by
    exact hd.tendsto.eventually (eventually_ne_nhds (by simpa using hD1))
  have hp : (fun h : ℝ => ((A*D-C*B).comp (X+1)).eval h) =O[𝓝 0] (fun h => h^(2*d+1)) := by
    apply hh.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [hbne,hdne] with h hb hd
    simp only [eval_comp,eval_add,eval_X,eval_one,eval_sub,eval_mul,Pi.mul_apply]
    rw [add_comm h 1]
    field_simp
    <;> ring
  have hdeg : ((A*D-C*B).comp (X+1)).natDegree < 2*d+1 := by
    have h1 := natDegree_sub_le_of_le (natDegree_mul_le_of_le hA hD) (natDegree_mul_le_of_le hC hB)
    have h2 := natDegree_comp_le (p:=A*D-C*B) (q:=X+1)
    have h3 : (X+1:ℝ[X]).natDegree ≤ 1 := natDegree_add_le_of_degree_le (by simp) (by simp)
    have h4 : ((A*D-C*B).comp (X+1)).natDegree ≤ (A*D-C*B).natDegree :=
      h2.trans (by simpa using Nat.mul_le_mul_left (A*D-C*B).natDegree h3)
    omega
  have hzero := polynomial_contact_zero _ _ hdeg hp
  apply sub_eq_zero.mp
  apply Polynomial.funext
  intro R
  have he := congrArg (Polynomial.eval (R-1)) hzero
  simpa using he

end LeanMath.Papers.V14AnalyticUniqueness
