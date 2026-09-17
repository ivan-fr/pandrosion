import LeanMath.Papers.RectanglePencils

noncomputable section
namespace LeanMath.Papers.RectanglePencilsPade
open LeanMath.Papers LeanMath.Papers.RectangleRaw
open Filter Set Function
open scoped Topology

def aa (p : ℕ) := ((p:ℝ)-1)*(2*(p:ℝ)-1)
def bb (p : ℕ) := 8*(p:ℝ)^2-2
def cc (p : ℕ) := ((p:ℝ)+1)*(2*(p:ℝ)+1)
def num (p : ℕ) (t : ℝ) := aa p*t^2+bb p*t+cc p
def den (p : ℕ) (t : ℝ) := cc p*t^2+bb p*t+aa p
def step (p : ℕ) (X s : ℝ) := s*num p (X*s^p)/den p (X*s^p)

theorem coeff_pos (p : ℕ) (hp : 2≤p) : 0<aa p ∧ 0<bb p ∧ 0<cc p := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  unfold aa bb cc
  have h1 : 0<(p:ℝ)-1 := by linarith
  have h2 : 0<2*(p:ℝ)-1 := by linarith
  exact ⟨mul_pos h1 h2,by nlinarith,by positivity⟩

theorem terms_pos (p : ℕ) (t : ℝ) (hp : 2≤p) (ht : 0<t) : 0<num p t ∧ 0<den p t := by
  obtain ⟨ha,hb,hc⟩ := coeff_pos p hp
  unfold num den; constructor <;> positivity

theorem step_pos (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) : 0<step p X s :=
  div_pos (mul_pos hs (terms_pos p _ hp (by positivity)).1) (terms_pos p _ hp (by positivity)).2

theorem difference (p : ℕ) (t : ℝ) : num p t-den p t=6*(p:ℝ)*(1-t)*(1+t) := by
  unfold num den aa bb cc; ring

theorem one (p : ℕ) (hp : 2≤p) : step p 1 1=1 := by
  have hd := (terms_pos p 1 hp (by norm_num)).2.ne'
  have he : num p 1=den p 1 := by unfold num den; ring
  simp only [step,one_pow,one_mul,he,div_self hd]

theorem hasDerivAt_step (p : ℕ) (X s : ℝ) (hp : 2≤p) (hd : den p (X*s^p)≠0) :
    HasDerivAt (step p X) (aa p*cc p*(X*s^p-1)^4/(den p (X*s^p))^2) s := by
  have hpow : s*s^(p-1)=s^p := by rw [← pow_succ']; congr 1; omega
  have hn : HasDerivAt (fun s : ℝ => num p (X*s^p))
      ((2*aa p*(X*s^p)+bb p)*X*((p:ℝ)*s^(p-1))) s := by
    convert! ((((((hasDerivAt_id s).pow p).const_mul X).pow 2).const_mul (aa p)).add
      ((((hasDerivAt_id s).pow p).const_mul X).const_mul (bb p))).add_const (cc p) using 1 <;> dsimp [num] <;> ring
  have hd' : HasDerivAt (fun s : ℝ => den p (X*s^p))
      ((2*cc p*(X*s^p)+bb p)*X*((p:ℝ)*s^(p-1))) s := by
    convert! ((((((hasDerivAt_id s).pow p).const_mul X).pow 2).const_mul (cc p)).add
      ((((hasDerivAt_id s).pow p).const_mul X).const_mul (bb p))).add_const (aa p) using 1 <;> dsimp [den] <;> ring
  convert! ((hasDerivAt_id s).mul hn).div hd' hd using 1
  simp only [Pi.mul_apply,id_eq,one_mul]
  field_simp [hd]
  unfold num den aa bb cc
  rw [← hpow]; ring

theorem continuousAt_step (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    ContinuousAt (step p X) s :=
  (hasDerivAt_step p X s hp (terms_pos p _ hp (by positivity)).2.ne').continuousAt

theorem monotone_positive (p : ℕ) (X : ℝ) (hp : 2≤p) (hX : 0<X) :
    MonotoneOn (step p X) (Ioi 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
    (fun s hs => (continuousAt_step p X s hp hX hs).continuousWithinAt)
  · intro s hs
    exact (hasDerivAt_step p X s hp (terms_pos p _ hp (by have : 0<s := interior_subset hs; positivity)).2.ne').hasDerivWithinAt
  · intro s hs
    have h := coeff_pos p hp
    exact div_nonneg (mul_nonneg (mul_pos h.1 h.2.2).le (by positivity)) (sq_nonneg _)

theorem unit_moves (p : ℕ) (s : ℝ) (hp : 2≤p) (hs : 0<s) :
    (s<1 → s<step p 1 s ∧ step p 1 s≤1) ∧
    (1<s → 1≤step p 1 s ∧ step p 1 s<s) := by
  have ht := terms_pos p (s^p) hp (pow_pos hs p)
  have he := difference p (s^p)
  have hm := monotone_positive p 1 hp (by norm_num)
  have hp' : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  constructor
  · intro h
    have hh : s^p<1 := pow_lt_one₀ hs.le h (by omega)
    refine ⟨?_,by simpa [one p hp] using hm hs (by norm_num : (1:ℝ)∈Ioi 0) h.le⟩
    unfold step; simp only [one_mul]
    apply (lt_div_iff₀ ht.2).mpr
    have hg : 0<6*(p:ℝ)*(1-s^p)*(1+s^p) := by positivity
    nlinarith [mul_pos hs hg]
  · intro h
    have hh : 1<s^p := one_lt_pow₀ h (by omega)
    refine ⟨by simpa [one p hp] using hm (by norm_num : (1:ℝ)∈Ioi 0) hs h.le,?_⟩
    unfold step; simp only [one_mul]
    apply (div_lt_iff₀ ht.2).mpr
    have hg : 6*(p:ℝ)*(1-s^p)*(1+s^p)<0 := by
      exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) (by linarith)) (by positivity)
    nlinarith [mul_neg_of_pos_of_neg hs hg]

theorem unit_global (p : ℕ) (s : ℝ) (hp : 2≤p) (hs : 0<s) :
    Tendsto (fun n : ℕ => (step p 1)^[n] s) atTop (𝓝 1) := by
  apply IntervalIteration.converge (step p 1) (min s 1) (max s 1) 1 s
    ⟨min_le_right _ _,le_max_right _ _⟩ ⟨min_le_left _ _,le_max_left _ _⟩
  · intro t ht
    exact continuousAt_step p 1 t hp (by norm_num) ((lt_min hs (by norm_num)).trans_le ht.1)
  · exact one p hp
  · intro t ht h
    exact (unit_moves p t hp ((lt_min hs (by norm_num)).trans_le ht.1)).1 h
  · intro t ht h
    exact (unit_moves p t hp ((lt_min hs (by norm_num)).trans_le ht.1)).2 h

theorem scale_step (p : ℕ) (X a u : ℝ) (ha : X*a^p=1) :
    step p X (a*u)=a*step p 1 u := by
  unfold step; rw [mul_pow]
  have h : X*(a^p*u^p)=u^p := by rw [← mul_assoc,ha,one_mul]
  rw [h]; simp only [one_mul]; ring

theorem global_with_root (p : ℕ) (X a s : ℝ) (hp : 2≤p)
    (ha : 0<a) (hs : 0<s) (hroot : X*a^p=1) :
    Tendsto (fun n : ℕ => (step p X)^[n] s) atTop (𝓝 a) := by
  have he : ∀ n : ℕ, (step p X)^[n] s=a*(step p 1)^[n] (s/a) := by
    intro n; induction n with
    | zero => change s=a*(s/a); field_simp
    | succ n ih => rw [iterate_succ_apply',iterate_succ_apply',ih,scale_step p X a _ hroot]
  have ht := (unit_global p (s/a) hp (div_pos hs ha)).const_mul a
  simpa only [← he,mul_one] using ht

theorem global_convergence (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => (step p X)^[n] s) atTop (𝓝 (X⁻¹ ^ (1/(p:ℝ)))) := by
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  apply global_with_root p X _ s hp (Real.rpow_pos_of_pos (inv_pos.mpr hX) _) hs
  rw [← Real.rpow_natCast,one_div,Real.rpow_inv_rpow (inv_nonneg.mpr hX.le) hp0,mul_inv_cancel₀ hX.ne']

def orderFactor (p : ℕ) (e : ℝ) := aa p*cc p*(sumPowers p (1+e))^4/(den p ((1+e)^p))^2

theorem order_five (p : ℕ) (hp : 2≤p) :
    Tendsto (fun e : ℝ => (step p 1 (1+e)-1)/e^5) (𝓝[≠] 0)
      (𝓝 (aa p*cc p/720)) := by
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  have hd0 : den p ((1+(0:ℝ))^p)≠0 := by simpa using (terms_pos p 1 hp (by norm_num)).2.ne'
  have hf0 : step p 1 (1+0)-1=0 := by simp [one p hp]
  have hc : ContinuousAt (fun e : ℝ => step p 1 (1+e)-1) 0 := by
    have hd1 := (terms_pos p 1 hp (by norm_num)).2.ne'
    unfold step num den
    apply ContinuousAt.sub _ continuousAt_const
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa [den] using hd1
  have hg : ContinuousAt (orderFactor p) 0 := by
    unfold orderFactor sumPowers den
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero _ hd0
  have hh : ∀ᶠ e : ℝ in 𝓝[≠] 0,
      HasDerivAt (fun e : ℝ => step p 1 (1+e)-1) (e^4*orderFactor p e) e := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (-1:ℝ)<0 by norm_num))] with e he
    have hpos : 0<1+e := by have : -1<e := he; linarith
    have hd := (terms_pos p _ hp (pow_pos hpos p)).2.ne'
    have hd' := ((hasDerivAt_step p 1 (1+e) hp (by simpa using hd)).comp e ((hasDerivAt_id e).const_add 1)).sub_const 1
    convert! hd' using 1
    simp only [one_mul,mul_one]
    have hi := sum_identity p (1+e)
    have hi' : (1+e)^p-1=e*sumPowers p (1+e) := by nlinarith [hi]
    rw [hi']; unfold orderFactor; ring
  have ht := LocalOrder.from_derivative 4 (fun e : ℝ => step p 1 (1+e)-1) (orderFactor p) hf0 hc hg hh
  have hv : orderFactor p 0/((4:ℝ)+1)=aa p*cc p/720 := by
    have hd : den p 1=12*(p:ℝ)^2 := by unfold den aa bb cc; ring
    simp only [orderFactor,add_zero,one_pow]
    rw [hd]; simp [sumPowers]; field_simp [hp0] <;> ring
  simpa only [Nat.reduceAdd,Nat.cast_ofNat,hv] using ht

theorem relative_order_five (p : ℕ) (X a : ℝ) (hp : 2≤p)
    (ha : 0<a) (hroot : X*a^p=1) :
    Tendsto (fun e : ℝ => (step p X (a*(1+e))/a-1)/e^5) (𝓝[≠] 0)
      (𝓝 (aa p*cc p/720)) := by
  simpa only [scale_step p X a _ hroot,mul_div_cancel_left₀ _ ha.ne'] using order_five p hp

theorem order_coefficient_pos (p : ℕ) (hp : 2≤p) : 0<aa p*cc p/720 :=
  div_pos (mul_pos (coeff_pos p hp).1 (coeff_pos p hp).2.2) (by norm_num)

/-- The two quadratic factors only require one square root. -/
def disc (p : ℕ) := bb p^2-4*aa p*cc p
def rPlus (p : ℕ) := (bb p+Real.sqrt (disc p))/(2*aa p)
def rMinus (p : ℕ) := (bb p-Real.sqrt (disc p))/(2*aa p)

theorem disc_formula (p : ℕ) : disc p=12*(p:ℝ)^2*(4*(p:ℝ)^2-1) := by
  unfold disc aa bb cc; ring

theorem disc_pos (p : ℕ) (hp : 2≤p) : 0<disc p := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  rw [disc_formula]
  have : 0<4*(p:ℝ)^2-1 := by nlinarith
  positivity

theorem roots_pos (p : ℕ) (hp : 2≤p) : 0<rPlus p ∧ 0<rMinus p := by
  have h := coeff_pos p hp
  obtain ⟨ha,hb0,hc⟩ := h
  have hs := Real.sq_sqrt (disc_pos p hp).le
  have hn := Real.sqrt_nonneg (disc p)
  have hb : Real.sqrt (disc p)<bb p := by
    change (Real.sqrt (disc p))^2=bb p^2-4*aa p*cc p at hs
    nlinarith [mul_pos ha hc]
  constructor
  · unfold rPlus; positivity
  · exact div_pos (sub_pos.mpr hb) (by positivity)

theorem roots_sum_product (p : ℕ) (hp : 2≤p) :
    rPlus p+rMinus p=bb p/aa p ∧ rPlus p*rMinus p=cc p/aa p := by
  have ha := (coeff_pos p hp).1.ne'
  have hs := Real.sq_sqrt (disc_pos p hp).le
  constructor
  · unfold rPlus rMinus; field_simp [ha] <;> ring
  · unfold rPlus rMinus
    field_simp [ha]
    change (Real.sqrt (disc p))^2=bb p^2-4*aa p*cc p at hs
    nlinarith

theorem factorization (p : ℕ) (t : ℝ) (hp : 2≤p) (ht : 0<t) :
    (t+rPlus p)/(rPlus p*t+1) * ((t+rMinus p)/(rMinus p*t+1))=num p t/den p t := by
  have hr := roots_pos p hp
  have hd := (terms_pos p t hp ht).2.ne'
  have hsum := (roots_sum_product p hp).1
  have hprod := (roots_sum_product p hp).2
  have ha := (coeff_pos p hp).1.ne'
  have hN : (t+rPlus p)*(t+rMinus p)=num p t/aa p := by
    unfold num
    have hh : (t+rPlus p)*(t+rMinus p)=t^2+(rPlus p+rMinus p)*t+rPlus p*rMinus p := by ring
    rw [hh,hsum,hprod]; field_simp [ha] <;> ring
  have hD : (rPlus p*t+1)*(rMinus p*t+1)=den p t/aa p := by
    unfold den
    have hh : (rPlus p*t+1)*(rMinus p*t+1)=rPlus p*rMinus p*t^2+(rPlus p+rMinus p)*t+1 := by ring
    rw [hh,hsum,hprod]; field_simp [ha] <;> ring
  rw [div_mul_div_comm,hN,hD]
  field_simp

/-- Four pencil joins for each factor, with both hubs equal to U[1/2] at t=1. -/
theorem normalized_factor (r t : ℝ) (hr : 0<r) (ht : 0<t) :
    ((1/(2*(1+r)))+(r/(2*(1+r)))/t) /
    ((r/(2*(1+r)))+(1/(2*(1+r)))/t)=(t+r)/(r*t+1) := by
  field_simp
  <;> ring


open LeanMath.Papers.RectanglePencils

def fA (r : ℝ) := 1/(2*(1+r))
def fB (r K : ℝ) := r/(2*(1+r)*K)
def fC (r : ℝ) := r/(2*(1+r))
def fD (r K : ℝ) := 1/(2*(1+r)*K)

theorem pair_ratio (r K q : ℝ) (hr : 0<r) (hK : 0<K) (hq : 0<q) :
    factor (fA r) (fB r K) q / factor (fC r) (fD r K) q = (K*q+r)/(r*(K*q)+1) := by
  unfold factor fA fB fC fD
  field_simp
  <;> ring

/-- Two four-join factors multiply to the fifth-order recurrence. -/
theorem two_factor_formula (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    s * (factor (fA (rPlus p)) (fB (rPlus p) (scale p*X)) (chain s (p-1)) /
      factor (fC (rPlus p)) (fD (rPlus p) (scale p*X)) (chain s (p-1))) *
    (factor (fA (rMinus p)) (fB (rMinus p) (scale p*X)) (chain s (p-1)) /
      factor (fC (rMinus p)) (fD (rMinus p) (scale p*X)) (chain s (p-1)))=step p X s := by
  have hr := roots_pos p hp
  have hK : 0<scale p*X := by unfold scale; positivity
  have hq : 0<chain s (p-1) := by unfold chain; positivity
  rw [pair_ratio _ _ _ hr.1 hK hq,pair_ratio _ _ _ hr.2 hK hq]
  have he : scale p*X*chain s (p-1)=X*s^p := by
    have h := chain_unscale s p (by omega)
    dsimp [scale]
    nlinarith [h]
  rw [he,mul_assoc,factorization p _ hp (by positivity)]
  unfold step; ring

/-- One square-root extension contains the two real factor parameters. -/
theorem roots_constructible (K : Subfield ℝ) (p : ℕ) (hp : 2≤p)
    (hsqrt : ∀ x : ℝ, x∈K → 0≤x → Real.sqrt x∈K) : rPlus p∈K ∧ rMinus p∈K := by
  have ha : aa p∈K := by unfold aa; field_membership
  have hb : bb p∈K := by unfold bb; field_membership
  have hc : cc p∈K := by unfold cc; field_membership
  have hd : disc p∈K := by unfold disc; field_membership
  have hs := hsqrt _ hd (disc_pos p hp).le
  unfold rPlus rMinus
  field_membership

/-- Every fixed projector for a [2/2] factor uses only field operations on r. -/
theorem factor_projectors_constructible (K : Subfield ℝ) (W H r C : ℝ)
    (hW : W∈K) (hH : H∈K) (hr : r∈K) (hC : C∈K) :
    RectangleConstructible.PointOver K (projector W H (fA r) (fB r C)) ∧
    RectangleConstructible.PointOver K (projector W H (fC r) (fD r C)) := by
  dsimp [RectangleConstructible.PointOver,projector,fA,fB,fC,fD]
  field_membership

end LeanMath.Papers.RectanglePencilsPade
