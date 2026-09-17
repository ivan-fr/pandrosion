import LeanMath.Papers.RectangleNewton
import LeanMath.Papers.RectangleConstructible
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! A fixed-center projection in the proportional rectangle. All degrees p ≥ 2.
The convergence theorem concerns the persistent inverse-root state s, not a
reinitialization from a displayed length. No historical priority is asserted. -/
noncomputable section
namespace LeanMath.Papers.RectangleProjective
open LeanMath.Papers LeanMath.Papers.RectangleGeometry LeanMath.Papers.RectangleReports
open LeanMath.Papers.RectangleRaw
open Filter Set Function
open scoped Topology

def num (p : ℕ) (t : ℝ) := 2*(p:ℝ)*((2*(p:ℝ)-1)*t+(p:ℝ)+1)
def den (p : ℕ) (t : ℝ) :=
  ((p:ℝ)+1)*t^2+2*(2*(p:ℝ)-1)*((p:ℝ)+1)*t+(2*(p:ℝ)-1)*((p:ℝ)-1)
def pole (p : ℕ) (t : ℝ) := ((p:ℝ)+1)*t+5*(p:ℝ)-1
def kappa (p : ℕ) (t : ℝ) := num p t / pole p t
def step (p : ℕ) (X s : ℝ) := s * num p (X*s^p) / den p (X*s^p)

theorem positive_terms (p : ℕ) (t : ℝ) (hp : 2≤p) (ht : 0<t) :
    0<num p t ∧ 0<den p t ∧ 0<pole p t := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have h1 : 0<(p:ℝ)-1 := by linarith
  have h2 : 0<2*(p:ℝ)-1 := by linarith
  have h5 : 0<5*(p:ℝ)-1 := by linarith
  dsimp [num,den,pole]
  constructor
  · positivity
  constructor
  · positivity
  · linarith [mul_pos (show 0<(p:ℝ)+1 by positivity) ht]

theorem step_pos (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    0<step p X s :=
  div_pos (mul_pos hs (positive_terms p _ hp (by positivity)).1)
    (positive_terms p _ hp (by positivity)).2.1

theorem numerator_difference (p : ℕ) (t : ℝ) :
    num p t-den p t=(1-t)*pole p t := by unfold num den pole; ring

theorem step_one (p : ℕ) (hp : 2≤p) : step p 1 1=1 := by
  have hd := (positive_terms p 1 hp (by norm_num)).2.1.ne'
  have he : num p 1=den p 1 := by unfold num den; ring
  simp only [step,one_pow,one_mul,he,div_self hd]

theorem hasDerivAt_step (p : ℕ) (X s : ℝ) (hp : 2≤p)
    (hd : den p (X*s^p)≠0) :
    HasDerivAt (step p X)
      (-2*(p:ℝ)*((p:ℝ)^2-1)*(2*(p:ℝ)-1)*(X*s^p-1)^3 / (den p (X*s^p))^2) s := by
  have hpow : s*s^(p-1)=s^p := by rw [← pow_succ']; congr 1; omega
  have hn : HasDerivAt (fun s : ℝ => num p (X*s^p))
      (2*(p:ℝ)*(2*(p:ℝ)-1)*X*((p:ℝ)*s^(p-1))) s := by
    convert! (((((hasDerivAt_id s).pow p).const_mul X).const_mul (2*(p:ℝ)-1)).add_const ((p:ℝ)+1)).const_mul (2*(p:ℝ)) using 1 <;> dsimp [num] <;> ring
  have hd' : HasDerivAt (fun s : ℝ => den p (X*s^p))
      ((2*((p:ℝ)+1)*(X*s^p)+2*(2*(p:ℝ)-1)*((p:ℝ)+1))*X*((p:ℝ)*s^(p-1))) s := by
    convert! ((((((hasDerivAt_id s).pow p).const_mul X).pow 2).const_mul ((p:ℝ)+1)).add
      ((((hasDerivAt_id s).pow p).const_mul X).const_mul (2*(2*(p:ℝ)-1)*((p:ℝ)+1)))).add_const ((2*(p:ℝ)-1)*((p:ℝ)-1)) using 1 <;> dsimp [den] <;> ring
  convert! ((hasDerivAt_id s).mul hn).div hd' hd using 1
  simp only [Pi.mul_apply,id_eq,one_mul]
  field_simp [hd]
  unfold num den
  rw [← hpow]
  ring

theorem step_continuous (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    ContinuousAt (step p X) s :=
  (hasDerivAt_step p X s hp (positive_terms p _ hp (by positivity)).2.1.ne').continuousAt

theorem unit_bound (p : ℕ) (s : ℝ) (hp : 2≤p) (hs : 0<s) : step p 1 s≤1 := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hc : 0≤2*(p:ℝ)*((p:ℝ)^2-1)*(2*(p:ℝ)-1) := by
    have : 0≤(p:ℝ)^2-1 := by nlinarith
    have : 0≤2*(p:ℝ)-1 := by linarith
    positivity
  by_cases h : s≤1
  · have hm : MonotoneOn (step p 1) (Icc s 1) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s 1)
        (fun x hx => (step_continuous p 1 x hp (by norm_num) (hs.trans_le hx.1)).continuousWithinAt)
      · intro x hx
        exact (hasDerivAt_step p 1 x hp
          (positive_terms p _ hp (by have : 0<x := hs.trans_le (interior_subset hx).1; positivity)).2.1.ne').hasDerivWithinAt
      · intro x hx
        have hx' := interior_subset hx
        have hpow : x^p≤1 := pow_le_one₀ (hs.trans_le hx'.1).le hx'.2
        have hz : (x^p-1)^3≤0 := by
          have hh : x^p-1≤0 := by linarith
          nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (x^p-1)) hh]
        simp only [one_mul]
        apply div_nonneg _ (sq_nonneg _)
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hc hz]
    simpa [step_one p hp] using hm ⟨le_rfl,h⟩ ⟨h,le_rfl⟩ h
  · have h' : 1≤s := le_of_not_ge h
    have hm : AntitoneOn (step p 1) (Icc 1 s) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 1 s)
        (fun x hx => (step_continuous p 1 x hp (by norm_num) (by linarith [hx.1])).continuousWithinAt)
      · intro x hx
        exact (hasDerivAt_step p 1 x hp
          (positive_terms p _ hp (by
            have hx0 : 0<x := lt_of_lt_of_le (by norm_num) (interior_subset hx).1
            exact mul_pos (by norm_num) (pow_pos hx0 p))).2.1.ne').hasDerivWithinAt
      · intro x hx
        have hpow : 1≤x^p := one_le_pow₀ (interior_subset hx).1
        simp only [one_mul]
        apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
        have : 0≤(x^p-1)^3 := pow_nonneg (by linarith) _
        nlinarith [mul_nonneg hc this]
    simpa [step_one p hp] using hm ⟨le_rfl,h'⟩ ⟨h',le_rfl⟩ h'

theorem unit_increases (p : ℕ) (s : ℝ) (hp : 2≤p) (hs : 0<s) (hs1 : s<1) :
    s<step p 1 s := by
  have ht : 0<s^p := pow_pos hs _
  have ht1 : s^p<1 := pow_lt_one₀ hs.le hs1 (by omega)
  have hd := (positive_terms p _ hp ht).2.1
  apply (lt_div_iff₀ (by simpa using hd)).mpr
  have hn := numerator_difference p (s^p)
  have hh := mul_pos (sub_pos.mpr ht1) (positive_terms p _ hp ht).2.2
  simp only [one_mul]
  nlinarith [mul_pos hs hh]

theorem unit_global (p : ℕ) (s : ℝ) (hp : 2≤p) (hs : 0<s) :
    Tendsto (fun n : ℕ => (step p 1)^[n] s) atTop (𝓝 1) := by
  let b := step p 1 s
  have hb : 0<b := step_pos p 1 s hp (by norm_num) hs
  have hb1 : b≤1 := unit_bound p s hp hs
  have ht : Tendsto (fun n : ℕ => (step p 1)^[n] b) atTop (𝓝 1) := by
    apply IntervalIteration.converge (step p 1) b 1 1 b ⟨hb1,le_rfl⟩ ⟨le_rfl,hb1⟩
    · intro t ht; exact step_continuous p 1 t hp (by norm_num) (hb.trans_le ht.1)
    · exact step_one p hp
    · intro t ht h; exact ⟨unit_increases p t hp (hb.trans_le ht.1) h,unit_bound p t hp (hb.trans_le ht.1)⟩
    · intro t ht h; exact False.elim (not_lt_of_ge ht.2 h)
  have he : (fun n : ℕ => (step p 1)^[n+1] s)=(fun n : ℕ => (step p 1)^[n] b) := by
    funext n; rw [iterate_succ_apply]
  exact (tendsto_add_atTop_iff_nat 1).mp (by rwa [he])

theorem step_scale (p : ℕ) (X a u : ℝ) (ha : X*a^p=1) :
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
    | succ n ih => rw [iterate_succ_apply',iterate_succ_apply',ih,step_scale p X a _ hroot]
  have ht := (unit_global p (s/a) hp (div_pos hs ha)).const_mul a
  simpa only [← he,mul_one] using ht

theorem global_convergence (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Tendsto (fun n : ℕ => (step p X)^[n] s) atTop (𝓝 (X⁻¹ ^ (1/(p:ℝ)))) := by
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  apply global_with_root p X _ s hp (Real.rpow_pos_of_pos (inv_pos.mpr hX) _) hs
  rw [← Real.rpow_natCast,one_div,Real.rpow_inv_rpow (inv_nonneg.mpr hX.le) hp0,mul_inv_cancel₀ hX.ne']

def orderFactor (p : ℕ) (e : ℝ) :=
  -2*(p:ℝ)*((p:ℝ)^2-1)*(2*(p:ℝ)-1)*(sumPowers p (1+e))^3/(den p ((1+e)^p))^2

theorem order_four (p : ℕ) (hp : 2≤p) :
    Tendsto (fun e : ℝ => (step p 1 (1+e)-1)/e^4) (𝓝[≠] 0)
      (𝓝 (-((p:ℝ)^2-1)*(2*(p:ℝ)-1)/72)) := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hp0 : (p:ℝ)≠0 := by linarith
  have hd0 : den p ((1+(0:ℝ))^p)≠0 := by simpa using (positive_terms p 1 hp (by norm_num)).2.1.ne'
  have hf0 : step p 1 (1+0)-1=0 := by simp [step_one p hp]
  have hc : ContinuousAt (fun e : ℝ => step p 1 (1+e)-1) 0 := by
    have hd1 := (positive_terms p 1 hp (by norm_num)).2.1.ne'
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
      HasDerivAt (fun e : ℝ => step p 1 (1+e)-1) (e^3*orderFactor p e) e := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (-1:ℝ)<0 by norm_num))] with e he
    have hpos : 0<1+e := by have : -1<e := he; linarith
    have hd := (positive_terms p _ hp (pow_pos hpos p)).2.1.ne'
    have hd' := ((hasDerivAt_step p 1 (1+e) hp (by simpa using hd)).comp e ((hasDerivAt_id e).const_add 1)).sub_const 1
    convert! hd' using 1
    simp only [one_mul,mul_one]
    have hi := sum_identity p (1+e)
    have hi' : (1+e)^p-1=e*sumPowers p (1+e) := by nlinarith [hi]
    rw [hi']; unfold orderFactor; ring
  have ht := LocalOrder.from_derivative 3 (fun e : ℝ => step p 1 (1+e)-1) (orderFactor p) hf0 hc hg hh
  have hv : orderFactor p 0/((3:ℝ)+1)= -((p:ℝ)^2-1)*(2*(p:ℝ)-1)/72 := by
    have hd : den p 1=6*(p:ℝ)^2 := by unfold den; ring
    simp only [orderFactor,add_zero,one_pow]
    rw [hd]
    simp [sumPowers]
    field_simp [hp0]
    <;> ring
  simpa only [Nat.reduceAdd,Nat.cast_ofNat,hv] using ht

theorem relative_order_four (p : ℕ) (X a : ℝ) (hp : 2≤p)
    (ha : 0<a) (hroot : X*a^p=1) :
    Tendsto (fun e : ℝ => (step p X (a*(1+e))/a-1)/e^4) (𝓝[≠] 0)
      (𝓝 (-((p:ℝ)^2-1)*(2*(p:ℝ)-1)/72)) := by
  simpa only [step_scale p X a _ hroot,mul_div_cancel_left₀ _ ha.ne'] using order_four p hp

theorem order_coefficient_negative (p : ℕ) (hp : 2≤p) :
    -((p:ℝ)^2-1)*(2*(p:ℝ)-1)/72<0 := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have h1 : 0<(p:ℝ)^2-1 := by nlinarith
  have h2 : 0<2*(p:ℝ)-1 := by linarith
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos h1) h2) (by norm_num)


/-- Fixed horizontal projection line. It passes through the pole on AB. -/
def ellY (W H X : ℝ) (p : ℕ) := H*(1+(5*(p:ℝ)-1)/(((p:ℝ)+1)*X))
def center (W H X : ℝ) (p : ℕ) : Point :=
  (W*(1+(5*(p:ℝ)-1)/(2*(p:ℝ)*(2*(p:ℝ)-1))),
   H*(1+((p:ℝ)+1)/((2*(p:ℝ)-1)*X)))
def projectedD (W H X s : ℝ) (p : ℕ) : Point :=
  (W+W*(5*(p:ℝ)-1)*pole p (X*s^p)/(((p:ℝ)+1)*num p (X*s^p)),ellY W H X p)
def supportSlope (W H X s : ℝ) (p : ℕ) := H/(W*X)*kappa p (X*s^p)

theorem D_on_ell (W H X s : ℝ) (p : ℕ) :
    On (horizontal (ellY W H X p)) (projectedD W H X s p) := by
  simp [On,horizontal,projectedD]

theorem D_on_ZE (W H X s : ℝ) (p : ℕ) (hp : 2≤p)
    (hX : 0<X) (hs : 0<s) :
    On (RectangleGeometry.join (center W H X p) (W,H*(1-s^p))) (projectedD W H X s p) := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hp0 : (p:ℝ)≠0 := by linarith
  have h2 : 2*(p:ℝ)-1≠0 := by linarith
  have h1 : (p:ℝ)+1≠0 := by linarith
  have hn := (positive_terms p (X*s^p) hp (by positivity)).1.ne'
  dsimp [On,RectangleGeometry.join,center,projectedD,ellY]
  field_simp [hp0,h2,h1,hX.ne',hn]
  unfold num pole
  ring_nf
  field_simp [show (-1:ℝ)+(p:ℝ)*2≠0 by linarith]
  <;> ring

theorem projection_det (W H X s : ℝ) (p : ℕ) :
    (RectangleGeometry.join (center W H X p) (W,H*(1-s^p))).a * (horizontal (ellY W H X p)).b -
    (horizontal (ellY W H X p)).a * (RectangleGeometry.join (center W H X p) (W,H*(1-s^p))).b =
      H*(((p:ℝ)+1)/((2*(p:ℝ)-1)*X)+s^p) := by
  dsimp [RectangleGeometry.join,center,horizontal]; ring

theorem projection_unique (W H X s : ℝ) (p : ℕ) (hp : 2≤p)
    (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    ∃! D : Point, On (RectangleGeometry.join (center W H X p) (W,H*(1-s^p))) D ∧
      On (horizontal (ellY W H X p)) D := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have h2 : 0<2*(p:ℝ)-1 := by linarith
  have hd : H*(((p:ℝ)+1)/((2*(p:ℝ)-1)*X)+s^p)≠0 := by positivity
  refine ⟨projectedD W H X s p,⟨D_on_ZE W H X s p hp hX hs,D_on_ell W H X s p⟩,?_⟩
  intro D hD
  apply intersection_unique _ _ _ _ _ hD ⟨D_on_ZE W H X s p hp hX hs,D_on_ell W H X s p⟩
  rwa [projection_det]

theorem D_on_support (W H X s : ℝ) (p : ℕ) (hp : 2≤p)
    (hW : 0<W) (hX : 0<X) (hs : 0<s) :
    On (RectangleGeometry.graph (supportSlope W H X s p) (H-supportSlope W H X s p*W))
      (projectedD W H X s p) := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have h1 : (p:ℝ)+1≠0 := by linarith
  have h := positive_terms p (X*s^p) hp (by positivity)
  dsimp [On,RectangleGeometry.graph,supportSlope,kappa,projectedD,ellY]
  field_simp [hW.ne',hX.ne',h1,h.1.ne',h.2.2.ne']
  unfold pole; ring

theorem support_gap (W H X s : ℝ) (p : ℕ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    supportSlope W H X s p-greenSlope W H X s p =
      H/(W*X)*(den p (X*s^p)/pole p (X*s^p)) := by
  have hq := (positive_terms p (X*s^p) hp (by positivity)).2.2.ne'
  unfold supportSlope greenSlope kappa
  field_simp [hq]
  unfold num den pole; ring

theorem report_formula (W H X s : ℝ) (p : ℕ) (hp : 2≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    reportState s (supportSlope W H X s p) (greenSlope W H X s p)=step p X s := by
  unfold reportState
  rw [support_gap W H X s p hp hX hs]
  unfold supportSlope kappa step
  have ht := positive_terms p (X*s^p) hp (by positivity)
  field_simp [hW.ne',hH.ne',hX.ne',ht.2.1.ne',ht.2.2.ne'] <;> ring

theorem geometric_readout (W H X s : ℝ) (p : ℕ) (hp : 2≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) (T : Point)
    (hT : On (RectangleGeometry.graph (supportSlope W H X s p) (H-supportSlope W H X s p*W)) T ∧
      On (RectangleGeometry.graph (greenSlope W H X s p) (H*(1-s)-greenSlope W H X s p*W)) T) :
    1-T.2/H=step p X s := by
  have hd := positive_terms p (X*s^p) hp (by positivity)
  have hg : 0<supportSlope W H X s p-greenSlope W H X s p := by
    rw [support_gap W H X s p hp hX hs]
    exact mul_pos (by positivity) (div_pos hd.2.1 hd.2.2)
  rw [report_unique W H s _ _ hg.ne' T hT,report_readout W H s _ _ hH.ne',
    report_formula W H X s p hp hW hH hX hs]

/-- All moving coordinates remain in the field of the inputs: no root extraction. -/
theorem coordinates_over (K : Subfield ℝ) (W H X s : ℝ) (p : ℕ)
    (hW : W∈K) (hH : H∈K) (hX : X∈K) (hs : s∈K) :
    RectangleConstructible.PointOver K (center W H X p) ∧
    RectangleConstructible.PointOver K (projectedD W H X s p) ∧ step p X s∈K := by
  dsimp [RectangleConstructible.PointOver,center,projectedD,ellY,step,num,den,pole]
  field_membership

theorem example_center : center 2 4 2 3=(44/15,28/5) := by norm_num [center]
theorem example_D : projectedD 2 4 2 (3/4) 3=(3524/789,11) := by
  norm_num [projectedD,ellY,num,pole]
theorem example_step : step 3 2 (3/4)=9468/11929 := by norm_num [step,num,den]

end LeanMath.Papers.RectangleProjective

