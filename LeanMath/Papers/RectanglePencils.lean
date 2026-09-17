import LeanMath.Papers.RectangleProjectiveVerification

/-! Finite affine charts for the pencil telescope. Excluded hubs at infinity
are explicit hypotheses: convergence of the rational map is a separate fact. -/
noncomputable section
namespace LeanMath.Papers.RectanglePencils
open LeanMath.Papers.RectangleGeometry LeanMath.Papers.RectangleReports
open LeanMath.Papers

def left (H v : ℝ) : Point := (0,H*(1-v))
def right (W H v : ℝ) : Point := (W,H*(1-v))
def hub (W H f : ℝ) : Point := (W*f/(f-1),H)

theorem hub_on_top (W H f : ℝ) : On (horizontal H) (hub W H f) := by
  simp [On,horizontal,hub]
theorem left_on_axis (H v : ℝ) : On (vertical 0) (left H v) := by simp [On,vertical,left]
theorem right_on_axis (W H v : ℝ) : On (vertical W) (right W H v) := by simp [On,vertical,right]

theorem multiply_incidence (W H v f : ℝ) (hf : f-1≠0) :
    On (join (hub W H f) (right W H v)) (left H (v*f)) := by
  dsimp [On,join,hub,right,left]; field_simp [hf]; ring

theorem multiply_det (W H v f : ℝ) (hf : f-1≠0) :
    (join (hub W H f) (right W H v)).a*(vertical 0).b-
      (vertical 0).a*(join (hub W H f) (right W H v)).b=W/(f-1) := by
  dsimp [join,hub,right,vertical]; field_simp [hf]; ring

theorem multiply_unique (W H v f : ℝ) (hW : W≠0) (hf : f-1≠0) (L : Point)
    (hL : On (join (hub W H f) (right W H v)) L ∧ On (vertical 0) L) :
    L=left H (v*f) := by
  apply intersection_unique _ _ _ _ _ hL ⟨multiply_incidence W H v f hf,left_on_axis H _⟩
  rw [multiply_det W H v f hf]
  exact div_ne_zero hW hf

theorem divide_incidence (W H v f : ℝ) (hf : f-1≠0) (hf0 : f≠0) :
    On (join (hub W H f) (left H v)) (right W H (v/f)) := by
  dsimp [On,join,hub,right,left]; field_simp [hf,hf0]; ring

theorem divide_unique (W H v f : ℝ) (hW : W≠0) (hf : f-1≠0) (hf0 : f≠0) (R : Point)
    (hR : On (join (hub W H f) (left H v)) R ∧ On (vertical W) R) :
    R=right W H (v/f) := by
  apply intersection_unique _ _ _ _ _ hR ⟨divide_incidence W H v f hf hf0,right_on_axis W H _⟩
  dsimp [join,hub,left,vertical]
  simpa using div_ne_zero (mul_ne_zero hW hf0) hf

/-- q_n encodes s^(n+1), with a level-dependent scale 2^n. -/
def chain (s : ℝ) (n : ℕ) := s^(n+1)/(2:ℝ)^n

theorem chain_start (s : ℝ) : chain s 0=s := by simp [chain]
theorem chain_step (s : ℝ) (n : ℕ) : (chain s n/2)/(1/s)=chain s (n+1) := by
  simp only [chain,div_div,div_one,one_div,div_inv_eq_mul]
  rw [pow_succ,pow_succ]
  ring

theorem chain_unscale (s : ℝ) (p : ℕ) (hp : 1≤p) :
    (2:ℝ)^(p-1)*chain s (p-1)=s^p := by
  unfold chain
  rw [show p-1+1=p by omega]
  field_simp

theorem chain_center (W H s : ℝ) (hs : s≠0) (hs1 : s≠1) :
    On (join (left H 1) (right W H s)) (hub W H (1/s)) := by
  dsimp [On,join,left,right,hub]
  have hf : 1/s-1≠0 := by intro h; apply hs1; field_simp at h; linarith
  field_simp [hf,hs]
  <;> ring

/-- A fixed projector produces f=a+b/q on the top line. -/
def projector (W H a b : ℝ) : Point := (-W*a/(1-a),H*(1-b/(1-a)))
def factor (a b q : ℝ) := a+b/q

theorem projector_incidence (W H a b q : ℝ) (hq : q≠0) (ha : 1-a≠0)
    (hf : factor a b q-1≠0) :
    On (join (projector W H a b) (right W H q)) (hub W H (factor a b q)) := by
  dsimp [On,join,projector,right,hub]
  field_simp [ha,hf]
  unfold factor
  field_simp [hq]
  <;> ring

theorem projector_gap (W H a b q : ℝ) (ha : 1-a≠0) (hq : q≠0) :
    (projector W H a b).2-(right W H q).2=H*q*(1-factor a b q)/(1-a) := by
  dsimp [projector,right,factor]; field_simp [ha,hq]; ring

theorem projector_unique (W H a b q : ℝ) (hH : H≠0) (hq : q≠0) (ha : 1-a≠0)
    (hf : factor a b q-1≠0) (U : Point)
    (hU : On (join (projector W H a b) (right W H q)) U ∧ On (horizontal H) U) :
    U=hub W H (factor a b q) := by
  apply intersection_unique _ _ _ _ _ hU ⟨projector_incidence W H a b q hq ha hf,hub_on_top W H _⟩
  simp only [join,horizontal,mul_one,zero_mul,sub_zero]
  change (projector W H a b).2-(right W H q).2≠0
  rw [projector_gap W H a b q ha hq]
  apply div_ne_zero (mul_ne_zero (mul_ne_zero hH hq) _) ha
  intro h; apply hf; linarith

/-- The four actual joins implement a ratio of two factors. -/
theorem four_join_readout (W H s q a b c d : ℝ)
    (hW : W≠0) (hH : H≠0) (hq : q≠0) (ha : 1-a≠0) (hc : 1-c≠0)
    (hf : factor a b q-1≠0) (hg : factor c d q-1≠0) (hg0 : factor c d q≠0)
    (U V L R : Point)
    (hU : On (join (projector W H a b) (right W H q)) U ∧ On (horizontal H) U)
    (hV : On (join (projector W H c d) (right W H q)) V ∧ On (horizontal H) V)
    (hL : On (join U (right W H s)) L ∧ On (vertical 0) L)
    (hR : On (join V L) R ∧ On (vertical W) R) :
    R=right W H (s*factor a b q/factor c d q) := by
  rw [projector_unique W H a b q hH hq ha hf U hU] at hL
  have he := multiply_unique W H s _ hW hf L hL
  rw [projector_unique W H c d q hH hq hc hg V hV,he] at hR
  exact divide_unique W H _ _ hW hg hg0 R hR

/-- Halley projector coefficients, accounting for the telescope scale. -/
def scale (p : ℕ) := (2:ℝ)^(p-1)
def aH (p : ℕ) := ((p:ℝ)-1)/(4*(p:ℝ))
def bH (p : ℕ) (X : ℝ) := ((p:ℝ)+1)/(4*(p:ℝ)*scale p*X)
def cH (p : ℕ) := ((p:ℝ)+1)/(4*(p:ℝ))
def dH (p : ℕ) (X : ℝ) := ((p:ℝ)-1)/(4*(p:ℝ)*scale p*X)

theorem halley_factor_formula (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : X≠0) (hs : s≠0) :
    s*factor (aH p) (bH p X) (chain s (p-1)) /
      factor (cH p) (dH p X) (chain s (p-1))=ad p X s := by
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  have hscale : scale p≠0 := by unfold scale; positivity
  have hsp : s^p≠0 := pow_ne_zero _ hs
  unfold factor aH bH cH dH chain ad
  rw [show p-1+1=p by omega]
  unfold scale at *
  field_simp [hp0,hX,hs,hsp]
  <;> ring

theorem halley_center_a (p : ℕ) (W H X : ℝ) (hp : 2≤p) (hX : X≠0) :
    projector W H (aH p) (bH p X)=
      (-W*((p:ℝ)-1)/(3*(p:ℝ)+1),H*(1-((p:ℝ)+1)/(scale p*X*(3*(p:ℝ)+1)))) := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hp0 : (p:ℝ)≠0 := by linarith
  have h3 : 3*(p:ℝ)+1≠0 := by linarith
  have hs : 0<scale p := by unfold scale; positivity
  have h3' : (1:ℝ)+(p:ℝ)*3≠0 := by linarith
  have hs3 : (p:ℝ)*scale p*3+scale p≠0 := by positivity
  ext <;> dsimp [projector,aH,bH] <;> field_simp [hp0,h3,hX] <;> ring_nf <;> field_simp [h3',hs3,hs.ne'] <;> ring

theorem halley_center_b (p : ℕ) (W H X : ℝ) (hp : 2≤p) (hX : X≠0) :
    projector W H (cH p) (dH p X)=
      (-W*((p:ℝ)+1)/(3*(p:ℝ)-1),H*(1-((p:ℝ)-1)/(scale p*X*(3*(p:ℝ)-1)))) := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hp0 : (p:ℝ)≠0 := by linarith
  have h3 : 3*(p:ℝ)-1≠0 := by linarith
  ext <;> dsimp [projector,cH,dH] <;> field_simp [hp0,h3,hX] <;> ring

/-- At t=1 both correction hubs are U[1/2], always finite. -/
theorem halley_root_factors (p : ℕ) (X q : ℝ) (hp : 2≤p) (hq : scale p*X*q=1) :
    factor (aH p) (bH p X) q=1/2 ∧ factor (cH p) (dH p X) q=1/2 := by
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (show p≠0 by omega)
  dsimp [factor,aH,bH,cH,dH]
  rw [div_div,div_div]
  have he : 4*(p:ℝ)*scale p*X*q=4*(p:ℝ) := by nlinarith [hq]
  rw [he]
  constructor <;> field_simp [hp0] <;> ring

/-- Algebraic map realized by the finite construction on its admissible chart. -/
def pencilHalley (p : ℕ) (X s : ℝ) := ad p X s

theorem halley_global (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    Filter.Tendsto (fun n : ℕ => (pencilHalley p X)^[n] s) Filter.atTop
      (nhds (X⁻¹ ^ (1/(p:ℝ)))) := RectangleDynamics.ad_global_convergence p X s hp hX hs

theorem example_q : chain (3/4) 2=27/256 := by norm_num [chain]
theorem example_Za : projector 2 4 (aH 3) (bH 3 2)=(-2/5,19/5) := by
  norm_num [projector,aH,bH,scale]
theorem example_Zb : projector 2 4 (cH 3) (dH 3 2)=(-1,31/8) := by
  norm_num [projector,cH,dH,scale]
theorem example_readout : pencilHalley 3 2 (3/4)=273/344 := by norm_num [pencilHalley,ad]


/-- Rational fixed projectors are in the field generated by the inputs. -/
theorem projectors_over (K : Subfield ℝ) (W H a b : ℝ)
    (hW : W∈K) (hH : H∈K) (ha : a∈K) (hb : b∈K) :
    RectangleConstructible.PointOver K (projector W H a b) := by
  dsimp [RectangleConstructible.PointOver,projector]
  field_membership

theorem chain_center_unique (W H s : ℝ) (hH : H≠0) (hs : s≠0) (hs1 : s≠1)
    (U : Point) (hU : On (join (left H 1) (right W H s)) U ∧ On (horizontal H) U) :
    U=hub W H (1/s) := by
  apply intersection_unique _ _ _ _ _ hU ⟨chain_center W H s hs hs1,hub_on_top W H _⟩
  dsimp [join,left,right,horizontal]
  have h : 1-s≠0 := by intro h; apply hs1; linarith
  simpa using neg_ne_zero.mpr (mul_ne_zero hH h)

/-- One outward and one return join implement the scaled power recurrence. -/
theorem chain_cycle (W H s : ℝ) (n : ℕ) (hs : s≠0) (hs1 : s≠1) :
    On (join (hub W H (1/2)) (right W H (chain s n))) (left H (chain s n/2)) ∧
    On (join (hub W H (1/s)) (left H (chain s n/2))) (right W H (chain s (n+1))) := by
  have hf : 1/s-1≠0 := by intro h; apply hs1; field_simp at h; linarith
  constructor
  · convert multiply_incidence W H (chain s n) (1/2) (by norm_num) using 1 <;> congr 1 <;> ring
  · rw [← chain_step s n]
    exact divide_incidence W H _ _ hf (one_div_ne_zero hs)

/-- Halley implemented by the four correction joins, conditional only on
finite-chart nondegeneracy plus the actual incidence data. -/
theorem halley_construction_readout (W H X s : ℝ) (p : ℕ) (hp : 2≤p)
    (hW : W≠0) (hH : H≠0) (hX : X≠0) (hs : s≠0)
    (ha : 1-aH p≠0) (hc : 1-cH p≠0)
    (hf : factor (aH p) (bH p X) (chain s (p-1))-1≠0)
    (hg : factor (cH p) (dH p X) (chain s (p-1))-1≠0)
    (hg0 : factor (cH p) (dH p X) (chain s (p-1))≠0)
    (U V L R : Point)
    (hU : On (join (projector W H (aH p) (bH p X)) (right W H (chain s (p-1)))) U ∧ On (horizontal H) U)
    (hV : On (join (projector W H (cH p) (dH p X)) (right W H (chain s (p-1)))) V ∧ On (horizontal H) V)
    (hL : On (join U (right W H s)) L ∧ On (vertical 0) L)
    (hR : On (join V L) R ∧ On (vertical W) R) :
    R=right W H (ad p X s) := by
  have hq : chain s (p-1)≠0 := by unfold chain; exact div_ne_zero (pow_ne_zero _ hs) (by positivity)
  rw [four_join_readout W H s _ _ _ _ _ hW hH hq ha hc hf hg hg0 U V L R hU hV hL hR,
    halley_factor_formula p X s hp hX hs]


/-- s=1 is a genuine affine-chart obstruction, not a root-method failure. -/
theorem initial_chart_failure (W H : ℝ) (hW : W≠0) (hH : H≠0) :
    ¬∃ U : Point, On (join (left H 1) (right W H 1)) U ∧ On (horizontal H) U := by
  rintro ⟨U,hU,hTop⟩
  have hy : U.2=H := by simpa [On,horizontal] using hTop
  have hz : W*U.2=0 := by simpa [On,join,left,right] using hU
  rw [hy] at hz
  exact mul_ne_zero hW hH hz

/-- X=2,s=1/2,p=3 sends the second correction hub to infinity. -/
theorem example_correction_chart_failure :
    ¬∃ U : Point,
      On (join (projector 2 4 (cH 3) (dH 3 2)) (right 2 4 (chain (1/2) 2))) U ∧
      On (horizontal 4) U := by
  rintro ⟨U,hU,hTop⟩
  norm_num [On,join,projector,cH,dH,scale,right,chain,horizontal] at hU hTop
  linarith

open Filter Set
open scoped Topology

theorem halley_relative_order_three (p : ℕ) (X a : ℝ) (hp : 2≤p)
    (ha : 0<a) (hroot : X*a^p=1) :
    Tendsto (fun e : ℝ => (pencilHalley p X (a*(1+e))/a-1)/e^3) (𝓝[≠] 0)
      (𝓝 (((p:ℝ)^2-1)/12)) := RectangleDynamics.ad_relative_order_three p X a hp ha hroot

end LeanMath.Papers.RectanglePencils
