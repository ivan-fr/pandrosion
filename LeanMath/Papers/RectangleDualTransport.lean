import LeanMath.Papers.RectangleGeometry
import Mathlib.Analysis.Real.Sqrt

/-! Post-V20 fixed-AK transports. Exact real incidence and algebra, independent
of browser arithmetic. These certificates do not assert cost optimality or
uniform floating-point conditioning. -/
noncomputable section
namespace LeanMath.Papers.RectangleDualTransport
open RectangleGeometry

def numeratorH (p t : ℝ) := p+1+(p-1)*t
def denominatorH (p t : ℝ) := p-1+(p+1)*t
def numeratorP (p t : ℝ) := 2*p*((2*p-1)*t+p+1)
def denominatorP (p t : ℝ) := (p+1)*t^2+2*(2*p-1)*(p+1)*t+(2*p-1)*(p-1)
def divisorP (p t : ℝ) := (p+1)*t+5*p-1
def rad (p t : ℝ) := ((p-2)*(t^2+1)+(10*p+4)*t)/(12*p)
def g (p t : ℝ) := (p-1)*Real.sqrt (rad p t)
def beta (p : ℝ) := (p-1)*Real.sqrt ((p-2)/(12*p))
def alpha (p : ℝ) := (5*p+2)/(p-2)
def transport (p C : ℝ) := p*(1-1/C)
def ratio (p r : ℝ) := p/(p-r)
def endpoint (W H X p t κ : ℝ) : Point := (W*κ/p,H*(1-t/X))
def anchor (H X : ℝ) : Point := (0,H*(1-1/X))

theorem arbitrary_correction (p C : ℝ) (hp : p≠0) (hC : C≠0) :
    ratio p (transport p C)=C := by
  unfold ratio transport
  have h : p-p*(1-1/C)=p/C := by ring
  rw [h]; field_simp

theorem gauge_invariance (a κ r : ℝ) (ha : a≠0) :
    (a*κ)/(a*κ-a*r)=κ/(κ-r) := by
  rw [← mul_sub, mul_div_mul_left _ _ ha]

theorem redistribution (p κ t : ℝ) (hp : p≠0) (hk : κ≠0)
    (hd : κ-1+t≠0) : ratio p (p*(1-t)/κ)=κ/(κ-1+t) := by
  have he : p-p*(1-t)/κ=p*(κ-1+t)/κ := by field_simp; ring
  unfold ratio; rw [he]; field_simp

/-- The common correction identity with both slopes variable. -/
theorem generalized_report (s p r L : ℝ) (hL : L≠0) :
    reportState s (L*p) (L*r)=s*ratio p r := by
  unfold reportState ratio
  rw [← mul_sub]
  calc
    L*p*s/(L*(p-r)) = L*(p*s)/(L*(p-r)) := by ring
    _ = (p*s)/(p-r) := mul_div_mul_left _ _ hL
    _ = s*(p/(p-r)) := by ring

theorem endpoint_incidence (W H X p t κ : ℝ)
    (hW : W≠0) (hX : X≠0) (hp : p≠0) (hk : κ≠0) :
    On (graph (H/(W*X)*(p*(1-t)/κ)) (H*(1-1/X)))
      (endpoint W H X p t κ) := by
  rw [graph_on]; dsimp [endpoint]; field_simp; ring

theorem endpoint_horizontal (W H X p t κ : ℝ) :
    On (horizontal (H*(1-t/X))) (endpoint W H X p t κ) := by
  simp [On,horizontal,endpoint]

theorem transport_join_proper (W H X p t κ : ℝ)
    (hW : W≠0) (hp : p≠0) (hk : κ≠0) :
    Proper (join (anchor H X) (endpoint W H X p t κ)) := by
  right
  simpa [join,anchor,endpoint] using div_ne_zero (mul_ne_zero hW hk) hp

/-- Actual intersection of fixed AK with the parallel to MR through P. -/
def dualPoint (W H X p s t κ : ℝ) : Point :=
  (W-W*X*s*κ/(p*(κ-1+t)), H-H*s*κ/(κ-1+t))

theorem fixed_ak_actual_incidence (W H X p s t κ : ℝ)
    (hp : p≠0) (hX : X≠0) (hd : κ-1+t≠0) :
    On (join (W,H) (W*(1-X/p),0)) (dualPoint W H X p s t κ) ∧
    On (parallel (join (anchor H X) (endpoint W H X p t κ)) (W,H*(1-s)))
      (dualPoint W H X p s t κ) := by
  dsimp [On,join,parallel,anchor,endpoint,dualPoint]
  constructor <;> field_simp <;> ring

theorem fixed_ak_determinant (W H X p s t κ : ℝ) (hp : p≠0) (hX : X≠0) :
    let l := join (W,H) (W*(1-X/p),0)
    let m := parallel (join (anchor H X) (endpoint W H X p t κ)) (W,H*(1-s))
    l.a*m.b-m.a*l.b = H*W*(κ-1+t)/p := by
  dsimp [join,parallel,anchor,endpoint]; field_simp; ring

theorem fixed_ak_actual_unique (W H X p s t κ : ℝ)
    (hW : W≠0) (hH : H≠0) (hX : X≠0) (hp : p≠0) (hd : κ-1+t≠0)
    (T : Point)
    (hT : On (join (W,H) (W*(1-X/p),0)) T ∧
      On (parallel (join (anchor H X) (endpoint W H X p t κ)) (W,H*(1-s))) T) :
    T=dualPoint W H X p s t κ := by
  apply intersection_unique _ _ _ T _ hT (fixed_ak_actual_incidence W H X p s t κ hp hX hd)
  rw [fixed_ak_determinant W H X p s t κ hp hX]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hH hW) hd) hp

theorem fixed_ak_actual_readout (W H X p s t κ : ℝ) (hH : H≠0) :
    1-(dualPoint W H X p s t κ).2/H=s*κ/(κ-1+t) := by
  dsimp [dualPoint]; field_simp; ring

theorem transport_at_root (p κ : ℝ) : p*(1-(1:ℝ))/κ=0 := by ring

theorem newton_transport (p t : ℝ) : ratio p (1-t)=p/(p-1+t) := by
  unfold ratio; congr 1; ring

theorem halley_transport (p t : ℝ) (hp : p≠0)
    (hN : numeratorH p t≠0) (hD : denominatorH p t≠0) :
    ratio p (2*p*(1-t)/numeratorH p t)=numeratorH p t/denominatorH p t := by
  have he : p-2*p*(1-t)/numeratorH p t=p*denominatorH p t/numeratorH p t := by
    apply (eq_div_iff hN).2
    rw [sub_mul, div_mul_cancel₀ _ hN]
    unfold numeratorH denominatorH; ring
  unfold ratio; rw [he]; field_simp

/-- In particular, the coefficient in the proposed Halley numerator must be 2p. -/
theorem halley_required_slope (p t : ℝ) (hN : numeratorH p t≠0)
    (hD : denominatorH p t≠0) :
    transport p (numeratorH p t/denominatorH p t)=2*p*(1-t)/numeratorH p t := by
  unfold transport; field_simp; unfold numeratorH denominatorH; ring

theorem projective_factorization (p t : ℝ) :
    denominatorP p t-numeratorP p t=(t-1)*divisorP p t := by
  unfold denominatorP numeratorP divisorP; ring

theorem projective_transport (p t : ℝ) (hp : p≠0)
    (hN : numeratorP p t≠0) (hD : denominatorP p t≠0) :
    ratio p (p*(1-t)*divisorP p t/numeratorP p t)=numeratorP p t/denominatorP p t := by
  have he : p-p*(1-t)*divisorP p t/numeratorP p t=p*denominatorP p t/numeratorP p t := by
    field_simp; have := projective_factorization p t; nlinarith [this]
  unfold ratio; rw [he]; field_simp

theorem arc_transport (p t g : ℝ) (hp : p≠0) (hg : 1+g≠0) (hd : t+g≠0) :
    ratio p (p*(1-t)/(1+g))=(1+g)/(t+g) := by
  have he : p-p*(1-t)/(1+g)=p*(t+g)/(1+g) := by field_simp; ring
  unfold ratio; rw [he]; field_simp

/-- Halley endpoint is obtained on the existing last horizontal by a fixed rail. -/
theorem halley_rail (W H X p t : ℝ) (hW : W≠0) (hH : H≠0)
    (hX : X≠0) (hp : p≠0) :
    On (⟨2*p/W,(p-1)*X/H,p+1+(p-1)*X⟩ : Line)
      (endpoint W H X p t (numeratorH p t/2)) := by
  dsimp [On,endpoint,numeratorH]; field_simp; ring

theorem halley_rail_transverse (W H X p : ℝ) (hW : W≠0) (hp : p≠0) :
    (2*p/W)*1-0*((p-1)*X/H)≠0 := by
  simpa using div_ne_zero (mul_ne_zero (show (2:ℝ)≠0 by norm_num) hp) hW

/-- One projection encodes the projective support coefficient as a horizontal length. -/
theorem projective_projection (W H X p t : ℝ) (hX : X≠0)
    (hv : p+1≠0) (hd : divisorP p t≠0) :
    On (join (2*W*(2*p-1)/(p+1),H+H*(5*p-1)/(X*(p+1)))
      (W,H*(1-t/X)))
      (2*W*((2*p-1)*t+p+1)/divisorP p t,H*(1-1/X)) := by
  dsimp [On,join]; unfold divisorP at *; field_simp; ring

/-- The radius-scaling projection; λ=1 needs no projection. -/
theorem radius_projection (W y yG lam : ℝ) (hl : lam-1≠0) :
    On (join (W*lam/(lam-1),yG) (W,y)) (0,yG+lam*(y-yG)) := by
  dsimp [On,join]; field_simp; ring

theorem radical_decomposition (p t : ℝ) (hp : p≠0) (h2 : p-2≠0) :
    (p-2)/(12*p)*(t^2+2*alpha p*t+1)=rad p t := by
  unfold alpha rad; field_simp; ring

theorem rad_positive (p t : ℝ) (hp : 3≤p) (ht : 0<t) : 0<rad p t := by
  unfold rad
  have h1 : 0<p-2 := by linarith
  have h2 : 0<10*p+4 := by linarith
  have h3 : 0<12*p := by linarith
  exact div_pos (add_pos (mul_pos h1 (by positivity)) (mul_pos h2 ht)) h3

theorem g_positive (p t : ℝ) (hp : 3≤p) (ht : 0<t) : 0<g p t := by
  exact mul_pos (by linarith) (Real.sqrt_pos.2 (rad_positive p t hp ht))

theorem alpha_gt_one (p : ℝ) (hp : 3≤p) : 1<alpha p := by
  unfold alpha
  apply (lt_div_iff₀ (by linarith : 0<p-2)).2
  linarith

theorem beta_positive (p : ℝ) (hp : 3≤p) : 0<beta p := by
  unfold beta
  apply mul_pos (by linarith)
  apply Real.sqrt_pos.2
  exact div_pos (by linarith) (by linarith)

theorem radical_identity (p t : ℝ) (hp : 3≤p) (ht : 0<t) :
    beta p*Real.sqrt (t^2+2*alpha p*t+1)=g p t := by
  have hb : 0≤(p-2)/(12*p) := le_of_lt (div_pos (by linarith) (by linarith))
  rw [beta,g, mul_assoc, ← Real.sqrt_mul hb]
  rw [radical_decomposition p t (by linarith) (by linarith)]

/-- Positive branch of the circle, with a separately scaled vertical radius. -/
theorem arc_circle_incidence (W p b a t y : ℝ)
    (ha : 0≤a^2-1) (ht : 0≤t^2+2*a*t+1) :
    (W*(1+b*Real.sqrt (t^2+2*a*t+1))/p-W/p)^2+
      (y-(y+W*b/p*Real.sqrt (a^2-1)))^2 = (W*b/p*(t+a))^2 := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt ht
  calc
    _ = (W*b/p)^2*((Real.sqrt (t^2+2*a*t+1))^2+(Real.sqrt (a^2-1))^2) := by ring
    _ = _ := by rw [h1,h2]; ring

theorem arc_right_branch_unique (x c d radius u : ℝ)
    (hx : c≤x) (hu : c≤u)
    (he : (x-c)^2+d^2=radius^2) (hf : (u-c)^2+d^2=radius^2) : x=u := by
  nlinarith [sq_nonneg (x-u)]

theorem arc_endpoint_right (W p t : ℝ) (hW : 0<W) (hp : 3≤p) (ht : 0<t) :
    W/p<W*(1+g p t)/p := by
  apply (div_lt_div_iff_of_pos_right (by linarith : 0<p)).2
  have hg := g_positive p t hp ht
  nlinarith

theorem positive_coefficients (p t : ℝ) (hp : 3≤p) (ht : 0<t) :
    0<numeratorH p t ∧ 0<denominatorH p t ∧
    0<numeratorP p t ∧ 0<denominatorP p t ∧ 0<divisorP p t := by
  have h1 : 0<p-1 := by linarith
  have h2 : 0<p+1 := by linarith
  have h3 : 0<2*p-1 := by linarith
  have h4 : 0<p := by linarith
  have h5 : 0<5*p-1 := by linarith
  unfold numeratorH denominatorH numeratorP denominatorP divisorP
  refine ⟨?_,?_,?_,?_,?_⟩
  · positivity
  · positivity
  · positivity
  · positivity
  · nlinarith [mul_pos h2 ht]

theorem fixed_ak_gap (p C : ℝ) (hp : 0<p) (hC : 0<C) :
    0<p-transport p C := by
  have he : p-transport p C=p/C := by unfold transport; ring
  rw [he]; exact div_pos hp hC

end LeanMath.Papers.RectangleDualTransport
