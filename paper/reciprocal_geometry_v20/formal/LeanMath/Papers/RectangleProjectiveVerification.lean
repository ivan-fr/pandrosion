import LeanMath.Papers.RectangleProjective

noncomputable section
namespace LeanMath.Papers.RectangleProjective
open LeanMath.Papers.RectangleGeometry LeanMath.Papers.RectangleReports

/-- The projection lands strictly to the right of A, so AD is a proper line. -/
theorem D_right_of_A (W H X s : ℝ) (p : ℕ) (hp : 2≤p)
    (hW : 0<W) (hX : 0<X) (hs : 0<s) : W<(projectedD W H X s p).1 := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have h5 : 0<5*(p:ℝ)-1 := by linarith
  have ht := positive_terms p (X*s^p) hp (by positivity)
  dsimp [projectedD]
  exact lt_add_of_pos_right W (div_pos (mul_pos (mul_pos hW h5) ht.2.2)
    (mul_pos (by positivity) ht.1))

theorem join_support_equiv (W H k : ℝ) (D T : Point) (hx : D.1-W≠0)
    (hD : On (graph k (H-k*W)) D) :
    On (join (W,H) D) T ↔ On (graph k (H-k*W)) T := by
  dsimp [On,join,graph] at *
  constructor
  · intro ht
    have he : (D.1-W)*(-k*T.1+T.2-(H-k*W))=0 := by
      linear_combination ht + (T.1-W)*hD
    have hz := (mul_eq_zero.mp he).resolve_left hx
    linarith
  · intro ht
    linear_combination (D.1-W)*ht-(T.1-W)*hD

/-- End-to-end: projection incidence, actual join AD, and the report parallel
force the claimed next inverse-root state. -/
theorem construction_readout (W H X s : ℝ) (p : ℕ) (hp : 2≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) (D T : Point)
    (hD : On (join (center W H X p) (W,H*(1-s^p))) D ∧
      On (horizontal (ellY W H X p)) D)
    (hT : On (join (W,H) D) T ∧
      On (graph (greenSlope W H X s p) (H*(1-s)-greenSlope W H X s p*W)) T) :
    1-T.2/H=step p X s := by
  have hd := projection_unique W H X s p hp hH hX hs
  have he : D=projectedD W H X s p := hd.unique hD ⟨D_on_ZE W H X s p hp hX hs,D_on_ell W H X s p⟩
  subst D
  apply geometric_readout W H X s p hp hW hH hX hs T
  exact ⟨(join_support_equiv W H _ _ T (sub_pos.mpr (D_right_of_A W H X s p hp hW hX hs)).ne'
    (D_on_support W H X s p hp hW hX hs)).mp hT.1,hT.2⟩

/-- Explicitly constructing the two intersections is always possible. -/
theorem construction_exists (W H X s : ℝ) (p : ℕ) (hp : 2≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    ∃ D T : Point,
      (On (join (center W H X p) (W,H*(1-s^p))) D ∧ On (horizontal (ellY W H X p)) D) ∧
      (On (join (W,H) D) T ∧ On (graph (greenSlope W H X s p) (H*(1-s)-greenSlope W H X s p*W)) T) ∧
      1-T.2/H=step p X s := by
  let D := projectedD W H X s p
  let k := supportSlope W H X s p
  let m := greenSlope W H X s p
  let T := reportPoint W H s k m
  have hd : On (join (center W H X p) (W,H*(1-s^p))) D ∧ On (horizontal (ellY W H X p)) D :=
    ⟨D_on_ZE W H X s p hp hX hs,D_on_ell W H X s p⟩
  have ht := positive_terms p (X*s^p) hp (by positivity)
  have hg : 0<k-m := by
    dsimp [k,m]; rw [support_gap W H X s p hp hX hs]
    exact mul_pos (by positivity) (div_pos ht.2.1 ht.2.2)
  have hT' := report_incidence W H s k m hg.ne'
  have hT : On (join (W,H) D) T ∧ On (graph m (H*(1-s)-m*W)) T := by
    refine ⟨?_,hT'.2⟩
    exact (join_support_equiv W H k D T (sub_pos.mpr (D_right_of_A W H X s p hp hW hX hs)).ne'
      (D_on_support W H X s p hp hW hX hs)).mpr hT'.1
  exact ⟨D,T,hd,hT,construction_readout W H X s p hp hW hH hX hs D T hd hT⟩

/-- The ordinary root variable y=1/s uses the rational [2/1] correction. -/
theorem inverse_correction (p : ℕ) (X s : ℝ) :
    (step p X s)⁻¹=s⁻¹*(den p (X*s^p)/num p (X*s^p)) := by
  simp [step,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

/-- Cubic Taylor polynomial of (1+d)^(1/p). -/
def rootJet3 (p : ℕ) (d : ℝ) :=
  1+d/(p:ℝ)+(1-(p:ℝ))*d^2/(2*(p:ℝ)^2)+
    (1-(p:ℝ))*(1-2*(p:ℝ))*d^3/(6*(p:ℝ)^3)

/-- Polynomial Padé certificate: matching through degree three with nonzero
linear denominator at d=0. This is an exact identity, not a sampled fit. -/
theorem pade_certificate (p : ℕ) (d : ℝ) (hp : (p:ℝ)≠0) :
    den p (1+d)-num p (1+d)*rootJet3 p d=
      -d^4*((p:ℝ)-1)*(2*(p:ℝ)-1)^2/(3*(p:ℝ)^2) := by
  unfold den num rootJet3
  field_simp [hp]
  <;> ring

/-- A normalized homography (p+b*d)/(1+c*d) with the required two jet
coefficients has uniquely determined b and c. Scope: homographies only. -/
theorem homography_jet_unique (p : ℕ) (b c : ℝ) (hp : 2≤p)
    (h1 : 2*(b-(p:ℝ)*c)=(p:ℝ)-1)
    (h2 : 12*(p:ℝ)*((p:ℝ)*c^2-b*c)= -((p:ℝ)^2-1)) :
    c=((p:ℝ)+1)/(6*(p:ℝ)) ∧ b=(2*(p:ℝ)-1)/3 := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have hp0 : (p:ℝ)≠0 := by linarith
  have hm : (p:ℝ)-1≠0 := by linarith
  have he : ((p:ℝ)-1)*(6*(p:ℝ)*c-((p:ℝ)+1))=0 := by
    linear_combination -6*(p:ℝ)*c*h1-h2
  have hh := (mul_eq_zero.mp he).resolve_left hm
  constructor
  · apply (eq_div_iff (by positivity : (6:ℝ)*(p:ℝ)≠0)).mpr
    nlinarith
  · nlinarith

/-- Positive inputs land below the inverse root after one step. -/
theorem bound_with_root (p : ℕ) (X a s : ℝ) (hp : 2≤p)
    (ha : 0<a) (hs : 0<s) (hroot : X*a^p=1) : step p X s≤a := by
  have h := unit_bound p (s/a) hp (div_pos hs ha)
  have he : a*(s/a)=s := by field_simp
  rw [← he,step_scale p X a _ hroot]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha.le

end LeanMath.Papers.RectangleProjective
