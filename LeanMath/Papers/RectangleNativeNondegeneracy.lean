import LeanMath.Papers.RectangleFastPower
import LeanMath.Papers.RectangleFixedCircleStereo

/-! Post-V20 incidence audit of the original four rectangle protocols.
All certificates concern actual joins, parallels, meets, and selected circle
branches. They do not use scalar convergence as an existence argument. -/
noncomputable section
namespace LeanMath.Papers.RectangleNativeNondegeneracy
open RectangleGeometry RectangleReports

def det (l m : Line) := l.a*m.b-m.a*l.b
def FinitePair (l m : Line) : Prop := det l m ≠ 0 ∧ ∃! Q : Point, On l Q ∧ On m Q

theorem finite_pair (l m : Line) (h : det l m ≠ 0) : FinitePair l m := by
  refine ⟨h,meet l m,meet_on l m h,?_⟩
  intro Q hQ; exact intersection_unique l m h Q _ hQ (meet_on l m h)

theorem finite_pair_proper (l m : Line) (h : det l m ≠ 0) : Proper l ∧ Proper m := by
  constructor <;> by_contra hn
  · simp only [Proper,not_or,not_not] at hn
    apply h; simp [det,hn.1,hn.2]
  · simp only [Proper,not_or,not_not] at hn
    apply h; simp [det,hn.1,hn.2]

structure NativeCertificate (W H s : ℝ) : Prop where
  red : Proper (join (leftLevel H s 1) (W,0))
  initial : FinitePair (horizontal (H*(1-s))) (vertical 0)
  initial_value : meet (horizontal (H*(1-s))) (vertical 0) = leftLevel H s 1
  step : ∀ j : ℕ, FinitePair (vertical 0)
    (parallel (join (leftLevel H s 1) (W,0)) (diagonalLevel W H s j))
  step_value : ∀ j : ℕ, meet (vertical 0)
    (parallel (join (leftLevel H s 1) (W,0)) (diagonalLevel W H s j)) = leftLevel H s (j+1)
  diagonal : ∀ j : ℕ, FinitePair (horizontal (leftLevel H s j).2) (join (0,H) (W,0))
  diagonal_value : ∀ j : ℕ, meet (horizontal (leftLevel H s j).2) (join (0,H) (W,0)) = diagonalLevel W H s j
  output : ∀ j : ℕ, FinitePair (horizontal (leftLevel H s j).2) (vertical W)
  output_value : ∀ j : ℕ, meet (horizontal (leftLevel H s j).2) (vertical W) = (W,H*(1-s^j))

theorem native_telescope (W H s : ℝ) (hW : W≠0) (hH : H≠0) : NativeCertificate W H s := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact Or.inr (by simpa [join,leftLevel] using hW)
  · apply finite_pair; norm_num [det,horizontal,vertical]
  · simp [meet,horizontal,vertical,leftLevel]
  · intro j; apply finite_pair; simpa [det,vertical,parallel,join,leftLevel] using hW
  · intro j
    apply chain_step_unique W H s j hW
    exact meet_on _ _ (by simpa [vertical,parallel,join,leftLevel] using hW)
  · intro j; apply finite_pair; simpa [det,horizontal,join] using neg_ne_zero.mpr hH
  · intro j; apply chain_horizontal_unique W H s j hH
    exact meet_on _ _ (by simpa [horizontal,join] using neg_ne_zero.mpr hH)
  · intro j; apply finite_pair; norm_num [det,horizontal,vertical]
  · intro j; simp [meet,horizontal,vertical,leftLevel]

theorem native_at_one (W H : ℝ) (j : ℕ) :
    leftLevel H 1 j=(0,0) ∧ diagonalLevel W H 1 j=(W,0) := by
  simp [leftLevel,diagonalLevel]

def M (H X : ℝ) : Point := (0,H*(1-1/X))
def E (W H s : ℝ) (p : ℕ) : Point := (W,H*(1-s^p))
def P (W H s : ℝ) : Point := (W,H*(1-s))
def reportLine (W H X s : ℝ) (p : ℕ) := parallel (join (M H X) (E W H s p)) (P W H s)

structure ReportCertificate (W H X s : ℝ) (p : ℕ) (D : Point) : Prop where
  green : Proper (join (M H X) (E W H s p))
  support : Proper (join (W,H) D)
  report : FinitePair (join (W,H) D) (reportLine W H X s p)
  finish : ∀ T : Point, FinitePair (horizontal T.2) (vertical W)

theorem report_determinant (W H X s k : ℝ) (p : ℕ) (D : Point)
    (hD : On (graph k (H-k*W)) D) (hW : W≠0) (hX : X≠0) :
    det (join (W,H) D) (reportLine W H X s p) = -W*(D.1-W)*(k-greenSlope W H X s p) := by
  dsimp [On,graph] at hD
  dsimp [det,join,reportLine,parallel,M,E,P,greenSlope]
  field_simp [hW,hX]
  linear_combination -W*X*hD

theorem report_certificate (W H X s k : ℝ) (p : ℕ) (D : Point)
    (hW : W≠0) (hX : X≠0) (hx : D.1-W≠0)
    (hD : On (graph k (H-k*W)) D) (hg : k-greenSlope W H X s p≠0) :
    ReportCertificate W H X s p D := by
  have hd : det (join (W,H) D) (reportLine W H X s p) ≠ 0 := by
    rw [report_determinant W H X s k p D hD hW hX]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hW) hx) hg
  refine ⟨Or.inr ?_,(finite_pair_proper _ _ hd).1,finite_pair _ _ hd,?_⟩
  · simpa [join,M,E] using hW
  · intro T; apply finite_pair; norm_num [det,horizontal,vertical]

def K (W X : ℝ) (p : ℕ) : Point := (W*(1-X/(p:ℝ)),0)

theorem AK_support (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    ReportCertificate W H X s p (K W X p) := by
  have hp' : (3:ℝ)≤p := by exact_mod_cast hp
  apply report_certificate W H X s (akSlope W H X p) p _ hW.ne' hX.ne'
  · have hk : (K W X p).1-W = -W*X/(p:ℝ) := by dsimp [K]; ring
    rw [hk]; exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hW.ne') hX.ne') (by linarith)
  · exact AK_through_K W H X p (by linarith) hW.ne' hX.ne'
  · exact (gaps_pos W H X s p (by omega) hW hH hX hs).1.ne'

-- The strict lower-half-plane condition selects one of two transverse intersections.
def circleEquation (F Q : Point) (r : ℝ) : Prop := (Q.1-F.1)^2+(Q.2-F.2)^2=r^2
def margin (F : Point) (dx r : ℝ) := r^2-(dx-F.1)^2
def lowerD (F : Point) (dx r : ℝ) : Point := (dx,F.2-Real.sqrt (margin F dx r))
def LowerCircleCertificate (F : Point) (dx r : ℝ) (D : Point) : Prop :=
  0<r ∧ 0<margin F dx r ∧
  (D.1=dx ∧ circleEquation F D r ∧ D.2<F.2) ∧
  ∀ Q : Point, Q.1=dx → circleEquation F Q r → Q.2<F.2 → Q=D

theorem lower_circle (F : Point) (dx r : ℝ) (hr : 0<r) (hm : 0<margin F dx r) :
    LowerCircleCertificate F dx r (lowerD F dx r) := by
  have hs := Real.sqrt_pos.2 hm
  have hsq : Real.sqrt (margin F dx r)^2 = r^2-(dx-F.1)^2 := Real.sq_sqrt hm.le
  refine ⟨hr,hm,⟨rfl,?_,?_⟩,?_⟩
  · dsimp [circleEquation,lowerD]; nlinarith
  · dsimp [lowerD]; linarith
  · intro Q hx hc hy
    apply Prod.ext hx
    dsimp [lowerD]
    dsimp [circleEquation] at hc
    rw [hx] at hc
    nlinarith [sq_nonneg (Q.2-F.2+Real.sqrt (margin F dx r))]

def centeredF (W H X : ℝ) (p : ℕ) : Point :=
  (W-2*W/((p:ℝ)-1),H-H*((p:ℝ)+1)/(X*((p:ℝ)-1)))

theorem centered_circle (W H X s : ℝ) (p : ℕ) (hH : 0<H) (hs : 0<s) :
    LowerCircleCertificate (centeredF W H X p) (centeredF W H X p).1 (H*s^p) (movingD W H X s p) := by
  have hr : 0<H*s^p := mul_pos hH (pow_pos hs p)
  have hm : margin (centeredF W H X p) (centeredF W H X p).1 (H*s^p) = (H*s^p)^2 := by simp [margin]
  have hc := lower_circle (centeredF W H X p) (centeredF W H X p).1 (H*s^p) hr (by rw [hm]; positivity)
  have he : lowerD (centeredF W H X p) (centeredF W H X p).1 (H*s^p) = movingD W H X s p := by
    dsimp [lowerD]; rw [hm,Real.sqrt_sq hr.le]
    ext <;> dsimp [centeredF,movingD] <;> ring
  rwa [he] at hc

theorem AD_support (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    ReportCertificate W H X s p (movingD W H X s p) := by
  have hp' : (3:ℝ)≤p := by exact_mod_cast hp
  have hp1 : (p:ℝ)-1≠0 := by linarith
  apply report_certificate W H X s (adSlope W H X s p) p _ hW.ne' hX.ne'
  · dsimp [movingD]; simp only [sub_sub_cancel_left]
    exact neg_ne_zero.mpr (div_ne_zero (by positivity) hp1)
  · exact AD_through_D W H X s p hp1 hW.ne' hX.ne'
  · exact (gaps_pos W H X s p (by omega) hW hH hX hs).2.ne'

theorem projective_projection (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    FinitePair (join (RectangleProjective.center W H X p) (E W H s p))
      (horizontal (RectangleProjective.ellY W H X p)) := by
  apply finite_pair
  unfold det E
  rw [RectangleProjective.projection_det]
  have hp' : (3:ℝ)≤p := by exact_mod_cast hp
  have h2 : 0<2*(p:ℝ)-1 := by linarith
  positivity

theorem projective_support (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    ReportCertificate W H X s p (RectangleProjective.projectedD W H X s p) := by
  apply report_certificate W H X s (RectangleProjective.supportSlope W H X s p) p _ hW.ne' hX.ne'
  · exact (sub_pos.mpr (RectangleProjective.D_right_of_A W H X s p (by omega) hW hX hs)).ne'
  · exact RectangleProjective.D_on_support W H X s p (by omega) hW hX hs
  · rw [RectangleProjective.support_gap W H X s p (by omega) hX hs]
    have ht := RectangleProjective.positive_terms p (X*s^p) (by omega) (by positivity)
    exact (mul_pos (by positivity) (div_pos ht.2.1 ht.2.2)).ne'

def alpha (p : ℕ) : ℝ := (5*(p:ℝ)+2)/((p:ℝ)-2)
def beta (p : ℕ) : ℝ := ((p:ℝ)-1)*Real.sqrt (((p:ℝ)-2)/(12*(p:ℝ)))
def arcDx (W : ℝ) (p : ℕ) := W-W/beta p
def arcDelta (H X : ℝ) (p : ℕ) := H/X*Real.sqrt ((alpha p)^2-1)
def arcF (W H X : ℝ) (p : ℕ) : Point := (arcDx W p+arcDelta H X p,H-H/(X*beta p))
def arcG (W H X : ℝ) (p : ℕ) : Point := (W,H+H*alpha p/X)
def arcRadius (H X s : ℝ) (p : ℕ) := H/X*(X*s^p+alpha p)
def arcD (W H X s : ℝ) (p : ℕ) := lowerD (arcF W H X p) (arcDx W p) (arcRadius H X s p)
def arcSlope (W H X s : ℝ) (p : ℕ) := H/(W*X)+beta p/W*Real.sqrt (margin (arcF W H X p) (arcDx W p) (arcRadius H X s p))

theorem arc_parameters (p : ℕ) (hp : 3≤p) : 1<alpha p ∧ 0<beta p := by
  have hp' : (3:ℝ)≤p := by exact_mod_cast hp
  have h2 : 0<(p:ℝ)-2 := by linarith
  constructor
  · apply (lt_div_iff₀ h2).2; linarith
  · unfold beta
    apply mul_pos (by linarith)
    apply Real.sqrt_pos.2
    exact div_pos h2 (by positivity)

theorem arc_radius_transfer (W H X s : ℝ) (p : ℕ) (hX : X≠0) :
    ((E W H s p).1-(arcG W H X p).1)^2+
      ((E W H s p).2-(arcG W H X p).2)^2 = (arcRadius H X s p)^2 := by
  dsimp [E,arcG,arcRadius]; field_simp [hX]; ring

theorem arc_margin_identity (W H X s : ℝ) (p : ℕ) (hp : 3≤p) :
    margin (arcF W H X p) (arcDx W p) (arcRadius H X s p) =
      (H/X)^2*((X*s^p)^2+2*alpha p*(X*s^p)+1) := by
  have ha := (arc_parameters p hp).1
  have hsq := Real.sq_sqrt (show 0≤(alpha p)^2-1 by nlinarith)
  dsimp [margin,arcF,arcDelta,arcRadius]
  nlinarith [sq_nonneg (H/X)]

theorem arc_transverse (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    0<margin (arcF W H X p) (arcDx W p) (arcRadius H X s p) := by
  rw [arc_margin_identity W H X s p hp]
  have ha : 0<alpha p := lt_trans (by norm_num) (arc_parameters p hp).1
  positivity

theorem decentered_circle (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    LowerCircleCertificate (arcF W H X p) (arcDx W p) (arcRadius H X s p) (arcD W H X s p) := by
  apply lower_circle
  · unfold arcRadius
    have ha : 0<alpha p := lt_trans (by norm_num) (arc_parameters p hp).1
    positivity
  · exact arc_transverse W H X s p hp hH hX hs

theorem arc_support_incidence (W H X s : ℝ) (p : ℕ) (hp : 3≤p) (hW : W≠0) (hX : X≠0) :
    On (graph (arcSlope W H X s p) (H-arcSlope W H X s p*W)) (arcD W H X s p) := by
  have hb := (arc_parameters p hp).2.ne'
  dsimp only [On,graph,arcD,lowerD,arcF,arcDx,arcSlope]
  field_simp [hW,hX,hb]; ring

theorem arc_support_gap (W H X s : ℝ) (p : ℕ) :
    arcSlope W H X s p-greenSlope W H X s p =
      H/(W*X)*(X*s^p)+beta p/W*Real.sqrt (margin (arcF W H X p) (arcDx W p) (arcRadius H X s p)) := by
  dsimp [arcSlope,greenSlope]; ring

theorem decentered_support (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    ReportCertificate W H X s p (arcD W H X s p) := by
  have hb := (arc_parameters p hp).2
  apply report_certificate W H X s (arcSlope W H X s p) p _ hW.ne' hX.ne'
  · dsimp [arcD,lowerD,arcDx]; simp only [sub_sub_cancel_left]
    exact neg_ne_zero.mpr (div_ne_zero hW.ne' hb.ne')
  · exact arc_support_incidence W H X s p hp hW.ne' hX.ne'
  · rw [arc_support_gap]
    have hm := arc_transverse W H X s p hp hH hX hs
    have hh := Real.sqrt_pos.2 hm
    exact ne_of_gt (by positivity)

theorem centered_radius_transfer (W H s : ℝ) (p : ℕ) :
    circleEquation (W,H) (E W H s p) (H*s^p) := by
  dsimp [circleEquation,E]; ring

-- Complete native certificates: telescope + preparation + actual support report.
theorem OriginalAK_global_geometric_existence (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    NativeCertificate W H s ∧ ReportCertificate W H X s p (K W X p) :=
  ⟨native_telescope W H s hW.ne' hH.ne',AK_support W H X s p hp hW hH hX hs⟩

theorem OriginalAD_global_geometric_existence (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    NativeCertificate W H s ∧ circleEquation (W,H) (E W H s p) (H*s^p) ∧
    LowerCircleCertificate (centeredF W H X p) (centeredF W H X p).1 (H*s^p) (movingD W H X s p) ∧
    ReportCertificate W H X s p (movingD W H X s p) :=
  ⟨native_telescope W H s hW.ne' hH.ne',centered_radius_transfer W H s p,centered_circle W H X s p hH hs,AD_support W H X s p hp hW hH hX hs⟩

theorem OriginalProjectiveAD_global_geometric_existence (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    NativeCertificate W H s ∧
    FinitePair (join (RectangleProjective.center W H X p) (E W H s p)) (horizontal (RectangleProjective.ellY W H X p)) ∧
    (meet (join (RectangleProjective.center W H X p) (E W H s p)) (horizontal (RectangleProjective.ellY W H X p)) = RectangleProjective.projectedD W H X s p) ∧
    ReportCertificate W H X s p (RectangleProjective.projectedD W H X s p) := by
  have hpr := projective_projection W H X s p hp hH hX hs
  refine ⟨native_telescope W H s hW.ne' hH.ne',hpr,?_,projective_support W H X s p hp hW hH hX hs⟩
  exact intersection_unique _ _ hpr.1 _ _ (meet_on _ _ hpr.1)
    ⟨RectangleProjective.D_on_ZE W H X s p (by omega) hX hs,RectangleProjective.D_on_ell W H X s p⟩

theorem OriginalDecenteredAD_global_geometric_existence (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    NativeCertificate W H s ∧ circleEquation (arcG W H X p) (E W H s p) (arcRadius H X s p) ∧
    LowerCircleCertificate (arcF W H X p) (arcDx W p) (arcRadius H X s p) (arcD W H X s p) ∧
    ReportCertificate W H X s p (arcD W H X s p) :=
  ⟨native_telescope W H s hW.ne' hH.ne',arc_radius_transfer W H X s p hX.ne',decentered_circle W H X s p hp hH hX hs,decentered_support W H X s p hp hW hH hX hs⟩

-- Homogeneous cross products are authoritative: finite affine certificates
-- imply a nonzero homogeneous meet weight, not just solvable scalar formulas.
structure Homogeneous where
  x : ℝ
  y : ℝ
  w : ℝ
  deriving DecidableEq

def hcross (a b : Homogeneous) : Homogeneous :=
  ⟨a.y*b.w-a.w*b.y,a.w*b.x-a.x*b.w,a.x*b.y-a.y*b.x⟩
def hline (l : Line) : Homogeneous := ⟨l.a,l.b,-l.c⟩
def hpoint (Q : Point) : Homogeneous := ⟨Q.1,Q.2,1⟩
def direction (l : Line) : Homogeneous := ⟨l.b,-l.a,0⟩

theorem homogeneous_meet_finite (l m : Line) (h : FinitePair l m) :
    (hcross (hline l) (hline m)).w ≠ 0 := by
  simpa [hcross,hline,det,mul_comm] using h.1

theorem parallel_direction_nonzero (l : Line) (h : Proper l) :
    (direction l).x≠0 ∨ (direction l).y≠0 := by
  rcases h with ha | hb
  · exact Or.inr (neg_ne_zero.mpr ha)
  · exact Or.inl hb

theorem parallel_projective_continuation (l : Line) (Q : Point) (h : Proper l) :
    (hcross (direction l) (hpoint Q)).x≠0 ∨ (hcross (direction l) (hpoint Q)).y≠0 := by
  rcases h with ha | hb
  · left; simpa [hcross,direction,hpoint] using neg_ne_zero.mpr ha
  · right; simpa [hcross,direction,hpoint] using neg_ne_zero.mpr hb

theorem parallel_homogeneous_identity (l : Line) (Q : Point) :
    hcross (direction l) (hpoint Q) =
      ⟨-(parallel l Q).a,-(parallel l Q).b,(parallel l Q).c⟩ := by
  cases l; cases Q; simp [hcross,direction,hpoint,parallel,add_comm,mul_comm]

theorem red_direction (W H s : ℝ) :
    direction (join (leftLevel H s 1) (W,0)) = ⟨W,-H*(1-s),0⟩ := by
  simp [direction,join,leftLevel]

theorem red_horizontal_iff (W H s : ℝ) (hH : H≠0) :
    (join (leftLevel H s 1) (W,0)).a=0 ↔ s=1 := by
  simp only [join,leftLevel,pow_one,sub_zero,mul_eq_zero,hH,false_or]
  constructor <;> intro h <;> linarith

theorem projective_exception_equation (W H X s : ℝ) (p : ℕ) (hp : 3≤p) (hX : X≠0) :
    det (join (RectangleProjective.center W H X p) (E W H s p)) (horizontal (RectangleProjective.ellY W H X p)) =
      H/((2*(p:ℝ)-1)*X)*((2*(p:ℝ)-1)*(X*s^p)+(p:ℝ)+1) := by
  have hp' : (3:ℝ)≤p := by exact_mod_cast hp
  unfold det E
  rw [RectangleProjective.projection_det]
  field_simp [hX,show 2*(p:ℝ)-1≠0 by linarith]
  ring_nf
  field_simp [show (-1:ℝ)+(p:ℝ)*2≠0 by linarith]
  ring

theorem proper_join_distinct (A B : Point) (h : Proper (join A B)) : A≠B := by
  intro he; subst B
  simpa [Proper,join] using h

theorem projective_Z_ne_E (W H X s : ℝ) (p : ℕ) (hp : 3≤p) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    RectangleProjective.center W H X p ≠ E W H s p :=
  proper_join_distinct _ _ (finite_pair_proper _ _ (projective_projection W H X s p hp hH hX hs).1).1

theorem residual_normalization (X s c : ℝ) (p : ℕ) (hc : c≠0) :
    (c^p*X)*(s/c)^p=X*s^p := by
  rw [div_pow]; field_simp

theorem residual_exception_invariant (X s c : ℝ) (p : ℕ) (hc : c≠0) (f : ℝ→ℝ) :
    f ((c^p*X)*(s/c)^p)=0 ↔ f (X*s^p)=0 := by rw [residual_normalization X s c p hc]

theorem state_marker_moves (s c : ℝ) (hc : c≠0) : s/c=1 ↔ s=c := by
  rw [div_eq_iff hc]; simp

theorem target_marker_moves (X c d : ℝ) (p : ℕ) (hc : c≠0) :
    c^p*X=d ↔ X=d/c^p := by rw [eq_div_iff (pow_ne_zero p hc)]; ring_nf

theorem normalization_positive (X s c : ℝ) (p : ℕ) (hX : 0<X) (hs : 0<s) (hc : 0<c) :
    0<c^p*X ∧ 0<s/c := ⟨mul_pos (pow_pos hc p) hX,div_pos hs hc⟩

-- The fast stage and the native correction certificates compose without
-- duplicating any correction-support proof.
def FastCertificate (W H s : ℝ) (p : ℕ) : Prop :=
  (∀ a b : ℝ, FinitePair (RectangleFastPower.multiplier W H a b) (vertical W)) ∧
  (∀ a : ℝ, FinitePair (parallel (RectangleFastPower.transfer W H) (RectangleFastPower.R W H a)) (horizontal H)) ∧
  RectangleFastPower.geometricPower W H s p = E W H s p

theorem fast_telescope (W H s : ℝ) (p : ℕ) (hH : H≠0) : FastCertificate W H s p := by
  refine ⟨?_,?_,RectangleFastPower.geometricPower_eq W H s p hH⟩
  · intro a b; exact finite_pair _ _ (RectangleFastPower.multiplier_transverse W H a b hH)
  · intro a; apply finite_pair
    simpa [det,parallel,RectangleFastPower.transfer,RectangleFastPower.unit,join,horizontal] using hH

theorem FastAK_global_geometric_existence (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    FastCertificate W H s p ∧ ReportCertificate W H X s p (K W X p) :=
  ⟨fast_telescope W H s p hH.ne',(OriginalAK_global_geometric_existence W H X s p hp hW hH hX hs).2⟩

theorem FastAD_global_geometric_existence (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    FastCertificate W H s p ∧ circleEquation (W,H) (E W H s p) (H*s^p) ∧
    LowerCircleCertificate (centeredF W H X p) (centeredF W H X p).1 (H*s^p) (movingD W H X s p) ∧
    ReportCertificate W H X s p (movingD W H X s p) :=
  ⟨fast_telescope W H s p hH.ne',(OriginalAD_global_geometric_existence W H X s p hp hW hH hX hs).2⟩

theorem FastProjectiveAD_global_geometric_existence (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    FastCertificate W H s p ∧
    FinitePair (join (RectangleProjective.center W H X p) (E W H s p)) (horizontal (RectangleProjective.ellY W H X p)) ∧
    (meet (join (RectangleProjective.center W H X p) (E W H s p)) (horizontal (RectangleProjective.ellY W H X p)) = RectangleProjective.projectedD W H X s p) ∧
    ReportCertificate W H X s p (RectangleProjective.projectedD W H X s p) :=
  ⟨fast_telescope W H s p hH.ne',(OriginalProjectiveAD_global_geometric_existence W H X s p hp hW hH hX hs).2⟩

theorem FastDecenteredAD_global_geometric_existence (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    FastCertificate W H s p ∧ circleEquation (arcG W H X p) (E W H s p) (arcRadius H X s p) ∧
    LowerCircleCertificate (arcF W H X p) (arcDx W p) (arcRadius H X s p) (arcD W H X s p) ∧
    ReportCertificate W H X s p (arcD W H X s p) :=
  ⟨fast_telescope W H s p hH.ne',(OriginalDecenteredAD_global_geometric_existence W H X s p hp hW hH hX hs).2⟩

theorem homogeneous_meet_readout (l m : Line) :
    let q := hcross (hline l) (hline m)
    q.x/q.w=(meet l m).1 ∧ q.y/q.w=(meet l m).2 := by
  dsimp [hcross,hline,meet]
  constructor <;> congr 1 <;> ring

theorem parallel_direction_display (l : Line) (hl : Proper l) :
    RectangleFixedCircleStereo.sx (direction l).x (direction l).y 0=0 ∧
    RectangleFixedCircleStereo.sy (direction l).x (direction l).y 0=0 ∧
    RectangleFixedCircleStereo.sz (direction l).x (direction l).y 0=1 := by
  apply RectangleFixedCircleStereo.all_directions_at_north
  rcases parallel_direction_nonzero l hl with hx | hy
  · exact ne_of_gt (by nlinarith [sq_pos_of_ne_zero hx,sq_nonneg (direction l).y])
  · exact ne_of_gt (by nlinarith [sq_pos_of_ne_zero hy,sq_nonneg (direction l).x])

theorem distinct_infinite_directions :
    (hcross (direction (horizontal 0)) (direction (vertical 0))).w = -1 := by
  norm_num [hcross,direction,horizontal,vertical]

theorem M_vertex_marker (H X : ℝ) (hH : H≠0) (hX : X≠0) :
    M H X=(0,0) ↔ X=1 := by
  constructor
  · intro h
    have hy := congrArg Prod.snd h
    dsimp [M] at hy
    have he : 1-1/X=0 := (mul_eq_zero.mp hy).resolve_left hH
    field_simp [hX] at he
    linarith
  · intro h; subst X; simp [M]

theorem K_vertex_marker (W X : ℝ) (p : ℕ) (hW : W≠0) (hp : (p:ℝ)≠0) :
    K W X p=(0,0) ↔ X=(p:ℝ) := by
  constructor
  · intro h
    have hx := congrArg Prod.fst h
    dsimp [K] at hx
    have he : 1-X/(p:ℝ)=0 := (mul_eq_zero.mp hx).resolve_left hW
    field_simp [hp] at he
    linarith
  · intro h; subst X; simp [K,hp]

theorem green_horizontal_iff (W H X s : ℝ) (p : ℕ) (hH : H≠0) (hX : X≠0) :
    (join (M H X) (E W H s p)).a=0 ↔ X*s^p=1 := by
  dsimp [join,M,E]
  constructor <;> intro h
  · have he : H*(s^p-1/X)=0 := by nlinarith
    have he' := (mul_eq_zero.mp he).resolve_left hH
    field_simp [hX] at he'
    nlinarith
  · field_simp [hX]
    linear_combination H*h

end LeanMath.Papers.RectangleNativeNondegeneracy
