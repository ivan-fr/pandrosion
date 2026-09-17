import LeanMath.Papers.RectangleGeometry

noncomputable section
namespace LeanMath.Papers.RectangleReports
open LeanMath.Papers.RectangleGeometry

def greenSlope (W H X s : ℝ) (p : ℕ) := H/(W*X)*(1-X*s^p)
def akSlope (W H X : ℝ) (p : ℕ) := H*(p:ℝ)/(W*X)
def adSlope (W H X s : ℝ) (p : ℕ) := H/(2*W*X)*((p:ℝ)+1+((p:ℝ)-1)*X*s^p)
def ak (p : ℕ) (X s : ℝ) := (p:ℝ)*s/((p:ℝ)-1+X*s^p)
def ad (p : ℕ) (X s : ℝ) :=
  s*((p:ℝ)+1+((p:ℝ)-1)*X*s^p)/((p:ℝ)-1+((p:ℝ)+1)*X*s^p)
def movingD (W H X s : ℝ) (p : ℕ) : Point :=
  (W-2*W/((p:ℝ)-1),H*(1-s^p)-H*((p:ℝ)+1)/(X*((p:ℝ)-1)))

theorem green_through_M (W H X s : ℝ) (p : ℕ) (hW : W ≠ 0) (hX : X ≠ 0) :
    On (graph (greenSlope W H X s p) (H*(1-1/X))) (0,H*(1-1/X)) := by
  simp [On,graph]

theorem green_through_E (W H X s : ℝ) (p : ℕ) (hW : W ≠ 0) (hX : X ≠ 0) :
    On (graph (greenSlope W H X s p) (H*(1-1/X))) (W,H*(1-s^p)) := by
  dsimp [On,graph,greenSlope]; field_simp; ring

theorem AK_through_K (W H X : ℝ) (p : ℕ) (hp : (p:ℝ) ≠ 0)
    (hW : W ≠ 0) (hX : X ≠ 0) :
    On (graph (akSlope W H X p) (H-akSlope W H X p*W))
      (W*(1-X/(p:ℝ)),0) := by
  dsimp [On,graph,akSlope]; field_simp; ring

theorem AD_through_D (W H X s : ℝ) (p : ℕ) (hp : (p:ℝ)-1 ≠ 0)
    (hW : W ≠ 0) (hX : X ≠ 0) :
    On (graph (adSlope W H X s p) (H-adSlope W H X s p*W))
      (movingD W H X s p) := by
  dsimp [On,graph,adSlope,movingD]; field_simp; ring

theorem through_A (W H k : ℝ) : On (graph k (H-k*W)) (W,H) := by
  dsimp [On,graph]; ring

theorem D_is_fixed_translation (W H X s : ℝ) (p : ℕ) :
    movingD W H X s p =
      ((W,H*(1-s^p)).1-2*W/((p:ℝ)-1),
       (W,H*(1-s^p)).2-H*((p:ℝ)+1)/(X*((p:ℝ)-1))) := rfl

theorem D_cubic_two (s : ℝ) : movingD 2 4 2 s 3=(0,-4*s^3) := by
  ext <;> norm_num [movingD] <;> ring

theorem D_compass_transfer (s : ℝ) (hs : 0<s) :
    (movingD 2 4 2 s 3).1=0 ∧ (movingD 2 4 2 s 3).2<0 ∧
    (movingD 2 4 2 s 3).2^2=(4-(4*(1-s^3)))^2 := by
  rw [D_cubic_two]; dsimp
  refine ⟨rfl,?_,?_⟩
  · have : 0<s^3 := pow_pos hs _; linarith
  · ring

theorem ak_gap (W H X s : ℝ) (p : ℕ) :
    akSlope W H X p-greenSlope W H X s p=
      H/(W*X)*((p:ℝ)-1+X*s^p) := by
  unfold akSlope greenSlope; ring

theorem ad_gap (W H X s : ℝ) (p : ℕ) :
    adSlope W H X s p-greenSlope W H X s p=
      H/(2*W*X)*((p:ℝ)-1+((p:ℝ)+1)*X*s^p) := by
  unfold adSlope greenSlope; ring

theorem denominators_pos (p : ℕ) (X s : ℝ) (hp : 2≤p) (hX : 0<X) (hs : 0<s) :
    0<(p:ℝ)-1+X*s^p ∧ 0<(p:ℝ)-1+((p:ℝ)+1)*X*s^p := by
  have hp' : (2:ℝ)≤p := by exact_mod_cast hp
  have : 0<(p:ℝ)-1 := by linarith
  constructor <;> positivity

theorem gaps_pos (W H X s : ℝ) (p : ℕ) (hp : 2≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    0<akSlope W H X p-greenSlope W H X s p ∧
    0<adSlope W H X s p-greenSlope W H X s p := by
  rw [ak_gap,ad_gap]
  have hd := denominators_pos p X s hp hX hs
  exact ⟨mul_pos (by positivity) hd.1,mul_pos (by positivity) hd.2⟩

theorem ak_report (W H X s : ℝ) (p : ℕ)
    (hW : W ≠ 0) (hH : H ≠ 0) (hX : X ≠ 0) :
    reportState s (akSlope W H X p) (greenSlope W H X s p)=ak p X s := by
  unfold reportState; rw [ak_gap]; unfold akSlope ak
  field_simp <;> ring

theorem ad_report (W H X s : ℝ) (p : ℕ)
    (hW : W ≠ 0) (hH : H ≠ 0) (hX : X ≠ 0) :
    reportState s (adSlope W H X s p) (greenSlope W H X s p)=ad p X s := by
  unfold reportState; rw [ad_gap]; unfold adSlope ad
  field_simp <;> ring

/-- The unique intersection followed by horizontal projection computes AK. -/
theorem ak_geometric_readout (W H X s : ℝ) (p : ℕ) (hp : 2≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) (T : Point)
    (hT : On (graph (akSlope W H X p) (H-akSlope W H X p*W)) T ∧
      On (graph (greenSlope W H X s p) (H*(1-s)-greenSlope W H X s p*W)) T) :
    1-T.2/H=ak p X s := by
  rw [report_unique W H s _ _ (gaps_pos W H X s p hp hW hH hX hs).1.ne' T hT,
    report_readout W H s _ _ hH.ne',ak_report W H X s p hW.ne' hH.ne' hX.ne']

/-- The unique intersection followed by horizontal projection computes AD. -/
theorem ad_geometric_readout (W H X s : ℝ) (p : ℕ) (hp : 2≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) (T : Point)
    (hT : On (graph (adSlope W H X s p) (H-adSlope W H X s p*W)) T ∧
      On (graph (greenSlope W H X s p) (H*(1-s)-greenSlope W H X s p*W)) T) :
    1-T.2/H=ad p X s := by
  rw [report_unique W H s _ _ (gaps_pos W H X s p hp hW hH hX hs).2.ne' T hT,
    report_readout W H s _ _ hH.ne',ad_report W H X s p hW.ne' hH.ne' hX.ne']
/-- Both constructions have a unique geometric interception for every positive input. -/
theorem reports_exist_unique (W H X s : ℝ) (p : ℕ) (hp : 2≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) :
    (∃! T : Point, On (graph (akSlope W H X p) (H-akSlope W H X p*W)) T ∧
      On (graph (greenSlope W H X s p) (H*(1-s)-greenSlope W H X s p*W)) T) ∧
    (∃! T : Point, On (graph (adSlope W H X s p) (H-adSlope W H X s p*W)) T ∧
      On (graph (greenSlope W H X s p) (H*(1-s)-greenSlope W H X s p*W)) T) := by
  have hg := gaps_pos W H X s p hp hW hH hX hs
  constructor
  · exact ⟨reportPoint W H s _ _,report_incidence W H s _ _ hg.1.ne',
      fun T ht => report_unique W H s _ _ hg.1.ne' T ht⟩
  · exact ⟨reportPoint W H s _ _,report_incidence W H s _ _ hg.2.ne',
      fun T ht => report_unique W H s _ _ hg.2.ne' T ht⟩

end LeanMath.Papers.RectangleReports
