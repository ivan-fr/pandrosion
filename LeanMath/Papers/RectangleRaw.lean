import LeanMath.Papers.RectangleReports
import Mathlib.Algebra.Ring.GeomSum

noncomputable section
namespace LeanMath.Papers.RectangleRaw
open LeanMath.Papers.RectangleGeometry LeanMath.Papers.RectangleReports

def sumPowers (p : ℕ) (s : ℝ) := ∑ j ∈ Finset.range p, s^j
def raw (p : ℕ) (X s : ℝ) := 1-(X-1)/(X*sumPowers p s)
def rawPoint (W H X s : ℝ) (p : ℕ) : Point :=
  (W-W*(1-s)/(1-s^p),H*(1-1/X)*(1-s)/(1-s^p))
def rawSlope (W H X : ℝ) := -H*(1-1/X)/W

theorem sum_identity (p : ℕ) (s : ℝ) : sumPowers p s*(1-s)=1-s^p := by
  induction p with
  | zero => simp [sumPowers]
  | succ p ih =>
    simp only [sumPowers,Finset.sum_range_succ] at *
    rw [pow_succ]; nlinarith [ih]

theorem raw_incidence (W H X s : ℝ) (p : ℕ) (hW : W ≠ 0)
    (hX : X ≠ 0) (hs : 1-s^p ≠ 0) :
    On (graph (rawSlope W H X) (H*(1-1/X))) (rawPoint W H X s p) ∧
    On (graph (greenSlope W H X s p) (H*(1-s)-greenSlope W H X s p*W))
      (rawPoint W H X s p) := by
  simp only [graph_on]
  dsimp [rawPoint,rawSlope,greenSlope]
  constructor <;> field_simp [hW,hX,hs] <;> ring

theorem raw_gap (W H X s : ℝ) (p : ℕ) (hX : X ≠ 0) :
    rawSlope W H X-greenSlope W H X s p=H/W*(s^p-1) := by
  dsimp [rawSlope,greenSlope]; field_simp; ring

theorem raw_unique (W H X s : ℝ) (p : ℕ)
    (hW : W ≠ 0) (hH : H ≠ 0) (hX : X ≠ 0) (hs : 1-s^p ≠ 0) (T : Point)
    (hT : On (graph (rawSlope W H X) (H*(1-1/X))) T ∧
      On (graph (greenSlope W H X s p) (H*(1-s)-greenSlope W H X s p*W)) T) :
    T=rawPoint W H X s p := by
  apply intersection_unique _ _ _ _ _ hT (raw_incidence W H X s p hW hX hs)
  change -rawSlope W H X*1- -greenSlope W H X s p*1≠0
  have hg := raw_gap W H X s p hX
  have hp : s^p-1≠0 := by intro he; apply hs; linarith
  have hn := mul_ne_zero (div_ne_zero hH hW) hp
  intro he; apply hn; linarith

theorem raw_readout (W H X s : ℝ) (p : ℕ) (hH : H ≠ 0)
    (hX : X ≠ 0) (hs : 1-s^p ≠ 0) : 1-(rawPoint W H X s p).2/H=raw p X s := by
  have hi := sum_identity p s
  have hz : sumPowers p s≠0 := by intro hz; rw [hz,zero_mul] at hi; exact hs hi.symm
  have hs1 : 1-s≠0 := by intro h; rw [h,mul_zero] at hi; exact hs hi.symm
  have hr : (1-s)/(1-s^p)=1/sumPowers p s := by
    apply (div_eq_div_iff hs hz).mpr; nlinarith [hi]
  dsimp [rawPoint,raw]
  rw [show H*(1-1/X)*(1-s)/(1-s^p)/H=(1-1/X)*((1-s)/(1-s^p)) by field_simp]
  rw [hr]; field_simp

theorem raw_neutral (p : ℕ) (X : ℝ) (hp : (p:ℝ)≠0) (hX : X≠0) :
    raw p X 1=((p:ℝ)-1+X⁻¹)/(p:ℝ) := by
  simp [raw,sumPowers]
  field_simp; ring

/-- At s=1 the raw geometric intersection is not unique. -/
theorem raw_neutral_degenerate (W H X : ℝ) (p : ℕ) (hW : W ≠ 0) (hX : X≠0) :
    graph (rawSlope W H X) (H*(1-1/X)) =
      graph (greenSlope W H X 1 p) (H*(1-1)-greenSlope W H X 1 p*W) := by
  have he : rawSlope W H X=greenSlope W H X 1 p := by
    have := raw_gap W H X 1 p hX; simp only [one_pow,sub_self,mul_zero] at this; linarith
  rw [← he]; congr 1
  unfold rawSlope; field_simp; ring
end LeanMath.Papers.RectangleRaw
