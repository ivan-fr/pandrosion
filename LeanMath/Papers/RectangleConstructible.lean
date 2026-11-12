import LeanMath.Papers.RectangleBilateral
import Mathlib.Algebra.Field.Subfield.Basic

/-! Closure certificate: all line-based points lie in every subfield containing
input lengths. Only the explicitly isolated semicircle uses a square root. -/
noncomputable section
namespace LeanMath.Papers.RectangleConstructible
open LeanMath.Papers.RectangleGeometry LeanMath.Papers.RectangleReports

def PointOver (K : Subfield ℝ) (P : Point) := P.1∈K ∧ P.2∈K
def LineOver (K : Subfield ℝ) (l : Line) := l.a∈K ∧ l.b∈K ∧ l.c∈K

macro "field_membership" : tactic => `(tactic|
  aesop (add safe apply [Subfield.add_mem, Subfield.sub_mem, Subfield.mul_mem,
    Subfield.div_mem, Subfield.neg_mem, Subfield.pow_mem, natCast_mem,
    Subfield.zero_mem, Subfield.one_mem]))

theorem join_over (K : Subfield ℝ) (P Q : Point) (hP : PointOver K P) (hQ : PointOver K Q) :
    LineOver K (join P Q) := by
  rcases hP with ⟨hp,hp'⟩; rcases hQ with ⟨hq,hq'⟩
  dsimp [LineOver,join]; field_membership

theorem parallel_over (K : Subfield ℝ) (l : Line) (P : Point)
    (hl : LineOver K l) (hP : PointOver K P) : LineOver K (parallel l P) := by
  rcases hl with ⟨ha,hb,hc⟩; rcases hP with ⟨hx,hy⟩
  dsimp [LineOver,parallel]; field_membership

theorem meet_over (K : Subfield ℝ) (l m : Line) (hl : LineOver K l) (hm : LineOver K m) :
    PointOver K (meet l m) := by
  rcases hl with ⟨ha,hb,hc⟩; rcases hm with ⟨hd,he,hf⟩
  dsimp [PointOver,meet]; field_membership

theorem levels_over (K : Subfield ℝ) (W H s : ℝ) (j : ℕ)
    (hW : W∈K) (hH : H∈K) (hs : s∈K) :
    PointOver K (leftLevel H s j) ∧ PointOver K (diagonalLevel W H s j) := by
  dsimp [PointOver,leftLevel,diagonalLevel]; field_membership

theorem movingD_over (K : Subfield ℝ) (W H X s : ℝ) (p : ℕ)
    (hW : W∈K) (hH : H∈K) (hX : X∈K) (hs : s∈K) :
    PointOver K (movingD W H X s p) := by
  dsimp [PointOver,movingD]; field_membership

theorem steps_over (K : Subfield ℝ) (X s : ℝ) (p : ℕ) (hX : X∈K) (hs : s∈K) :
    ak p X s∈K ∧ ad p X s∈K := by
  dsimp [ak,ad]; field_membership

/-- Exact scope of the additional compass primitive. -/
theorem altitude_over (K : Subfield ℝ)
    (hsqrt : ∀ x : ℝ, x∈K → 0≤x → Real.sqrt x∈K)
    (l h : ℝ) (hl : l∈K) (hh : h∈K) (hl0 : 0≤l) (hh0 : 0≤h) :
    PointOver K (RectangleBilateral.altitude l h) := by
  exact ⟨K.zero_mem,hsqrt _ (K.mul_mem hl hh) (mul_nonneg hl0 hh0)⟩
end LeanMath.Papers.RectangleConstructible
