import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Cartesian incidence proofs for the proportional rectangle. Lines are represented
by nonzero normal vectors. No root oracle is used in any point construction. -/
noncomputable section
namespace LeanMath.Papers.RectangleGeometry
abbrev Point := ℝ × ℝ
structure Line where
  a : ℝ
  b : ℝ
  c : ℝ

def On (l : Line) (P : Point) : Prop := l.a * P.1 + l.b * P.2 = l.c
def Proper (l : Line) : Prop := l.a ≠ 0 ∨ l.b ≠ 0
def join (P Q : Point) : Line :=
  ⟨P.2-Q.2, Q.1-P.1, (P.2-Q.2)*P.1+(Q.1-P.1)*P.2⟩
def parallel (l : Line) (P : Point) : Line := ⟨l.a,l.b,l.a*P.1+l.b*P.2⟩
def horizontal (y : ℝ) : Line := ⟨0,1,y⟩
def vertical (x : ℝ) : Line := ⟨1,0,x⟩
def graph (k b : ℝ) : Line := ⟨-k,1,b⟩
def Parallel (l m : Line) : Prop := l.a*m.b=m.a*l.b

theorem join_left (P Q : Point) : On (join P Q) P := by rfl
theorem join_right (P Q : Point) : On (join P Q) Q := by dsimp [On,join]; ring
theorem parallel_through (l : Line) (P : Point) : On (parallel l P) P := by rfl
theorem parallel_direction (l : Line) (P : Point) : Parallel (parallel l P) l := by rfl
theorem graph_proper (k b : ℝ) : Proper (graph k b) := by simp [Proper,graph]
theorem graph_on (k b : ℝ) (P : Point) : On (graph k b) P ↔ P.2=b+k*P.1 := by
  dsimp [On,graph]; constructor <;> intro h <;> linarith

def meet (l m : Line) : Point :=
  ((l.c*m.b-m.c*l.b)/(l.a*m.b-m.a*l.b),
   (l.a*m.c-m.a*l.c)/(l.a*m.b-m.a*l.b))

theorem meet_on (l m : Line) (h : l.a*m.b-m.a*l.b ≠ 0) :
    On l (meet l m) ∧ On m (meet l m) := by
  dsimp [On,meet]
  constructor <;> rw [← mul_div_assoc, ← mul_div_assoc, ← add_div] <;>
    apply (div_eq_iff h).mpr <;> ring

theorem intersection_unique (l m : Line) (h : l.a*m.b-m.a*l.b ≠ 0)
    (P Q : Point) (hP : On l P ∧ On m P) (hQ : On l Q ∧ On m Q) : P=Q := by
  rcases P with ⟨x,y⟩; rcases Q with ⟨u,v⟩
  dsimp [On] at hP hQ
  have hx : (l.a*m.b-m.a*l.b)*(x-u)=0 := by
    linear_combination m.b*hP.1-l.b*hP.2-m.b*hQ.1+l.b*hQ.2
  have hy : (l.a*m.b-m.a*l.b)*(y-v)=0 := by
    linear_combination l.a*hP.2-m.a*hP.1-l.a*hQ.2+m.a*hQ.1
  have := (mul_eq_zero.mp hx).resolve_left h
  have := (mul_eq_zero.mp hy).resolve_left h
  ext <;> dsimp <;> linarith

def leftLevel (H s : ℝ) (j : ℕ) : Point := (0,H*(1-s^j))
def diagonalLevel (W H s : ℝ) (j : ℕ) : Point := (W*s^j,H*(1-s^j))

theorem chain_horizontal (W H s : ℝ) (j : ℕ) :
    On (horizontal (leftLevel H s j).2) (diagonalLevel W H s j) := by
  simp [On,horizontal,leftLevel,diagonalLevel]
theorem chain_left (H s : ℝ) (j : ℕ) : On (vertical 0) (leftLevel H s j) := by
  simp [On,vertical,leftLevel]
theorem chain_diagonal (W H s : ℝ) (j : ℕ) :
    On (join (0,H) (W,0)) (diagonalLevel W H s j) := by
  dsimp [On,join,diagonalLevel]; ring

theorem chain_step (W H s : ℝ) (j : ℕ) :
    On (parallel (join (leftLevel H s 1) (W,0)) (diagonalLevel W H s j))
      (leftLevel H s (j+1)) := by
  dsimp [On,parallel,join,leftLevel,diagonalLevel]
  rw [pow_succ]; ring

theorem chain_step_unique (W H s : ℝ) (j : ℕ) (hW : W ≠ 0) (Q : Point)
    (hQ : On (vertical 0) Q ∧
      On (parallel (join (leftLevel H s 1) (W,0)) (diagonalLevel W H s j)) Q) :
    Q=leftLevel H s (j+1) := by
  apply intersection_unique (vertical 0)
    (parallel (join (leftLevel H s 1) (W,0)) (diagonalLevel W H s j)) _ Q _ hQ
    ⟨chain_left H s (j+1),chain_step W H s j⟩
  simpa [vertical,parallel,join,leftLevel] using hW

theorem chain_horizontal_unique (W H s : ℝ) (j : ℕ) (hH : H ≠ 0) (Q : Point)
    (hQ : On (horizontal (leftLevel H s j).2) Q ∧ On (join (0,H) (W,0)) Q) :
    Q=diagonalLevel W H s j := by
  apply intersection_unique (horizontal (leftLevel H s j).2) (join (0,H) (W,0)) _ Q _ hQ
    ⟨chain_horizontal W H s j,chain_diagonal W H s j⟩
  simpa [horizontal,join] using neg_ne_zero.mpr hH

/-- Shared geometric report on a line through A with slope k. -/
def reportPoint (W H s k m : ℝ) : Point :=
  (W-H*s/(k-m), H-k*(H*s/(k-m)))
def reportState (s k m : ℝ) := k*s/(k-m)

theorem report_incidence (W H s k m : ℝ) (h : k-m ≠ 0) :
    On (graph k (H-k*W)) (reportPoint W H s k m) ∧
    On (graph m (H*(1-s)-m*W)) (reportPoint W H s k m) := by
  simp only [graph_on]; dsimp [reportPoint]
  constructor
  · ring
  · field_simp [h]; ring

theorem report_unique (W H s k m : ℝ) (h : k-m ≠ 0) (T : Point)
    (hT : On (graph k (H-k*W)) T ∧ On (graph m (H*(1-s)-m*W)) T) :
    T=reportPoint W H s k m := by
  apply intersection_unique _ _ _ _ _ hT (report_incidence W H s k m h)
  dsimp [graph]; intro hz; apply h; linarith

theorem report_readout (W H s k m : ℝ) (hH : H ≠ 0) :
    1-(reportPoint W H s k m).2/H = reportState s k m := by
  dsimp [reportPoint,reportState]; field_simp; ring

theorem horizontal_report (W H s k m : ℝ) :
    On (horizontal (reportPoint W H s k m).2)
      (W,(reportPoint W H s k m).2) ∧
    On (vertical W) (W,(reportPoint W H s k m).2) := by
  simp [On,horizontal,vertical]
end LeanMath.Papers.RectangleGeometry
