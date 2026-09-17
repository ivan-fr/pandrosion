import LeanMath.Papers.RectanglePencilsPade

/-! Stereographic encoding of a homogeneous line coordinate. This is a display
certificate, not an identification of spherical circles with projective lines. -/
noncomputable section
namespace LeanMath.Papers.RectangleStereographic

def den (u w : ℝ) := u^2+w^2
def circleX (u w : ℝ) := 2*u*w/den u w
def circleY (u w : ℝ) := (u^2-w^2)/den u w

theorem denominator_pos (u w : ℝ) (h : u ≠ 0 ∨ w ≠ 0) : 0 < den u w := by
  dsimp [den]
  rcases h with hu | hw
  · have := sq_pos_of_ne_zero hu; nlinarith [sq_nonneg w]
  · have := sq_pos_of_ne_zero hw; nlinarith [sq_nonneg u]

theorem on_circle (u w : ℝ) (h : u ≠ 0 ∨ w ≠ 0) :
    circleX u w ^2 + circleY u w ^2 = 1 := by
  have hd := ne_of_gt (denominator_pos u w h)
  dsimp [circleX,circleY]
  field_simp
  dsimp [den] at *
  nlinarith [sq_nonneg u, sq_nonneg w]

theorem north (u : ℝ) (hu : u ≠ 0) :
    circleX u 0 = 0 ∧ circleY u 0 = 1 := by
  simp [circleX,circleY,den,hu]

theorem affine (u : ℝ) :
    circleX u 1 = 2*u/(1+u^2) ∧ circleY u 1 = (u^2-1)/(1+u^2) := by
  simp [circleX,circleY,den,add_comm]

theorem scale_invariant (u w k : ℝ) (hk : k ≠ 0) :
    circleX (k*u) (k*w) = circleX u w ∧
    circleY (k*u) (k*w) = circleY u w := by
  dsimp [circleX,circleY,den]
  constructor <;> field_simp <;> ring

def sphereDen (x y w : ℝ) := x^2+y^2+w^2

theorem on_sphere (x y w : ℝ) (hd : sphereDen x y w ≠ 0) :
    (2*x*w/sphereDen x y w)^2 + (2*y*w/sphereDen x y w)^2 +
      ((x^2+y^2-w^2)/sphereDen x y w)^2 = 1 := by
  field_simp
  dsimp [sphereDen] at *
  ring

theorem multiply_horizontal (W H v : ℝ) :
    (LeanMath.Papers.RectanglePencils.left H (v*1)).2 =
    (LeanMath.Papers.RectanglePencils.right W H v).2 := by
  simp [LeanMath.Papers.RectanglePencils.left,LeanMath.Papers.RectanglePencils.right]

theorem divide_horizontal (W H v : ℝ) :
    (LeanMath.Papers.RectanglePencils.right W H (v/1)).2 =
    (LeanMath.Papers.RectanglePencils.left H v).2 := by
  simp [LeanMath.Papers.RectanglePencils.left,LeanMath.Papers.RectanglePencils.right]
end LeanMath.Papers.RectangleStereographic
