import LeanMath.Papers.RectangleFixedCircle
import LeanMath.Papers.RectangleStereographic

/-! The sphere is a display of homogeneous incidences. A similarity, rather than
independent axis normalization, preserves the fixed Euclidean circle. -/
noncomputable section
namespace LeanMath.Papers.RectangleFixedCircleStereo

def norm (x y w : ℝ) := x^2+y^2+w^2
def sx (x y w : ℝ) := 2*x*w/norm x y w
def sy (x y w : ℝ) := 2*y*w/norm x y w
def sz (x y w : ℝ) := (x^2+y^2-w^2)/norm x y w

theorem on_sphere (x y w : ℝ) (hn : norm x y w≠0) :
    sx x y w^2+sy x y w^2+sz x y w^2=1 := by
  dsimp [sx,sy,sz]; field_simp [hn]; unfold norm; ring

theorem line_plane_identity (a b c x y w : ℝ) (hn : norm x y w≠0) :
    a*sx x y w+b*sy x y w+c*(1-sz x y w)=2*w*(a*x+b*y+c*w)/norm x y w := by
  dsimp [sx,sy,sz]; field_simp [hn]; unfold norm; ring

theorem line_image (a b c x y w : ℝ) (hn : norm x y w≠0)
    (hi : a*x+b*y+c*w=0) : a*sx x y w+b*sy x y w+c*(1-sz x y w)=0 := by
  rw [line_plane_identity a b c x y w hn,hi]; ring

theorem circle_plane_identity (h j c x y w : ℝ) (hn : norm x y w≠0) :
    -2*h*sx x y w-2*j*sy x y w+(1-c)*sz x y w+(1+c)
      =2*(x^2+y^2-2*h*x*w-2*j*y*w+c*w^2)/norm x y w := by
  dsimp [sx,sy,sz]; field_simp [hn]; unfold norm; ring

theorem circle_image (h j r x y w : ℝ) (hn : norm x y w≠0)
    (hi : (x-h*w)^2+(y-j*w)^2=r^2*w^2) :
    -2*h*sx x y w-2*j*sy x y w+(1-(h^2+j^2-r^2))*sz x y w+(1+(h^2+j^2-r^2))=0 := by
  rw [circle_plane_identity h j (h^2+j^2-r^2) x y w hn]
  have he : x^2+y^2-2*h*x*w-2*j*y*w+(h^2+j^2-r^2)*w^2=0 := by nlinarith [hi]
  rw [he]; ring

theorem north_excluded_from_circle_plane (c : ℝ) : (1-c)*1+(1+c)=2 := by ring

theorem all_directions_at_north (x y : ℝ) (hn : x^2+y^2≠0) :
    sx x y 0=0 ∧ sy x y 0=0 ∧ sz x y 0=1 := by
  simp [sx,sy,sz,norm,hn]

theorem homogeneous_scale (x y w k : ℝ) (hk : k≠0) :
    sx (k*x) (k*y) (k*w)=sx x y w ∧
    sy (k*x) (k*y) (k*w)=sy x y w ∧
    sz (k*x) (k*y) (k*w)=sz x y w := by
  dsimp [sx,sy,sz,norm]
  repeat' constructor
  all_goals field_simp [hk] <;> ring

theorem similarity_circle_identity (x y w ox oy h j r scale : ℝ) (hs : scale≠0) :
    ((x-ox*w)/scale-(h-ox)/scale*w)^2+
    ((y-oy*w)/scale-(j-oy)/scale*w)^2-(r/scale)^2*w^2
      =((x-h*w)^2+(y-j*w)^2-r^2*w^2)/scale^2 := by
  field_simp [hs]; ring

theorem finite_inverse (x y w : ℝ) (hn : norm x y w≠0) (hw : w≠0) :
    sx x y w/(1-sz x y w)=x/w ∧ sy x y w/(1-sz x y w)=y/w := by
  have hd : 1-sz x y w=2*w^2/norm x y w := by
    dsimp [sz]; field_simp [hn]; unfold norm; ring
  rw [hd]
  dsimp [sx,sy]
  constructor <;> field_simp [hn,hw]

end LeanMath.Papers.RectangleFixedCircleStereo
