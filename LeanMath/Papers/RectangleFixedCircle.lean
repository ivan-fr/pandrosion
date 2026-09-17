import LeanMath.Papers.RectanglePencilsPade
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Inverse [2/2] Padé model, stable square-root branches and fixed-circle certificates.
The geometric results have explicit affine-chart hypotheses. -/
noncomputable section
namespace LeanMath.Papers.RectangleFixedCircle
open LeanMath.Papers LeanMath.Papers.RectangleGeometry
open Filter
open scoped Topology

def A (p : ℝ) := (p+1)*(p+2)
def B (p : ℝ) := p^2-4
def C (p : ℝ) := (p-1)*(p-2)
def N (p v : ℝ) := C p*v^2-2*B p*v+A p
def D (p v : ℝ) := A p*v^2-2*B p*v+C p
def delta (p t : ℝ) := (42*p^2-24)*t-3*(p^2-4)*(1+t^2)
def equation (p t v : ℝ) := N p v-t*D p v

theorem at_one (p : ℝ) : N p 1=12 ∧ D p 1=12 := by
  constructor <;> dsimp [N,D,A,B,C] <;> ring

theorem discriminant (p t : ℝ) :
    delta p t=(B p*(1-t))^2-(C p-t*A p)*(A p-t*C p) := by
  unfold delta A B C; ring

theorem reciprocity (p v : ℝ) (hv : v≠0) :
    N p (1/v)*v^2=D p v ∧ D p (1/v)*v^2=N p v := by
  constructor <;> unfold N D <;> field_simp <;> ring

theorem derivative_certificate (p v : ℝ) :
    p*N p v*D p v+v*((2*C p*v-2*B p)*D p v-N p v*(2*A p*v-2*B p))
      =p*A p*C p*(v-1)^4 := by
  unfold N D A B C; ring

theorem positive_quadratics (p v : ℝ) (hp : 2<p) : 0<N p v ∧ 0<D p v := by
  have ha : 0<A p := by unfold A; positivity
  have hc : 0<C p := by unfold C; apply mul_pos <;> linarith
  have hb : 0<3*(p^2-4) := by nlinarith
  have hn : C p*N p v=(C p*v-B p)^2+3*(p^2-4) := by unfold N A B C; ring
  have hd : A p*D p v=(A p*v-B p)^2+3*(p^2-4) := by unfold D A B C; ring
  constructor
  · nlinarith [sq_nonneg (C p*v-B p)]
  · nlinarith [sq_nonneg (A p*v-B p)]

/-- This chart is stable on the side t ≤ 1. -/
theorem branch_left (p t r : ℝ) (hr : r^2=delta p t)
    (hd : B p*(1-t)+r≠0) :
    equation p t ((A p-t*C p)/(B p*(1-t)+r))=0 := by
  have hh := discriminant p t
  unfold equation N D
  field_simp [hd]
  linear_combination (A p-t*C p)*(hr.trans hh)

/-- Conjugate chart avoids the removable 0/0 at t=A/C. -/
theorem branch_right (p t r : ℝ) (hr : r^2=delta p t)
    (hd : t*A p-C p≠0) :
    equation p t ((r-B p*(1-t))/(t*A p-C p))=0 := by
  have hh := discriminant p t
  unfold equation N D
  field_simp [hd]
  linear_combination (C p-t*A p)*(hr.trans hh)

theorem sqrt_branch_left (p t : ℝ) (ht : 0≤delta p t)
    (hd : B p*(1-t)+Real.sqrt (delta p t)≠0) :
    equation p t ((A p-t*C p)/(B p*(1-t)+Real.sqrt (delta p t)))=0 :=
  branch_left p t _ (Real.sq_sqrt ht) hd

theorem sqrt_branch_right (p t : ℝ) (ht : 0≤delta p t)
    (hd : t*A p-C p≠0) :
    equation p t ((Real.sqrt (delta p t)-B p*(1-t))/(t*A p-C p))=0 :=
  branch_right p t _ (Real.sq_sqrt ht) hd

theorem second_degree_exact (t v : ℝ) : equation 2 t v=12*(1-t*v^2) := by
  unfold equation N D A B C; ring

/-- Generic second intersection of a circle through (W,0) with a pencil line. -/
def normDir (W H rho v : ℝ) := (W*v)^2+(H*(rho-v))^2
def dotDir (W H rho h j v : ℝ) := (W-h)*(W*v)-j*(H*(rho-v))
def gx (W H rho h j v : ℝ) := W-2*dotDir W H rho h j v*(W*v)/normDir W H rho v
def gy (W H rho h j v : ℝ) := -2*dotDir W H rho h j v*(H*(rho-v))/normDir W H rho v

theorem circle_incidence (W H rho h j v : ℝ) (hn : normDir W H rho v≠0) :
    (gx W H rho h j v-h)^2+(gy W H rho h j v-j)^2=(W-h)^2+j^2 := by
  dsimp [gx,gy]
  field_simp [hn]
  dsimp [normDir,dotDir]
  ring

theorem pencil_incidence (W H rho h j v : ℝ) :
    H*(rho-v)*(gx W H rho h j v-W)=W*v*gy W H rho h j v := by
  dsimp [gx,gy]; ring

/-- Polynomial certificate for Z,T,G incidence; no division by a vanishing chart. -/
def incidenceNumerator (W H rho h j zx zy k _p t v : ℝ) :=
    (W-zx)*(-2*dotDir W H rho h j v*(H*(rho-v))-zy*normDir W H rho v)-
    (H*(1-k*t)-zy)*((W-zx)*normDir W H rho v-2*dotDir W H rho h j v*(W*v))

theorem projection_incidence (W H rho h j zx zy k p t v : ℝ)
    (hn : normDir W H rho v≠0)
    (he : incidenceNumerator W H rho h j zx zy k p t v=0) :
    On (RectangleGeometry.join (zx,zy) (W,H*(1-k*t))) (gx W H rho h j v,gy W H rho h j v) := by
  dsimp [On,RectangleGeometry.join,gx,gy]
  field_simp [hn]
  dsimp [incidenceNumerator] at he
  nlinarith [he]

theorem cubic_geometry_certificate (t v : ℝ) :
    incidenceNumerator 2 4 (1/2) (-152/113) (126/113) (478/113) (396/113) (5/113) 3 t v
      = (10080/12769)*equation 3 t v := by
  unfold incidenceNumerator dotDir normDir equation N D A B C
  ring



def polyL (p : ℝ) := p^3+12*p^2+39*p-26
def scaleK (p : ℝ) := (p-2)*(p^2-4*p+13)/polyL p
def centerX (p : ℝ) := 2-72*p*(p+4)/((p-1)*polyL p)
def centerY (p : ℝ) := 24*p*(p-2)*(p+4)/((p-1)*polyL p)
def poleX (p : ℝ) := 2-24*p*(p+4)*(p-2)/((p-4)*polyL p)
def poleY (p : ℝ) := 24*p*(p^2+2*p-26)/((p-4)*polyL p)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem general_geometry_certificate (p t v : ℝ)
    (h1 : p-1≠0) (h4 : p-4≠0) (hL : polyL p≠0) :
    incidenceNumerator 2 4 (1/2) (centerX p) (centerY p) (poleX p) (poleY p) (scaleK p) p t v
      = (-384*p*(p-2)*(p+4)*(p^2-4*p+13)/((p-4)*(p-1)*(polyL p)^2))*equation p t v := by
  unfold incidenceNumerator dotDir normDir centerX centerY poleX poleY scaleK equation N D A B C
  field_simp [h1,h4,hL]
  unfold polyL
  ring

theorem fourth_geometry_certificate (t v : ℝ) :
    incidenceNumerator 2 4 (1/3) (13502/7167) (3328/2389) (-214/2389) (2432/2389) (145/2389) 4 t v
      = (-7720960/51365889)*equation 4 t v := by
  unfold incidenceNumerator dotDir normDir equation N D A B C
  ring

/-- Input log-error on the local inverse branch, parameterized by v=1+u. -/
def inputLog (p u : ℝ) := (Real.log (N p (1+u))-Real.log (D p (1+u)))/p
def outputLog (p u : ℝ) := inputLog p u+Real.log (1+u)
def orderFactor (p u : ℝ) := A p*C p/((1+u)*N p (1+u)*D p (1+u))

theorem input_zero (p : ℝ) : inputLog p 0=0 := by
  simp [inputLog,(at_one p).1,(at_one p).2]

theorem input_derivative (p u : ℝ) (hp : 2<p) :
    HasDerivAt (inputLog p)
      (((2*C p*(1+u)-2*B p)/N p (1+u)-(2*A p*(1+u)-2*B p)/D p (1+u))/p) u := by
  have hpos := positive_quadratics p (1+u) hp
  have hn : HasDerivAt (fun u : ℝ => N p (1+u)) (2*C p*(1+u)-2*B p) u := by
    convert! (((((hasDerivAt_id u).const_add 1).pow 2).const_mul (C p)).sub
      (((hasDerivAt_id u).const_add 1).const_mul (2*B p))).add_const (A p) using 1 <;> dsimp [N] <;> ring
  have hd : HasDerivAt (fun u : ℝ => D p (1+u)) (2*A p*(1+u)-2*B p) u := by
    convert! (((((hasDerivAt_id u).const_add 1).pow 2).const_mul (A p)).sub
      (((hasDerivAt_id u).const_add 1).const_mul (2*B p))).add_const (C p) using 1 <;> dsimp [D] <;> ring
  exact ((hn.log hpos.1.ne').sub (hd.log hpos.2.ne')).div_const p

theorem input_derivative_zero (p : ℝ) (hp : 2<p) : HasDerivAt (inputLog p) (-1) 0 := by
  have hh := input_derivative p 0 hp
  convert! hh using 1
  rw [add_zero,(at_one p).1,(at_one p).2]
  have hp0 : p≠0 := by linarith
  unfold A B C; field_simp [hp0]; ring

theorem output_derivative (p u : ℝ) (hp : 2<p) (hu : 1+u≠0) :
    HasDerivAt (outputLog p) (u^4*orderFactor p u) u := by
  have hn := (positive_quadratics p (1+u) hp).1.ne'
  have hd := (positive_quadratics p (1+u) hp).2.ne'
  have hp0 : p≠0 := by linarith
  have hh := (input_derivative p u hp).add (((hasDerivAt_id u).const_add 1).log hu)
  convert! hh using 1
  unfold orderFactor
  simp only [id_eq]
  field_simp [hn,hd,hp0,hu]
  have he := derivative_certificate p (1+u)
  linear_combination -he

/-- True order-five limit, in the local inverse-branch parameter. -/
theorem output_contact_five (p : ℝ) (hp : 2<p) :
    Tendsto (fun u : ℝ => outputLog p u/u^5) (𝓝[≠] 0) (𝓝 (A p*C p/720)) := by
  have hf0 : outputLog p 0=0 := by simp [outputLog,input_zero]
  have hf : ContinuousAt (outputLog p) 0 := (output_derivative p 0 hp (by norm_num)).continuousAt
  have hg : ContinuousAt (orderFactor p) 0 := by
    unfold orderFactor
    apply ContinuousAt.div continuousAt_const
    · unfold N D; fun_prop
    · simp [(at_one p).1,(at_one p).2]
  have hh : ∀ᶠ u : ℝ in 𝓝[≠] 0, HasDerivAt (outputLog p) (u^4*orderFactor p u) u := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show (-1:ℝ)<0 by norm_num))] with u hu
    apply output_derivative p u hp
    have : -1<u := hu
    linarith
  have ht := LocalOrder.from_derivative 4 (outputLog p) (orderFactor p) hf0 hf hg hh
  have he : orderFactor p 0/((4:ℝ)+1)=A p*C p/720 := by
    simp only [orderFactor,add_zero,(at_one p).1,(at_one p).2]
    ring
  simpa only [Nat.reduceAdd,Nat.cast_ofNat,he] using ht

/-- Logarithmic errors satisfy e+ / e^5 → -(p²-1)(p²-4)/720.
The parameter runs through the unique inverse branch near v=1. -/
theorem logarithmic_order_five (p : ℝ) (hp : 2<p) :
    Tendsto (fun u : ℝ => outputLog p u/(inputLog p u)^5) (𝓝[≠] 0)
      (𝓝 (-(p^2-1)*(p^2-4)/720)) := by
  have hi : Tendsto (fun u : ℝ => inputLog p u/u) (𝓝[≠] 0) (𝓝 (-1)) := by
    simpa [input_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using (input_derivative_zero p hp).tendsto_slope_zero
  have ht := (output_contact_five p hp).div (hi.pow 5) (by norm_num)
  have he : A p*C p/720/(-1:ℝ)^5= -(p^2-1)*(p^2-4)/720 := by unfold A C; ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u≠0 := hu
  dsimp
  rw [div_pow,div_div_div_cancel_right₀ (pow_ne_zero 5 hu0)]



/-- Reading the pencil parameter on the top rail. -/
theorem top_readout_incidence (W H rho h j v : ℝ) (hv : rho-v≠0) :
    On (RectangleGeometry.join (W,0) (gx W H rho h j v,gy W H rho h j v))
      (W*rho/(rho-v),H) := by
  have he := pencil_incidence W H rho h j v
  dsimp [On,RectangleGeometry.join]
  field_simp [hv]
  nlinarith [he]

theorem top_is_hub (W H rho v : ℝ) (hv : v≠0) (hr : rho-v≠0) :
    (W*rho/(rho-v),H)=RectanglePencils.hub W H (rho/v) := by
  have hf : rho/v-1≠0 := by
    intro h
    have h1 : rho/v=1 := by linarith
    exact hr (sub_eq_zero.mpr ((div_eq_one_iff_eq hv).mp h1))
  ext <;> dsimp [RectanglePencils.hub] <;> field_simp [hv,hr,hf] <;> ring

/-- The last actual line produces sv from the saved point rho*s. -/
theorem final_readout (W H rho s v : ℝ) (hW : W≠0) (hv : v≠0) (hrho : rho≠0)
    (hf : rho/v-1≠0) (P : Point)
    (hP : On (RectangleGeometry.join (RectanglePencils.hub W H (rho/v))
      (RectanglePencils.left H (rho*s))) P ∧ On (vertical W) P) :
    P=RectanglePencils.right W H (s*v) := by
  have he := RectanglePencils.divide_unique W H (rho*s) (rho/v) hW hf (div_ne_zero hrho hv) P hP
  have hh : rho*s/(rho/v)=s*v := by field_simp [hrho,hv]
  simpa only [hh] using he

/-- Closed telescope normalization, including the two exceptional fixed factors. -/
theorem weighted_chain (p : ℕ) (k X rho s : ℝ) (hp : 3≤p) (hrho : rho≠0) :
    s^p*rho*(1/2:ℝ)^(p-3)*(k*X*2^(p-3)/rho)=k*(X*s^p) := by
  rw [one_div_pow]
  field_simp [hrho]
  <;> ring

theorem positive_preparation_scale (p : ℝ) (hp : 3≤p) : 0<polyL p ∧ 0<scaleK p := by
  have hp0 : 0<p := by linarith
  have hL : 0<polyL p := by
    unfold polyL
    have : 0<p^3 := pow_pos hp0 3
    nlinarith [sq_nonneg p]
  refine ⟨hL,?_⟩
  unfold scaleK
  apply div_pos _ hL
  apply mul_pos
  · linarith
  · nlinarith [sq_nonneg (p-2)]

theorem rational_preparation (K : Subfield ℝ) (p : ℝ) (hp : p∈K) :
    centerX p∈K ∧ centerY p∈K ∧ poleX p∈K ∧ poleY p∈K ∧ scaleK p∈K := by
  dsimp [centerX,centerY,poleX,poleY,scaleK,polyL]
  repeat' constructor
  all_goals field_membership

end LeanMath.Papers.RectangleFixedCircle
