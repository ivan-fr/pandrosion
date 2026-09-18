import LeanMath.Papers.RectangleNativeNondegeneracy

/-! Post-V20 initialization by midpoint comparisons, with no root oracle in the
algorithm. Calibration is exact in this model; browser rounding has a separate
outward-interval certificate and is not identified with exact real arithmetic. -/
noncomputable section
namespace LeanMath.Papers.RectangleInitialization
open RectangleNativeNondegeneracy RectangleGeometry

def residual (X s : ℝ) (p : ℕ) := X*s^p
def mid (b : ℝ × ℝ) := (b.1+b.2)/2
def step (X : ℝ) (p : ℕ) (b : ℝ × ℝ) : ℝ × ℝ :=
  if residual X (mid b) p < 3/2 then (mid b,b.2) else (b.1,mid b)
def bisect (X : ℝ) (p : ℕ) (b : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => b
  | n+1 => step X p (bisect X p b n)
def Bracket (X : ℝ) (p : ℕ) (b : ℝ × ℝ) : Prop :=
  0≤b.1 ∧ b.1≤b.2 ∧ residual X b.1 p≤3/2 ∧ 3/2≤residual X b.2 p

theorem residual_mono (X a b : ℝ) (p : ℕ) (hX : 0≤X) (ha : 0≤a) (hab : a≤b) :
    residual X a p≤residual X b p := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab _) hX

theorem step_invariant (X : ℝ) (p : ℕ) (b : ℝ×ℝ) (_hX : 0≤X) (hb : Bracket X p b) :
    Bracket X p (step X p b) ∧ b.1≤(step X p b).1 ∧ (step X p b).2≤b.2 ∧
    (step X p b).2-(step X p b).1=(b.2-b.1)/2 := by
  rcases hb with ⟨hl,hle,hfl,hfu⟩
  have hm1 : b.1≤mid b := by dsimp [mid]; linarith
  have hm2 : mid b≤b.2 := by dsimp [mid]; linarith
  unfold step
  split_ifs with h
  · exact ⟨⟨hl.trans hm1,hm2,h.le,hfu⟩,hm1,le_rfl,by dsimp [mid]; ring⟩
  · exact ⟨⟨hl,hm1,hfl,le_of_not_gt h⟩,le_rfl,hm2,by dsimp [mid]; ring⟩

theorem bisection_invariant (X : ℝ) (p : ℕ) (b : ℝ×ℝ) (hX : 0≤X) (hb : Bracket X p b) (n : ℕ) :
    Bracket X p (bisect X p b n) ∧ b.1≤(bisect X p b n).1 ∧ (bisect X p b n).2≤b.2 ∧
    (bisect X p b n).2-(bisect X p b n).1=(b.2-b.1)/(2:ℝ)^n := by
  induction n with
  | zero => simpa [bisect] using hb
  | succ n ih =>
    have h := step_invariant X p _ hX ih.1
    refine ⟨h.1,ih.2.1.trans h.2.1,h.2.2.1.trans ih.2.2.1,?_⟩
    change (step X p _).2-(step X p _).1=_
    rw [h.2.2.2,ih.2.2.2,pow_succ]; ring

theorem residual_width_bound (X l u B : ℝ) (p : ℕ) (hX : 0≤X)
    (hl : 0≤l) (hlu : l≤u) (huB : u≤B) :
    residual X u p-residual X l p ≤ X*((u-l)*(p:ℝ)*B^(p-1)) := by
  have hu : 0≤u := hl.trans hlu
  have hpw := pow_le_pow_left₀ hl hlu p
  have h := abs_pow_sub_pow_le (a:=u) (b:=l) p
  rw [abs_of_nonneg (sub_nonneg.mpr hpw),abs_of_nonneg (sub_nonneg.mpr hlu),abs_of_nonneg hu,abs_of_nonneg hl,max_eq_left hlu] at h
  have hh : u^p-l^p ≤ (u-l)*(p:ℝ)*B^(p-1) := h.trans (by gcongr)
  dsimp [residual]
  nlinarith [mul_le_mul_of_nonneg_left hh hX]

/-- Any valid finite bracket reaches a dyadic midpoint whose residual is in [1,2]. -/
theorem bisection_terminates (X : ℝ) (p : ℕ) (b : ℝ×ℝ) (hX : 0<X)
    (hp : 0<p) (hb : Bracket X p b) :
    ∃ n : ℕ, 0<mid (bisect X p b n) ∧
      1≤residual X (mid (bisect X p b n)) p ∧ residual X (mid (bisect X p b n)) p≤2 := by
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (2*X*(b.2-b.1)*(p:ℝ)*b.2^(p-1)) (by norm_num : (1:ℝ)<2)
  have hi := bisection_invariant X p b hX.le hb n
  let l := (bisect X p b n).1
  let u := (bisect X p b n).2
  have hl : 0≤l := hi.1.1
  have hlu : l≤u := hi.1.2.1
  have hgap := residual_width_bound X l u b.2 p hX.le hl hlu hi.2.2.1
  have hw : u-l=(b.2-b.1)/(2:ℝ)^n := hi.2.2.2
  have hsmall : X*((u-l)*(p:ℝ)*b.2^(p-1))<1/2 := by
    rw [hw]
    apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have hd : (0:ℝ)<2^n := by positivity
    have he : X*(((b.2-b.1)/2^n)*(p:ℝ)*b.2^(p-1))*2 = (2*X*(b.2-b.1)*(p:ℝ)*b.2^(p-1))/2^n := by ring
    rw [he]; exact (div_lt_one hd).2 hn
  have hfl : 1<residual X l p := by have hh := hi.1.2.2.2; linarith
  have hfu : residual X u p<2 := by have hh := hi.1.2.2.1; linarith
  have hm1 : l≤mid (bisect X p b n) := by dsimp [l,u,mid] at *; linarith
  have hm2 : mid (bisect X p b n)≤u := by dsimp [l,u,mid] at *; linarith
  have hmpos : 0<mid (bisect X p b n) := by
    have hln : l≠0 := by intro hz; norm_num [residual,hz,ne_of_gt hp] at hfl
    exact lt_of_lt_of_le (lt_of_le_of_ne hl (Ne.symm hln)) hm1
  exact ⟨n,hmpos,(hfl.le.trans (residual_mono X _ _ p hX.le hl hm1)),
    (residual_mono X _ _ p hX.le (hl.trans hm1) hm2).trans hfu.le⟩

/-- A power-of-two upper bracket exists; no p-th root is evaluated. -/
theorem dyadic_bracket_exists (X : ℝ) (p : ℕ) (hX : 0<X) (hp : 0<p) :
    ∃ m : ℕ, Bracket X p (0,(2:ℝ)^m) := by
  obtain ⟨m,hm⟩ := pow_unbounded_of_one_lt (1+2/X) (by norm_num : (1:ℝ)<2)
  have hB : (1:ℝ)≤2^m := by
    have : (0:ℝ)<2/X := by positivity
    linarith
  have hpow : (2:ℝ)^m≤((2:ℝ)^m)^p := le_self_pow₀ hB (by omega)
  refine ⟨m,by norm_num,by positivity,?_,?_⟩
  · norm_num [residual,ne_of_gt hp]
  · have hh : 2/X<(2:ℝ)^m := by linarith
    have hh' : 2<X*(2:ℝ)^m := by nlinarith [(div_lt_iff₀ hX).mp hh]
    have hh'' := mul_le_mul_of_nonneg_left hpow hX.le
    dsimp [residual]; linarith

/-- Initialization is obtained by finitely many power-of-two and midpoint operations. -/
theorem GeometricInitializationTheorem (X : ℝ) (p : ℕ) (hX : 0<X) (hp : 3≤p) :
    ∃ m n : ℕ, let c := mid (bisect X p (0,(2:ℝ)^m) n)
      0<c ∧ 1≤X*c^p ∧ X*c^p≤2 := by
  obtain ⟨m,hm⟩ := dyadic_bracket_exists X p hX (by omega)
  obtain ⟨n,hn⟩ := bisection_terminates X p _ hX (by omega) hm
  exact ⟨m,n,hn⟩

theorem calibration_conjugacy (X c u : ℝ) (p : ℕ) :
    (X*c^p)*u^p=X*(c*u)^p := by rw [mul_pow]; ring

theorem calibration_initial_band (X c : ℝ) (p : ℕ) (h : 1≤X*c^p ∧ X*c^p≤2) :
    1≤residual (X*c^p) 1 p ∧ residual (X*c^p) 1 p≤2 := by simpa [residual] using h

theorem initialized_power_points (W H : ℝ) (j : ℕ) :
    leftLevel H 1 j=(0,0) ∧ diagonalLevel W H 1 j=(W,0) := native_at_one W H j

theorem initialized_M_bound (H Y : ℝ) (hH : 0≤H) (hY : 1≤Y ∧ Y≤2) :
    0≤(M H Y).2 ∧ (M H Y).2≤H/2 := by
  have hpos : 0<Y := by linarith
  have hlo : (1:ℝ)/2≤1/Y := (div_le_div_iff₀ (by norm_num) hpos).2 (by linarith)
  have hhi : 1/Y≤1 := (div_le_one hpos).2 hY.1
  dsimp [M]; constructor <;> nlinarith

theorem initialized_K_bound (W Y : ℝ) (p : ℕ) (hW : 0≤W) (hp : 3≤p) (hY : 1≤Y ∧ Y≤2) :
    W/3≤(K W Y p).1 ∧ (K W Y p).1≤W := by
  have hp' : (3:ℝ)≤p := by exact_mod_cast hp
  have hpos : (0:ℝ)<p := by linarith
  have hYpos : 0≤Y := by linarith [hY.1]
  have hy : 0≤Y/(p:ℝ) := div_nonneg hYpos hpos.le
  have hy' : Y/(p:ℝ)≤2/3 := (div_le_div_iff₀ hpos (by norm_num)).2 (by nlinarith)
  dsimp [K]; constructor <;> nlinarith

inductive Method | AK | AD | projective | arc

def update (method : Method) (p : ℕ) (X s : ℝ) : ℝ :=
  match method with
  | .AK => RectangleReports.ak p X s
  | .AD => RectangleReports.ad p X s
  | .projective => RectangleProjective.step p X s
  | .arc => RectangleFastPower.arcSupport p s (X*s^p)

def orbit (method : Method) (p : ℕ) (X s : ℝ) : ℕ → ℝ
  | 0 => s
  | n+1 => update method p X (orbit method p X s n)

theorem update_positive (method : Method) (p : ℕ) (X s : ℝ) (hp : 3≤p) (hX : 0<X) (hs : 0<s) :
    0<update method p X s := by
  cases method with
  | AK => exact RectangleNewton.ak_pos p X s (by omega) hX hs
  | AD => exact RectangleDynamics.ad_pos p X s (by omega) hX hs
  | projective => exact RectangleProjective.step_pos p X s (by omega) hX hs
  | arc =>
    have hp' : (3:ℝ)≤p := by exact_mod_cast hp
    have hm : 0≤(p:ℝ)-1 := by linarith
    have hg : 0≤((p:ℝ)-1)*Real.sqrt (RectangleDecenteredArc.rad p (X*s^p)) := mul_nonneg hm (Real.sqrt_nonneg _)
    dsimp [update,RectangleFastPower.arcSupport]
    have ht : 0<X*s^p := by positivity
    exact div_pos (mul_pos hs (by linarith)) (by linarith)

theorem orbit_positive (method : Method) (p : ℕ) (X s : ℝ) (hp : 3≤p) (hX : 0<X) (hs : 0<s) (n : ℕ) :
    0<orbit method p X s n := by
  induction n with
  | zero => exact hs
  | succ n ih => exact update_positive method p X _ hp hX ih

theorem update_calibration (method : Method) (p : ℕ) (X c u : ℝ) :
    update method p X (c*u)=c*update method p (X*c^p) u := by
  have ht := (calibration_conjugacy X c u p).symm
  cases method
  all_goals dsimp [update,RectangleReports.ak,RectangleReports.ad,RectangleProjective.step,RectangleFastPower.arcSupport]
  all_goals simp only [mul_assoc] at ht ⊢
  all_goals rw [ht]; ring

theorem orbit_calibration (method : Method) (p : ℕ) (X c u : ℝ) (n : ℕ) :
    orbit method p X (c*u) n=c*orbit method p (X*c^p) u n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [orbit,ih,update_calibration]; rfl

-- Actual correction geometry, with transferred-radius and selected-branch certificates.
def SupportCertificate (method : Method) (W H X s : ℝ) (p : ℕ) : Prop :=
  match method with
  | .AK => ReportCertificate W H X s p (K W X p)
  | .AD => circleEquation (W,H) (E W H s p) (H*s^p) ∧
      LowerCircleCertificate (centeredF W H X p) (centeredF W H X p).1 (H*s^p) (RectangleReports.movingD W H X s p) ∧
      ReportCertificate W H X s p (RectangleReports.movingD W H X s p)
  | .projective => FinitePair (join (RectangleProjective.center W H X p) (E W H s p)) (horizontal (RectangleProjective.ellY W H X p)) ∧
      (meet (join (RectangleProjective.center W H X p) (E W H s p)) (horizontal (RectangleProjective.ellY W H X p))=RectangleProjective.projectedD W H X s p) ∧
      ReportCertificate W H X s p (RectangleProjective.projectedD W H X s p)
  | .arc => circleEquation (arcG W H X p) (E W H s p) (arcRadius H X s p) ∧
      LowerCircleCertificate (arcF W H X p) (arcDx W p) (arcRadius H X s p) (arcD W H X s p) ∧
      ReportCertificate W H X s p (arcD W H X s p)

theorem support_exists (method : Method) (W H X s : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (hX : 0<X) (hs : 0<s) : SupportCertificate method W H X s p := by
  cases method with
  | AK => exact (OriginalAK_global_geometric_existence W H X s p hp hW hH hX hs).2
  | AD => exact (OriginalAD_global_geometric_existence W H X s p hp hW hH hX hs).2
  | projective => exact (OriginalProjectiveAD_global_geometric_existence W H X s p hp hW hH hX hs).2
  | arc => exact (OriginalDecenteredAD_global_geometric_existence W H X s p hp hW hH hX hs).2

/-- Every subsequent exact iterate has both a native and binary finite realization. -/
theorem calibrated_orbit_geometry (method : Method) (W H X c : ℝ) (p : ℕ) (hp : 3≤p)
    (hW : 0<W) (hH : 0<H) (_hc : 0<c) (hband : 1≤X*c^p ∧ X*c^p≤2) (n : ℕ) :
    let s := orbit method p (X*c^p) 1 n
    NativeCertificate W H s ∧ FastCertificate W H s p ∧ SupportCertificate method W H (X*c^p) s p := by
  have hY : 0<X*c^p := by linarith [hband.1]
  have hs := orbit_positive method p (X*c^p) 1 hp hY (by norm_num) n
  exact ⟨native_telescope W H _ hW.ne' hH.ne',fast_telescope W H _ p hH.ne',support_exists method W H _ _ p hp hW hH hY hs⟩

/-- A rounded calibrated input produces a bounded relative residual perturbation;
this does not assert that floating-point line intersections are exact. -/
theorem calibration_residual_error (X c Y u ε : ℝ) (p : ℕ) (hY : 1≤Y)
    (hu : 0≤u) (hε : 0≤ε) (herr : |X*c^p-Y|≤ε) :
    |X*(c*u)^p-Y*u^p|≤ε*(Y*u^p) := by
  have he : X*(c*u)^p-Y*u^p=(X*c^p-Y)*u^p := by rw [mul_pow]; ring
  rw [he,abs_mul,abs_of_nonneg (pow_nonneg hu p)]
  calc
    |X*c^p-Y| * u^p ≤ ε*u^p := mul_le_mul_of_nonneg_right herr (pow_nonneg hu p)
    _ ≤ ε*(Y*u^p) := by nlinarith [mul_le_mul_of_nonneg_right hY (pow_nonneg hu p)]

/-- Soundness of a residual-band decision from any containing interval. -/
theorem interval_acceptance (X c lo hi : ℝ) (p : ℕ) (hl : lo≤X*c^p) (hh : X*c^p≤hi)
    (hlo : 1≤lo) (hhi : hi≤2) : 1≤X*c^p ∧ X*c^p≤2 := ⟨hlo.trans hl,hh.trans hhi⟩

theorem positive_interval_product (a b al ah bl bh : ℝ)
    (hal : 0≤al) (hbl : 0≤bl) (ha : al≤a ∧ a≤ah) (hb : bl≤b ∧ b≤bh) :
    al*bl≤a*b ∧ a*b≤ah*bh := by
  exact ⟨mul_le_mul ha.1 hb.1 hbl (hal.trans ha.1),mul_le_mul ha.2 hb.2 (hbl.trans hb.1) (hal.trans (ha.1.trans ha.2))⟩

theorem dyadic_endpoints (X : ℝ) (p m n : ℕ) :
    ∃ a b : ℤ, (bisect X p (0,(2:ℝ)^m) n).1=(a:ℝ)/(2:ℝ)^n ∧
      (bisect X p (0,(2:ℝ)^m) n).2=(b:ℝ)/(2:ℝ)^n := by
  induction n with
  | zero => exact ⟨0,(2:ℤ)^m,by simp [bisect],by simp [bisect]⟩
  | succ n ih =>
    obtain ⟨a,b,ha,hb⟩ := ih
    dsimp only [bisect,step]
    split_ifs
    · refine ⟨a+b,2*b,?_,?_⟩
      · dsimp [mid]; rw [ha,hb]; push_cast; rw [pow_succ]; ring
      · dsimp only; rw [hb]; push_cast; rw [pow_succ]; ring
    · refine ⟨2*a,a+b,?_,?_⟩
      · dsimp only; rw [ha]; push_cast; rw [pow_succ]; ring
      · dsimp [mid]; rw [ha,hb]; push_cast; rw [pow_succ]; ring

theorem dyadic_midpoint (X : ℝ) (p m n : ℕ) :
    ∃ z : ℤ, mid (bisect X p (0,(2:ℝ)^m) n)=(z:ℝ)/(2:ℝ)^(n+1) := by
  obtain ⟨a,b,ha,hb⟩ := dyadic_endpoints X p m n
  refine ⟨a+b,?_⟩
  dsimp [mid]; rw [ha,hb]; push_cast; rw [pow_succ]; ring

/-- The selected scale is a positive dyadic rational, not an evaluated root. -/
theorem positive_dyadic_initialization (X : ℝ) (p : ℕ) (hX : 0<X) (hp : 3≤p) :
    ∃ n : ℕ, ∃ z : ℤ, let c := (z:ℝ)/(2:ℝ)^n
      0<c ∧ 1≤X*c^p ∧ X*c^p≤2 := by
  obtain ⟨m,n,hc,hlo,hhi⟩ := GeometricInitializationTheorem X p hX hp
  obtain ⟨z,hz⟩ := dyadic_midpoint X p m n
  exact ⟨n+1,z,by simpa only [hz] using And.intro hc (And.intro hlo hhi)⟩

/-- Integer rounding primitives used for outward mantissa truncation. -/
theorem round_down_bound (n d : ℕ) : n/d*d≤n := Nat.div_mul_le_self n d

theorem round_up_bound (n d : ℕ) (hd : 0<d) : n≤((n+d-1)/d)*d := by
  have hm := Nat.mod_lt (n+d-1) hd
  have he := Nat.div_add_mod (n+d-1) d
  rw [Nat.mul_comm] at he
  omega

end LeanMath.Papers.RectangleInitialization
