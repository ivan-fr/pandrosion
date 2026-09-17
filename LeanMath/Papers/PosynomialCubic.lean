import LeanMath.Papers.GlobalPosynomial

noncomputable section
set_option maxSynthPendingDepth 3
namespace LeanMath.Papers.PosynomialCubic
open Set PosynomialSystem PosynomialDifferential CompactPosynomial

variable {n M : ℕ} [Nonempty (Fin M)] (P : System n M)

def curve (c x v : Space n) (t : ℝ) := logPartition P (x+t • v)-c
def curveD1 (x v : Space n) (t : ℝ) := jacobian P (x+t • v) v
def curveD2 (x v : Space n) (t : ℝ) := hessian P (x+t • v) v v
def curveD3 (x v : Space n) (t : ℝ) := third P (x+t • v) v v v

theorem line_deriv (x v : Space n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => x+u • v) v t := by
  convert! (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v) using 1 <;> simp

theorem curve_deriv (c x v : Space n) (t : ℝ) :
    HasDerivAt (curve P c x v) (curveD1 P x v t) t :=
  ((hasFDerivAt_logPartition P _).comp_hasDerivAt t (line_deriv x v t)).sub_const c

theorem curveD1_deriv (x v : Space n) (t : ℝ) :
    HasDerivAt (curveD1 P x v) (curveD2 P x v t) t := by
  have hd := (((smooth_jacobian P).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt
    t (line_deriv x v t)).clm_apply (hasDerivAt_const t v)
  convert! hd using 1 <;> simp [curveD1,curveD2,hessian]

theorem curveD2_deriv (x v : Space n) (t : ℝ) :
    HasDerivAt (curveD2 P x v) (curveD3 P x v t) t := by
  have hd := ((((smooth_hessian P).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt
    t (line_deriv x v t)).clm_apply (hasDerivAt_const t v)).clm_apply (hasDerivAt_const t v)
  convert! hd using 1 <;> simp [curveD2,curveD3,third]

theorem curve_jets (c x v : Space n) :
    EqOn (iteratedDerivWithin 1 (curve P c x v) (Icc 0 1)) (curveD1 P x v) (Icc 0 1) ∧
    EqOn (iteratedDerivWithin 2 (curve P c x v) (Icc 0 1)) (curveD2 P x v) (Icc 0 1) ∧
    EqOn (iteratedDerivWithin 3 (curve P c x v) (Icc 0 1)) (curveD3 P x v) (Icc 0 1) := by
  have hu := uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1)
  have h1 : EqOn (iteratedDerivWithin 1 (curve P c x v) (Icc 0 1))
      (curveD1 P x v) (Icc 0 1) := by
    intro t ht
    rw [iteratedDerivWithin_succ,iteratedDerivWithin_zero]
    exact (curve_deriv P c x v t).hasDerivWithinAt.derivWithin (hu t ht)
  have h2 : EqOn (iteratedDerivWithin 2 (curve P c x v) (Icc 0 1))
      (curveD2 P x v) (Icc 0 1) := by
    intro t ht
    rw [show (2:ℕ)=1+1 from rfl,iteratedDerivWithin_succ]
    rw [derivWithin_congr h1 (h1 ht)]
    exact (curveD1_deriv P x v t).hasDerivWithinAt.derivWithin (hu t ht)
  refine ⟨h1,h2,?_⟩
  intro t ht
  rw [show (3:ℕ)=2+1 from rfl,iteratedDerivWithin_succ]
  rw [derivWithin_congr h2 (h2 ht)]
  exact (curveD2_deriv P x v t).hasDerivWithinAt.derivWithin (hu t ht)

theorem curve_smooth (c x v : Space n) : ContDiff ℝ 3 (curve P c x v) := by
  have hg : ContDiff ℝ 3 (logPartition P) := (smooth_logPartition P).of_le le_top
  have hc : ContDiff ℝ 3 (fun t : ℝ => logPartition P (x+t • v)) :=
    hg.comp (by fun_prop : ContDiff ℝ 3 (fun t : ℝ => x+t • v))
  exact hc.sub contDiff_const

theorem root_segment_mem (x z : Space n) (hx : ‖x-z‖ ≤ 1)
    (t : ℝ) (ht : t ∈ Icc 0 1) : x+t • (z-x) ∈ Metric.closedBall z 1 := by
  rw [Metric.mem_closedBall,dist_eq_norm]
  have he : x+t • (z-x)-z = (1-t) • (x-z) := by
    simp only [sub_smul,one_smul,smul_sub]
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith [ht.2])]
  nlinarith [norm_nonneg (x-z),ht.1,ht.2]

theorem uniform_root_taylor (c z : Space n) (hz : logPartition P z = c) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space n, ‖x-z‖ ≤ 1 →
      ‖(logPartition P x-c)+jacobian P x (z-x)+(1/2:ℝ) • hessian P x (z-x) (z-x)‖
        ≤ C * ‖z-x‖^3 := by
  obtain ⟨C,hC,hb⟩ := third_direction_bounded_on_closedBall P z 1
  refine ⟨C/2,by positivity,fun x hx => ?_⟩
  have hj := curve_jets P c x (z-x)
  have h0 : (0:ℝ) ∈ Icc 0 1 := by norm_num
  have ht := CubicReversion.path_taylor_bound (curve P c x (z-x)) (z-x)
    (jacobian P x (z-x)) (hessian P x (z-x) (z-x)) C (curve_smooth P c x (z-x)).contDiffOn
    (by simpa [curveD1] using hj.1 h0) (by simpa [curveD2] using hj.2.1 h0)
    (fun t ht => by rw [hj.2.2 ht]; exact hb _ (root_segment_mem x z hx t ht) (z-x))
  have hc0 : curve P c x (z-x) 0 = logPartition P x-c := by simp [curve]
  have hc1 : curve P c x (z-x) 1 = 0 := by simp [curve,hz]
  rw [hc0,hc1] at ht
  have he : (0:Space n)-(logPartition P x-c)-jacobian P x (z-x)-
      (1/2:ℝ) • hessian P x (z-x) (z-x) =
      -((logPartition P x-c)+jacobian P x (z-x)+(1/2:ℝ) • hessian P x (z-x) (z-x)) := by abel
  rw [he,norm_neg] at ht
  exact ht

def candidate (hdet : ∀ A ∈ rowHull P, A.det ≠ 0) (c x : Space n) :=
  x+CubicReversion.cubicCorrection (jacobianEquiv P hdet x) (hessian P x) (logPartition P x-c)

theorem uniform_cubic_error [Nontrivial (Space n)] (hdet : ∀ A ∈ rowHull P, A.det ≠ 0)
    (c z : Space n) (hz : logPartition P z = c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space n, ‖x-z‖ ≤ 1 →
      ‖candidate P hdet c x-z‖ ≤ C * ‖x-z‖^3 := by
  obtain ⟨σ,hσ,hsigma⟩ := jacobian_uniform_lower_bound P hdet
  obtain ⟨H,hH⟩ := (isCompact_closedBall z 1).exists_bound_of_continuousOn
    (smooth_hessian P).continuous.continuousOn
  let H₀ := |H|+1
  have hH₀ : 0 ≤ H₀ := by dsimp [H₀]; positivity
  obtain ⟨Q,hQ,hrem⟩ := uniform_root_taylor P c z hz
  let K := σ⁻¹
  let A := K*(H₀/2+Q)
  let C := K*(Q+H₀*A*(2+A)/2)
  have hK : 0 ≤ K := inv_nonneg.mpr hσ.le
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨C,by dsimp [C]; positivity,fun x hx => ?_⟩
  have hi : ∀ v, ‖(jacobianEquiv P hdet x).symm v‖ ≤ K*‖v‖ := by
    intro v
    have hh := hsigma x ((jacobianEquiv P hdet x).symm v)
    have he : jacobian P x ((jacobianEquiv P hdet x).symm v) = v :=
      (jacobianEquiv P hdet x).apply_symm_apply v
    rw [he] at hh
    change _ ≤ σ⁻¹*‖v‖
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hσ).mpr (by nlinarith)
  have hB : ∀ u v, ‖hessian P x u v‖ ≤ H₀*‖u‖*‖v‖ := by
    intro u v
    have hb : ‖hessian P x‖ ≤ H₀ :=
      (hH x (by simpa [Metric.mem_closedBall,dist_eq_norm] using hx)).trans (by
        dsimp [H₀]; linarith [le_abs_self H])
    exact ((hessian P x).le_opNorm₂ u v).trans (by gcongr)
  have hh := CubicReversion.cubic_error (jacobianEquiv P hdet x) (hessian P x)
    (logPartition P x-c) (z-x) K H₀ Q hK hH₀ hQ.le hi hB
    (by simpa [norm_sub_rev] using hx) (hrem x hx)
  change ‖x+CubicReversion.cubicCorrection _ _ _-z‖ ≤ _
  have he : x+CubicReversion.cubicCorrection (jacobianEquiv P hdet x) (hessian P x)
      (logPartition P x-c)-z = CubicReversion.cubicCorrection (jacobianEquiv P hdet x)
      (hessian P x) (logPartition P x-c)-(z-x) := by abel
  rw [he]
  simpa only [norm_sub_rev z x] using hh

theorem uniform_cubic_residual [Nontrivial (Space n)] (hdet : ∀ A ∈ rowHull P, A.det ≠ 0)
    (c z : Space n) (hz : logPartition P z = c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Space n, ‖x-z‖ ≤ 1 →
      ‖logPartition P (candidate P hdet c x)-c‖ ≤ C * ‖x-z‖^3 := by
  obtain ⟨C,hC,hb⟩ := uniform_cubic_error P hdet c z hz
  obtain ⟨L,hL⟩ := GlobalPosynomial.global_lipschitz P
  refine ⟨(L:ℝ)*C,mul_nonneg L.coe_nonneg hC,fun x hx => ?_⟩
  have hl := hL.norm_sub_le (candidate P hdet c x) z
  rw [hz] at hl
  exact hl.trans (by nlinarith [mul_le_mul_of_nonneg_left (hb x hx) L.coe_nonneg])

/-- The actual posynomial cubic candidate is eventually accepted along any convergent
sequence, for every fixed positive residual threshold. -/
theorem eventual_cubic_acceptance [Nontrivial (Space n)]
    (hdet : ∀ A ∈ rowHull P, A.det ≠ 0) (c z : Space n) (hz : logPartition P z = c)
    (u : ℕ → Space n) (hu : Filter.Tendsto u Filter.atTop (nhds z))
    (θ : ℝ) (hθ : 0 < θ) :
    ∃ K : ℕ, ∀ k ≥ K, ‖logPartition P (candidate P hdet c (u k))-c‖ ≤
      θ * ‖logPartition P (u k)-c‖ := by
  obtain ⟨σ,hσ,hb⟩ := GlobalPosynomial.global_lower_bound P hdet
  obtain ⟨C,_,hC⟩ := uniform_cubic_residual P hdet c z hz
  apply MultivariateGuard.eventual_acceptance (fun x => ‖logPartition P x-c‖)
    (candidate P hdet c) z u σ θ C 1 2 (by norm_num) hσ hθ (by norm_num)
  · intro x
    simpa only [dist_eq_norm,hz] using hb x z
  · intro x hx
    exact hC x (by simpa only [dist_eq_norm] using hx.le)
  · exact hu

end LeanMath.Papers.PosynomialCubic
