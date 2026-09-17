import LeanMath.Papers.PosynomialDifferential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Antilipschitz
import LeanMath.Papers.LogThompson

/-! Rectangularity closes the secant gap: scalar mean value points may differ by row.
This avoids a Bochner-integral construction of a common averaged Jacobian. -/
noncomputable section
namespace LeanMath.Papers.GlobalPosynomial
open Set PosynomialSystem CompactPosynomial PosynomialDifferential
open scoped NNReal

variable {n M : ℕ} [Nonempty (Fin M)] (P : System n M)

theorem secant_matrix (x y : Space n) :
    ∃ A ∈ rowHull P, logPartition P x - logPartition P y = A.mulVec (x-y) := by
  have htimes : ∀ i : Fin n, ∃ t : ℝ,
      rowDerivative P i (y+t • (x-y)) (x-y) = logPartition P x i-logPartition P y i := by
    intro i
    let φ := fun t : ℝ => logPartition P (y+t • (x-y)) i
    let ψ := fun t : ℝ => rowDerivative P i (y+t • (x-y)) (x-y)
    have hd : ∀ t, HasDerivAt φ (ψ t) t := by
      intro t
      have hl : HasDerivAt (fun u : ℝ => y+u • (x-y)) (x-y) t := by
        convert! (hasDerivAt_const t y).add ((hasDerivAt_id t).smul_const (x-y)) using 1 <;> simp
      exact (hasFDerivAt_log_row P i (y+t • (x-y))).comp_hasDerivAt t hl
    have hc : Continuous φ := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
    obtain ⟨t,_,ht⟩ := exists_hasDerivAt_eq_slope φ ψ (by norm_num : (0:ℝ)<1)
      hc.continuousOn (fun t _ => hd t)
    refine ⟨t,?_⟩
    simpa [φ,ψ] using ht
  choose τ hτ using htimes
  refine ⟨fun i => meanRow P i (y+τ i • (x-y)),
    fun i => mean_mem_hull P i _, ?_⟩
  funext i
  change logPartition P x i-logPartition P y i = ∑ j,
    meanRow P i (y+τ i • (x-y)) j * (x-y) j
  rw [← hτ i]
  exact jacobian_apply P (y+τ i • (x-y)) (x-y) i

theorem global_lower_bound [Nontrivial (Space n)]
    (hdet : ∀ A ∈ rowHull P, A.det ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ x y : Space n,
      σ * ‖x-y‖ ≤ ‖logPartition P x-logPartition P y‖ := by
  obtain ⟨σ,hσ,hb⟩ := CompactPosynomial.uniform_lower_bound P hdet
  refine ⟨σ,hσ,fun x y => ?_⟩
  obtain ⟨A,hA,he⟩ := secant_matrix P x y
  rw [he]
  exact hb A hA (x-y)

theorem global_lipschitz : ∃ B : ℝ≥0, LipschitzWith B (logPartition P) := by
  obtain ⟨C,hC⟩ := (operatorHull_compact P).exists_bound_of_continuousOn continuous_id.continuousOn
  let B : ℝ≥0 := ⟨|C|+1,by positivity⟩
  refine ⟨B,lipschitzWith_of_nnnorm_fderiv_le
    (fun x => (hasFDerivAt_logPartition P x).differentiableAt) ?_⟩
  intro x
  rw [(hasFDerivAt_logPartition P x).fderiv]
  have hm : jacobian P x ∈ matrixOperator '' rowHull P :=
    ⟨fun i => meanRow P i x,fun i => mean_mem_hull P i x,(jacobian_eq_mean_operator P x).symm⟩
  have hb : ‖jacobian P x‖ ≤ (B : ℝ) := (hC _ hm).trans
    (by change C ≤ |C|+1; linarith [le_abs_self C])
  exact_mod_cast hb

theorem injective [Nontrivial (Space n)] (hdet : ∀ A ∈ rowHull P, A.det ≠ 0) :
    Function.Injective (logPartition P) := by
  obtain ⟨σ,hσ,hb⟩ := global_lower_bound P hdet
  exact CompactJacobian.injective_of_lower_bound _ σ hσ hb

theorem surjective [Nontrivial (Space n)] (hdet : ∀ A ∈ rowHull P, A.det ≠ 0) :
    Function.Surjective (logPartition P) := by
  obtain ⟨σ,hσ,hb⟩ := global_lower_bound P hdet
  let K : ℝ≥0 := ⟨σ⁻¹, inv_nonneg.mpr hσ.le⟩
  have ha : AntilipschitzWith K (logPartition P) := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    simp only [dist_eq_norm]
    change ‖x-y‖ ≤ σ⁻¹ * ‖logPartition P x-logPartition P y‖
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hσ).mpr (by nlinarith [hb x y])
  obtain ⟨B,hB⟩ := global_lipschitz P
  have hc := ha.isClosed_range hB.uniformContinuous
  have ho : IsOpen (Set.range (logPartition P)) := by
    simpa using (open_logPartition P hdet) Set.univ isOpen_univ
  have he : Set.range (logPartition P) = Set.univ :=
    (show IsClopen (Set.range (logPartition P)) from ⟨hc,ho⟩).eq_univ (Set.range_nonempty _)
  exact Set.range_eq_univ.mp he

theorem unique_solution [Nontrivial (Space n)] (hdet : ∀ A ∈ rowHull P, A.det ≠ 0)
    (c : Space n) : ∃! x, logPartition P x = c := by
  obtain ⟨x,hx⟩ := surjective P hdet c
  exact ⟨x,hx,fun y hy => injective P hdet (hy.trans hx.symm)⟩

theorem unique_positive_solution [Nontrivial (Space n)]
    (hdet : ∀ A ∈ rowHull P, A.det ≠ 0) (c : Space n) :
    ∃! u : LogThompson.Positive n, logPartition P (LogThompson.encode (fun _ => 1) u) = c := by
  obtain ⟨x,hx,huniq⟩ := unique_solution P hdet c
  have hw : ∀ i : Fin n, (0:ℝ)<1 := fun _ => zero_lt_one
  refine ⟨LogThompson.decode (fun _ => 1) x,?_,?_⟩
  · simpa only [LogThompson.encode_decode _ _ hw] using hx
  · intro y hy
    have hh := congrArg (LogThompson.decode (fun _ => 1)) (huniq _ hy)
    simpa only [LogThompson.decode_encode _ _ hw] using hh

end LeanMath.Papers.GlobalPosynomial
