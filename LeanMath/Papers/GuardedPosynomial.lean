import LeanMath.Papers.PosynomialCubic
import LeanMath.Papers.DampedNewton

noncomputable section
namespace LeanMath.Papers.GuardedPosynomial
open Set Function Filter PosynomialSystem PosynomialCubic CompactPosynomial
open scoped Topology

variable {n M : ℕ} [Nonempty (Fin M)] [Nontrivial (Space n)] (P : System n M)

def residual (c x : Space n) := ‖logPartition P x-c‖
def solverStep (hdet : ∀ A ∈ rowHull P, A.det ≠ 0) (c : Space n)
    (S : Space n → Space n) (a : ℝ) :=
  DampedNewton.guarded (residual P c) (candidate P hdet c) S a

/-- Full global/local assembly for the actual posynomial cubic candidate.
The fallback descent certificate remains explicit and can be supplied by
`DampedNewton.residual_descent` from quantitative Taylor data. -/
theorem global_and_eventually_cubic (hdet : ∀ A ∈ rowHull P, A.det ≠ 0)
    (c : Space n) (S : Space n → Space n) (a : ℝ) (ha : 0 < a) (x₀ : Space n)
    (hstart : 0 < residual P c x₀)
    (hS : ∀ x, residual P c (S x) ≤
      (1-DampedNewton.damping a (residual P c x)/2)*residual P c x) :
    ∃ z : Space n, logPartition P z = c ∧
      Tendsto (fun k => (solverStep P hdet c S a)^[k] x₀) atTop (𝓝 z) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∃ K : ℕ, ∀ k ≥ K,
        (solverStep P hdet c S a)^[k+1] x₀ = candidate P hdet c ((solverStep P hdet c S a)^[k] x₀) ∧
        ‖(solverStep P hdet c S a)^[k+1] x₀-z‖ ≤ C*‖(solverStep P hdet c S a)^[k] x₀-z‖^3 := by
  obtain ⟨z,hz,_⟩ := GlobalPosynomial.unique_solution P hdet c
  obtain ⟨σ,hσ,hb⟩ := GlobalPosynomial.global_lower_bound P hdet
  let f := solverStep P hdet c S a
  have hf := DampedNewton.guarded_descent (residual P c) (candidate P hdet c) S a hS
  have hconv : Tendsto (fun k => f^[k] x₀) atTop (𝓝 z) :=
    DampedNewton.orbit_converges (residual P c) f a σ x₀ z ha hσ hstart
      (fun x => norm_nonneg _) hf (fun x => by simpa only [residual,hz] using hb x z)
  obtain ⟨K₁,hK₁⟩ := eventual_cubic_acceptance P hdet c z hz (fun k => f^[k] x₀)
    hconv (1/2) (by norm_num)
  obtain ⟨K₂,hK₂⟩ := Metric.tendsto_atTop.mp hconv 1 (by norm_num)
  obtain ⟨C,hC,hlocal⟩ := uniform_cubic_error P hdet c z hz
  refine ⟨z,hz,hconv,C,hC,max K₁ K₂,fun k hk => ?_⟩
  have he : f^[k+1] x₀ = candidate P hdet c (f^[k] x₀) := by
    rw [iterate_succ_apply']
    exact DampedNewton.guarded_accepts_half (residual P c) (candidate P hdet c) S a
      (f^[k] x₀) (norm_nonneg _) (hK₁ k ((le_max_left _ _).trans hk))
  refine ⟨he,?_⟩
  change ‖f^[k+1] x₀-z‖ ≤ C*‖f^[k] x₀-z‖^3
  rw [he]
  exact hlocal _ (by simpa only [dist_eq_norm] using (hK₂ k ((le_max_right _ _).trans hk)).le)

end LeanMath.Papers.GuardedPosynomial
