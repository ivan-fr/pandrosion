import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! Uniform lower bounds for compact families of injective operators.
The proof minimizes on the product with the unit sphere; it does not assume
continuity of a separately defined smallest-singular-value function. -/
noncomputable section
namespace LeanMath.Papers.CompactJacobian
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]

theorem uniform_lower_bound (K : Set (E →L[ℝ] E)) (hK : IsCompact K)
    (hne : K.Nonempty) (hinj : ∀ A ∈ K, Function.Injective A) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ A ∈ K, ∀ v : E, σ * ‖v‖ ≤ ‖A v‖ := by
  have hs : (sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  have hc : Continuous (fun p : (E →L[ℝ] E) × E => ‖p.1 p.2‖) :=
    (continuous_fst.clm_apply continuous_snd).norm
  obtain ⟨p,hp,hmin⟩ := (hK.prod (isCompact_sphere (0 : E) 1)).exists_isMinOn
    (hne.prod hs) hc.continuousOn
  have hp1 : ‖p.2‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hp.2
  have hp0 : p.2 ≠ 0 := by intro h; simp [h] at hp1
  have hpos : 0 < ‖p.1 p.2‖ := norm_pos_iff.mpr (by
    intro h
    exact hp0 (hinj p.1 hp.1 (by simpa using h)))
  refine ⟨‖p.1 p.2‖, hpos, ?_⟩
  intro A hA v
  by_cases hv : v = 0
  · simp [hv]
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖)⁻¹ • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hvp, inv_mul_cancel₀ hvp.ne']
  have hm := hmin (show (A, (‖v‖)⁻¹ • v) ∈ K ×ˢ sphere (0 : E) 1 from
    ⟨hA, (by simpa [mem_sphere, dist_zero_right] using hu)⟩)
  change ‖p.1 p.2‖ ≤ ‖A ((‖v‖)⁻¹ • v)‖ at hm
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hvp] at hm
  have hh := mul_le_mul_of_nonneg_right hm hvp.le
  calc
    ‖p.1 p.2‖ * ‖v‖ ≤ (‖v‖⁻¹ * ‖A v‖) * ‖v‖ := hh
    _ = ‖A v‖ := by field_simp

/-- Finite exponent choices have a compact convex hull, in operator or matrix coordinates. -/
theorem finite_hull_compact {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    {s : Set V} (hs : s.Finite) : IsCompact (convexHull ℝ s) :=
  hs.isCompact_convexHull ℝ

/-- Applying the compact-family bound to secant matrices gives a global lower estimate.
The secant representation is explicit; integration of the Jacobian is a separate step. -/
theorem lower_bound_of_secants (R : E → E) (K : Set (E →L[ℝ] E))
    (hK : IsCompact K) (hne : K.Nonempty) (hinj : ∀ A ∈ K, Function.Injective A)
    (hsec : ∀ x y, ∃ A ∈ K, R x - R y = A (x-y)) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ x y, σ * ‖x-y‖ ≤ ‖R x-R y‖ := by
  obtain ⟨σ,hσ,hbound⟩ := uniform_lower_bound K hK hne hinj
  refine ⟨σ,hσ,fun x y => ?_⟩
  obtain ⟨A,hA,he⟩ := hsec x y
  rw [he]
  exact hbound A hA (x-y)

theorem injective_of_lower_bound (R : E → E) (σ : ℝ) (hσ : 0 < σ)
    (hb : ∀ x y, σ * ‖x-y‖ ≤ ‖R x-R y‖) : Function.Injective R := by
  intro x y hxy
  have h := hb x y
  rw [hxy, sub_self, norm_zero] at h
  have hn : ‖x-y‖ = 0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

end LeanMath.Papers.CompactJacobian
