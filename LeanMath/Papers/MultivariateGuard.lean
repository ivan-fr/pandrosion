import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

/-! Abstract global safeguard and eventual acceptance. The local candidate estimate is
an explicit hypothesis, not a claim that tensor reversion has been formalized. -/
noncomputable section
namespace LeanMath.Papers.MultivariateGuard
open Filter Function
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def fallback (R : E → E) (η : ℝ) (x : E) := x - η • R x

theorem fallback_lipschitz (R : E → E) (J : E → E →L[ℝ] E)
    (η : ℝ) (q : ℝ≥0) (hJ : ∀ x, HasFDerivAt R (J x) x)
    (hb : ∀ x, ‖ContinuousLinearMap.id ℝ E - η • J x‖ ≤ q) :
    LipschitzWith q (fallback R η) := by
  have hd : ∀ x, HasFDerivAt (fallback R η)
      (ContinuousLinearMap.id ℝ E - η • J x) x :=
    fun x => (hasFDerivAt_id x).sub ((hJ x).const_smul η)
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (hd x).differentiableAt)
  intro x
  rw [(hd x).fderiv]
  exact_mod_cast hb x

theorem fixed_iff_root (R : E → E) (η : ℝ) (hη : η ≠ 0) (x : E) :
    IsFixedPt (fallback R η) x ↔ R x = 0 := by
  change x - η • R x = x ↔ R x = 0
  rw [sub_eq_self, smul_eq_zero]
  simp [hη]

theorem exists_unique_root [CompleteSpace E] (R : E → E) (η : ℝ)
    (hη : η ≠ 0) (q : ℝ≥0) (hq : q < 1)
    (hS : LipschitzWith q (fallback R η)) : ∃! x, R x = 0 := by
  have hc : ContractingWith q (fallback R η) := ⟨hq, hS⟩
  refine ⟨hc.fixedPoint, (fixed_iff_root R η hη _).mp hc.fixedPoint_isFixedPt, ?_⟩
  intro y hy
  exact hc.fixedPoint_unique ((fixed_iff_root R η hη _).mpr hy)

/-- Residual/error equivalence follows from the fallback contraction itself. -/
theorem residual_bounds (R : E → E) (η : ℝ) (hη : 0 < η) (q : ℝ≥0)
    (hS : LipschitzWith q (fallback R η)) (z : E) (hz : R z = 0) (x : E) :
    (1 - (q : ℝ)) * ‖x-z‖ ≤ η * ‖R x‖ ∧
      η * ‖R x‖ ≤ (1 + (q : ℝ)) * ‖x-z‖ := by
  have hfix : fallback R η z = z := by simp [fallback, hz]
  have hs := hS.norm_sub_le x z
  rw [hfix] at hs
  have ha : x-z = η • R x + (fallback R η x-z) := by unfold fallback; abel
  have hb : η • R x = (x-z) - (fallback R η x-z) := by simp [fallback]
  have h1 := norm_add_le (η • R x) (fallback R η x-z)
  rw [← ha, norm_smul, Real.norm_eq_abs, abs_of_pos hη] at h1
  have h2 := norm_sub_le (x-z) (fallback R η x-z)
  rw [← hb, norm_smul, Real.norm_eq_abs, abs_of_pos hη] at h2
  constructor <;> nlinarith

variable {X : Type*} [MetricSpace X]

def accepted (r : X → ℝ) (N : X → X) (θ : ℝ) (x : X) := r (N x) ≤ θ * r x

def step (r : X → ℝ) (N S : X → X) (θ : ℝ) (x : X) : X := by
  classical
  exact if accepted r N θ x then N x else S x

theorem step_contracts (r : X → ℝ) (N S : X → X) (z : X)
    (m B q θ : ℝ) (hm : 0 < m) (hθ : 0 ≤ θ) (hbudget : θ * B ≤ q * m)
    (hl : ∀ x, m * dist x z ≤ r x) (hu : ∀ x, r x ≤ B * dist x z)
    (hs : ∀ x, dist (S x) z ≤ q * dist x z) (x : X) :
    dist (step r N S θ x) z ≤ q * dist x z := by
  unfold step
  split_ifs with ha
  · have h1 := hl (N x)
    have h2 := mul_le_mul_of_nonneg_left (hu x) hθ
    have h3 := mul_le_mul_of_nonneg_right hbudget (dist_nonneg (x := x) (y := z))
    change r (N x) ≤ θ * r x at ha
    nlinarith
  · exact hs x

theorem orbit_bound (f : X → X) (z x : X) (q : ℝ) (hq : 0 ≤ q)
    (hf : ∀ y, dist (f y) z ≤ q * dist y z) (n : ℕ) :
    dist (f^[n] x) z ≤ q^n * dist x z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply']
    calc
      dist (f (f^[n] x)) z ≤ q * dist (f^[n] x) z := hf _
      _ ≤ q * (q^n * dist x z) := mul_le_mul_of_nonneg_left ih hq
      _ = q^(n+1) * dist x z := by ring

theorem orbit_converges (f : X → X) (z x : X) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hf : ∀ y, dist (f y) z ≤ q * dist y z) :
    Tendsto (fun n => f^[n] x) atTop (𝓝 z) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const (dist x z)
  have he : ∀ᶠ n : ℕ in atTop, q^n * dist x z < ε :=
    (tendsto_order.mp ht).2 ε (by simpa using hε)
  obtain ⟨K, hK⟩ := eventually_atTop.mp he
  exact ⟨K, fun n hn => (orbit_bound f z x q hq hf n).trans_lt (hK n hn)⟩

/-- A local residual bound of any integer order > 1 implies eventual acceptance
along every convergent sequence. Exact roots are covered without division by error. -/
theorem eventual_acceptance (r : X → ℝ) (N : X → X) (z : X)
    (u : ℕ → X) (m θ C δ : ℝ) (k : ℕ) (hk : 0 < k)
    (hm : 0 < m) (hθ : 0 < θ) (hδ : 0 < δ)
    (hl : ∀ x, m * dist x z ≤ r x)
    (hlocal : ∀ x, dist x z < δ → r (N x) ≤ C * dist x z ^ (k+1))
    (hu : Tendsto u atTop (𝓝 z)) :
    ∃ K : ℕ, ∀ n ≥ K, accepted r N θ (u n) := by
  have hd : Tendsto (fun n => dist (u n) z) atTop (𝓝 0) := by
    simpa using hu.dist (tendsto_const_nhds (x := z))
  have hp : Tendsto (fun n => C * dist (u n) z ^ k) atTop (𝓝 0) := by
    simpa [zero_pow (Nat.ne_of_gt hk)] using (hd.pow k).const_mul C
  have he : ∀ᶠ n : ℕ in atTop, dist (u n) z < δ :=
    (tendsto_order.mp hd).2 δ hδ
  have hb : ∀ᶠ n : ℕ in atTop, C * dist (u n) z ^ k < θ * m :=
    (tendsto_order.mp hp).2 (θ * m) (mul_pos hθ hm)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (he.and hb)
  refine ⟨K, fun n hn => ?_⟩
  have h := hK n hn
  have h1 := hlocal (u n) h.1
  have h2 := mul_le_mul_of_nonneg_right h.2.le (dist_nonneg (x := u n) (y := z))
  have h3 := mul_le_mul_of_nonneg_left (hl (u n)) hθ.le
  unfold accepted
  rw [pow_succ] at h1
  nlinarith

theorem eventual_candidate (r : X → ℝ) (N S : X → X) (z x : X)
    (m B q θ C δ : ℝ) (k : ℕ) (hk : 0 < k)
    (hm : 0 < m) (hθ : 0 < θ) (hδ : 0 < δ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hbudget : θ * B ≤ q * m)
    (hl : ∀ y, m * dist y z ≤ r y) (hu : ∀ y, r y ≤ B * dist y z)
    (hs : ∀ y, dist (S y) z ≤ q * dist y z)
    (hlocal : ∀ y, dist y z < δ → r (N y) ≤ C * dist y z ^ (k+1)) :
    ∃ K : ℕ, ∀ n ≥ K,
      (step r N S θ)^[n+1] x = N ((step r N S θ)^[n] x) := by
  have hc := step_contracts r N S z m B q θ hm hθ.le hbudget hl hu hs
  have ht := orbit_converges (step r N S θ) z x q hq hq1 hc
  obtain ⟨K,hK⟩ := eventual_acceptance r N z _ m θ C δ k hk hm hθ hδ hl hlocal ht
  refine ⟨K, fun n hn => ?_⟩
  rw [iterate_succ_apply']
  simp only [step, if_pos (hK n hn)]

/-- Once accepted in the local region, the candidate's residual order transfers to error. -/
theorem accepted_local_order (r : X → ℝ) (N S : X → X) (z x : X)
    (m θ C δ : ℝ) (p : ℕ) (hm : 0 < m)
    (hl : ∀ y, m * dist y z ≤ r y)
    (hlocal : ∀ y, dist y z < δ → r (N y) ≤ C * dist y z ^ p)
    (hx : dist x z < δ) (ha : accepted r N θ x) :
    dist (step r N S θ x) z ≤ (C / m) * dist x z ^ p := by
  simp only [step, if_pos ha]
  have h := (hl (N x)).trans (hlocal x hx)
  calc
    dist (N x) z ≤ (C * dist x z ^ p) / m :=
      (le_div_iff₀ hm).mpr (by nlinarith)
    _ = (C / m) * dist x z ^ p := by ring

end LeanMath.Papers.MultivariateGuard
