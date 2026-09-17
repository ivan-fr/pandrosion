import LeanMath.Papers.Dyadic
import Mathlib.Topology.Basic

noncomputable section
namespace LeanMath.Papers.Hybrid
open Function Filter
open scoped Topology

def step (localStep : ℝ → ℝ) (ρ ε e : ℝ) : ℝ :=
  if |e| ≤ ε then localStep e else ρ*e

/-- The guarded algorithm must reach the local cell in finite time. -/
theorem finite_entry (f : ℝ → ℝ) (ρ ε e : ℝ) (hρ : |ρ| < 1) (hε : 0 < ε) :
    ∃ N : ℕ, |(step f ρ ε)^[N] e| ≤ ε := by
  by_contra! hn
  have heq : ∀ n : ℕ, (step f ρ ε)^[n] e=ρ^n*e := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [iterate_succ_apply']
      rw [step,if_neg (not_le.mpr (hn n)),ih,pow_succ]
      ring
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ρ) hρ).mul_const |e|
  have hev : ∀ᶠ n : ℕ in atTop, |ρ|^n*|e| < ε := by
    apply (tendsto_order.mp ht).2 ε
    simpa using hε
  obtain ⟨n,hn'⟩ := hev.exists
  have h := hn n
  rw [heq,abs_mul,abs_pow] at h
  linarith

/-- Invariance prevents any return to the fallback after entry. -/
theorem local_tail (f : ℝ → ℝ) (ρ ε e : ℝ)
    (hinv : ∀ t, |t| ≤ ε → |f t| ≤ ε) (he : |e| ≤ ε) :
    ∀ n : ℕ, (step f ρ ε)^[n] e=f^[n] e ∧ |f^[n] e| ≤ ε := by
  intro n
  induction n with
  | zero => exact ⟨rfl,he⟩
  | succ n ih =>
    rw [iterate_succ_apply',iterate_succ_apply',ih.1]
    exact ⟨if_pos ih.2,hinv _ ih.2⟩

theorem eventual_local (f : ℝ → ℝ) (ρ ε e : ℝ) (hρ : |ρ| < 1) (hε : 0 < ε)
    (hinv : ∀ t, |t| ≤ ε → |f t| ≤ ε) :
    ∃ N : ℕ, |(step f ρ ε)^[N] e| ≤ ε ∧
      ∀ n : ℕ, (step f ρ ε)^[n+N] e=f^[n] ((step f ρ ε)^[N] e) := by
  obtain ⟨N,hN⟩ := finite_entry f ρ ε e hρ hε
  refine ⟨N,hN,fun n => ?_⟩
  rw [iterate_add_apply]
  exact (local_tail f ρ ε _ hinv hN n).1

theorem permanent_entry (f : ℝ → ℝ) (ρ ε e : ℝ) (hρ : |ρ| < 1) (hε : 0 < ε)
    (hinv : ∀ t, |t| ≤ ε → |f t| ≤ ε) :
    ∃ N : ℕ, ∀ n : ℕ, |(step f ρ ε)^[n+N] e| ≤ ε := by
  obtain ⟨N,hN,ht⟩ := eventual_local f ρ ε e hρ hε hinv
  refine ⟨N,fun n => ?_⟩
  rw [ht]
  exact (local_tail f ρ ε _ hinv hN n).2

/-- A finite fallback prefix preserves the local convergence theorem. -/
theorem converge (f : ℝ → ℝ) (ρ ε e : ℝ) (hρ : |ρ| < 1) (hε : 0 < ε)
    (hinv : ∀ t, |t| ≤ ε → |f t| ≤ ε)
    (hlocal : ∀ t, |t| ≤ ε → Tendsto (fun n : ℕ => f^[n] t) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (step f ρ ε)^[n] e) atTop (𝓝 0) := by
  obtain ⟨N,hN,htail⟩ := eventual_local f ρ ε e hρ hε hinv
  have ht := hlocal _ hN
  have hs : Tendsto (fun n : ℕ => (step f ρ ε)^[n+N] e) atTop (𝓝 0) := by
    simpa only [htail] using ht
  exact (tendsto_add_atTop_iff_nat N).mp hs

end LeanMath.Papers.Hybrid
