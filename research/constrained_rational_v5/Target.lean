import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Fin.VecNotation
namespace PandrosionTarget
noncomputable def target (p : ℕ) (y : ℝ) := Real.tanh (Real.artanh y / p)
def H (p : ℕ) (y v : ℝ) := (1+y)*(1-v)^p-(1-y)*(1+v)^p

theorem lower_gate (p : ℕ) (hp : 0 < p) (y v : ℝ)
    (hy : y ∈ Set.Ioo (-1:ℝ) 1) (hv : v ∈ Set.Ioo (-1:ℝ) 1)
    (hh : 0 ≤ H p y v) : v ≤ target p y := by
  have hpy : (0:ℝ) < p := by exact_mod_cast hp
  have hvm : 0 < 1-v := by linarith [hv.2]
  have hym : 0 < 1-y := by linarith [hy.2]
  have hvp : 0 < (1+v)/(1-v) := div_pos (by linarith [hv.1]) hvm
  have hratio : ((1+v)/(1-v))^p ≤ (1+y)/(1-y) := by
    rw [div_pow]
    apply (div_le_div_iff₀ (pow_pos hvm p) hym).mpr
    dsimp [H] at hh
    nlinarith
  have hlog := Real.log_le_log (pow_pos hvp p) hratio
  rw [Real.log_pow] at hlog
  have hart : Real.artanh v ≤ Real.artanh y / p := by
    apply (le_div_iff₀ hpy).mpr
    rw [Real.artanh_eq_half_log ⟨hv.1.le,hv.2.le⟩,
      Real.artanh_eq_half_log ⟨hy.1.le,hy.2.le⟩]
    nlinarith
  apply (Real.artanh_le_artanh_iff hv ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩).mp
  simpa [target, Real.artanh_tanh] using hart

theorem upper_gate (p : ℕ) (hp : 0 < p) (y v : ℝ)
    (hy : y ∈ Set.Ioo (-1:ℝ) 1) (hv : v ∈ Set.Ioo (-1:ℝ) 1)
    (hh : H p y v ≤ 0) : target p y ≤ v := by
  have hpy : (0:ℝ) < p := by exact_mod_cast hp
  have hvm : 0 < 1-v := by linarith [hv.2]
  have hym : 0 < 1-y := by linarith [hy.2]
  have hyp : 0 < (1+y)/(1-y) := div_pos (by linarith [hy.1]) hym
  have hratio : (1+y)/(1-y) ≤ ((1+v)/(1-v))^p := by
    rw [div_pow]
    apply (div_le_div_iff₀ hym (pow_pos hvm p)).mpr
    dsimp [H] at hh
    nlinarith
  have hlog := Real.log_le_log hyp hratio
  rw [Real.log_pow] at hlog
  have hart : Real.artanh y / p ≤ Real.artanh v := by
    apply (div_le_iff₀ hpy).mpr
    rw [Real.artanh_eq_half_log ⟨hv.1.le,hv.2.le⟩,
      Real.artanh_eq_half_log ⟨hy.1.le,hy.2.le⟩]
    nlinarith
  apply (Real.artanh_le_artanh_iff ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩ hv).mp
  simpa [target, Real.artanh_tanh] using hart
#print axioms lower_gate
#print axioms upper_gate
end PandrosionTarget
namespace PandrosionTarget

theorem ratio_mem (N D : ℝ) (hd : 0 < D) (hm : 0 < D-N) (hp : 0 < D+N) :
    N/D ∈ Set.Ioo (-1:ℝ) 1 := by
  constructor
  · apply (lt_div_iff₀ hd).mpr; linarith
  · apply (div_lt_iff₀ hd).mpr; linarith

theorem H_ratio (p : ℕ) (y N D : ℝ) (hd : D ≠ 0) :
    H p y (N/D) = ((1+y)*(D-N)^p-(1-y)*(D+N)^p)/D^p := by
  have hm : 1-N/D = (D-N)/D := by field_simp
  have hp : 1+N/D = (D+N)/D := by field_simp
  rw [H, hm, hp, div_pow, div_pow]
  ring

theorem lower_ratio (p : ℕ) (hp : 0 < p) (y N D : ℝ)
    (hy : y ∈ Set.Ioo (-1:ℝ) 1) (hd : 0 < D) (hm : 0 < D-N) (hplus : 0 < D+N)
    (h : 0 ≤ (1+y)*(D-N)^p-(1-y)*(D+N)^p) : N/D ≤ target p y := by
  apply lower_gate p hp y (N/D) hy (ratio_mem N D hd hm hplus)
  rw [H_ratio p y N D hd.ne']
  exact div_nonneg h (pow_pos hd p).le

theorem upper_ratio (p : ℕ) (hp : 0 < p) (y N D : ℝ)
    (hy : y ∈ Set.Ioo (-1:ℝ) 1) (hd : 0 < D) (hm : 0 < D-N) (hplus : 0 < D+N)
    (h : (1+y)*(D-N)^p-(1-y)*(D+N)^p ≤ 0) : target p y ≤ N/D := by
  apply upper_gate p hp y (N/D) hy (ratio_mem N D hd hm hplus)
  rw [H_ratio p y N D hd.ne']
  exact div_nonpos_of_nonpos_of_nonneg h (pow_pos hd p).le
end PandrosionTarget
