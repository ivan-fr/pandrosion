import LeanMath.Papers.BilateralLocal
import LeanMath.Papers.BilateralRange
import LeanMath.Papers.IntervalIteration
import LeanMath.Papers.Hybrid

noncomputable section
namespace LeanMath.Papers.RealBracket.Local
open Real Filter Set Function
open scoped Topology

def radius (p : ℝ) := log (1+1/sqrt p)/p

theorem radius_pos (p : ℝ) (hp : 0 < p) : 0 < radius p := by
  exact div_pos (log_pos (by linarith [one_div_pos.mpr (sqrt_pos_of_pos hp)])) hp

theorem error_zero (p : ℝ) (hp : 1 < p) : error p 0=0 := by
  simp [error,center_one p hp]

theorem error_odd (p e : ℝ) (hp : 1 < p) : error p (-e)= -error p e := by
  have he : exp (-p*(-e))=(exp (-p*e))⁻¹ := by rw [←exp_neg]; congr 1; ring
  unfold error
  rw [he,center_reciprocal p _ hp (exp_pos _),log_inv]
  ring

theorem error_continuous (p e : ℝ) (hp : 1 < p) : ContinuousAt (error p) e := by
  have hf : ContinuousAt (fun e : ℝ => exp (-p*e)) e := by fun_prop
  have hg := (continuousAt_center p _ hp (exp_pos (-p*e))).comp (f := fun e : ℝ => exp (-p*e)) hf
  exact continuousAt_id.add (hg.log (center_pos p _ hp (exp_pos _)).ne')

theorem negative_cell_step (p e : ℝ) (hp : 3 ≤ p) (he : -radius p ≤ e) (he0 : e < 0) :
    e < error p e ∧ error p e < 0 := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  let R := exp (-p*e)
  have hR : 1 < R := by
    dsimp [R]
    exact one_lt_exp_iff.mpr (mul_pos_of_neg_of_neg (by linarith) he0)
  have hR0 : 0 < R := by linarith
  have hrad : p*radius p=log (1+1/sqrt p) := by unfold radius; field_simp
  have hlog : -p*e ≤ log (1+1/sqrt p) := by nlinarith
  have hbound : R ≤ 1+1/sqrt p := by
    have h := exp_le_exp.mpr hlog
    rwa [exp_log (by positivity : 0 < 1+1/sqrt p)] at h
  have hpr : sqrt p*(R-1) ≤ 1 := by
    have h := (le_div_iff₀ (sqrt_pos_of_pos hp0)).mp
      (show R-1 ≤ 1/sqrt p by linarith)
    nlinarith
  have hq : 0 ≤ sqrt p*(R-1) := by positivity
  have hsq : (sqrt p*(R-1))^2 ≤ 1 := by nlinarith
  have hcell : p*(R-1)^2 ≤ 1 := by
    simpa only [mul_pow,sq_sqrt hp0.le] using hsq
  have hlo := center_above_one_on_cell p R hp hR hcell
  have hhi := center_below_root p R (by linarith) hR
  have hl := (log_lt_log_iff (by norm_num : (0:ℝ)<1) (center_pos p R hp1 hR0)).mpr hlo
  have hh := (log_lt_log_iff (center_pos p R hp1 hR0) (rpow_pos_of_pos hR0 _)).mpr hhi
  have hrootlog : log (R^(1/p))= -e := by
    rw [log_rpow hR0]
    dsimp [R]
    rw [log_exp]
    field_simp
  rw [hrootlog] at hh
  simp only [log_one] at hl
  change e < e+log (center p R) ∧ e+log (center p R) < 0
  constructor <;> linarith

theorem positive_cell_step (p e : ℝ) (hp : 3 ≤ p) (he : e ≤ radius p) (he0 : 0 < e) :
    0 < error p e ∧ error p e < e := by
  have h := negative_cell_step p (-e) hp (by linarith) (by linarith)
  rw [error_odd p e (by linarith)] at h
  constructor <;> linarith [h.1,h.2]

theorem cell_invariant (p e : ℝ) (hp : 3 ≤ p) (he : |e| ≤ radius p) :
    |error p e| ≤ radius p := by
  obtain ⟨hlo,hhi⟩ := abs_le.mp he
  rcases lt_trichotomy e 0 with h | h | h
  · have hh := negative_cell_step p e hp hlo h
    rw [abs_of_neg hh.2]
    linarith [hh.1]
  · subst e
    rw [error_zero p (by linarith),abs_zero]
    exact (radius_pos p (by linarith)).le
  · have hh := positive_cell_step p e hp hhi h
    rw [abs_of_pos hh.1]
    linarith [hh.2]

theorem cell_convergence (p e : ℝ) (hp : 3 ≤ p) (he : |e| ≤ radius p) :
    Tendsto (fun n : ℕ => (error p)^[n] e) atTop (𝓝 0) := by
  have hrad := radius_pos p (by linarith)
  apply IntervalIteration.converge (error p) (-radius p) (radius p) 0 e
    ⟨by linarith,hrad.le⟩ (abs_le.mp he)
  · exact fun t _ => error_continuous p t (by linarith)
  · exact error_zero p (by linarith)
  · intro t ht h
    have hh := negative_cell_step p t hp ht.1 h
    exact ⟨hh.1,hh.2.le⟩
  · intro t ht h
    have hh := positive_cell_step p t hp ht.2 h
    exact ⟨hh.1.le,hh.2⟩

theorem error_two (e : ℝ) : error 2 e=0 := by
  unfold error
  rw [square_root_exact _ (exp_pos _),log_sqrt (exp_pos _).le,log_exp]
  ring

theorem quadratic_local_convergence (e : ℝ) :
    Tendsto (fun n : ℕ => (error 2)^[n] e) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have he : (fun n : ℕ => (error 2)^[n+1] e)=(fun _ : ℕ => (0:ℝ)) := by
    funext n
    rw [iterate_succ_apply',error_two]
  rw [he]
  exact tendsto_const_nhds

theorem dyadic_center_convergence (p s : ℕ) (hp : 2 ≤ p) (e : ℝ) :
    Tendsto (fun n : ℕ =>
      (Hybrid.step (error p) (Dyadic.rho p (Dyadic.denominator p s)) (radius p))^[n] e)
      atTop (𝓝 0) := by
  have hb := Dyadic.dyadic_strict_bound p s (by omega)
  have hpow : (1:ℝ) ≤ 2^(s+1) := one_le_pow₀ (by norm_num)
  have hrho : |Dyadic.rho p (Dyadic.denominator p s)| < 1 :=
    hb.trans_le ((div_le_one (by positivity)).mpr hpow)
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  apply Hybrid.converge _ _ _ e hrho (radius_pos p hp0)
  · intro t ht
    by_cases h2 : p=2
    · subst p
      norm_num only [Nat.cast_ofNat] at ht ⊢
      rw [error_two,abs_zero]
      exact (radius_pos 2 (by norm_num)).le
    · have hp3 : (3:ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
      exact cell_invariant p t hp3 ht
  · intro t ht
    by_cases h2 : p=2
    · subst p
      exact quadratic_local_convergence t
    · have hp3 : (3:ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
      exact cell_convergence p t hp3 ht

end LeanMath.Papers.RealBracket.Local
