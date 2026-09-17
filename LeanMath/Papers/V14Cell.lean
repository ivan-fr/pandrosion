import LeanMath.Papers.V14Local
import LeanMath.Papers.BilateralHybrid

/-! Ordered exact corrections on the entry cell of Theorem 9.5. -/
noncomputable section
namespace LeanMath.Papers.V14Cell
open Real Set Filter
open scoped Topology
open LeanMath.Papers.Cayley LeanMath.Papers.V14Local LeanMath.Papers.V14Coefficients
open LeanMath.Papers.RealBracket

theorem Q_positive_le_Q9 (i : Index) (a y : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hy : 0 < y) :
    0 < Q i a y ∧ Q i a y ≤ Q9 a y := by
  obtain ⟨h3,h5,h7,h9⟩ := polynomial_ordering a y ha0 ha1 hy
  cases i with
  | five => exact ⟨h3,(h5.trans (h7.trans h9)).le⟩
  | seven => exact ⟨h3.trans h5,(h7.trans h9).le⟩
  | nine => exact ⟨(h3.trans h5).trans h7,h9.le⟩
  | eleven => exact ⟨((h3.trans h5).trans h7).trans h9,le_rfl⟩

theorem Q_mem (i : Index) (a y : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hy : |y| ≤ 1/4) :
    Q i a y ∈ Ioo (-1) 1 := by
  have hb := V14Comparison.Q9_mem a |y| ha0 ha1 (by simpa using hy)
  rcases lt_trichotomy y 0 with h | h | h
  · have hq := Q_positive_le_Q9 i a (-y) ha0 ha1 (by linarith)
    rw [abs_of_neg h] at hb
    rw [Q_odd] at hq
    exact ⟨by linarith [hb.2,hq.2],by linarith [hq.1]⟩
  · subst y; simp [Q_zero]
  · have hq := Q_positive_le_Q9 i a y ha0 ha1 h
    rw [abs_of_pos h] at hb
    exact ⟨by linarith [hq.1],hq.2.trans_lt hb.2⟩

theorem coordinate_cell (p R : ℝ) (hp : 3 ≤ p) (hR : 1 < R)
    (hcell : p*(R-1)^2 ≤ 1) : 0 < chi R ∧ chi R ≤ 1/4 := by
  have hs : 3*(R-1)^2 ≤ 1 := by
    nlinarith [mul_nonneg (show 0 ≤ p-3 by linarith) (sq_nonneg (R-1))]
  have hRmax : R ≤ 5/3 := by nlinarith
  unfold chi
  exact ⟨div_pos (by linarith) (by linarith),
    (div_le_iff₀ (by linarith : 0 < R+1)).mpr (by linarith)⟩

/-- Every member lies strictly between the center and the root on the upper cell. -/
theorem correction_bounds (i : Index) (p R : ℝ) (hp : 3 ≤ p) (hR : 1 < R)
    (hcell : p*(R-1)^2 ≤ 1) :
    1 < center p R ∧ center p R < correction i p R ∧ correction i p R < R^(1/p) := by
  have hp2 : 2 < p := by linarith
  have hR0 : 0 < R := by linarith
  have ha := V14Defect.a_mem p hp2
  have hy := coordinate_cell p R hp hR hcell
  have hab : |chi R| ≤ 1/4 := by rw [abs_of_pos hy.1]; exact hy.2
  have hq := Q_positive_le_Q9 i _ _ ha.1 ha.2 hy.1
  have hqm := Q_mem i _ _ ha.1 ha.2 hab
  have hdef := V14Comparison.Q9_below_exact_defect p _ hp2 hy.1 hy.2
  have hdmem : V14Defect.defectCoordinate p (chi R) ∈ Ioo (-1) 1 :=
    ⟨neg_one_lt_tanh _,tanh_lt_one _⟩
  have hlow : 1 < unchi (Q i (V14Defect.a p) (chi R)) := by
    unfold unchi
    apply (lt_div_iff₀ (by linarith [hqm.2])).mpr
    linarith [hq.1]
  have hhigh : unchi (Q i (V14Defect.a p) (chi R)) <
      unchi (V14Defect.defectCoordinate p (chi R)) :=
    strictMonoOn_one_add_div_one_sub hqm hdmem (hq.2.trans_lt hdef)
  have hG := center_pos p R (by linarith) hR0
  have hex := V14Defect.exact_correction p (chi R) hp2 (chi_mem R hR0)
  rw [unchi_chi R hR0] at hex
  refine ⟨center_above_one_on_cell p R hp hR hcell,?_,?_⟩
  · unfold correction
    nlinarith [mul_lt_mul_of_pos_left hlow hG]
  · unfold correction
    rw [← hex]
    exact mul_lt_mul_of_pos_left hhigh hG

/-- Equation 9.22's chain between the four successive corrections. -/
theorem corrections_ordered (p R : ℝ) (hp : 3 ≤ p) (hR : 1 < R)
    (hcell : p*(R-1)^2 ≤ 1) :
    correction .five p R < correction .seven p R ∧
    correction .seven p R < correction .nine p R ∧
    correction .nine p R < correction .eleven p R := by
  have hp2 : 2 < p := by linarith
  have hR0 : 0 < R := by linarith
  have ha := V14Defect.a_mem p hp2
  have hy := coordinate_cell p R hp hR hcell
  have hab : |chi R| ≤ 1/4 := by rw [abs_of_pos hy.1]; exact hy.2
  obtain ⟨_,h5,h7,h9⟩ := polynomial_ordering _ _ ha.1 ha.2 hy.1
  have hG := center_pos p R (by linarith) hR0
  have hm := fun i => Q_mem i _ _ ha.1 ha.2 hab
  exact ⟨mul_lt_mul_of_pos_left (strictMonoOn_one_add_div_one_sub (hm .five) (hm .seven) h5) hG,
    mul_lt_mul_of_pos_left (strictMonoOn_one_add_div_one_sub (hm .seven) (hm .nine) h7) hG,
    mul_lt_mul_of_pos_left (strictMonoOn_one_add_div_one_sub (hm .nine) (hm .eleven) h9) hG⟩


/-- The paper's logarithmic entry radius implies its upper residual cell. -/
theorem upper_residual_cell (p e : ℝ) (hp : 3 ≤ p)
    (he : -Local.radius p ≤ e) (he0 : e < 0) :
    1 < exp (-p*e) ∧ p*(exp (-p*e)-1)^2 ≤ 1 := by
  have hp0 : 0 < p := by linarith
  have hrad : p*Local.radius p=log (1+1/sqrt p) := by unfold Local.radius; field_simp
  have hlog : -p*e ≤ log (1+1/sqrt p) := by nlinarith
  have hbound : exp (-p*e) ≤ 1+1/sqrt p := by
    have h := exp_le_exp.mpr hlog
    rwa [exp_log (by positivity : 0 < 1+1/sqrt p)] at h
  have hR : 1 < exp (-p*e) := one_lt_exp_iff.mpr (mul_pos_of_neg_of_neg (by linarith) he0)
  have hpr : sqrt p*(exp (-p*e)-1) ≤ 1 := by
    have h := (le_div_iff₀ (sqrt_pos_of_pos hp0)).mp
      (show exp (-p*e)-1 ≤ 1/sqrt p by linarith)
    nlinarith
  have hq : 0 ≤ sqrt p*(exp (-p*e)-1) := by positivity
  have hsq : (sqrt p*(exp (-p*e)-1))^2 ≤ 1 := by nlinarith
  exact ⟨hR,by simpa only [mul_pow,sq_sqrt hp0.le] using hsq⟩

theorem error_zero (i : Index) (p : ℝ) (hp : 2 < p) : rootLogError i p 0 = 0 := by
  simp [rootLogError,correction,chi,Q_zero,unchi,center_one p (by linarith)]

theorem coordinate_odd (p e : ℝ) : errorCoordinate p (-e) = -errorCoordinate p e := by
  have he : exp (-p*(-e))=(exp (-p*e))⁻¹ := by rw [← exp_neg]; congr 1; ring
  unfold errorCoordinate
  rw [he,chi_inv _ (exp_pos _)]

theorem error_odd (i : Index) (p e : ℝ) (hp : 2 < p) : rootLogError i p (-e) = -rootLogError i p e := by
  have he : exp (-p*(-e))=(exp (-p*e))⁻¹ := by rw [← exp_neg]; congr 1; ring
  unfold rootLogError
  rw [he,correction_reciprocal i p _ hp (exp_pos _),log_inv]
  ring

theorem negative_cell_step (i : Index) (p e : ℝ) (hp : 3 ≤ p)
    (he : -Local.radius p ≤ e) (he0 : e < 0) :
    e < rootLogError i p e ∧ rootLogError i p e < 0 := by
  have hcell := upper_residual_cell p e hp he he0
  obtain ⟨hG,hlo,hhi⟩ := correction_bounds i p _ hp hcell.1 hcell.2
  have hC : 0 < correction i p (exp (-p*e)) := by linarith
  have hloglo : 0 < log (correction i p (exp (-p*e))) := log_pos (by linarith)
  have hloghi := (log_lt_log_iff hC (rpow_pos_of_pos (exp_pos (-p*e)) (1/p))).mpr hhi
  rw [log_rpow (exp_pos _),log_exp] at hloghi
  have hp0 : p ≠ 0 := by linarith
  have hroot : 1/p*(-p*e) = -e := by field_simp
  rw [hroot] at hloghi
  unfold rootLogError
  exact ⟨by linarith,by linarith⟩

theorem positive_cell_step (i : Index) (p e : ℝ) (hp : 3 ≤ p)
    (he : e ≤ Local.radius p) (he0 : 0 < e) :
    0 < rootLogError i p e ∧ rootLogError i p e < e := by
  have h := negative_cell_step i p (-e) hp (by linarith) (by linarith)
  rw [error_odd i p e (by linarith)] at h
  exact ⟨by linarith [h.2],by linarith [h.1]⟩

theorem coordinate_small (p e : ℝ) (hp : 3 ≤ p) (he : |e| ≤ Local.radius p) :
    |errorCoordinate p e| ≤ 1/4 := by
  obtain ⟨hel,heh⟩ := abs_le.mp he
  rcases lt_trichotomy e 0 with h | h | h
  · have hc := upper_residual_cell p e hp hel h
    have hy := coordinate_cell p _ hp hc.1 hc.2
    change |chi (exp (-p*e))| ≤ 1/4
    rw [abs_of_pos hy.1]; exact hy.2
  · subst e; simp [errorCoordinate_zero]
  · have hc := upper_residual_cell p (-e) hp (by linarith) (by linarith)
    have hy := coordinate_cell p _ hp hc.1 hc.2
    have hh : |errorCoordinate p (-e)| ≤ 1/4 := by unfold errorCoordinate; rw [abs_of_pos hy.1]; exact hy.2
    simpa only [coordinate_odd,abs_neg] using hh

theorem error_continuous (i : Index) (p e : ℝ) (hp : 3 ≤ p)
    (he : |e| ≤ Local.radius p) : ContinuousAt (rootLogError i p) e := by
  have hp2 : 2 < p := by linarith
  have ha := V14Defect.a_mem p hp2
  have hm := Q_mem i _ _ ha.1 ha.2 (coordinate_small p e hp he)
  have hce : ContinuousAt (errorCoordinate p) e := by
    unfold errorCoordinate chi
    fun_prop (disch := positivity)
  have hcq := (Q_continuous i (V14Defect.a p)).continuousAt.comp hce
  have hcu : ContinuousAt (fun e => unchi (Q i (V14Defect.a p) (errorCoordinate p e))) e := by
    unfold unchi
    exact (continuousAt_const.add hcq).div (continuousAt_const.sub hcq) (by linarith [hm.2])
  have hcg := (continuousAt_center p (exp (-p*e)) (by linarith) (exp_pos _)).comp (f:=fun e : ℝ => exp (-p*e))
    (show ContinuousAt (fun e : ℝ => exp (-p*e)) e by fun_prop)
  have hpos := mul_pos (center_pos p _ (by linarith) (exp_pos (-p*e))) (unchi_pos _ hm)
  exact continuousAt_id.add ((hcg.mul hcu).log hpos.ne')

/-- The cell is invariant for each actual center-defect correction. -/
theorem cell_invariant (i : Index) (p e : ℝ) (hp : 3 ≤ p) (he : |e| ≤ Local.radius p) :
    |rootLogError i p e| ≤ Local.radius p := by
  obtain ⟨hel,heh⟩ := abs_le.mp he
  rcases lt_trichotomy e 0 with h | h | h
  · have hh := negative_cell_step i p e hp hel h
    rw [abs_of_neg hh.2]; linarith [hh.1]
  · subst e
    rw [error_zero i p (by linarith),abs_zero]
    exact (Local.radius_pos p (by linarith)).le
  · have hh := positive_cell_step i p e hp heh h
    rw [abs_of_pos hh.1]; linarith [hh.2]

/-- The convergence assertion of Theorem 9.5, in logarithmic root error. -/
theorem cell_convergence (i : Index) (p e : ℝ) (hp : 3 ≤ p) (he : |e| ≤ Local.radius p) :
    Tendsto (fun n : ℕ => (rootLogError i p)^[n] e) atTop (𝓝 0) := by
  have hr := Local.radius_pos p (by linarith)
  apply LeanMath.Papers.IntervalIteration.converge (rootLogError i p)
    (-Local.radius p) (Local.radius p) 0 e ⟨by linarith,hr.le⟩ (abs_le.mp he)
  · intro t ht; exact error_continuous i p t hp (abs_le.mpr ht)
  · exact error_zero i p (by linarith)
  · intro t ht h
    have hh := negative_cell_step i p t hp ht.1 h
    exact ⟨hh.1,hh.2.le⟩
  · intro t ht h
    have hh := positive_cell_step i p t hp ht.2 h
    exact ⟨hh.1.le,hh.2⟩

/-- Corollary 9.6: global convergence of the guarded logarithmic error recurrence. -/
theorem global_convergence (i : Index) (p s : ℕ) (hp : 3 ≤ p) (e : ℝ) :
    Tendsto (fun n : ℕ =>
      (LeanMath.Papers.Hybrid.step (rootLogError i p)
        (LeanMath.Papers.Dyadic.rho p (LeanMath.Papers.Dyadic.denominator p s))
        (Local.radius p))^[n] e) atTop (𝓝 0) := by
  have hb := LeanMath.Papers.Dyadic.dyadic_strict_bound p s (by omega)
  have hpow : (1:ℝ) ≤ 2^(s+1) := one_le_pow₀ (by norm_num)
  have hrho : |LeanMath.Papers.Dyadic.rho p (LeanMath.Papers.Dyadic.denominator p s)| < 1 :=
    hb.trans_le ((div_le_one (by positivity)).mpr hpow)
  have hp3 : (3:ℝ) ≤ p := by exact_mod_cast hp
  exact LeanMath.Papers.Hybrid.converge _ _ _ e hrho
    (Local.radius_pos p (by linarith)) (fun t ht => cell_invariant i p t hp3 ht)
    (fun t ht => cell_convergence i p t hp3 ht)

end LeanMath.Papers.V14Cell
