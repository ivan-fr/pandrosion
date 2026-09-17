import LeanMath.Papers.CumulantPropagation
import Mathlib.Algebra.Polynomial.Eval.Degree

noncomputable section
namespace LeanMath.Papers.PolynomialPaths
open Real Polynomial Filter Set
open scoped Topology
open SeriesReversion AnalyticReversion

def CoeffAnalytic (P : ℝ → Polynomial ℝ) (r : ℝ) := ∀ j, AnalyticAt ℝ (fun x => (P x).coeff j) r

theorem path_C (a : ℝ → ℝ) (r : ℝ) (ha : AnalyticAt ℝ a r) :
    CoeffAnalytic (fun x => C (a x)) r := by
  intro j
  by_cases hj : j=0
  · simpa [Polynomial.coeff_C,hj] using ha
  · simp only [Polynomial.coeff_C,if_neg hj]
    exact analyticAt_const

theorem path_X (r : ℝ) : CoeffAnalytic (fun _ => (X : Polynomial ℝ)) r :=
  fun _ => analyticAt_const

theorem path_add (P Q : ℝ → Polynomial ℝ) (r : ℝ) (hP : CoeffAnalytic P r) (hQ : CoeffAnalytic Q r) :
    CoeffAnalytic (fun x => P x+Q x) r := by
  intro j
  simp only [Polynomial.coeff_add]
  exact (hP j).fun_add (hQ j)

theorem path_mul (P Q : ℝ → Polynomial ℝ) (r : ℝ) (hP : CoeffAnalytic P r) (hQ : CoeffAnalytic Q r) :
    CoeffAnalytic (fun x => P x*Q x) r := by
  intro j
  simp only [Polynomial.coeff_mul]
  exact Finset.analyticAt_fun_sum _ (fun ij _ => (hP ij.1).mul (hQ ij.2))

theorem jet_degree (a b c d e f : ℝ) : (jet a b c d e f).natDegree ≤ 6 := by
  unfold jet
  compute_degree!

/-- The full composition has degree at most 36, independently of its coefficients. -/
theorem composition_degree (a b c d e f : ℝ) :
    ((inverseJet a b c d e f).comp (jet a b c d e f)).natDegree < 37 := by
  have hi : (inverseJet a b c d e f).natDegree ≤ 6 := jet_degree _ _ _ _ _ _
  have hp := jet_degree a b c d e f
  have h : ((inverseJet a b c d e f).comp (jet a b c d e f)).natDegree ≤
      (inverseJet a b c d e f).natDegree*(jet a b c d e f).natDegree := Polynomial.natDegree_comp_le
  have hm : (inverseJet a b c d e f).natDegree*(jet a b c d e f).natDegree ≤ 6*6 := Nat.mul_le_mul hi hp
  omega

/-- Factor the first seven powers using a finite sum with a fixed degree bound. -/
theorem eval_tail (P : Polynomial ℝ) (hdeg : P.natDegree < 37)
    (hlo : ∀ j < 7, P.coeff j=(X : Polynomial ℝ).coeff j) (t : ℝ) :
    P.eval t-t=t^7*∑ j ∈ Finset.range 30, P.coeff (j+7)*t^j := by
  rw [Polynomial.eval_eq_sum_range' hdeg]
  rw [show 37=7+30 from rfl,Finset.sum_range_add]
  have hfirst : (∑ j ∈ Finset.range 7, P.coeff j*t^j)=t := by
    have he : (∑ j ∈ Finset.range 7, P.coeff j*t^j)=
        ∑ j ∈ Finset.range 7, (X : Polynomial ℝ).coeff j*t^j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hlo j (Finset.mem_range.mp hj)]
    rw [he]
    norm_num [Finset.sum_range_succ,Polynomial.coeff_X]
  rw [hfirst]
  rw [add_sub_cancel_left,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_comm 7 j,pow_add]
  ring

theorem path_jet (a b c d e f : ℝ → ℝ) (r : ℝ)
    (ha : AnalyticAt ℝ a r) (hb : AnalyticAt ℝ b r) (hc : AnalyticAt ℝ c r)
    (hd : AnalyticAt ℝ d r) (he : AnalyticAt ℝ e r) (hf : AnalyticAt ℝ f r) :
    CoeffAnalytic (fun x => jet (a x) (b x) (c x) (d x) (e x) (f x)) r := by
  unfold jet
  repeat' first | apply path_mul | apply path_add | apply path_C |
    exact path_X r | exact ha | exact hb | exact hc | exact hd | exact he | exact hf

set_option maxHeartbeats 0 in
theorem path_inverse_composition (a b c d e f : ℝ → ℝ) (r : ℝ)
    (ha : AnalyticAt ℝ a r) (hb : AnalyticAt ℝ b r) (hc : AnalyticAt ℝ c r)
    (hd : AnalyticAt ℝ d r) (he : AnalyticAt ℝ e r) (hf : AnalyticAt ℝ f r) (ha0 : a r ≠ 0) :
    CoeffAnalytic (fun x => (inverseJet (a x) (b x) (c x) (d x) (e x) (f x)).comp
      (jet (a x) (b x) (c x) (d x) (e x) (f x))) r := by
  have hP := path_jet a b c d e f r ha hb hc hd he hf
  have h1 : AnalyticAt ℝ (fun x => c1 (a x)) r := by unfold c1; fun_prop (disch := positivity)
  have h2 : AnalyticAt ℝ (fun x => c2 (a x) (b x)) r := by unfold c2; fun_prop (disch := positivity)
  have h3 : AnalyticAt ℝ (fun x => c3 (a x) (b x) (c x)) r := by unfold c3; fun_prop (disch := positivity)
  have h4 : AnalyticAt ℝ (fun x => c4 (a x) (b x) (c x) (d x)) r := by unfold c4; fun_prop (disch := positivity)
  have h5 : AnalyticAt ℝ (fun x => c5 (a x) (b x) (c x) (d x) (e x)) r := by unfold c5; fun_prop (disch := positivity)
  have h6 : AnalyticAt ℝ (fun x => c6 (a x) (b x) (c x) (d x) (e x) (f x)) r := by unfold c6; fun_prop (disch := positivity)
  unfold inverseJet
  unfold jet at hP
  simp only [jet,Polynomial.mul_comp,Polynomial.add_comp,Polynomial.X_comp,Polynomial.C_comp]
  have H6 := path_mul _ _ r hP (path_C _ r h6)
  have H5 := path_mul _ _ r hP (path_add _ _ r (path_C _ r h5) H6)
  have H4 := path_mul _ _ r hP (path_add _ _ r (path_C _ r h4) H5)
  have H3 := path_mul _ _ r hP (path_add _ _ r (path_C _ r h3) H4)
  have H2 := path_mul _ _ r hP (path_add _ _ r (path_C _ r h2) H3)
  exact path_mul _ _ r hP (path_add _ _ r (path_C _ r h1) H2)

end LeanMath.Papers.PolynomialPaths
