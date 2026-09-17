import LeanMath.Papers.WidthLocal
import LeanMath.Papers.AnalyticLimitFactor

/-! Full quadratic width expansions printed in the v14, with cubic remainders. -/
noncomputable section
namespace LeanMath.Papers.V14WidthRemainders
open Real Filter Asymptotics
open scoped Topology
open LeanMath.Papers.RealBracket LeanMath.Papers.RealBracket.WidthLocal

/-- An analytic leading limit supplies a remainder one degree higher. -/
theorem leading_remainder (f : ℝ → ℝ) (n : ℕ) (c : ℝ) (ha : AnalyticAt ℝ f 0)
    (ht : Tendsto (fun x : ℝ => f x/x^n) (𝓝[≠] 0) (𝓝 c)) :
    (fun x => f x-c*x^n) =O[𝓝 0] (fun x => x^(n+1)) := by
  obtain ⟨B,hB,he⟩ := AnalyticLimitFactor.expansion_of_limit f n c ha ht
  apply (BranchTaylor.analytic_remainder_bigO B (n+1) hB).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [he] with x hx
  linarith

theorem full_analytic (p : ℝ) (hp : 1<p) : AnalyticAt ℝ (full p) 0 := by
  unfold full
  fun_prop (disch := norm_num <;> linarith)

theorem upper_analytic (p : ℝ) (hp : 1<p) : AnalyticAt ℝ (upperError p) 0 := by
  unfold upperError
  fun_prop (disch := norm_num <;> linarith)

theorem full_remainder (p : ℝ) (hp : 1<p) :
    (fun t : ℝ => full p t-(p-1)^2/p^2*t^2) =O[𝓝 0] (fun t => t^3) :=
  leading_remainder _ 2 _ (full_analytic p hp) (full_order_two p hp)

theorem upper_remainder (p : ℝ) (hp : 1<p) :
    (fun t : ℝ => upperError p t-(p-1)^2/(2*p^2)*t^2) =O[𝓝 0] (fun t => t^3) :=
  leading_remainder _ 2 _ (upper_analytic p hp) (upper_order_two p hp)

/-- The expansion for the actual logarithmic width log(L/D). -/
theorem bilateral_width_remainder (p : ℝ) (hp : 1<p) :
    (fun t : ℝ => log (upper p (1+t)/lower p (1+t))-(p-1)^2/p^2*t^2)
      =O[𝓝 0] (fun t => t^3) := by
  apply (full_remainder p hp).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [Ioi_mem_nhds (by norm_num : (-1:ℝ)<0)] with t ht
  change -1<t at ht
  rw [full_eq_width p t hp ht,log_div (upper_pos p (1+t) hp (by linarith)).ne'
    (lower_pos p (1+t) hp (by linarith)).ne']

/-- The expansion for the actual upper endpoint's logarithmic root error. -/
theorem upper_endpoint_remainder (p : ℝ) (hp : 1<p) :
    (fun t : ℝ => log (upper p (1+t))-log (1+t)/p-(p-1)^2/(2*p^2)*t^2)
      =O[𝓝 0] (fun t => t^3) := by
  apply (upper_remainder p hp).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [Ioi_mem_nhds (by norm_num : (-1:ℝ)<0)] with t ht
  change -1<t at ht
  rw [log_upper p (1+t) hp (by linarith)]
  rfl

end LeanMath.Papers.V14WidthRemainders
