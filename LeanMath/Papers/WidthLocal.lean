import LeanMath.Papers.WidthComparison
import LeanMath.Papers.CayleyLocal
import LeanMath.Papers.LocalOrder

noncomputable section
namespace LeanMath.Papers.RealBracket.WidthLocal
open Real Filter Set
open scoped Topology

def full (p d : ℝ) := (p-1)*(log ((p-1)*(1+d)+1)+log (1+d+p-1)-log (1+d)-2*log p)
def upperError (p d : ℝ) := (2-p)*log (1+d)+(p-1)*(log ((p-1)*(1+d)+1)-log p)-log (1+d)/p
def fullFactor (p d : ℝ) := (p-1)^2*(2+d)/((1+d)*((p-1)*(1+d)+1)*(1+d+p-1))
def upperFactor (p d : ℝ) := (p-1)^2/(p*(1+d)*((p-1)*(1+d)+1))

theorem full_zero (p : ℝ) : full p 0=0 := by
  simp [full,show (1:ℝ)+p-1=p by ring,show log p+log p-2*log p=0 by ring]

theorem upper_zero (p : ℝ) : upperError p 0=0 := by simp [upperError]

theorem full_derivative (p d : ℝ) (hp : 1 < p) (hd : -1 < d) :
    HasDerivAt (full p) (d*fullFactor p d) d := by
  have hR : 0 < 1+d := by linarith
  have hA : 0 < (p-1)*(1+d)+1 := by positivity
  have hB : 0 < 1+d+p-1 := by linarith
  have hr := (hasDerivAt_id d).const_add 1
  have ha := ((hr.const_mul (p-1)).add_const 1).log hA.ne'
  have hb := ((hr.add_const p).sub_const 1).log hB.ne'
  convert! ((((ha.add hb).sub (hr.log hR.ne')).sub_const (2*log p)).const_mul (p-1)) using 1
  unfold fullFactor
  simp only [id_eq]
  generalize heR : 1+d=R at *
  generalize heA : (p-1)*R+1=A at *
  generalize heB : R+p-1=B at *
  field_simp [hR.ne',hA.ne',hB.ne']
  subst A B R
  ring

theorem upper_derivative (p d : ℝ) (hp : 1 < p) (hd : -1 < d) :
    HasDerivAt (upperError p) (d*upperFactor p d) d := by
  have hp0 : p ≠ 0 := by linarith
  have hR : 0 < 1+d := by linarith
  have hA : 0 < (p-1)*(1+d)+1 := by positivity
  have hr := (hasDerivAt_id d).const_add 1
  have ha := ((hr.const_mul (p-1)).add_const 1).log hA.ne'
  convert! (((hr.log hR.ne').const_mul (2-p)).add
    ((ha.sub_const (log p)).const_mul (p-1))).sub ((hr.log hR.ne').div_const p) using 1
  unfold upperFactor
  simp only [id_eq]
  generalize heR : 1+d=R at *
  generalize heA : (p-1)*R+1=A at *
  field_simp [hR.ne',hA.ne',hp0]
  subst A R
  ring

theorem factors_continuous (p : ℝ) (hp : 1 < p) :
    ContinuousAt (fullFactor p) 0 ∧ ContinuousAt (upperFactor p) 0 := by
  have hp0 : 0 < p := by linarith
  have hA : 0 < p-1+1 := by linarith
  have hB : 0 < 1+p-1 := by linarith
  constructor
  · unfold fullFactor
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simp only [add_zero,mul_one,one_mul]
      positivity
  · unfold upperFactor
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simp only [add_zero,mul_one]
      positivity

theorem full_order_two (p : ℝ) (hp : 1 < p) :
    Tendsto (fun d : ℝ => full p d/d^2) (𝓝[≠] 0) (𝓝 ((p-1)^2/p^2)) := by
  have hd : ∀ᶠ d in 𝓝[≠] (0:ℝ), HasDerivAt (full p) (d^1*fullFactor p d) d := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (-1:ℝ)<0))] with d hd
    simpa using full_derivative p d hp hd
  have h := LocalOrder.from_derivative 1 (full p) (fullFactor p) (full_zero p)
    (full_derivative p 0 hp (by norm_num)).continuousAt (factors_continuous p hp).1 hd
  have he : fullFactor p 0/((1:ℝ)+1)=(p-1)^2/p^2 := by
    unfold fullFactor
    ring
  simpa only [Nat.cast_one,Nat.reduceAdd,he] using h

theorem upper_order_two (p : ℝ) (hp : 1 < p) :
    Tendsto (fun d : ℝ => upperError p d/d^2) (𝓝[≠] 0) (𝓝 ((p-1)^2/(2*p^2))) := by
  have hd : ∀ᶠ d in 𝓝[≠] (0:ℝ), HasDerivAt (upperError p) (d^1*upperFactor p d) d := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (-1:ℝ)<0))] with d hd
    simpa using upper_derivative p d hp hd
  have h := LocalOrder.from_derivative 1 (upperError p) (upperFactor p) (upper_zero p)
    (upper_derivative p 0 hp (by norm_num)).continuousAt (factors_continuous p hp).2 hd
  have he : upperFactor p 0/((1:ℝ)+1)=(p-1)^2/(2*p^2) := by
    unfold upperFactor
    ring
  simpa only [Nat.cast_one,Nat.reduceAdd,he] using h

/-- The seventh-order Cayley error is negligible on the quadratic width scale. -/
theorem cayley_negligible (p : ℝ) (hp : 1 < p) :
    Tendsto (fun d : ℝ => Cayley.logGap p (d/(2+d))/d^2) (𝓝[≠] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun d : ℝ => d/(2+d)) 0 :=
    continuousAt_id.div (continuousAt_const.add continuousAt_id) (by norm_num)
  have hne : ∀ᶠ d : ℝ in 𝓝[≠] 0, d ≠ 0 ∧ 2+d ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (-1:ℝ)<0))] with d hd hbound
    change -1 < d at hbound
    exact ⟨hd,by linarith⟩
  have ht : Tendsto (fun d : ℝ => d/(2+d)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [hne] with d hd
      exact div_ne_zero hd.1 hd.2
  have hf : ContinuousAt (fun d : ℝ => d^5/(2+d)^7) 0 :=
    (continuousAt_id.pow 5).div ((continuousAt_const.add continuousAt_id).pow 7) (by norm_num)
  have hz : Tendsto (fun d : ℝ => d^5/(2+d)^7) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hf.tendsto.mono_left nhdsWithin_le_nhds
  have hh := ((Cayley.gap_order_seven p hp).comp ht).mul hz
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [hne] with d hd
  dsimp only [Function.comp_def]
  field_simp [hd.1,hd.2]

/-- The explicit logarithmic expression is the original interval width. -/
theorem full_eq_width (p d : ℝ) (hp : 1 < p) (hd : -1 < d) :
    full p d=log (upper p (1+d))-log (lower p (1+d)) := by
  rw [log_upper p (1+d) hp (by linarith),log_lower p (1+d) hp (by linarith)]
  unfold full
  ring

theorem cayley_log_error (p d : ℝ) (hp : 1 < p) (hd : -1 < d) :
    Cayley.logGap p (d/(2+d))=log (Cayley.C₇ p (1+d))-log (1+d)/p := by
  have hR : 0 < 1+d := by linarith
  have he : Cayley.chi (1+d)=d/(2+d) := by unfold Cayley.chi; congr 1 <;> ring
  rw [←he]
  unfold Cayley.logGap
  rw [Cayley.logCoord_eq _ (Cayley.P₅_mem p _ hp (Cayley.chi_mem _ hR)),
    Cayley.logCoord_eq _ (Cayley.chi_mem _ hR),Cayley.unchi_chi _ hR]
  rfl

/-- The refined upper width tends to half the full width near the root. -/
theorem upper_width_ratio_limit (p : ℝ) (hp : 1 < p) :
    Tendsto (fun d : ℝ =>
      (log (upper p (1+d))-log (Cayley.C₇ p (1+d)))/
      (log (upper p (1+d))-log (lower p (1+d)))) (𝓝[≠] 0) (𝓝 (1/2)) := by
  have hden : (p-1)^2/p^2 ≠ 0 := by positivity
  have h := ((upper_order_two p hp).sub (cayley_negligible p hp)).div (full_order_two p hp) hden
  have he : ((p-1)^2/(2*p^2)-0)/((p-1)^2/p^2)=(1:ℝ)/2 := by
    have hp0 : p ≠ 0 := by linarith
    have hp1 : p-1 ≠ 0 := by linarith
    field_simp
    <;> ring
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (-1:ℝ)<0))] with d hd hbound
  change -1 < d at hbound
  dsimp only [Pi.div_apply]
  rw [←sub_div,div_div_div_cancel_right₀ (pow_ne_zero 2 hd)]
  rw [cayley_log_error p d hp hbound,full_eq_width p d hp hbound,
    log_upper p (1+d) hp (by linarith)]
  congr 1
  unfold upperError
  ring

/-- Two-sided local half-width law for the actual certified interval. -/
theorem width_ratio_limit (p : ℝ) (hp : 1 < p) :
    Tendsto (widthRatio p) (𝓝[≠] 1) (𝓝 (1/2)) := by
  have hu : Tendsto (fun d : ℝ => upperRatio p (1+d)) (𝓝[≠] 0) (𝓝 (1/2)) :=
    upper_width_ratio_limit p hp
  have hl : Tendsto (fun d : ℝ => 1-upperRatio p (1+d)) (𝓝[≠] 0) (𝓝 (1/2)) := by
    convert tendsto_const_nhds.sub hu using 1 <;> norm_num
  have hh : Tendsto (fun d : ℝ => widthRatio p (1+d)) (𝓝[≠] 0) (𝓝 (1/2)) :=
    hu.if' hl
  have ht : Tendsto (fun R : ℝ => R-1) (𝓝[≠] 1) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun R : ℝ => R-1) 1 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with R hR
      exact sub_ne_zero.mpr hR
  convert hh.comp ht using 1
  funext R
  dsimp only [Function.comp_def]
  congr 1
  ring

end LeanMath.Papers.RealBracket.WidthLocal
