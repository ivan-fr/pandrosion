import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! Exact real geometry of dyadic geometric subdivision and its Padé readout.
No floating-point or electrical-error assertion is made by these theorems. -/
noncomputable section
namespace LeanMath.Papers.GeometricSubdivision
open Real Set

def P (t z : ℝ) : ℝ := 12 + 6 * (2+t)*z + (t+1)*(t+2)*z^2
def Q (t z : ℝ) : ℝ := 12 + 6 * (2-t)*z + (t-1)*(t-2)*z^2
def R (t z : ℝ) : ℝ := P t z / Q t z

theorem P_pos {t z : ℝ} (ht : 0 ≤ t) (hz : 0 ≤ z) : 0 < P t z := by
 unfold P
 positivity

theorem Q_pos {t z : ℝ} (ht : t ≤ 1) (hz : 0 ≤ z) : 0 < Q t z := by
 have h1 : 0 ≤ (t-1)*(t-2) := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
 have h2 : 0 ≤ 6*(2-t)*z := mul_nonneg (by linarith) hz
 unfold Q
 nlinarith [mul_nonneg h1 (sq_nonneg z)]

theorem residual (t z : ℝ) :
 (1+z)*((6*(2+t)+2*(t+1)*(t+2)*z)*Q t z - P t z*(6*(2-t)+2*(t-1)*(t-2)*z)) - t*P t z*Q t z
 = -t*(1-t^2)*(4-t^2)*z^4 := by unfold P Q; ring

theorem residual_nonpos {t z : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
 -t*(1-t^2)*(4-t^2)*z^4 ≤ 0 := by
 have hsq : t^2 ≤ 1 := by nlinarith [mul_nonneg ht (sub_nonneg.mpr ht1)]
 have h1 : 0 ≤ 1-t^2 := by linarith
 have h4 : 0 ≤ 4-t^2 := by linarith
 have : 0 ≤ t*(1-t^2)*(4-t^2)*z^4 := mul_nonneg (mul_nonneg (mul_nonneg ht h1) h4) (by positivity)
 nlinarith

private theorem dP (t z : ℝ) : HasDerivAt (P t) (6*(2+t)+2*(t+1)*(t+2)*z) z := by
 convert ((hasDerivAt_const z (12:ℝ)).add (((hasDerivAt_id z).const_mul (6*(2+t))))).add (((hasDerivAt_id z).pow 2).const_mul ((t+1)*(t+2))) using 1 <;> first | rfl | (simp only [id_eq]; ring)
private theorem dQ (t z : ℝ) : HasDerivAt (Q t) (6*(2-t)+2*(t-1)*(t-2)*z) z := by
 convert ((hasDerivAt_const z (12:ℝ)).add (((hasDerivAt_id z).const_mul (6*(2-t))))).add (((hasDerivAt_id z).pow 2).const_mul ((t-1)*(t-2))) using 1 <;> first | rfl | (simp only [id_eq]; ring)

def logRatio (t z : ℝ) : ℝ := log (P t z) - log (Q t z) - t*log (1+z)
private theorem dlogRatio {t z : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hz : 0 ≤ z) :
 HasDerivAt (logRatio t)
 ((6*(2+t)+2*(t+1)*(t+2)*z)/P t z -
 (6*(2-t)+2*(t-1)*(t-2)*z)/Q t z - t/(1+z)) z := by
 have hbase : HasDerivAt (fun x : ℝ => 1+x) 1 z := by simpa using (hasDerivAt_id z).const_add 1
 have hlast := (hbase.log (by linarith : 1+z ≠ 0)).const_mul t
 convert (((dP t z).log (P_pos ht hz).ne').sub ((dQ t z).log (Q_pos ht1 hz).ne')).sub hlast using 1 <;> first | rfl | (simp only [one_div]; ring)


/-- Global lower bound, including both endpoint weights. -/
theorem pade_le_rpow {t z : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hz : 0 ≤ z) :
 R t z ≤ (1+z)^t := by
 have hd := fun x (hx : 0 ≤ x) => dlogRatio ht ht1 hx
 have ha : AntitoneOn (logRatio t) (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx0 : 0 ≤ x := interior_subset hx
    rw [(hd x hx0).deriv]
    have hp := P_pos ht hx0
    have hq := Q_pos ht1 hx0
    have hres := residual_nonpos (z := x) ht ht1
    rw [← residual t x] at hres
    have he : (6*(2+t)+2*(t+1)*(t+2)*x)/P t x - (6*(2-t)+2*(t-1)*(t-2)*x)/Q t x - t/(1+x) =
      ((1+x)*((6*(2+t)+2*(t+1)*(t+2)*x)*Q t x-P t x*(6*(2-t)+2*(t-1)*(t-2)*x))-t*P t x*Q t x)/(P t x*Q t x*(1+x)) := by
      field_simp [hp.ne', hq.ne', (show 1+x ≠ 0 by linarith)]
    rw [he]
    exact div_nonpos_of_nonpos_of_nonneg hres (by positivity)

 have h := ha (show (0:ℝ) ∈ Ici 0 by simp) hz hz
 have h0 : logRatio t 0 = 0 := by simp [logRatio, P, Q]
 rw [h0] at h
 have hp := P_pos ht hz
 have hq := Q_pos ht1 hz
 apply (log_le_log_iff (div_pos hp hq) (rpow_pos_of_pos (by linarith : 0 < 1+z) t)).mp
 rw [log_rpow (by linarith : 0 < 1+z)]
 change log (P t z / Q t z) ≤ _
 rw [log_div hp.ne' hq.ne']
 dsimp [logRatio] at h
 linarith

/-- Complementary weights turn the same lower Padé formula into an upper bound. -/
theorem pade_bracket {t z : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hz : 0 ≤ z) :
 R t z ≤ (1+z)^t ∧ (1+z)^t ≤ (1+z)/R (1-t) z := by
 refine ⟨pade_le_rpow ht ht1 hz, ?_⟩
 have hc := pade_le_rpow (t := 1-t) (by linarith) (by linarith) hz
 have hr : 0 < R (1-t) z := div_pos (P_pos (by linarith) hz) (Q_pos (by linarith) hz)
 apply (le_div_iff₀ hr).mpr
 calc
  (1+z)^t * R (1-t) z ≤ (1+z)^t * (1+z)^(1-t) := mul_le_mul_of_nonneg_left hc (rpow_nonneg (by linarith) _)
  _ = 1+z := by rw [← rpow_add (by linarith : 0 < 1+z)]; simp

/-- Polynomial contact of order five: Q times the degree-four Taylor polynomial minus P
is divisible by z^5, with an explicit polynomial remainder. -/
theorem contact_order_five (t z : ℝ) :
 Q t z * (1+t*z+t*(t-1)/2*z^2+t*(t-1)*(t-2)/6*z^3+t*(t-1)*(t-2)*(t-3)/24*z^4) - P t z
 = z^5 * (-t*(t-7)*(t-2)^2*(t-1)/12 + t*(t-1)^2*(t-2)^2*(t-3)/24*z) := by
 unfold P Q
 ring

/-- The subtraction-free Padé increment used for a centered electrical readout. -/
theorem centered_increment {t z : ℝ} (ht : t ≤ 1) (hz : 0 ≤ z) :
 R t z - 1 = t * (6*z*(2+z)/Q t z) := by
 have h := (Q_pos ht hz).ne'
 unfold R
 field_simp
 unfold P Q
 ring

/-- A mean-proportional construction gives the exponent midpoint. -/
theorem midpoint_length {X : ℝ} (hX : 0 < X) (a b : ℝ) :
 sqrt (X^a * X^b) = X^((a+b)/2) := by
 rw [← rpow_add hX, sqrt_eq_rpow, ← rpow_mul hX.le]
 congr 1
 ring

/-- Each branch retains theta and halves the exponent width. -/
theorem subdivision_step {a b theta : ℝ} (ha : a ≤ theta) (hb : theta ≤ b) :
 (if theta ≤ (a+b)/2 then
    a ≤ theta ∧ theta ≤ (a+b)/2 ∧ (a+b)/2-a=(b-a)/2
  else (a+b)/2 ≤ theta ∧ theta ≤ b ∧ b-(a+b)/2=(b-a)/2) := by
 split_ifs with h
 · exact ⟨ha,h,by ring⟩
 · exact ⟨(lt_of_not_ge h).le,hb,by ring⟩

theorem weight_mem {a b theta : ℝ} (hab : a < b) (ha : a ≤ theta) (hb : theta ≤ b) :
 0 ≤ (theta-a)/(b-a) ∧ (theta-a)/(b-a) ≤ 1 := by
 constructor
 · exact div_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hab.le)
 · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith)

/-- The position weight recovers the original real exponent exactly. -/
theorem exponent_identity {a b theta : ℝ} (hab : a < b) :
 (1-(theta-a)/(b-a))*a + ((theta-a)/(b-a))*b = theta := by
 field_simp [(sub_pos.mpr hab).ne']
 ring

/-- Transfer the Padé bracket to the geometric mean of any positive ordered rails. -/
theorem scaled_pade_bracket {A B t : ℝ} (hA : 0 < A) (hAB : A ≤ B)
 (ht : 0 ≤ t) (ht1 : t ≤ 1) :
 A*R t (B/A-1) ≤ A*(B/A)^t ∧ A*(B/A)^t ≤ B/R (1-t) (B/A-1) := by
 have hz : 0 ≤ B/A-1 := by apply sub_nonneg.mpr; exact (le_div_iff₀ hA).mpr (by simpa)
 have h := pade_bracket ht ht1 hz
 have he : 1+(B/A-1) = B/A := by ring
 rw [he] at h
 constructor
 · exact mul_le_mul_of_nonneg_left h.1 hA.le
 · calc
    A*(B/A)^t ≤ A*((B/A)/R (1-t) (B/A-1)) := mul_le_mul_of_nonneg_left h.2 hA.le
    _ = B/R (1-t) (B/A-1) := by rw [← mul_div_assoc, mul_div_cancel₀ B hA.ne']

/-- Exact relative width of the fifth-order bracket; no cancellation in this expression. -/
theorem pade_width {t z : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hz : 0 ≤ z) :
 ((1+z)/R (1-t) z)/R t z - 1 =
 t*(1-t)*(2-t)*(1+t)*z^5/(P t z*P (1-t) z) := by
 have hp := (P_pos ht hz).ne'
 have hpc := (P_pos (show 0 ≤ 1-t by linarith) hz).ne'
 have hq := (Q_pos ht1 hz).ne'
 have hqc := (Q_pos (show 1-t ≤ 1 by linarith) hz).ne'
 unfold R
 field_simp
 unfold P Q
 ring

/-- Uniform, explicit order-five width estimate for every real weight. -/
theorem pade_width_bound {t z : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (hz : 0 ≤ z) :
 ((1+z)/R (1-t) z)/R t z - 1 ≤ z^5/256 := by
 rw [pade_width ht ht1 hz]
 have hP : ∀ s : ℝ, 0 ≤ s → 12 ≤ P s z := by
  intro s hs
  have h : 0 ≤ 6*(2+s)*z+(s+1)*(s+2)*z^2 := by positivity
  unfold P
  linarith
 have hp := hP t ht
 have hpc := hP (1-t) (by linarith)
 have hd : 144 ≤ P t z*P (1-t) z := by
  nlinarith [mul_nonneg (show 0 ≤ P t z-12 by linarith) (show 0 ≤ P (1-t) z-12 by linarith)]
 have hu0 : 0 ≤ t*(1-t) := mul_nonneg ht (by linarith)
 have hu1 : t*(1-t) ≤ 1/4 := by nlinarith [sq_nonneg (t-1/2)]
 have hu2 : (t*(1-t))^2 ≤ 1/16 := by
  nlinarith [mul_nonneg (show 0 ≤ 1/4-t*(1-t) by linarith) (show 0 ≤ 1/4+t*(1-t) by linarith)]
 have hc : t*(1-t)*(2-t)*(1+t) ≤ 9/16 := by nlinarith
 have hn := mul_le_mul_of_nonneg_right hc (pow_nonneg hz 5)
 apply (div_le_iff₀ (by linarith : 0 < P t z*P (1-t) z)).mpr
 have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ z^5/256 by positivity)
 nlinarith

/-- Rail interpolation equals the requested power, with no rationality hypothesis. -/
theorem rail_power {X a b theta : ℝ} (hX : 0 < X) (hab : a < b) :
 X^a * (X^b/X^a)^((theta-a)/(b-a)) = X^theta := by
 rw [← rpow_sub hX, ← rpow_mul hX.le, ← rpow_add hX]
 congr 1
 have he := exponent_identity (theta := theta) hab
 nlinarith

/-- End-to-end Padé root bracket for real p and an enclosing exponent interval. -/
theorem real_root_bracket {X p a b : ℝ} (hX : 1 ≤ X) (_hp : 1 ≤ p)
 (hab : a < b) (ha : a ≤ 1/p) (hb : 1/p ≤ b) :
 let t := (1/p-a)/(b-a)
 let z := X^b/X^a-1
 X^a * R t z ≤ X^(1/p) ∧ X^(1/p) ≤ X^b/R (1-t) z := by
 dsimp
 have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
 have ht := weight_mem hab ha hb
 have hAB : X^a ≤ X^b := rpow_le_rpow_of_exponent_le hX hab.le
 have h := scaled_pade_bracket (rpow_pos_of_pos hX0 a) hAB ht.1 ht.2
 rw [rail_power hX0 hab] at h
 exact h

/-- The actual dyadic interval controller. Equality selects the left half. -/
def interval (theta : ℝ) : ℕ → ℝ × ℝ
 | 0 => (0,1)
 | n+1 => let i := interval theta n
          if theta ≤ (i.1+i.2)/2 then (i.1,(i.1+i.2)/2)
          else ((i.1+i.2)/2,i.2)

/-- All depths retain the requested exponent and have exactly dyadic width. -/
theorem interval_spec {theta : ℝ} (ht : 0 ≤ theta) (ht1 : theta ≤ 1) (n : ℕ) :
 (interval theta n).1 ≤ theta ∧ theta ≤ (interval theta n).2 ∧
 (interval theta n).2-(interval theta n).1=(1/2:ℝ)^n := by
 induction n with
 | zero => simpa [interval] using And.intro ht ht1
 | succ n ih =>
   simp only [interval]
   split_ifs with h
   · refine ⟨ih.1,h,?_⟩
     dsimp
     rw [pow_succ, ← ih.2.2]
     ring
   · refine ⟨(lt_of_not_ge h).le,ih.2.1,?_⟩
     dsimp
     rw [pow_succ, ← ih.2.2]
     ring

/-- The normalized rail gap depends on X and depth only, not on the real exponent. -/
theorem gap_independent_of_exponent {X theta : ℝ} (hX : 0 < X)
 (ht : 0 ≤ theta) (ht1 : theta ≤ 1) (n : ℕ) :
 X^(interval theta n).2 / X^(interval theta n).1 - 1 = X^((1/2:ℝ)^n)-1 := by
 rw [← rpow_sub hX, (interval_spec ht ht1 n).2.2]

/-- Root enclosure for every finite subdivision depth and every real p ≥ 1. -/
theorem constructed_root_bracket {X p : ℝ} (hX : 1 ≤ X) (hp : 1 ≤ p) (n : ℕ) :
 let i := interval (1/p) n
 let t := (1/p-i.1)/(i.2-i.1)
 let z := X^i.2/X^i.1-1
 X^i.1 * R t z ≤ X^(1/p) ∧ X^(1/p) ≤ X^i.2/R (1-t) z := by
 have hp0 : 0 < p := by linarith
 have ht : 0 ≤ 1/p := by positivity
 have ht1 : 1/p ≤ 1 := (div_le_one hp0).mpr hp
 have hs := interval_spec ht ht1 n
 have hab : (interval (1/p) n).1 < (interval (1/p) n).2 := by
  have hpos : (0:ℝ) < (1/2:ℝ)^n := by positivity
  linarith [hs.2.2]
 exact real_root_bracket hX hp hab hs.1 hs.2.1

end LeanMath.Papers.GeometricSubdivision
