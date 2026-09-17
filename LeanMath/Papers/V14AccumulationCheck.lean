import LeanMath.Papers.V14BernsteinCertificate

/-! A finite rational checker for the accumulated derivative bounds. -/
namespace LeanMath.Papers.V14AccumulationCheck
open Finset

def partialSum (w : ℚ) (v : ℕ → ℚ) (start n : ℕ) : ℚ :=
  ∑ j ∈ range n, v (start+j)*w

def check (w eta : ℚ) (b : ℕ → ℚ×ℚ) (start : ℕ) : ℕ → ℚ → ℚ → Bool
  | 0, _, _ => true
  | n+1, L, U =>
    decide (|L+min 0 (b start).1*w|≤eta ∧ |U+max 0 (b start).2*w|≤eta) &&
      check w eta b (start+1) n (L+(b start).1*w) (U+(b start).2*w)

theorem partialSum_succ (w : ℚ) (v : ℕ → ℚ) (start n : ℕ) :
    partialSum w v start (n+1)=v start*w+partialSum w v (start+1) n := by
  unfold partialSum
  rw [sum_range_succ']
  simp only [Nat.add_zero]
  have he : (fun j => v (start+(j+1))*w)=(fun j => v (start+1+j)*w) := by
    funext j; congr 2 <;> omega
  rw [he]
  ring

theorem check_sound (w eta : ℚ) (b : ℕ → ℚ×ℚ) (start n : ℕ) (L U : ℚ)
    (hc : check w eta b start n L U=true) :
    ∀ i<n,
      |L+partialSum w (fun j => (b j).1) start i+min 0 (b (start+i)).1*w|≤eta ∧
      |U+partialSum w (fun j => (b j).2) start i+max 0 (b (start+i)).2*w|≤eta := by
  induction n generalizing start L U with
  | zero => intro i hi; omega
  | succ n ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
    intro i hi
    cases i with
    | zero => simpa [partialSum] using hc.1
    | succ i =>
      have hh := ih (start+1) (L+(b start).1*w) (U+(b start).2*w) hc.2 i (by omega)
      rw [partialSum_succ,partialSum_succ]
      convert hh using 1 <;> congr 2 <;> first | omega | ring

/-- The accepted checker closes exactly the prefix inequalities used by the uniform theorem. -/
theorem uniform_prefix_checks (w eta : ℚ) (b : ℕ → ℚ×ℚ) (n : ℕ)
    (hc : check w eta b 0 n 0 0=true) :
    ∀ i<n,
      |LeanMath.Papers.V14BernsteinCertificate.prefixSum (fun j => (j:ℚ)*w) (fun j => (b j).1) i+
        min 0 (b i).1*((i+1:ℕ)*w-(i:ℚ)*w)|≤eta ∧
      |LeanMath.Papers.V14BernsteinCertificate.prefixSum (fun j => (j:ℚ)*w) (fun j => (b j).2) i+
        max 0 (b i).2*((i+1:ℕ)*w-(i:ℚ)*w)|≤eta := by
  intro i hi
  have hh := check_sound w eta b 0 n 0 0 hc i hi
  have hs : ∀ j : ℕ, ((j+1:ℕ):ℚ)*w-(j:ℚ)*w=w := by intro j; push_cast; ring
  simpa only [LeanMath.Papers.V14BernsteinCertificate.prefixSum,partialSum,Nat.zero_add,zero_add,hs] using hh

theorem prefix_scaling (w s : ℚ) (v : ℕ → ℚ) (i : ℕ) :
    LeanMath.Papers.V14BernsteinCertificate.prefixSum (fun j => (j:ℚ)*w) (fun j => s*v j) i =
      (s*w)*partialSum 1 v 0 i := by
  unfold LeanMath.Papers.V14BernsteinCertificate.prefixSum partialSum
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  push_cast
  ring

/-- Dyadic bounds share a denominator. Factoring it out leaves small integer-sized checks. -/
theorem scaled_prefix_checks (w s E : ℚ) (hw : 0≤w) (hs : 0≤s) (b : ℕ → ℚ×ℚ) (n : ℕ)
    (hc : check 1 E b 0 n 0 0=true) :
    ∀ i<n,
      |LeanMath.Papers.V14BernsteinCertificate.prefixSum (fun j => (j:ℚ)*w) (fun j => s*(b j).1) i+
        min 0 (s*(b i).1)*((i+1:ℕ)*w-(i:ℚ)*w)|≤s*w*E ∧
      |LeanMath.Papers.V14BernsteinCertificate.prefixSum (fun j => (j:ℚ)*w) (fun j => s*(b j).2) i+
        max 0 (s*(b i).2)*((i+1:ℕ)*w-(i:ℚ)*w)|≤s*w*E := by
  intro i hi
  have hh := check_sound 1 E b 0 n 0 0 hc i hi
  simp only [zero_add,Nat.zero_add,mul_one] at hh
  have hmin : min 0 (s*(b i).1)=s*min 0 (b i).1 := by
    simpa using (mul_min_of_nonneg 0 (b i).1 hs).symm
  have hmax : max 0 (s*(b i).2)=s*max 0 (b i).2 := by
    simpa using (mul_max_of_nonneg 0 (b i).2 hs).symm
  have hwidth : ((i+1:ℕ):ℚ)*w-(i:ℚ)*w=w := by push_cast; ring
  rw [prefix_scaling,prefix_scaling,hmin,hmax,hwidth]
  have hl := mul_le_mul_of_nonneg_left hh.1 (mul_nonneg hs hw)
  have hu := mul_le_mul_of_nonneg_left hh.2 (mul_nonneg hs hw)
  constructor
  · calc
      _ = (s*w)*|partialSum 1 (fun j => (b j).1) 0 i + min 0 (b i).1| := by
        rw [show (s*w)*partialSum 1 (fun j => (b j).1) 0 i + s*min 0 (b i).1*w = (s*w)*(partialSum 1 (fun j => (b j).1) 0 i + min 0 (b i).1) by ring]
        rw [abs_mul, abs_of_nonneg (mul_nonneg hs hw)]
      _ ≤ _ := hl
  · calc
      _ = (s*w)*|partialSum 1 (fun j => (b j).2) 0 i + max 0 (b i).2| := by
        rw [show (s*w)*partialSum 1 (fun j => (b j).2) 0 i + s*max 0 (b i).2*w = (s*w)*(partialSum 1 (fun j => (b j).2) 0 i + max 0 (b i).2) by ring]
        rw [abs_mul, abs_of_nonneg (mul_nonneg hs hw)]
      _ ≤ _ := hu

end LeanMath.Papers.V14AccumulationCheck
