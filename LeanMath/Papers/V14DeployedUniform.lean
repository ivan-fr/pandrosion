import LeanMath.Papers.V14DeployedBudgets

/-! Concrete deployed error implications. The Segment witnesses are still required inputs. -/
noncomputable section
namespace LeanMath.Papers.V14DeployedUniform
open Polynomial
open LeanMath.Papers.V14DeployedCoefficients LeanMath.Papers.V14DeployedAccumulation
open LeanMath.Papers.V14DeployedBudgets LeanMath.Papers.V14BernsteinCertificate

theorem uniform31_of_segments
    (segments : ∀ (i : ℕ), i<256 → Segment
      (LeanMath.Papers.V14RationalCertificate.numerator A31 (A31.comp (-X)) 31)
      (LeanMath.Papers.V14RationalCertificate.denominator A31 (A31.comp (-X)) 31)
      ((i:ℚ)*width31) ((i+1:ℕ)*width31) (bounds31 i).1 (bounds31 i).2)
    (y : ℝ) (hy : |y|≤rho31) :
    |(A31.eval y/A31.eval (-y))/(LeanMath.Papers.Cayley.unchi y)^(1/(31:ℝ))-1| <
      (450/100)/(2:ℝ)^52 := by
  have hw : 0<width31 := by norm_num [width31]
  have hh := uniform_from_segments A31 31 (256*width31) eta31
    (fun i => (i:ℚ)*width31) (fun i => (bounds31 i).1) (fun i => (bounds31 i).2) 256
    (by norm_num) (by norm_num [width31]) eta31_range.1 eta31_range.2 (by norm_num)
    (by simp) (by norm_num)
    (by intro i hi; exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self i) hw)
    (by intro i hi; constructor
        · positivity
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hw.le)
    (by intro z hz; apply A31_positive z; norm_num [width31,rho31] at hz ⊢; exact hz)
    segments prefix31 y (by norm_num [width31,rho31] at hy ⊢; exact hy)
  exact hh.trans_lt budget31

theorem uniform63_of_segments
    (segments : ∀ (i : ℕ), i<256 → Segment
      (LeanMath.Papers.V14RationalCertificate.numerator A63 (A63.comp (-X)) 63)
      (LeanMath.Papers.V14RationalCertificate.denominator A63 (A63.comp (-X)) 63)
      ((i:ℚ)*width63) ((i+1:ℕ)*width63) (bounds63 i).1 (bounds63 i).2)
    (y : ℝ) (hy : |y|≤rho63) :
    |(A63.eval y/A63.eval (-y))/(LeanMath.Papers.Cayley.unchi y)^(1/(63:ℝ))-1| <
      (513/100)/(2:ℝ)^52 := by
  have hw : 0<width63 := by norm_num [width63]
  have hh := uniform_from_segments A63 63 (256*width63) eta63
    (fun i => (i:ℚ)*width63) (fun i => (bounds63 i).1) (fun i => (bounds63 i).2) 256
    (by norm_num) (by norm_num [width63]) eta63_range.1 eta63_range.2 (by norm_num)
    (by simp) (by norm_num)
    (by intro i hi; exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self i) hw)
    (by intro i hi; constructor
        · positivity
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hw.le)
    (by intro z hz; apply A63_positive z; norm_num [width63,rho63] at hz ⊢; exact hz)
    segments prefix63 y (by norm_num [width63,rho63] at hy ⊢; exact hy)
  exact hh.trans_lt budget63

theorem uniform127_of_segments
    (segments : ∀ (i : ℕ), i<256 → Segment
      (LeanMath.Papers.V14RationalCertificate.numerator A127 (A127.comp (-X)) 127)
      (LeanMath.Papers.V14RationalCertificate.denominator A127 (A127.comp (-X)) 127)
      ((i:ℚ)*width127) ((i+1:ℕ)*width127) (bounds127 i).1 (bounds127 i).2)
    (y : ℝ) (hy : |y|≤rho127) :
    |(A127.eval y/A127.eval (-y))/(LeanMath.Papers.Cayley.unchi y)^(1/(127:ℝ))-1| <
      (60/100)/(2:ℝ)^52 := by
  have hw : 0<width127 := by norm_num [width127]
  have hh := uniform_from_segments A127 127 (256*width127) eta127
    (fun i => (i:ℚ)*width127) (fun i => (bounds127 i).1) (fun i => (bounds127 i).2) 256
    (by norm_num) (by norm_num [width127]) eta127_range.1 eta127_range.2 (by norm_num)
    (by simp) (by norm_num)
    (by intro i hi; exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self i) hw)
    (by intro i hi; constructor
        · positivity
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hw.le)
    (by intro z hz; apply A127_positive z; norm_num [width127,rho127] at hz ⊢; exact hz)
    segments prefix127 y (by norm_num [width127,rho127] at hy ⊢; exact hy)
  exact hh.trans_lt budget127

theorem uniform255_of_segments
    (segments : ∀ (i : ℕ), i<256 → Segment
      (LeanMath.Papers.V14RationalCertificate.numerator A255 (A255.comp (-X)) 255)
      (LeanMath.Papers.V14RationalCertificate.denominator A255 (A255.comp (-X)) 255)
      ((i:ℚ)*width255) ((i+1:ℕ)*width255) (bounds255 i).1 (bounds255 i).2)
    (y : ℝ) (hy : |y|≤rho255) :
    |(A255.eval y/A255.eval (-y))/(LeanMath.Papers.Cayley.unchi y)^(1/(255:ℝ))-1| <
      (63/100)/(2:ℝ)^52 := by
  have hw : 0<width255 := by norm_num [width255]
  have hh := uniform_from_segments A255 255 (256*width255) eta255
    (fun i => (i:ℚ)*width255) (fun i => (bounds255 i).1) (fun i => (bounds255 i).2) 256
    (by norm_num) (by norm_num [width255]) eta255_range.1 eta255_range.2 (by norm_num)
    (by simp) (by norm_num)
    (by intro i hi; exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self i) hw)
    (by intro i hi; constructor
        · positivity
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hw.le)
    (by intro z hz; apply A255_positive z; norm_num [width255,rho255] at hz ⊢; exact hz)
    segments prefix255 y (by norm_num [width255,rho255] at hy ⊢; exact hy)
  exact hh.trans_lt budget255

end LeanMath.Papers.V14DeployedUniform
