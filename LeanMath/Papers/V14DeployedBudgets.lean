import LeanMath.Papers.V14DeployedAccumulation
import LeanMath.Papers.V14DeployedCoefficients

/-! Finite prefix and budget facts. Per-interval derivative certificates are still required. -/
namespace LeanMath.Papers.V14DeployedBudgets
open LeanMath.Papers.V14AccumulationCheck LeanMath.Papers.V14DeployedAccumulation
open LeanMath.Papers.V14DeployedCoefficients

theorem prefix31 : ∀ i<256,
    |LeanMath.Papers.V14BernsteinCertificate.prefixSum (fun j => (j:ℚ)*width31) (fun j => (bounds31 j).1) i+
      min 0 (bounds31 i).1*((i+1:ℕ)*width31-(i:ℚ)*width31)|≤eta31 ∧
    |LeanMath.Papers.V14BernsteinCertificate.prefixSum (fun j => (j:ℚ)*width31) (fun j => (bounds31 j).2) i+
      max 0 (bounds31 i).2*((i+1:ℕ)*width31-(i:ℚ)*width31)|≤eta31 :=
by
  simpa only [bounds31, eta_scaling31] using scaled_prefix_checks width31 scale cap31 (by norm_num [width31]) (by norm_num [scale]) integerBounds31 256 check31

theorem eta31_range : 0≤eta31 ∧ eta31<1 := by norm_num [eta31]

theorem budget31 : (eta31:ℝ)/(1-eta31)<(450/100)/(2:ℝ)^52 := by
  norm_num [eta31]

theorem endpoint31 : ((256:ℚ)*width31:ℝ)=rho31 := by
  norm_num [width31,rho31]

theorem prefix63 : ∀ i<256,
    |LeanMath.Papers.V14BernsteinCertificate.prefixSum (fun j => (j:ℚ)*width63) (fun j => (bounds63 j).1) i+
      min 0 (bounds63 i).1*((i+1:ℕ)*width63-(i:ℚ)*width63)|≤eta63 ∧
    |LeanMath.Papers.V14BernsteinCertificate.prefixSum (fun j => (j:ℚ)*width63) (fun j => (bounds63 j).2) i+
      max 0 (bounds63 i).2*((i+1:ℕ)*width63-(i:ℚ)*width63)|≤eta63 :=
by
  simpa only [bounds63, eta_scaling63] using scaled_prefix_checks width63 scale cap63 (by norm_num [width63]) (by norm_num [scale]) integerBounds63 256 check63

theorem eta63_range : 0≤eta63 ∧ eta63<1 := by norm_num [eta63]

theorem budget63 : (eta63:ℝ)/(1-eta63)<(513/100)/(2:ℝ)^52 := by
  norm_num [eta63]

theorem endpoint63 : ((256:ℚ)*width63:ℝ)=rho63 := by
  norm_num [width63,rho63]

theorem prefix127 : ∀ i<256,
    |LeanMath.Papers.V14BernsteinCertificate.prefixSum (fun j => (j:ℚ)*width127) (fun j => (bounds127 j).1) i+
      min 0 (bounds127 i).1*((i+1:ℕ)*width127-(i:ℚ)*width127)|≤eta127 ∧
    |LeanMath.Papers.V14BernsteinCertificate.prefixSum (fun j => (j:ℚ)*width127) (fun j => (bounds127 j).2) i+
      max 0 (bounds127 i).2*((i+1:ℕ)*width127-(i:ℚ)*width127)|≤eta127 :=
by
  simpa only [bounds127, eta_scaling127] using scaled_prefix_checks width127 scale cap127 (by norm_num [width127]) (by norm_num [scale]) integerBounds127 256 check127

theorem eta127_range : 0≤eta127 ∧ eta127<1 := by norm_num [eta127]

theorem budget127 : (eta127:ℝ)/(1-eta127)<(60/100)/(2:ℝ)^52 := by
  norm_num [eta127]

theorem endpoint127 : ((256:ℚ)*width127:ℝ)=rho127 := by
  norm_num [width127,rho127]

theorem prefix255 : ∀ i<256,
    |LeanMath.Papers.V14BernsteinCertificate.prefixSum (fun j => (j:ℚ)*width255) (fun j => (bounds255 j).1) i+
      min 0 (bounds255 i).1*((i+1:ℕ)*width255-(i:ℚ)*width255)|≤eta255 ∧
    |LeanMath.Papers.V14BernsteinCertificate.prefixSum (fun j => (j:ℚ)*width255) (fun j => (bounds255 j).2) i+
      max 0 (bounds255 i).2*((i+1:ℕ)*width255-(i:ℚ)*width255)|≤eta255 :=
by
  simpa only [bounds255, eta_scaling255] using scaled_prefix_checks width255 scale cap255 (by norm_num [width255]) (by norm_num [scale]) integerBounds255 256 check255

theorem eta255_range : 0≤eta255 ∧ eta255<1 := by norm_num [eta255]

theorem budget255 : (eta255:ℝ)/(1-eta255)<(63/100)/(2:ℝ)^52 := by
  norm_num [eta255]

theorem endpoint255 : ((256:ℚ)*width255:ℝ)=rho255 := by
  norm_num [width255,rho255]

end LeanMath.Papers.V14DeployedBudgets
