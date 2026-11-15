import Mathlib

/-! # Deflation of the root zero (pandroots 0.6.0)

The solver writes `P = X^k * Q` with `Q(0) ≠ 0` (it drops the `k` trailing zero coefficients), reports the
root `0` with multiplicity `k` and radius zero, and solves `Q` alone.  It keeps the discs found for `Q`
only if each of them is proved to stay away from `0` (`‖z‖ > r`).

* `exists_X_pow_mul`: dropping `k` zero trailing coefficients is a factorisation `P = X^k * Q`, and
  `Q(0)` is the coefficient of degree `k` of `P`;
* `roots_X_pow_mul`: the roots of `P` are `0`, `k` times, and the roots of `Q`;
* `rootMultiplicity_zero_X_pow_mul`: the multiplicity of `0` in `P` is exactly `k`;
* `rootMultiplicity_X_pow_mul_of_ne_zero`: every other point has the same multiplicity in `P` and in `Q`;
* `zero_notMem_closedBall`, `roots_filter_closedBall`: a disc with `‖z‖ > r` does not contain `0`, and
  holds the same roots of `P` as of `Q`, with the same multiplicities: its count for `Q` is its count for `P`;
* `roots_C_mul'`: a nonzero constant factor changes no root (the square-free factors of Yun's algorithm
  are computed up to such constants).

Not formalised: the Rust code (the floating-point test `|z| (1 - 4u) > r`, the test on the bit lengths of
multiprecision centres), and Yun's algorithm itself. -/

namespace LeanMath.Papers.ZeroDeflation
open Polynomial
open scoped Classical

variable {K : Type*} [Field K]

/-- Zero trailing coefficients: `P = X^k * Q`, and `Q(0)` is the coefficient of degree `k` of `P`. -/
theorem exists_X_pow_mul (P : K[X]) (k : ℕ) (h : ∀ d < k, P.coeff d = 0) :
    ∃ Q : K[X], P = X ^ k * Q ∧ Q.eval 0 = P.coeff k := by
  obtain ⟨Q, rfl⟩ := X_pow_dvd_iff.mpr h
  refine ⟨Q, rfl, ?_⟩
  rw [← coeff_zero_eq_eval_zero]
  simpa using (coeff_X_pow_mul Q k 0).symm

/-- The roots of `X^k * Q` are `0`, `k` times, and the roots of `Q`. -/
theorem roots_X_pow_mul (Q : K[X]) (k : ℕ) (hQ : Q ≠ 0) :
    (X ^ k * Q).roots = k • ({0} : Multiset K) + Q.roots := by
  have h : (X ^ k * Q : K[X]) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hQ
  rw [roots_mul h, roots_X_pow]

/-- The multiplicity of `0` in `X^k * Q` is exactly `k` when `Q(0) ≠ 0`. -/
theorem rootMultiplicity_zero_X_pow_mul (Q : K[X]) (k : ℕ) (h0 : Q.eval 0 ≠ 0) :
    (X ^ k * Q).rootMultiplicity 0 = k := by
  have hQ : Q ≠ 0 := by rintro rfl; simp at h0
  have h : (X ^ k * Q : K[X]) ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) hQ
  rw [← count_roots, roots_X_pow_mul Q k hQ, Multiset.count_add, Multiset.count_nsmul,
    Multiset.count_singleton_self, count_roots, rootMultiplicity_eq_zero h0]
  simp

/-- A point other than `0` has the same multiplicity in `X^k * Q` and in `Q`. -/
theorem rootMultiplicity_X_pow_mul_of_ne_zero (Q : K[X]) (k : ℕ) (hQ : Q ≠ 0) {z : K} (hz : z ≠ 0) :
    (X ^ k * Q).rootMultiplicity z = Q.rootMultiplicity z := by
  rw [← count_roots, roots_X_pow_mul Q k hQ, Multiset.count_add, Multiset.count_nsmul,
    Multiset.count_singleton, if_neg hz, count_roots]
  simp

/-- A nonzero constant factor changes no root. -/
theorem roots_C_mul' (P : K[X]) {a : K} (ha : a ≠ 0) : (C a * P).roots = P.roots :=
  roots_C_mul P ha

/-- A disc with `‖z‖ > r` does not contain `0`. -/
theorem zero_notMem_closedBall {z : ℂ} {r : ℝ} (h : r < ‖z‖) : (0 : ℂ) ∉ Metric.closedBall z r := by
  simp [Metric.mem_closedBall, dist_eq_norm, h]

/-- Such a disc holds the same roots of `X^k * Q` as of `Q`, with the same multiplicities. -/
theorem roots_filter_closedBall (Q : ℂ[X]) (k : ℕ) (hQ : Q ≠ 0) {z : ℂ} {r : ℝ} (h : r < ‖z‖) :
    (X ^ k * Q).roots.filter (· ∈ Metric.closedBall z r) = Q.roots.filter (· ∈ Metric.closedBall z r) := by
  rw [roots_X_pow_mul Q k hQ, Multiset.filter_add, Multiset.filter_nsmul,
    Multiset.filter_singleton, if_neg (zero_notMem_closedBall h)]
  simp

end LeanMath.Papers.ZeroDeflation
