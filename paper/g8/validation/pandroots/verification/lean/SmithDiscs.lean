import Mathlib

/-! # Smith's discs (note G8, Section 4): the covering half and the real-root criterion

For a monic polynomial `S` of degree `m` and distinct points `z₁, …, z_m`, put
`W_k = S(z_k) / ∏_{l ≠ k} (z_k - z_l)`.

* `partial_fractions`: off the nodes, `S(ζ) = ∏ (ζ - z_i) · (1 + ∑ W_k / (ζ - z_k))`
  (Lagrange interpolation of `S - ∏ (X - z_i)`);
* `smith_union`: every root of `S` lies in one of the discs `D(z_k, m |W_k|)`
  (first half of Theorem 4.1);
* `real_root_of_mirror`: Proposition 4.4, given the count: if a disc contains exactly one root, the roots
  are stable by conjugation and the mirror image of the disc meets no other disc, that root is real.

The count is in `FixedPointCertificate` (Theorem 4.2 and Corollary 4.3: one root in each disc, by a
contraction).  Not formalised: the second half of Theorem 4.1 (a connected component of `q` discs
contains exactly `q` roots), which rests on Gershgorin's second theorem, a continuity argument that is
not in Mathlib. -/

noncomputable section
namespace LeanMath.Papers.SmithDiscs
open Polynomial Finset Lagrange

variable {m : ℕ}

/-- The Weierstrass value `W_k = S(z_k) / ∏_{l ≠ k} (z_k - z_l)`. -/
def weierstrass (S : ℂ[X]) (z : Fin m → ℂ) (k : Fin m) : ℂ :=
  S.eval (z k) * nodalWeight univ z k

theorem weierstrass_eq (S : ℂ[X]) (z : Fin m → ℂ) (k : Fin m) :
    weierstrass S z k = S.eval (z k) / ∏ l ∈ univ.erase k, (z k - z l) := by
  rw [weierstrass, nodalWeight, prod_inv_distrib, div_eq_mul_inv]

/-- Off the nodes, `S(ζ) = ∏ (ζ - z_i) · (1 + ∑ W_k / (ζ - z_k))`. -/
theorem partial_fractions (S : ℂ[X]) (hS : S.Monic) (hdeg : S.natDegree = m) (z : Fin m → ℂ)
    (hz : Function.Injective z) (ζ : ℂ) (hζ : ∀ i, ζ ≠ z i) :
    S.eval ζ = (∏ i, (ζ - z i)) * (1 + ∑ k, weierstrass S z k * (ζ - z k)⁻¹) := by
  have hvs : Set.InjOn z (univ : Finset (Fin m)) := hz.injOn
  have h1 : S.degree = (nodal (univ : Finset (Fin m)) z).degree := by
    rw [degree_nodal, degree_eq_natDegree hS.ne_zero, hdeg, Finset.card_univ, Fintype.card_fin]
  have hlt : (S - nodal (univ : Finset (Fin m)) z).degree < #(univ : Finset (Fin m)) := by
    have h2 := degree_sub_lt_left h1 hS.ne_zero (by rw [hS.leadingCoeff, (nodal_monic).leadingCoeff])
    rwa [h1, degree_nodal] at h2
  have key := eq_interpolate_of_eval_eq (fun i => S.eval (z i)) hvs hlt
    (fun i hi => by rw [eval_sub, eval_nodal_at_node hi, sub_zero])
  have hx : ∀ i ∈ (univ : Finset (Fin m)), ζ ≠ z i := fun i _ => hζ i
  have h3 := congrArg (eval ζ) key
  rw [eval_sub, eval_interpolate_not_at_node _ hx, eval_nodal] at h3
  have h4 : ∑ k, weierstrass S z k * (ζ - z k)⁻¹
      = ∑ i, nodalWeight univ z i * (ζ - z i)⁻¹ * S.eval (z i) := by
    refine sum_congr rfl fun i _ => ?_
    rw [weierstrass]
    ring
  rw [h4, mul_add, mul_one, ← h3]
  ring

/-- First half of Smith's theorem: every root of `S` lies in a disc `D(z_k, m |W_k|)`. -/
theorem smith_union (S : ℂ[X]) (hS : S.Monic) (hdeg : S.natDegree = m) (z : Fin m → ℂ)
    (hz : Function.Injective z) (ζ : ℂ) (hroot : S.eval ζ = 0) :
    ∃ k, ‖ζ - z k‖ ≤ m * ‖weierstrass S z k‖ := by
  by_cases h : ∃ k, ζ = z k
  · obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    rw [hk, sub_self, norm_zero]
    positivity
  · push Not at h
    have hpf := partial_fractions S hS hdeg z hz ζ h
    rw [hroot] at hpf
    have hprod : (∏ i, (ζ - z i)) ≠ 0 := by
      rw [prod_ne_zero_iff]
      exact fun i _ => sub_ne_zero.mpr (h i)
    have hsum : ∑ k, weierstrass S z k * (ζ - z k)⁻¹ = -1 := by
      have h0 := (mul_eq_zero.mp hpf.symm).resolve_left hprod
      linear_combination h0
    by_contra hcon
    push Not at hcon
    have hne : (univ : Finset (Fin m)).Nonempty := by
      by_contra hemp
      rw [not_nonempty_iff_eq_empty] at hemp
      rw [hemp, sum_empty] at hsum
      norm_num at hsum
    have hm : (0 : ℝ) < m := by
      have : 0 < m := by
        obtain ⟨k, _⟩ := hne
        exact Fin.pos k
      exact_mod_cast this
    have hterm : ∀ k ∈ (univ : Finset (Fin m)), ‖weierstrass S z k * (ζ - z k)⁻¹‖ < 1 / m := by
      intro k _
      have hpos : 0 < ‖ζ - z k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (h k))
      rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_div_iff₀ hpos hm]
      have := hcon k
      linarith
    have hlt : ∑ k, ‖weierstrass S z k * (ζ - z k)⁻¹‖ < ∑ _k : Fin m, (1 : ℝ) / m :=
      sum_lt_sum_of_nonempty hne hterm
    have hone : ∑ _k : Fin m, (1 : ℝ) / m = 1 := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hnorm : ‖∑ k, weierstrass S z k * (ζ - z k)⁻¹‖ = 1 := by
      rw [hsum, norm_neg, norm_one]
    have := norm_sum_le (univ : Finset (Fin m)) (fun k => weierstrass S z k * (ζ - z k)⁻¹)
    linarith

/-- Proposition 4.3, given the count.  `R` is the set of roots, stable by conjugation (real
polynomial); the discs `D(z j, r j)` cover `R`; the disc `D(z k, r k)` contains one root only, `ζ`,
which lies in `D(c, ρ)`.  If the mirror image of `D(c, ρ)` is disjoint from every other disc, then
`ζ` is real. -/
theorem real_root_of_mirror {ι : Type*} (R : Set ℂ)
    (hconj : ∀ w ∈ R, (starRingEnd ℂ) w ∈ R) (z : ι → ℂ) (r : ι → ℝ)
    (hcover : ∀ w ∈ R, ∃ j, dist w (z j) ≤ r j) (k : ι) (c : ℂ) (ρ : ℝ) (ζ : ℂ) (hζR : ζ ∈ R)
    (hζ : dist ζ c ≤ ρ) (huniq : ∀ w ∈ R, dist w (z k) ≤ r k → w = ζ)
    (hmirror : ∀ j, j ≠ k → ρ + r j < dist ((starRingEnd ℂ) c) (z j)) : ζ.im = 0 := by
  obtain ⟨j, hj⟩ := hcover _ (hconj ζ hζR)
  have hjk : j = k := by
    by_contra hne
    have h1 := hmirror j hne
    have h2 : dist ((starRingEnd ℂ) c) (z j)
        ≤ dist ((starRingEnd ℂ) c) ((starRingEnd ℂ) ζ) + dist ((starRingEnd ℂ) ζ) (z j) :=
      dist_triangle _ _ _
    have h3 : dist ((starRingEnd ℂ) c) ((starRingEnd ℂ) ζ) = dist ζ c := by
      rw [Complex.dist_conj_conj, dist_comm]
    linarith
  subst hjk
  have := huniq _ (hconj ζ hζR) hj
  exact Complex.conj_eq_iff_im.mp this

end LeanMath.Papers.SmithDiscs
