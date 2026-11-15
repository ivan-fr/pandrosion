import LeanMath.Papers.SmithDiscs

/-! # A fixed-point certificate: exactly one root in a disc (note G8, Section 4, Theorem 4.2)

`S` is monic of degree `m`, `z₁, …, z_m` are distinct, `W_k = S(z_k) / ∏_{l ≠ k} (z_k - z_l)`.
Off the nodes, `S(ζ) = 0` if and only if `1 + ∑ W_l / (ζ - z_l) = 0`, that is,

  `ζ = Φ_k(ζ)`,  `Φ_k(w) = z_k - W_k / (1 + ∑_{l ≠ k} W_l / (w - z_l))`.

On the disc `D = D(z_k, ρ)`, with `δ_l = |z_k - z_l| - ρ > 0`, `σ = ∑_{l ≠ k} |W_l| / δ_l` and
`τ = ∑_{l ≠ k} |W_l| / δ_l²`: if `σ < 1`, `|W_k| ≤ ρ (1 - σ)` and `|W_k| τ < (1 - σ)²`, then `Φ_k` maps
`D` into itself and is a contraction there.  Hence (Banach) `D` contains exactly one root of `S`.

* `tail_norm_le`, `one_sub_le_norm`: the bounds on `D`;
* `phi_mapsTo`, `phi_lipschitz`: `Φ_k` maps `D` into `D` with Lipschitz constant `|W_k| τ / (1-σ)²`;
* `root_iff_fixed`: in `D`, the roots of `S` are the fixed points of `Φ_k`;
* `existsUnique_root` (Theorem 4.2): exactly one root in `D`;
* `all_roots_certified` (Corollary 4.3 (i)): if every disc passes and the discs are pairwise disjoint,
  `S` has exactly one root in each disc and no other root.
* `certificate_of_bounds`, `disjoint_of_bounds` (Corollary 4.3 (ii)): the test of the programs, on
  upper bounds `w_l` of the `|W_l|` and with the radius `2 w_k`, gives the hypotheses above;
* `all_roots_of_bounds`, `all_roots_of_bounds_leadingCoeff`: the complete statement, for a monic `S` and
  for any leading coefficient;
* `real_root_of_bounds`: the real-root flag (real coefficients, mirror disc);
* `all_roots_of_computed`, `real_root_of_computed`: the same with lower bounds of the gaps, that is,
  with the quantities the programs really compute.
* `real_disc_of_computed`: the real-root flag in the form tested since version 0.2.0 of the crate (a real
  disc that contains the disc and its mirror image), with the fact that this real disc holds one root only.

This replaces the appeal to Gershgorin's second theorem for an isolated disc: no continuity of the
roots is used, only the contraction principle. -/

noncomputable section
namespace LeanMath.Papers.FixedPointCertificate
open Polynomial Finset Lagrange Metric
open LeanMath.Papers.SmithDiscs

variable {m : ℕ}

/-- `∑_{l ≠ k} W_l / (w - z_l)`. -/
def tail (W z : Fin m → ℂ) (k : Fin m) (w : ℂ) : ℂ :=
  ∑ l ∈ univ.erase k, W l * (w - z l)⁻¹

/-- `Φ_k(w) = z_k - W_k / (1 + ∑_{l ≠ k} W_l / (w - z_l))`. -/
def phi (W z : Fin m → ℂ) (k : Fin m) (w : ℂ) : ℂ :=
  z k - W k / (1 + tail W z k w)

/-- `σ = ∑_{l ≠ k} |W_l| / (|z_k - z_l| - ρ)`. -/
def sigma (W z : Fin m → ℂ) (k : Fin m) (ρ : ℝ) : ℝ :=
  ∑ l ∈ univ.erase k, ‖W l‖ / (‖z k - z l‖ - ρ)

/-- `τ = ∑_{l ≠ k} |W_l| / (|z_k - z_l| - ρ)²`. -/
def tau (W z : Fin m → ℂ) (k : Fin m) (ρ : ℝ) : ℝ :=
  ∑ l ∈ univ.erase k, ‖W l‖ / (‖z k - z l‖ - ρ) ^ 2

section Analytic
variable (W z : Fin m → ℂ) (k : Fin m) (ρ : ℝ)

/-- On the disc, the other nodes stay at distance at least `|z_k - z_l| - ρ`. -/
theorem gap_le {w : ℂ} (hw : w ∈ closedBall (z k) ρ) (l : Fin m) :
    ‖z k - z l‖ - ρ ≤ ‖w - z l‖ := by
  have h1 : ‖z k - z l‖ ≤ ‖z k - w‖ + ‖w - z l‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h2 : ‖z k - w‖ ≤ ρ := by
    rw [mem_closedBall, dist_eq_norm] at hw
    rwa [norm_sub_rev]
  linarith

theorem tail_norm_le (hsep : ∀ l, l ≠ k → ρ < ‖z k - z l‖) {w : ℂ} (hw : w ∈ closedBall (z k) ρ) :
    ‖tail W z k w‖ ≤ sigma W z k ρ := by
  unfold tail sigma
  refine (norm_sum_le _ _).trans (sum_le_sum fun l hl => ?_)
  have hlk : l ≠ k := (mem_erase.mp hl).1
  have hpos : 0 < ‖z k - z l‖ - ρ := sub_pos.mpr (hsep l hlk)
  have hg := gap_le z k ρ hw l
  rw [norm_mul, norm_inv, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (norm_nonneg _) hpos hg

theorem one_sub_le_norm (hsep : ∀ l, l ≠ k → ρ < ‖z k - z l‖) {w : ℂ}
    (hw : w ∈ closedBall (z k) ρ) : 1 - sigma W z k ρ ≤ ‖1 + tail W z k w‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (-tail W z k w)
  rw [norm_neg, sub_neg_eq_add, norm_one] at h
  have := tail_norm_le W z k ρ hsep hw
  linarith

/-- `Φ_k` maps the disc into itself. -/
theorem phi_mapsTo (hsep : ∀ l, l ≠ k → ρ < ‖z k - z l‖) (hσ : sigma W z k ρ < 1)
    (hball : ‖W k‖ ≤ ρ * (1 - sigma W z k ρ)) {w : ℂ} (hw : w ∈ closedBall (z k) ρ) :
    phi W z k w ∈ closedBall (z k) ρ := by
  have h1 := one_sub_le_norm W z k ρ hsep hw
  have hpos : 0 < 1 - sigma W z k ρ := sub_pos.mpr hσ
  rw [mem_closedBall, dist_eq_norm, phi, sub_sub_cancel_left, norm_neg, norm_div]
  calc ‖W k‖ / ‖1 + tail W z k w‖ ≤ ‖W k‖ / (1 - sigma W z k ρ) :=
        div_le_div_of_nonneg_left (norm_nonneg _) hpos h1
    _ ≤ ρ := by rw [div_le_iff₀ hpos]; exact hball

/-- The variation of the tail on the disc. -/
theorem tail_sub_norm_le (hsep : ∀ l, l ≠ k → ρ < ‖z k - z l‖) {w w' : ℂ}
    (hw : w ∈ closedBall (z k) ρ) (hw' : w' ∈ closedBall (z k) ρ) :
    ‖tail W z k w - tail W z k w'‖ ≤ tau W z k ρ * ‖w - w'‖ := by
  unfold tail tau
  rw [← sum_sub_distrib, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun l hl => ?_)
  have hlk : l ≠ k := (mem_erase.mp hl).1
  have hpos : 0 < ‖z k - z l‖ - ρ := sub_pos.mpr (hsep l hlk)
  have hg := gap_le z k ρ hw l
  have hg' := gap_le z k ρ hw' l
  have hn : w - z l ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hpos hg)
  have hn' : w' - z l ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hpos hg')
  have e : W l * (w - z l)⁻¹ - W l * (w' - z l)⁻¹ = W l * (w' - w) / ((w - z l) * (w' - z l)) := by
    field_simp
    ring
  rw [e, norm_div, norm_mul, norm_mul, norm_sub_rev w' w]
  have hden : (‖z k - z l‖ - ρ) ^ 2 ≤ ‖w - z l‖ * ‖w' - z l‖ := by
    rw [sq]
    exact mul_le_mul hg hg' hpos.le (hpos.le.trans hg)
  calc ‖W l‖ * ‖w - w'‖ / (‖w - z l‖ * ‖w' - z l‖)
      ≤ ‖W l‖ * ‖w - w'‖ / (‖z k - z l‖ - ρ) ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_pos hpos 2) hden
    _ = ‖W l‖ / (‖z k - z l‖ - ρ) ^ 2 * ‖w - w'‖ := by ring

/-- `Φ_k` is Lipschitz on the disc with constant `|W_k| τ / (1 - σ)²`. -/
theorem phi_lipschitz (hsep : ∀ l, l ≠ k → ρ < ‖z k - z l‖) (hσ : sigma W z k ρ < 1) {w w' : ℂ}
    (hw : w ∈ closedBall (z k) ρ) (hw' : w' ∈ closedBall (z k) ρ) :
    ‖phi W z k w - phi W z k w'‖
      ≤ ‖W k‖ * tau W z k ρ / (1 - sigma W z k ρ) ^ 2 * ‖w - w'‖ := by
  have hpos : 0 < 1 - sigma W z k ρ := sub_pos.mpr hσ
  have h1 := one_sub_le_norm W z k ρ hsep hw
  have h1' := one_sub_le_norm W z k ρ hsep hw'
  have hn : 1 + tail W z k w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hpos h1)
  have hn' : 1 + tail W z k w' ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hpos h1')
  have e : phi W z k w - phi W z k w'
      = W k * (tail W z k w - tail W z k w') / ((1 + tail W z k w) * (1 + tail W z k w')) := by
    unfold phi
    field_simp
    ring
  have ht := tail_sub_norm_le W z k ρ hsep hw hw'
  have hden : (1 - sigma W z k ρ) ^ 2 ≤ ‖1 + tail W z k w‖ * ‖1 + tail W z k w'‖ := by
    rw [sq]
    exact mul_le_mul h1 h1' hpos.le (hpos.le.trans h1)
  rw [e, norm_div, norm_mul, norm_mul]
  have hnum : ‖W k‖ * ‖tail W z k w - tail W z k w'‖ ≤ ‖W k‖ * (tau W z k ρ * ‖w - w'‖) :=
    mul_le_mul_of_nonneg_left ht (norm_nonneg _)
  have hnum0 : 0 ≤ ‖W k‖ * (tau W z k ρ * ‖w - w'‖) :=
    le_trans (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hnum
  calc ‖W k‖ * ‖tail W z k w - tail W z k w'‖ / (‖1 + tail W z k w‖ * ‖1 + tail W z k w'‖)
      ≤ ‖W k‖ * (tau W z k ρ * ‖w - w'‖) / (‖1 + tail W z k w‖ * ‖1 + tail W z k w'‖) :=
        div_le_div_of_nonneg_right hnum (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ ‖W k‖ * (tau W z k ρ * ‖w - w'‖) / (1 - sigma W z k ρ) ^ 2 :=
        div_le_div_of_nonneg_left hnum0 (pow_pos hpos 2) hden
    _ = ‖W k‖ * tau W z k ρ / (1 - sigma W z k ρ) ^ 2 * ‖w - w'‖ := by ring

end Analytic

section Roots
variable (S : ℂ[X]) (z : Fin m → ℂ) (k : Fin m) (ρ : ℝ)

/-- In the disc, the roots of `S` are the fixed points of `Φ_k`. -/
theorem root_iff_fixed (hS : S.Monic) (hdeg : S.natDegree = m) (hz : Function.Injective z)
    (hsep : ∀ l, l ≠ k → ρ < ‖z k - z l‖) (hσ : sigma (weierstrass S z) z k ρ < 1)
    {ζ : ℂ} (hζ : ζ ∈ closedBall (z k) ρ) :
    S.eval ζ = 0 ↔ phi (weierstrass S z) z k ζ = ζ := by
  have hpos : 0 < 1 - sigma (weierstrass S z) z k ρ := sub_pos.mpr hσ
  have h1 := one_sub_le_norm (weierstrass S z) z k ρ hsep hζ
  have hG : 1 + tail (weierstrass S z) z k ζ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hpos h1)
  by_cases hk : ζ = z k
  · -- at the node `z_k`: `S(z_k) = 0` iff `W_k = 0`
    have hw : nodalWeight univ z k ≠ 0 := nodalWeight_ne_zero hz.injOn (mem_univ k)
    rw [hk] at hG ⊢
    constructor
    · intro h0
      have hWk : weierstrass S z k = 0 := by rw [weierstrass, h0, zero_mul]
      rw [phi, hWk, zero_div, sub_zero]
    · intro hfix
      rw [phi] at hfix
      have hdiv : weierstrass S z k / (1 + tail (weierstrass S z) z k (z k)) = 0 := by
        linear_combination -hfix
      have hWk : weierstrass S z k = 0 := by
        rcases div_eq_zero_iff.mp hdiv with h | h
        · exact h
        · exact absurd h hG
      rw [weierstrass] at hWk
      exact (mul_eq_zero.mp hWk).resolve_right hw
  · -- off the nodes: partial fractions
    have hoff : ∀ i, ζ ≠ z i := by
      intro i
      by_cases hik : i = k
      · rw [hik]
        exact hk
      · have hg := gap_le z k ρ hζ i
        have hp : 0 < ‖z k - z i‖ - ρ := sub_pos.mpr (hsep i hik)
        intro h
        rw [h, sub_self, norm_zero] at hg
        linarith
    have hpf := partial_fractions S hS hdeg z hz ζ hoff
    have hprod : (∏ i, (ζ - z i)) ≠ 0 := by
      rw [prod_ne_zero_iff]
      exact fun i _ => sub_ne_zero.mpr (hoff i)
    have hsplit : ∑ i, weierstrass S z i * (ζ - z i)⁻¹
        = weierstrass S z k * (ζ - z k)⁻¹ + tail (weierstrass S z) z k ζ := by
      rw [tail]
      exact (add_sum_erase univ (fun i => weierstrass S z i * (ζ - z i)⁻¹) (mem_univ k)).symm
    have ha : ζ - z k ≠ 0 := sub_ne_zero.mpr hk
    rw [hpf, hsplit, mul_eq_zero, or_iff_right hprod]
    constructor
    · intro h
      have e : (1 + (weierstrass S z k * (ζ - z k)⁻¹ + tail (weierstrass S z) z k ζ)) * (ζ - z k)
          = (1 + tail (weierstrass S z) z k ζ) * (ζ - z k) + weierstrass S z k := by
        field_simp
        ring
      rw [h, zero_mul] at e
      have hdiv : weierstrass S z k / (1 + tail (weierstrass S z) z k ζ) = z k - ζ := by
        rw [div_eq_iff hG]
        linear_combination -e
      rw [phi, hdiv]
      ring
    · intro hfix
      rw [phi] at hfix
      have hdiv : weierstrass S z k / (1 + tail (weierstrass S z) z k ζ) = z k - ζ := by
        linear_combination -hfix
      rw [div_eq_iff hG] at hdiv
      rw [hdiv]
      field_simp
      ring

/-- **The fixed-point certificate.**  If `σ < 1`, `|W_k| ≤ ρ (1 - σ)` and `|W_k| τ < (1 - σ)²`, the
disc `D(z_k, ρ)` contains exactly one root of `S`. -/
theorem existsUnique_root (hS : S.Monic) (hdeg : S.natDegree = m) (hz : Function.Injective z)
    (hρ : 0 ≤ ρ) (hsep : ∀ l, l ≠ k → ρ < ‖z k - z l‖)
    (hσ : sigma (weierstrass S z) z k ρ < 1)
    (hball : ‖weierstrass S z k‖ ≤ ρ * (1 - sigma (weierstrass S z) z k ρ))
    (hK : ‖weierstrass S z k‖ * tau (weierstrass S z) z k ρ
      < (1 - sigma (weierstrass S z) z k ρ) ^ 2) :
    ∃! ζ, ζ ∈ closedBall (z k) ρ ∧ S.eval ζ = 0 := by
  have hpos : 0 < 1 - sigma (weierstrass S z) z k ρ := sub_pos.mpr hσ
  have hτ : 0 ≤ tau (weierstrass S z) z k ρ :=
    sum_nonneg fun l _ => div_nonneg (norm_nonneg _) (sq_nonneg _)
  have hK0 : 0 ≤ ‖weierstrass S z k‖ * tau (weierstrass S z) z k ρ
      / (1 - sigma (weierstrass S z) z k ρ) ^ 2 :=
    div_nonneg (mul_nonneg (norm_nonneg _) hτ) (sq_nonneg _)
  have hK1 : ‖weierstrass S z k‖ * tau (weierstrass S z) z k ρ
      / (1 - sigma (weierstrass S z) z k ρ) ^ 2 < 1 := by
    rw [div_lt_one (pow_pos hpos 2)]
    exact hK
  have hsf : Set.MapsTo (phi (weierstrass S z) z k) (closedBall (z k) ρ) (closedBall (z k) ρ) :=
    fun w hw => phi_mapsTo (weierstrass S z) z k ρ hsep hσ hball hw
  have hf : ContractingWith
      (Real.toNNReal (‖weierstrass S z k‖ * tau (weierstrass S z) z k ρ
        / (1 - sigma (weierstrass S z) z k ρ) ^ 2))
      (hsf.restrict (phi (weierstrass S z) z k) (closedBall (z k) ρ) (closedBall (z k) ρ)) := by
    refine ⟨Real.toNNReal_lt_one.mpr hK1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hK0]
    exact phi_lipschitz (weierstrass S z) z k ρ hsep hσ x.2 y.2
  obtain ⟨y, hys, hfix, -⟩ := ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete hsf hf
    (mem_closedBall_self hρ) (edist_ne_top _ _)
  have hfy : phi (weierstrass S z) z k y = y := hfix
  refine ⟨y, ⟨hys, (root_iff_fixed S z k ρ hS hdeg hz hsep hσ hys).mpr hfy⟩, ?_⟩
  rintro y' ⟨hys', hroot'⟩
  have hfy' := (root_iff_fixed S z k ρ hS hdeg hz hsep hσ hys').mp hroot'
  have hl := phi_lipschitz (weierstrass S z) z k ρ hsep hσ hys' hys
  rw [hfy', hfy] at hl
  by_contra hne
  have hp : 0 < ‖y' - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  nlinarith

end Roots

/-- **All the roots.**  If every disc `D(z_k, ρ_k)` passes the fixed-point certificate and the discs are
pairwise disjoint, then `S` has exactly `m` roots, one in each disc: there are `ζ_1, …, ζ_m`, distinct,
with `ζ_k ∈ D(z_k, ρ_k)`, `S(ζ_k) = 0`, and every root of `S` is one of them. -/
theorem all_roots_certified (S : ℂ[X]) (hS : S.Monic) (hdeg : S.natDegree = m) (z : Fin m → ℂ)
    (hz : Function.Injective z) (ρ : Fin m → ℝ) (hρ : ∀ k, 0 ≤ ρ k)
    (hsep : ∀ k l, l ≠ k → ρ k < ‖z k - z l‖)
    (hσ : ∀ k, sigma (weierstrass S z) z k (ρ k) < 1)
    (hball : ∀ k, ‖weierstrass S z k‖ ≤ ρ k * (1 - sigma (weierstrass S z) z k (ρ k)))
    (hK : ∀ k, ‖weierstrass S z k‖ * tau (weierstrass S z) z k (ρ k)
      < (1 - sigma (weierstrass S z) z k (ρ k)) ^ 2)
    (hdisj : ∀ k l, k ≠ l → ρ k + ρ l < ‖z k - z l‖) :
    ∃ ζ : Fin m → ℂ, Function.Injective ζ ∧
      (∀ k, ζ k ∈ closedBall (z k) (ρ k) ∧ S.eval (ζ k) = 0) ∧
      ∀ w, S.eval w = 0 → ∃ k, w = ζ k := by
  have ex : ∀ k, ∃ ζ, ζ ∈ closedBall (z k) (ρ k) ∧ S.eval ζ = 0 := fun k =>
    (existsUnique_root S z k (ρ k) hS hdeg hz (hρ k) (hsep k) (hσ k) (hball k) (hK k)).exists
  choose ζ hζ using ex
  have hinj : Function.Injective ζ := by
    intro k l hkl
    by_contra hne
    have h1 := (hζ k).1
    have h2 := (hζ l).1
    rw [mem_closedBall, dist_eq_norm] at h1 h2
    rw [hkl] at h1
    have h3 : ‖z k - z l‖ ≤ ‖z k - ζ l‖ + ‖ζ l - z l‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev (z k) (ζ l)] at h3
    have := hdisj k l hne
    linarith
  refine ⟨ζ, hinj, hζ, ?_⟩
  intro w hw
  have hsub : univ.image ζ ⊆ S.roots.toFinset := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := mem_image.mp hx
    rw [Multiset.mem_toFinset, mem_roots hS.ne_zero]
    exact (hζ k).2
  have hcard : S.roots.toFinset.card ≤ (univ.image ζ).card := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
    calc S.roots.toFinset.card ≤ Multiset.card S.roots := Multiset.toFinset_card_le _
      _ ≤ S.natDegree := card_roots' S
      _ = m := hdeg
  have heq := eq_of_subset_of_card_le hsub hcard
  have hwmem : w ∈ univ.image ζ := by
    rw [heq, Multiset.mem_toFinset, mem_roots hS.ne_zero]
    exact hw
  obtain ⟨k, -, rfl⟩ := mem_image.mp hwmem
  exact ⟨k, rfl⟩

/-! ## The test of the programs (Corollary 4.3 (ii)) and the complete statements

The programs do not know `|W_l|` exactly but upper bounds `w_l`.  They take `ρ_k = 2 w_k` and check
`∑_{l ≠ k} w_l / (|z_k - z_l| - 2 w_k) < 1/2` and `w_k ∑_{l ≠ k} w_l / (|z_k - z_l| - 2 w_k)² < 1/4`. -/

section Bounds

/-- Corollary 4.3 (ii), first part: the test on the bounds gives the three hypotheses of the
fixed-point certificate for the radius `2 w_k`. -/
theorem certificate_of_bounds (S : ℂ[X]) (z : Fin m → ℂ) (k : Fin m) (w : Fin m → ℝ)
    (hw : ∀ l, ‖weierstrass S z l‖ ≤ w l)
    (hsep : ∀ l, l ≠ k → 2 * w k < ‖z k - z l‖)
    (hσ : ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) < 1 / 2)
    (hτ : w k * ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) ^ 2 < 1 / 4) :
    sigma (weierstrass S z) z k (2 * w k) < 1 ∧
    ‖weierstrass S z k‖ ≤ 2 * w k * (1 - sigma (weierstrass S z) z k (2 * w k)) ∧
    ‖weierstrass S z k‖ * tau (weierstrass S z) z k (2 * w k)
      < (1 - sigma (weierstrass S z) z k (2 * w k)) ^ 2 := by
  have hw0 : 0 ≤ w k := (norm_nonneg _).trans (hw k)
  have hg : ∀ l ∈ univ.erase k, 0 < ‖z k - z l‖ - 2 * w k := fun l hl =>
    sub_pos.mpr (hsep l (ne_of_mem_erase hl))
  have hσle : sigma (weierstrass S z) z k (2 * w k)
      ≤ ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) := by
    unfold sigma
    exact sum_le_sum fun l hl => div_le_div_of_nonneg_right (hw l) (hg l hl).le
  have hτle : tau (weierstrass S z) z k (2 * w k)
      ≤ ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) ^ 2 := by
    unfold tau
    exact sum_le_sum fun l _ => div_le_div_of_nonneg_right (hw l) (sq_nonneg _)
  have hτ0 : 0 ≤ tau (weierstrass S z) z k (2 * w k) :=
    sum_nonneg fun l _ => div_nonneg (norm_nonneg _) (sq_nonneg _)
  have hσ1 : sigma (weierstrass S z) z k (2 * w k) < 1 / 2 := lt_of_le_of_lt hσle hσ
  refine ⟨by linarith, ?_, ?_⟩
  · have h1 := hw k
    nlinarith [mul_nonneg hw0
      (show (0 : ℝ) ≤ 1 / 2 - sigma (weierstrass S z) z k (2 * w k) by linarith)]
  · have h1 : ‖weierstrass S z k‖ * tau (weierstrass S z) z k (2 * w k)
        ≤ w k * ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) ^ 2 :=
      mul_le_mul (hw k) hτle hτ0 hw0
    nlinarith

/-- Corollary 4.3 (ii), second part: the same test makes the disc `D(z_k, 2 w_k)` disjoint from every
other disc `D(z_l, 2 w_l)`. -/
theorem disjoint_of_bounds (z : Fin m → ℂ) (k l : Fin m) (w : Fin m → ℝ) (hl : l ≠ k)
    (hw0 : ∀ l, 0 ≤ w l) (hsep : ∀ l, l ≠ k → 2 * w k < ‖z k - z l‖)
    (hσ : ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) < 1 / 2) :
    2 * w k + 2 * w l < ‖z k - z l‖ := by
  have hg : 0 < ‖z k - z l‖ - 2 * w k := sub_pos.mpr (hsep l hl)
  have h1 : w l / (‖z k - z l‖ - 2 * w k)
      ≤ ∑ i ∈ univ.erase k, w i / (‖z k - z i‖ - 2 * w k) :=
    single_le_sum (f := fun i => w i / (‖z k - z i‖ - 2 * w k))
      (fun i hi => div_nonneg (hw0 i) (sub_pos.mpr (hsep i (ne_of_mem_erase hi))).le)
      (mem_erase.mpr ⟨hl, mem_univ l⟩)
  have h2 : w l / (‖z k - z l‖ - 2 * w k) < 1 / 2 := lt_of_le_of_lt h1 hσ
  rw [div_lt_iff₀ hg] at h2
  linarith

/-- **All the roots, from the numbers the programs compute** (monic `S`).  If the bounds `w_l` of the
`|W_l|` pass the test at every `k`, then `S` has exactly `m` roots, one in each disc `D(z_k, 2 w_k)`. -/
theorem all_roots_of_bounds (S : ℂ[X]) (hS : S.Monic) (hdeg : S.natDegree = m) (z : Fin m → ℂ)
    (w : Fin m → ℝ) (hw : ∀ l, ‖weierstrass S z l‖ ≤ w l)
    (hsep : ∀ k l, l ≠ k → 2 * w k < ‖z k - z l‖)
    (hσ : ∀ k, ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) < 1 / 2)
    (hτ : ∀ k, w k * ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) ^ 2 < 1 / 4) :
    ∃ ζ : Fin m → ℂ, Function.Injective ζ ∧
      (∀ k, ζ k ∈ closedBall (z k) (2 * w k) ∧ S.eval (ζ k) = 0) ∧
      ∀ x, S.eval x = 0 → ∃ k, x = ζ k := by
  have hw0 : ∀ l, 0 ≤ w l := fun l => (norm_nonneg _).trans (hw l)
  have hz : Function.Injective z := by
    intro k l hkl
    by_contra hne
    have h := hsep k l (Ne.symm hne)
    rw [hkl, sub_self, norm_zero] at h
    linarith [hw0 k]
  exact all_roots_certified S hS hdeg z hz (fun k => 2 * w k)
    (fun k => mul_nonneg zero_le_two (hw0 k)) hsep
    (fun k => (certificate_of_bounds S z k w hw (hsep k) (hσ k) (hτ k)).1)
    (fun k => (certificate_of_bounds S z k w hw (hsep k) (hσ k) (hτ k)).2.1)
    (fun k => (certificate_of_bounds S z k w hw (hsep k) (hσ k) (hτ k)).2.2)
    (fun k l hkl => disjoint_of_bounds z k l w (Ne.symm hkl) hw0 (hsep k) (hσ k))

theorem weierstrass_C_mul (a : ℂ) (S : ℂ[X]) (z : Fin m → ℂ) (k : Fin m) :
    weierstrass (C a * S) z k = a * weierstrass S z k := by
  simp only [weierstrass, eval_mul, eval_C]
  ring

/-- The same for any leading coefficient `c ≠ 0`, with `W_k = S(z_k) / (c ∏_{l ≠ k} (z_k - z_l))`:
this is the statement the programs use. -/
theorem all_roots_of_bounds_leadingCoeff (S : ℂ[X]) (hS : S ≠ 0) (hdeg : S.natDegree = m)
    (z : Fin m → ℂ) (w : Fin m → ℝ) (hw : ∀ l, ‖weierstrass S z l / S.leadingCoeff‖ ≤ w l)
    (hsep : ∀ k l, l ≠ k → 2 * w k < ‖z k - z l‖)
    (hσ : ∀ k, ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) < 1 / 2)
    (hτ : ∀ k, w k * ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) ^ 2 < 1 / 4) :
    ∃ ζ : Fin m → ℂ, Function.Injective ζ ∧
      (∀ k, ζ k ∈ closedBall (z k) (2 * w k) ∧ S.eval (ζ k) = 0) ∧
      ∀ x, S.eval x = 0 → ∃ k, x = ζ k := by
  have hc : S.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hS
  have hmonic : (C S.leadingCoeff⁻¹ * S).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hc)
  have hdeg' : (C S.leadingCoeff⁻¹ * S).natDegree = m := by
    rw [natDegree_C_mul (inv_ne_zero hc), hdeg]
  have hw' : ∀ l, ‖weierstrass (C S.leadingCoeff⁻¹ * S) z l‖ ≤ w l := fun l => by
    rw [weierstrass_C_mul, mul_comm, ← div_eq_mul_inv]
    exact hw l
  obtain ⟨ζ, hinj, hζ, hall⟩ := all_roots_of_bounds _ hmonic hdeg' z w hw' hsep hσ hτ
  refine ⟨ζ, hinj, fun k => ⟨(hζ k).1, ?_⟩, fun x hx => hall x ?_⟩
  · have h := (hζ k).2
    rw [eval_mul, eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hc)
  · rw [eval_mul, eval_C, hx, mul_zero]

/-- A polynomial with real coefficients takes conjugate values at conjugate points. -/
theorem eval_conj_of_real (S : ℂ[X]) (hreal : ∀ n, (S.coeff n).im = 0) (x : ℂ) :
    S.eval ((starRingEnd ℂ) x) = (starRingEnd ℂ) (S.eval x) := by
  rw [eval_eq_sum_range, eval_eq_sum_range, map_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [map_mul, map_pow, Complex.conj_eq_iff_im.mpr (hreal n)]

/-- **Real roots, from the numbers the programs compute** (Proposition 4.4 with the discs of
Corollary 4.3).  `S` has real coefficients and every disc passes the test.  If the mirror image of
`D(z_k, 2 w_k)` is disjoint from every other disc `D(z_j, 2 w_j)`, the root of `S` in `D(z_k, 2 w_k)`
is real. -/
theorem real_root_of_bounds (S : ℂ[X]) (hS : S ≠ 0) (hdeg : S.natDegree = m)
    (hreal : ∀ n, (S.coeff n).im = 0)
    (z : Fin m → ℂ) (w : Fin m → ℝ) (hw : ∀ l, ‖weierstrass S z l / S.leadingCoeff‖ ≤ w l)
    (hsep : ∀ k l, l ≠ k → 2 * w k < ‖z k - z l‖)
    (hσ : ∀ k, ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) < 1 / 2)
    (hτ : ∀ k, w k * ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) ^ 2 < 1 / 4)
    (k : Fin m)
    (hmirror : ∀ j, j ≠ k → 2 * w k + 2 * w j < dist ((starRingEnd ℂ) (z k)) (z j))
    (x : ℂ) (hx : S.eval x = 0) (hxk : x ∈ closedBall (z k) (2 * w k)) : x.im = 0 := by
  have hw0 : ∀ l, 0 ≤ w l := fun l => (norm_nonneg _).trans (hw l)
  obtain ⟨ζ, -, hζ, hall⟩ := all_roots_of_bounds_leadingCoeff S hS hdeg z w hw hsep hσ hτ
  have key : ∀ y, S.eval y = 0 → dist y (z k) ≤ 2 * w k → y = ζ k := by
    intro y hy hyk
    obtain ⟨j, rfl⟩ := hall y hy
    by_contra hne
    have hjk : j ≠ k := fun h => hne (by rw [h])
    have h1 := mem_closedBall.mp (hζ j).1
    have h2 := disjoint_of_bounds z k j w hjk hw0 (hsep k) (hσ k)
    have h3 : dist (z k) (z j) ≤ dist (z k) (ζ j) + dist (ζ j) (z j) := dist_triangle _ _ _
    rw [dist_comm (z k) (ζ j), dist_eq_norm (z k) (z j)] at h3
    linarith
  have hxk' := mem_closedBall.mp hxk
  exact real_root_of_mirror {y | S.eval y = 0}
    (fun y hy => by
      show S.eval ((starRingEnd ℂ) y) = 0
      rw [eval_conj_of_real S hreal, show S.eval y = 0 from hy, map_zero])
    z (fun j => 2 * w j)
    (fun y hy => by
      obtain ⟨j, rfl⟩ := hall y hy
      exact ⟨j, mem_closedBall.mp (hζ j).1⟩)
    k (z k) (2 * w k) x hx hxk'
    (fun y hy hyk => (key y hy hyk).trans (key x hx hxk').symm) hmirror

/-- What is really computed.  The programs do not know the gaps `|z_k - z_l| - 2 w_k` exactly either:
they use positive lower bounds `g k l`.  The test on `w` and `g` implies the test on the true gaps. -/
theorem bounds_of_computed (z : Fin m → ℂ) (w : Fin m → ℝ) (g : Fin m → Fin m → ℝ)
    (hw0 : ∀ l, 0 ≤ w l) (hg0 : ∀ k l, l ≠ k → 0 < g k l)
    (hg : ∀ k l, l ≠ k → g k l ≤ ‖z k - z l‖ - 2 * w k)
    (hσ : ∀ k, ∑ l ∈ univ.erase k, w l / g k l < 1 / 2)
    (hτ : ∀ k, w k * ∑ l ∈ univ.erase k, w l / g k l ^ 2 < 1 / 4) :
    (∀ k l, l ≠ k → 2 * w k < ‖z k - z l‖) ∧
    (∀ k, ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) < 1 / 2) ∧
    (∀ k, w k * ∑ l ∈ univ.erase k, w l / (‖z k - z l‖ - 2 * w k) ^ 2 < 1 / 4) := by
  refine ⟨fun k l h => by linarith [hg0 k l h, hg k l h], fun k => ?_, fun k => ?_⟩
  · refine lt_of_le_of_lt (sum_le_sum fun l hl => ?_) (hσ k)
    exact div_le_div_of_nonneg_left (hw0 l) (hg0 k l (ne_of_mem_erase hl))
      (hg k l (ne_of_mem_erase hl))
  · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (sum_le_sum fun l hl => ?_) (hw0 k)) (hτ k)
    exact div_le_div_of_nonneg_left (hw0 l) (pow_pos (hg0 k l (ne_of_mem_erase hl)) 2)
      (pow_le_pow_left₀ (hg0 k l (ne_of_mem_erase hl)).le (hg k l (ne_of_mem_erase hl)) 2)

/-- **The statement behind the output of the programs.**  `w l` bounds `|W_l|` from above, `g k l`
bounds the gap `|z_k - z_l| - 2 w_k` from below, and the two sums pass the test at every `k`.  Then
`S` has exactly `m` roots, one in each disc `D(z_k, 2 w_k)`. -/
theorem all_roots_of_computed (S : ℂ[X]) (hS : S ≠ 0) (hdeg : S.natDegree = m) (z : Fin m → ℂ)
    (w : Fin m → ℝ) (g : Fin m → Fin m → ℝ)
    (hw : ∀ l, ‖weierstrass S z l / S.leadingCoeff‖ ≤ w l)
    (hg0 : ∀ k l, l ≠ k → 0 < g k l) (hg : ∀ k l, l ≠ k → g k l ≤ ‖z k - z l‖ - 2 * w k)
    (hσ : ∀ k, ∑ l ∈ univ.erase k, w l / g k l < 1 / 2)
    (hτ : ∀ k, w k * ∑ l ∈ univ.erase k, w l / g k l ^ 2 < 1 / 4) :
    ∃ ζ : Fin m → ℂ, Function.Injective ζ ∧
      (∀ k, ζ k ∈ closedBall (z k) (2 * w k) ∧ S.eval (ζ k) = 0) ∧
      ∀ x, S.eval x = 0 → ∃ k, x = ζ k := by
  obtain ⟨h1, h2, h3⟩ := bounds_of_computed z w g
    (fun l => (norm_nonneg _).trans (hw l)) hg0 hg hσ hτ
  exact all_roots_of_bounds_leadingCoeff S hS hdeg z w hw h1 h2 h3

/-- The real-root flag of the programs, in the same computed form. -/
theorem real_root_of_computed (S : ℂ[X]) (hS : S ≠ 0) (hdeg : S.natDegree = m)
    (hreal : ∀ n, (S.coeff n).im = 0) (z : Fin m → ℂ) (w : Fin m → ℝ) (g : Fin m → Fin m → ℝ)
    (hw : ∀ l, ‖weierstrass S z l / S.leadingCoeff‖ ≤ w l)
    (hg0 : ∀ k l, l ≠ k → 0 < g k l) (hg : ∀ k l, l ≠ k → g k l ≤ ‖z k - z l‖ - 2 * w k)
    (hσ : ∀ k, ∑ l ∈ univ.erase k, w l / g k l < 1 / 2)
    (hτ : ∀ k, w k * ∑ l ∈ univ.erase k, w l / g k l ^ 2 < 1 / 4)
    (k : Fin m)
    (hmirror : ∀ j, j ≠ k → 2 * w k + 2 * w j < dist ((starRingEnd ℂ) (z k)) (z j))
    (x : ℂ) (hx : S.eval x = 0) (hxk : x ∈ closedBall (z k) (2 * w k)) : x.im = 0 := by
  obtain ⟨h1, h2, h3⟩ := bounds_of_computed z w g
    (fun l => (norm_nonneg _).trans (hw l)) hg0 hg hσ hτ
  exact real_root_of_bounds S hS hdeg hreal z w hw h1 h2 h3 k hmirror x hx hxk

/-- The real-root flag as the programs test it since version 0.2.0 of the crate: `c = Re z_k` and
`ρ = 2 w_k + |Im z_k|`, so that `D(c, ρ)` contains `D(z_k, 2 w_k)` and its mirror image.  If `D(c, ρ)` is at
distance more than `2 w_j` from every other `z_j`, the root of `S` in `D(z_k, 2 w_k)` is real, and it is the
only root of `S` in `D(c, ρ)`, the disc that the programs return. -/
theorem real_disc_of_computed (S : ℂ[X]) (hS : S ≠ 0) (hdeg : S.natDegree = m)
    (hreal : ∀ n, (S.coeff n).im = 0) (z : Fin m → ℂ) (w : Fin m → ℝ) (g : Fin m → Fin m → ℝ)
    (hw : ∀ l, ‖weierstrass S z l / S.leadingCoeff‖ ≤ w l)
    (hg0 : ∀ k l, l ≠ k → 0 < g k l) (hg : ∀ k l, l ≠ k → g k l ≤ ‖z k - z l‖ - 2 * w k)
    (hσ : ∀ k, ∑ l ∈ univ.erase k, w l / g k l < 1 / 2)
    (hτ : ∀ k, w k * ∑ l ∈ univ.erase k, w l / g k l ^ 2 < 1 / 4)
    (k : Fin m)
    (hclear : ∀ j, j ≠ k → 2 * w k + |(z k).im| + 2 * w j < dist ((z k).re : ℂ) (z j))
    (x : ℂ) (hx : S.eval x = 0) (hxk : x ∈ closedBall (z k) (2 * w k)) :
    x.im = 0 ∧ ∀ y, S.eval y = 0 → dist y ((z k).re : ℂ) ≤ 2 * w k + |(z k).im| → y = x := by
  obtain ⟨h1, h2, h3⟩ := bounds_of_computed z w g
    (fun l => (norm_nonneg _).trans (hw l)) hg0 hg hσ hτ
  obtain ⟨ζ, -, hζ, hall⟩ := all_roots_of_bounds_leadingCoeff S hS hdeg z w hw h1 h2 h3
  have hc : dist (z k) ((z k).re : ℂ) = |(z k).im| := by
    have h : z k - ((z k).re : ℂ) = ((z k).im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [dist_eq_norm, h, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have key : ∀ y, S.eval y = 0 → dist y ((z k).re : ℂ) ≤ 2 * w k + |(z k).im| → y = ζ k := by
    intro y hy hyc
    obtain ⟨j, rfl⟩ := hall y hy
    by_contra hne
    have hjk : j ≠ k := fun h => hne (by rw [h])
    have a1 := mem_closedBall.mp (hζ j).1
    have a2 := hclear j hjk
    have a3 : dist ((z k).re : ℂ) (z j) ≤ dist ((z k).re : ℂ) (ζ j) + dist (ζ j) (z j) :=
      dist_triangle _ _ _
    rw [dist_comm ((z k).re : ℂ) (ζ j)] at a3
    linarith
  have hxc : dist x ((z k).re : ℂ) ≤ 2 * w k + |(z k).im| := by
    have t1 := dist_triangle x (z k) ((z k).re : ℂ)
    have t2 := mem_closedBall.mp hxk
    linarith
  have hxζ := key x hx hxc
  refine ⟨?_, fun y hy hyc => (key y hy hyc).trans hxζ.symm⟩
  have hconj : S.eval ((starRingEnd ℂ) x) = 0 := by
    rw [eval_conj_of_real S hreal, hx, map_zero]
  have hd : dist ((starRingEnd ℂ) x) ((z k).re : ℂ) = dist x ((z k).re : ℂ) := by
    conv_lhs => rw [← Complex.conj_ofReal (z k).re, Complex.dist_conj_conj]
  have hcc : dist ((starRingEnd ℂ) x) ((z k).re : ℂ) ≤ 2 * w k + |(z k).im| := by
    rw [hd]
    exact hxc
  exact Complex.conj_eq_iff_im.mp ((key _ hconj hcc).trans hxζ.symm)

end Bounds

end LeanMath.Papers.FixedPointCertificate
