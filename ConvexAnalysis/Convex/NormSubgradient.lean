/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import ConvexAnalysis.Convex.Subgradient

/-!
# Subdifferential of the norm and Fenchel–Young inequalities

For a real inner product space `F`:

* `mem_subdiff_norm_iff`: `z ∈ ∂‖·‖(x)` iff `‖z‖ ≤ 1` and `⟪z, x⟫ = ‖x‖`, at every `x`
  (the library's `SubderivAt_of_norm_at_zero` is the case `x = 0`).
* `hasSubgradientAt_norm_iff`, `SubderivAt_norm`: the same statement for `HasSubgradientAt`
  and `SubderivAt`.
* `fenchel_young_norm`: `⟪x, s⟫ ≤ λ‖x‖` when `‖s‖ ≤ λ` (Fenchel–Young for `λ‖·‖`).
* `fenchel_young_quad`: `⟪a, r⟫ - ½‖r‖² - ⟪f, r⟫ ≤ ½‖a - f‖²` (Fenchel–Young for `½‖· - f‖²`).
-/

open scoped RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The subdifferential of the norm: `z ∈ ∂‖·‖(x)` iff `‖z‖ ≤ 1` and `⟪z, x⟫ = ‖x‖`.
For `x ≠ 0` this is `z = x/‖x‖`; for `x = 0` it is the closed unit ball. -/
theorem mem_subdiff_norm_iff {x z : F} :
    (∀ y, ‖x‖ + ⟪z, y - x⟫ ≤ ‖y‖) ↔ ‖z‖ ≤ 1 ∧ ⟪z, x⟫ = ‖x‖ := by
  constructor
  · intro h
    have h0 := h 0
    have h2 := h (x + x)
    have h3 := h (x + z)
    simp only [zero_sub, inner_neg_right, norm_zero, add_sub_cancel_right] at h0 h2
    rw [add_sub_cancel_left, real_inner_self_eq_norm_sq] at h3
    have hxx : ‖x + x‖ ≤ ‖x‖ + ‖x‖ := norm_add_le x x
    have hxz : ‖x + z‖ ≤ ‖x‖ + ‖z‖ := norm_add_le x z
    refine ⟨?_, by linarith⟩
    nlinarith [norm_nonneg z]
  · rintro ⟨hz, hzx⟩ y
    rw [inner_sub_right, hzx]
    have := real_inner_le_norm z y
    nlinarith [norm_nonneg y]

/-- `mem_subdiff_norm_iff` for the library's `HasSubgradientAt`. -/
theorem hasSubgradientAt_norm_iff {x z : F} :
    HasSubgradientAt (fun y : F => ‖y‖) z x ↔ ‖z‖ ≤ 1 ∧ ⟪z, x⟫ = ‖x‖ := by
  rw [← mem_subdiff_norm_iff]
  exact Iff.rfl

/-- The subdifferential of the norm at any point: `∂‖·‖(x) = {z | ‖z‖ ≤ 1, ⟪z, x⟫ = ‖x‖}`. -/
theorem SubderivAt_norm (x : F) :
    SubderivAt (fun y : F => ‖y‖) x = {z | ‖z‖ ≤ 1 ∧ ⟪z, x⟫ = ‖x‖} :=
  Set.ext fun _ => hasSubgradientAt_norm_iff

/-- Fenchel–Young for `λ‖·‖`: `⟪x, s⟫ ≤ λ‖x‖` when `‖s‖ ≤ λ`. -/
lemma fenchel_young_norm {lam : ℝ} {s : F} (hs : ‖s‖ ≤ lam) (x : F) : ⟪x, s⟫ ≤ lam * ‖x‖ := by
  calc ⟪x, s⟫ ≤ ‖x‖ * ‖s‖ := real_inner_le_norm x s
    _ ≤ ‖x‖ * lam := mul_le_mul_of_nonneg_left hs (norm_nonneg x)
    _ = lam * ‖x‖ := mul_comm _ _

/-- Fenchel–Young for `½‖· - f‖²`: `⟪a, r⟫ - ½‖r‖² - ⟪f, r⟫ ≤ ½‖a - f‖²`. -/
lemma fenchel_young_quad (a f r : F) :
    ⟪a, r⟫ - 1 / 2 * ‖r‖ ^ 2 - ⟪f, r⟫ ≤ 1 / 2 * ‖a - f‖ ^ 2 := by
  have h := norm_sub_sq_real (a - f) r
  have hi : ⟪a - f, r⟫ = ⟪a, r⟫ - ⟪f, r⟫ := inner_sub_left a f r
  nlinarith [sq_nonneg ‖a - f - r‖]
