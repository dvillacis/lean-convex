/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
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

/-- Subgradient of `λ‖·‖` for `λ ≥ 0`: `s ∈ ∂(λ‖·‖)(w)` iff `s = λ z` with `z ∈ ∂‖·‖(w)`. -/
theorem hasSubgradientAt_const_mul_norm_iff {lam : ℝ} (hlam : 0 ≤ lam) {w s : F} :
    HasSubgradientAt (fun y : F => lam * ‖y‖) s w ↔
      ∃ z : F, (‖z‖ ≤ 1 ∧ ⟪z, w⟫ = ‖w‖) ∧ s = lam • z := by
  constructor
  · intro h
    rcases eq_or_lt_of_le hlam with h0 | hpos
    · -- `λ = 0`: `s` is a subgradient of `0`, so `s = 0`
      subst h0
      have hs : s = 0 := by
        have := h (w + s)
        simp only [zero_mul, add_sub_cancel_left, real_inner_self_eq_norm_sq, ge_iff_le,
          zero_add] at this
        exact norm_eq_zero.1 (by nlinarith [norm_nonneg s])
      classical
      refine ⟨if w = 0 then 0 else ‖w‖⁻¹ • w, ?_, by simp [hs]⟩
      split_ifs with hw
      · simp [hw]
      · have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
        refine ⟨by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn], ?_⟩
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp
    · refine ⟨lam⁻¹ • s, mem_subdiff_norm_iff.1 fun y => ?_, by
        rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]⟩
      have := h y
      rw [real_inner_smul_left]
      simp only [ge_iff_le] at this
      have e : lam⁻¹ * ⟪s, y - w⟫ ≤ ‖y‖ - ‖w‖ := by
        rw [inv_mul_le_iff₀ hpos]; linarith
      linarith
  · rintro ⟨z, hz, rfl⟩ y
    have := mem_subdiff_norm_iff.2 hz y
    rw [ge_iff_le, real_inner_smul_left]
    nlinarith

section LeastSquares

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- `v ↦ ½‖A v - f‖²` is convex. -/
theorem convexOn_half_norm_sq_sub (A : E →L[ℝ] G) (f : G) :
    ConvexOn ℝ Set.univ (fun v => 1 / 2 * ‖A v - f‖ ^ 2) := by
  have hn : ConvexOn ℝ Set.univ (fun v => ‖A v - f‖) := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have e : A (a • x + b • y) - f = a • (A x - f) + b • (A y - f) := by
      obtain rfl : b = 1 - a := by linarith
      rw [map_add, map_smul, map_smul]
      module
    simp only [smul_eq_mul]
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have := (hn.pow (fun _ _ => norm_nonneg _) 2).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa [Pi.pow_apply, smul_eq_mul] using this

/-- `v ↦ ½‖A v - f‖²` has gradient `A† (A u - f)`. -/
theorem hasGradientAt_half_norm_sq_sub [CompleteSpace E] [CompleteSpace G] (A : E →L[ℝ] G)
    (f : G) (u : E) :
    HasGradientAt (fun v => 1 / 2 * ‖A v - f‖ ^ 2) (ContinuousLinearMap.adjoint A (A u - f)) u := by
  have h : HasFDerivAt (fun v => A v - f) A u := A.hasFDerivAt.sub_const f
  have := (h.norm_sq).const_mul (1 / 2)
  rw [hasGradientAt_iff_hasFDerivAt]
  refine this.congr_fderiv ?_
  ext v
  simp [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]

end LeastSquares
