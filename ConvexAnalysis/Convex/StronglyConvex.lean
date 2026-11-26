/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Strong
import ConvexAnalysis.Function.Lsmooth

/-!
  the properties of strongly convex function and gradient descent method
  for strongly convex function
-/
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {s : Set E} {f : E → ℝ} {m : ℝ} {xm xm' : E} {f' : E → E} {mp : m > 0}

section Strongly_Convex

open Set InnerProductSpace

theorem Strongly_Convex_Bound (m : ℝ) (strongly_convex : StrongConvexOn s m f) :
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
     ∀ ⦃a⦄, 0 < a → ∀ ⦃b⦄, 0 < b → a + b = 1 → f (a • x + b • y)
       ≤ a * f x + b * f y - m / 2 * a * b * ‖x - y‖ ^ 2 := by
  intro x xs y ys a ap b bp abp
  rcases strongly_convex with ⟨_, sc⟩
  have anneg : a ≥ 0 := by linarith
  have bnneg : b ≥ 0 := by linarith
  rcases sc xs ys anneg bnneg abp with ineq
  simp at ineq
  rw [mul_comm (m / 2), mul_assoc a, mul_comm (m / 2),← mul_assoc, mul_assoc (a * b)]
  apply ineq

theorem stronglyConvexOn_def (hs : Convex ℝ s)
    (hfun : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
      ∀ ⦃a⦄, 0 ≤ a → ∀ ⦃b⦄, 0 ≤ b → a + b = 1 → f (a • x + b • y)
        ≤ a * f x + b * f y - m / 2 * a * b * ‖x - y‖ ^ 2) :
    StrongConvexOn s m f := by
  constructor
  · exact hs
  intro x hx y hy a b ha hb hab
  specialize hfun hx hy ha hb hab
  simp only [smul_eq_mul]
  linarith [hfun]

theorem Strongly_Convex_Unique_Minima (hsc : StrongConvexOn s m f) {mp : m > 0}
    (min : IsMinOn f s xm) (min' : IsMinOn f s xm') (hxm : xm ∈ s) (hxm' : xm' ∈ s) : xm = xm' := by
  by_contra neq
  push Not at neq
  have eq : f xm = f xm' := by
    apply le_antisymm
    · apply min hxm'
    · apply min' hxm
  let x := (2 : ℝ)⁻¹ • xm + (2 : ℝ)⁻¹ • xm'
  have xeq : x = (2 : ℝ)⁻¹ • xm + (2 : ℝ)⁻¹ • xm' := by rfl
  rcases hsc with ⟨cr, sc⟩
  have : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have p : (0 : ℝ) < 1 / 2 := by norm_num
  have xs : x ∈ s := by
    rcases convex_iff_forall_pos.mp cr hxm hxm' p p (by norm_num) with cxs
    simp at cxs
    rw [← xeq] at cxs
    apply cxs
  specialize sc hxm hxm' this this (by norm_num)
  simp at sc
  rw [← xeq,← eq] at sc
  rw [← two_mul,← mul_assoc, mul_inv_cancel₀ (by norm_num), one_mul] at sc
  have normp : ‖xm - xm'‖ > 0 := by
    apply norm_sub_pos_iff.mpr
    apply neq
  have nng : m / 2 * ‖xm - xm'‖ ^ 2 > 0 := by
    apply mul_pos
    · linarith
    · apply pow_pos; linarith
  apply absurd (min xs)
  simp
  calc
    f x ≤ f xm - 2⁻¹ * 2⁻¹ * (m / 2 * ‖xm - xm'‖ ^ 2) := by apply sc
    _ < f xm := by apply lt_of_sub_pos; simp; apply nng


/--
The sum of a convex function and a square of norm is strongly convex
-/
lemma strongconvex_of_convex_add_sq (f : E → ℝ) (x : E) (hfun : ConvexOn ℝ univ f) :
    StrongConvexOn univ (1 : ℝ) fun u ↦ f u + ‖u - x‖ ^ 2 / 2 := by
  rw [ConvexOn] at hfun
  rcases hfun with ⟨conv, hfun⟩
  rw [StrongConvexOn, UniformConvexOn]
  constructor
  · exact conv
  · intro y yin z zin a b anneg bnneg absum1
    have h1 := hfun yin zin anneg bnneg absum1
    simp only [smul_eq_mul] at h1 ⊢
    obtain rfl : b = 1 - a := by linarith
    have eq1 : a • y + (1 - a) • z - x = a • (y - x) + (1 - a) • (z - x) := by module
    have eq2 (u v : E) : ‖a • u + (1 - a) • v‖ ^ 2 = (1 - a) * ‖v‖ ^ 2
        + a * ‖u‖ ^ 2 - a * (1 - a) * ‖u - v‖ ^ 2 := by
      rw [norm_add_sq_real, norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right,
        norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
        sq_abs]
      ring
    have h2 := eq2 (y - x) (z - x)
    rw [sub_sub_sub_cancel_right, ← eq1] at h2
    linarith

end Strongly_Convex

section

variable [CompleteSpace E]

theorem Strong_Convex_lower (hsc : StrongConvexOn s m f) (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) :
    ∀ x ∈ s, ∀ y ∈ s, inner ℝ (f' x - f' y) (x - y) ≥ m * ‖x - y‖ ^ 2 := by
  intro x xs y ys
  have cvx := strongConvexOn_iff_convex.mp hsc
  have grd := sub_normsquare_gradient hf m
  have grm := Convex_monotone_gradient' cvx grd x xs y ys
  have e : f' x - m • x - (f' y - m • y) = (f' x - f' y) - m • (x - y) := by
    rw [smul_sub]; abel
  rw [e, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at grm
  linarith

theorem Lower_Strong_Convex (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) (hs : Convex ℝ s)
    (h : ∀ x ∈ s, ∀ y ∈ s, inner ℝ (f' x - f' y) (x - y) ≥ m * ‖x - y‖ ^ 2) :
    StrongConvexOn s m f := by
  apply strongConvexOn_iff_convex.mpr
  have grd := sub_normsquare_gradient hf m
  apply monotone_gradient_convex' hs grd
  intro x xs y ys
  specialize h x xs y ys
  have e : f' x - m • x - (f' y - m • y) = (f' x - f' y) - m • (x - y) := by
    rw [smul_sub]; abel
  rw [e, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  linarith

theorem Strong_Convex_iff_lower (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) (hs : Convex ℝ s) :
    StrongConvexOn s m f ↔ ∀ x ∈ s, ∀ y ∈ s, inner ℝ (f' x - f' y) (x - y) ≥ m * ‖x - y‖ ^ 2 :=
  ⟨fun hsc x xs y ys ↦ Strong_Convex_lower hsc hf x xs y ys, fun h ↦ Lower_Strong_Convex hf hs h⟩

theorem Strong_Convex_second_lower (hsc : StrongConvexOn s m f)
    (hf : ∀ x ∈ s, HasGradientAt f (f' x) x) : ∀ x ∈ s, ∀ y ∈ s,
    f y ≥ f x + inner ℝ (f' x) (y - x) + m / 2 * ‖y - x‖ ^ 2 := by
  intro x xs y ys
  have cvx := strongConvexOn_iff_convex.mp hsc
  have foc := Convex_first_order_condition' (f' := fun x ↦ f' x - m • x)
    (sub_normsquare_gradient hf m x xs) cvx xs y ys
  have e1 : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ 2 := by
    have := norm_add_sq_real x (y - x)
    rwa [add_sub_cancel] at this
  simp only [inner_sub_left, real_inner_smul_left] at foc
  rw [e1] at foc
  linarith

end
