/-
Copyright (c) 2023 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Yuxuan Wu, Shengyang Xu
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Strong
import ConvexAnalysis.Convex.StronglyConvex
import ConvexAnalysis.Algorithm.GD.GradientDescent

/-!
# GradientDescentStronglyConvex

## Main results

  This file mainly concentrates on the Gradient Descent algorithm for
  smooth strongly convex optimization problems.

  We prove the O(ρ^k) rate for this algorithm.

-/

section Strongly_Convex_Gradient_Descent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ} {m : ℝ} {f' : E → E} {xm x₀ : E} {x : ℕ → E}
variable {a : ℝ} {x y : E} {l : NNReal}

open Set

theorem Strong_convex_Lipschitz_smooth (hsc : StrongConvexOn univ m f) (mp : m > 0)
    (hf : ∀ x, HasGradientAt f (f' x) x) (h₂ : LipschitzWith l f') (hl : l > (0 : ℝ)) :
    inner ℝ (f' x - f' y) (x - y) ≥ m * l / (m + l) * ‖x - y‖ ^ 2
    + 1 / (m + l) * ‖f' x - f' y‖ ^ 2 := by
  have hsc' := hsc
  rw [StrongConvexOn, UniformConvexOn] at hsc
  rcases hsc with ⟨cov, hsc⟩
  let phi : E → ℝ := fun x ↦ l / 2 * ‖x‖ ^ 2 - f x
  have convphi : ConvexOn ℝ univ phi :=
    lipschitz_to_lnorm_sub_convex cov (fun x _ ↦ hf x) (lipschitzOnWith_univ.mpr h₂) hl
  let g : E → ℝ := fun x ↦ f x - m / 2 * ‖x‖ ^ 2
  let g' : E → E := fun x ↦ f' x - m • x
  let h : E → ℝ := fun x ↦ (l - m) / 2 * ‖x‖ ^ 2 - g x
  have gderiv : ∀ (x : E), HasGradientAt g (g' x) x := fun x ↦
    sub_normsquare_gradient (s := univ) (fun x _ ↦ hf x) m x (mem_univ x)
  have convg : ConvexOn ℝ univ g := strongConvexOn_iff_convex.mp hsc'
  have convh : ConvexOn ℝ univ h := by
    have hh : h = phi := by
      funext x; simp only [h, phi, g]; ring
    rw [hh]; exact convphi
  have mlpos : 0 < m + l := by linarith
  have final (u v : E) (key : ‖u‖ ^ 2 + m * l * ‖v‖ ^ 2 ≤ (m + l) * inner ℝ u v) :
      inner ℝ u v ≥ m * l / (m + l) * ‖v‖ ^ 2 + 1 / (m + l) * ‖u‖ ^ 2 := by
    rw [ge_iff_le]
    calc m * l / (m + l) * ‖v‖ ^ 2 + 1 / (m + l) * ‖u‖ ^ 2
        = (‖u‖ ^ 2 + m * l * ‖v‖ ^ 2) / (m + l) := by ring
      _ ≤ ((m + l) * inner ℝ u v) / (m + l) := div_le_div_of_nonneg_right key mlpos.le
      _ = inner ℝ u v := mul_div_cancel_left₀ _ mlpos.ne'
  by_cases coef: 0 < l - m
  · have eq1 : inner ℝ (g' x - g' y) (x - y) ≥ 1 / (l - m) * ‖g' x - g' y‖ ^ 2 := by
      apply convex_to_lower gderiv
      change ConvexOn ℝ univ h; apply convh; apply coef; apply convg
    let alpha : E := f' x - f' y
    let beta : E := x - y
    have eq2 : g' x - g' y = alpha - m • beta := by
      simp only [g', alpha, beta]; module
    rw [eq2] at eq1
    have eq3 (u v : E) : inner ℝ (u - m • v) v ≥ 1 / (l - m) * ‖u - m • v‖ ^ 2
      → inner ℝ u v ≥ m * l / (m + l) * ‖v‖ ^ 2 + 1 / (m + l) * ‖u‖ ^ 2 := by
      have hn : ‖u - m • v‖ ^ 2 = ‖u‖ ^ 2 + m ^ 2 * ‖v‖ ^ 2 - 2 * m * inner ℝ u v := by
        rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
          sq_abs]; ring
      intro h0
      rw [hn, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h0
      have h1 := mul_le_mul_of_nonneg_left (ge_iff_le.mp h0) coef.le
      rw [← mul_assoc, mul_one_div_cancel coef.ne', one_mul] at h1
      apply final
      nlinarith [h1]
    exact eq3 alpha beta eq1
  · let alpha : E := f' x - f' y
    let beta : E := x - y
    have eq1 : inner ℝ alpha beta ≥ m * ‖beta‖ ^ 2 :=
      Strong_Convex_lower hsc' (fun x _ ↦ hf x) x (mem_univ x) y (mem_univ y)
    have eq2 : inner ℝ alpha beta ≥ 1 / l * ‖alpha‖ ^ 2 :=
      lipschitz_to_lower hf h₂ (hsc'.strictConvexOn mp).convexOn hl x y
    rw [ge_iff_le] at eq1
    rw [ge_iff_le] at eq2
    have hlm : (l : ℝ) ≤ m := by linarith
    have eq3 (u v : E) (h1 : m * ‖v‖ ^ 2 ≤ inner ℝ u v) (h2 : 1 / l * ‖u‖ ^ 2 ≤ inner ℝ u v):
      inner ℝ u v ≥ m * l / (m + l) * ‖v‖ ^ 2 + 1 / (m + l) * ‖u‖ ^ 2 := by
        apply final
        have eq4 : m * l * ‖v‖ ^ 2 ≤ m * inner ℝ u v := by
          calc
            _ ≤ m * m * ‖v‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlm mp.le) (by positivity)
            _ = m * (m * ‖v‖ ^ 2) := by ring
            _ ≤ m * inner ℝ u v := mul_le_mul_of_nonneg_left h1 mp.le
        have eq5 : ‖u‖ ^ 2 ≤ l * inner ℝ u v := by
          have := mul_le_mul_of_nonneg_left h2 (le_of_lt hl)
          rwa [← mul_assoc, mul_one_div_cancel (ne_of_gt hl), one_mul] at this
        linarith
    exact eq3 alpha beta eq1 eq2

lemma lipschitz_derivxm_eq_zero (h₁ : ∀ x : E, HasGradientAt f (f' x) x)
    (h₂ : LipschitzWith l f') (min: IsMinOn f Set.univ xm) (hl: l > (0 : ℝ)) : f' xm = 0 := by
  have eq1 : ∀ x : E, 1 / (2 * l) * ‖f' x‖ ^ 2 ≤ f x - f xm := by
    apply lipschitz_minima_lower_bound h₁ h₂ min hl
  specialize eq1 xm
  rw [sub_self] at eq1
  have hpos : (0 : ℝ) < 1 / (2 * l) := by positivity
  have hle : ‖f' xm‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖f' xm‖]
  exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm hle (sq_nonneg _)))

variable (hsc : StrongConvexOn univ m f) {alg : Gradient_Descent_fix_stepsize f f' x₀}

lemma gradient_method_strong_convex (hm : m > 0) (min : IsMinOn f univ xm)
    (step₂ : alg.a ≤ 2 / (m + alg.l)) (hsc : StrongConvexOn univ m f) :
    ∀ k : ℕ , ‖alg.x k - xm‖ ^ 2 ≤ (1 - alg.a *
    (2 * m * alg.l / (m + alg.l))) ^ k * ‖x₀ - xm‖ ^ 2 := by
  have : LipschitzWith alg.l f' := alg.smooth
  have hl : alg.l > (0 : ℝ) := alg.hl
  have ha : alg.a > 0 := alg.step₁
  have mlpos : 0 < m + alg.l := by linarith
  have reduction : ∀ k : ℕ ,
    ‖alg.x (k + 1) - xm‖ ^ 2 ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l)))
    * ‖alg.x k - xm‖ ^ 2 := by
      intro k
      rw [alg.update k]
      have hI : inner ℝ (alg.x k - xm) (f' (alg.x k)) ≥
          m * alg.l / (m + alg.l) * ‖alg.x k - xm‖ ^ 2
          + 1 / (m + alg.l) * ‖f' (alg.x k)‖ ^ 2 := by
        have eq1 : f' (alg.x k) = f' (alg.x k) - f' xm := by
          rw [lipschitz_derivxm_eq_zero alg.diff alg.smooth min hl, sub_zero]
        rw [eq1, real_inner_comm]
        exact Strong_convex_Lipschitz_smooth hsc hm alg.diff alg.smooth alg.hl
      have hexp : ‖alg.x k - alg.a • f' (alg.x k) - xm‖ ^ 2 = ‖alg.x k - xm‖ ^ 2
          - 2 * alg.a * inner ℝ (alg.x k - xm) (f' (alg.x k))
          + alg.a ^ 2 * ‖f' (alg.x k)‖ ^ 2 := by
        rw [sub_right_comm, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
          Real.norm_eq_abs, sq_abs]; ring
      have h2aI := mul_le_mul_of_nonneg_left (ge_iff_le.mp hI) (by linarith : (0 : ℝ) ≤ 2 * alg.a)
      have haG : alg.a * (alg.a - 2 / (m + alg.l)) * ‖f' (alg.x k)‖ ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos ha.le (by linarith)) (by positivity)
      rw [hexp]
      have e1 : 2 * alg.a * (m * alg.l / (m + alg.l) * ‖alg.x k - xm‖ ^ 2
          + 1 / (m + alg.l) * ‖f' (alg.x k)‖ ^ 2) = alg.a * (2 * m * alg.l / (m + alg.l))
          * ‖alg.x k - xm‖ ^ 2 + 2 * alg.a * (1 / (m + alg.l)) * ‖f' (alg.x k)‖ ^ 2 := by ring
      have e2 : alg.a * (alg.a - 2 / (m + alg.l)) * ‖f' (alg.x k)‖ ^ 2 =
          alg.a ^ 2 * ‖f' (alg.x k)‖ ^ 2 - 2 * alg.a * (1 / (m + alg.l)) * ‖f' (alg.x k)‖ ^ 2 := by
        ring
      rw [e1] at h2aI
      rw [e2] at haG
      linarith
  have eq : 0 ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) := by
    have h1 : alg.a * (2 * m * alg.l / (m + alg.l)) ≤
        2 / (m + alg.l) * (2 * m * alg.l / (m + alg.l)) :=
      mul_le_mul_of_nonneg_right step₂ (by positivity)
    have h2 : 2 / (m + alg.l) * (2 * m * alg.l / (m + alg.l)) ≤ 1 := by
      rw [div_mul_div_comm, div_le_one (by positivity)]
      nlinarith [sq_nonneg (m - alg.l)]
    linarith
  intro k
  induction k with
  | zero => simp [alg.initial]
  | succ q IH1 =>
    calc
      ‖alg.x (q + 1) - xm‖ ^ 2
          ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) * ‖alg.x q - xm‖ ^ 2 := reduction q
      _ ≤ (1 - alg.a * (2 * m * alg.l / (m + alg.l))) *
          ((1 - alg.a * (2 * m * alg.l / (m + alg.l))) ^ q * ‖x₀ - xm‖ ^ 2) :=
        mul_le_mul_of_nonneg_left IH1 eq
      _ = (1 - alg.a * (2 * m * alg.l / (m + alg.l))) ^ (q + 1) * ‖x₀ - xm‖ ^ 2 := by ring

end Strongly_Convex_Gradient_Descent
