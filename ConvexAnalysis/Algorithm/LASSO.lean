/-
Copyright (c) 2024 Yuxuan Wu, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Wu, Chenyi Li
-/
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.CStarAlgebra.Matrix
import ConvexAnalysis.Algorithm.ProximalGradient

set_option linter.unusedVariables false

/-!
# LASSO

## Main results

  This file mainly concentrates on the definition and the proof of the convergence rate
  of the Lasso problem using proximal gradient method.

-/
section property

variable {n m : ℕ+} {t μ : ℝ}
variable {b : (Fin m) → ℝ} {A : Matrix (Fin m) (Fin n) ℝ}
variable {f h : (y : EuclideanSpace ℝ (Fin n)) → ℝ}
variable {f' : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n))}

/- Definition of `‖ ‖₁, ‖ ‖₂`, consistent with the general definition in ℝⁿ -/

local notation "‖" x "‖₂" =>
  @Norm.norm (EuclideanSpace ℝ (Fin m)) (PiLp.instNorm 2 fun _ ↦ ℝ) (WithLp.toLp 2 x)
local notation "‖" x "‖₁" => (Finset.sum Finset.univ (fun (i : Fin n) => ‖x i‖))

open Set Real Matrix Finset

/- `u ⬝ Av = Aᵀu ⬝ v` for u v in EuclideanSpace -/

lemma dot_mul_eq_transpose_mul_dot (u : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin n)) :
      u ⬝ᵥ A *ᵥ v = Aᵀ *ᵥ u ⬝ᵥ v := by
    symm; rw [← vecMul_transpose, transpose_transpose, dotProduct_mulVec]

/- `Au - Av = A(u - v)` for u v in EuclideanSpace -/

lemma mulVec_sub (u v : Fin n → ℝ) : A *ᵥ u - A *ᵥ v = A *ᵥ (u - v) := by
    rw [sub_eq_add_neg u v, mulVec_add, mulVec_neg, sub_eq_add_neg]

/- `‖x‖₂ ^ 2 = x ⬝ x` for x in EuclideanSpace -/

lemma norm2eq_dot (x :  EuclideanSpace ℝ (Fin m)) : ‖x‖₂ ^ 2 = x ⬝ᵥ x := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt, dotProduct]
  · apply Finset.sum_congr rfl
    intro z _; simp [pow_two]
  · apply sum_nonneg; exact fun i _ => sq_nonneg _

/- `⟪x, y⟫_ℝ = x ⬝ y` for x y in EuclideanSpace -/

lemma real_inner_eq_dot (x y : EuclideanSpace ℝ (Fin m)) : inner ℝ x y = x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/- gradient of a quadratic in ℝⁿ -/

lemma quadratic_gradient : ∀ x : (EuclideanSpace ℝ (Fin n)),
    HasGradientAt (fun x : (EuclideanSpace ℝ (Fin n)) => ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)))
    (WithLp.toLp 2 ((2 : ℝ) • Aᵀ *ᵥ A *ᵥ x)) x := by
  intro x
  rw [HasGradient_iff_Convergence_Point]
  intro ε εpos
  set normA := ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖ with hnormA
  have norm_mul (z : EuclideanSpace ℝ (Fin n)) : ‖A *ᵥ z‖₂ ≤ normA * ‖z‖ :=
    Matrix.l2_opNorm_mulVec A z
  have normAnn : 0 ≤ normA := norm_nonneg _
  have hpos : 0 < normA ^ 2 + 1 := by positivity
  refine ⟨ε / (normA ^ 2 + 1), div_pos εpos hpos, ?_⟩
  intro y ydist
  have key : (A *ᵥ y) ⬝ᵥ (A *ᵥ y) - (A *ᵥ x) ⬝ᵥ (A *ᵥ x)
      - inner ℝ (WithLp.toLp 2 ((2 : ℝ) • Aᵀ *ᵥ A *ᵥ x) : EuclideanSpace ℝ (Fin n)) (y - x)
      = (A *ᵥ (y - x)) ⬝ᵥ (A *ᵥ (y - x)) := by
    simp only [real_inner_eq_dot, WithLp.ofLp_sub]
    rw [smul_dotProduct, dotProduct_comm (Aᵀ *ᵥ _), dotProduct_mulVec (y.ofLp - x.ofLp),
      vecMul_transpose]
    simp only [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, smul_eq_mul]
    rw [dotProduct_comm (A *ᵥ x.ofLp) (A *ᵥ y.ofLp)]
    ring
  rw [key, ← norm2eq_dot, norm_pow, norm_norm, norm_sub_rev x y]
  have h1 : ‖A *ᵥ (y - x)‖₂ ^ 2 ≤ (normA * ‖y - x‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_mul (y - x)) 2
  have h2 : normA ^ 2 * ‖y - x‖ ≤ ε := by
    rw [norm_sub_rev] at ydist
    calc normA ^ 2 * ‖y - x‖ ≤ (normA ^ 2 + 1) * (ε / (normA ^ 2 + 1)) := by
          apply mul_le_mul (by linarith) ydist (norm_nonneg _) (by positivity)
      _ = ε := by field_simp
  calc ‖A *ᵥ (y - x)‖₂ ^ 2 ≤ (normA * ‖y - x‖) ^ 2 := h1
    _ = (normA ^ 2 * ‖y - x‖) * ‖y - x‖ := by ring
    _ ≤ ε * ‖y - x‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

/- gradient of a linear map in ℝⁿ -/

private lemma linear_gradient : ∀ x : (EuclideanSpace ℝ (Fin n)),
    HasGradientAt (fun x : (EuclideanSpace ℝ (Fin n)) => (b ⬝ᵥ (A *ᵥ x)))
    (WithLp.toLp 2 (Aᵀ *ᵥ b)) x := by
  intro x
  rw [HasGradient_iff_Convergence_Point]
  intro ε εpos
  refine ⟨ε, εpos, ?_⟩
  intro y _
  have key : b ⬝ᵥ (A *ᵥ y) - b ⬝ᵥ (A *ᵥ x)
      - inner ℝ (WithLp.toLp 2 (Aᵀ *ᵥ b) : EuclideanSpace ℝ (Fin n)) (y - x) = 0 := by
    simp only [real_inner_eq_dot, WithLp.ofLp_sub]
    rw [mulVec_transpose, dotProduct_mulVec, dotProduct_mulVec, dotProduct_sub]
    ring
  rw [key, norm_zero]
  exact mul_nonneg (le_of_lt εpos) (norm_nonneg _)

/- gradient of the square of an affine map in ℝⁿ -/

theorem affine_sq_gradient :  ∀ x : (EuclideanSpace ℝ (Fin n)),
    HasGradientAt (fun x : (EuclideanSpace ℝ (Fin n)) => ((1 / 2) * ‖A *ᵥ x - b‖₂ ^ 2))
    (WithLp.toLp 2 (Aᵀ *ᵥ (A *ᵥ x - b))) x := by
  intro x
  have hq := (quadratic_gradient (A := A) x).const_mul' (b := 1 / 2)
  have hl := linear_gradient (A := A) (b := b) x
  have := (hq.sub hl).add_const ((1 / 2) * b ⬝ᵥ b)
  convert this using 1
  · ext z
    rw [norm2eq_dot, WithLp.ofLp_toLp, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      dotProduct_comm (A *ᵥ z.ofLp) b]
    ring
  · ext i
    simp only [PiLp.sub_apply, PiLp.smul_apply, WithLp.toLp_smul, Matrix.mulVec_sub,
      Pi.sub_apply, smul_eq_mul]
    ring

/- the square of an affine map is convex on ℝⁿ-/

lemma affine_sq_convex :
    ConvexOn ℝ univ (fun x : (EuclideanSpace ℝ (Fin n)) => ((1 / 2) * ‖A *ᵥ x - b‖₂ ^ 2)) := by
  apply monotone_gradient_convex'
  apply convex_univ
  exact (fun x _ => affine_sq_gradient x)
  intro x _ y _
  rw [real_inner_eq_dot]
  simp only [WithLp.ofLp_sub, sub_sub_sub_cancel_right, ← Matrix.mulVec_sub]
  rw [dotProduct_comm, dotProduct_mulVec, vecMul_transpose]
  simpa using dotProduct_self_star_nonneg (A *ᵥ (x.ofLp - y.ofLp))

/- ‖ ‖₁ is convex on ℝⁿ -/

lemma norm_one_convex : ConvexOn ℝ univ (fun x : (EuclideanSpace ℝ (Fin n)) => ‖x‖₁) := by
  rw [ConvexOn]
  constructor; use convex_univ
  intro x _ y _ a b anneg bnneg _
  rw [smul_eq_mul, smul_eq_mul, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  simp
  calc
    |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
    _ = a * |x i| + b * |y i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg anneg, abs_of_nonneg bnneg]

/- `sgn(x)|x| = x` -/

lemma real_sign_mul_abs (x : ℝ) : Real.sign (x) * |x| = x := by
  by_cases xpos : 0 < x
  · rw [Real.sign_of_pos xpos]; simp; linarith
  · push Not at xpos
    by_cases xzero : x = 0
    · rw [xzero]; simp
    · push Not at xzero
      have xneg : x < 0 := by
        contrapose! xzero; linarith
      rw [Real.sign_of_neg xneg]; simp; rw [neg_eq_iff_eq_neg, abs_eq_neg_self]; linarith

/- the proximal of ‖ ‖₁ in ℝⁿ -/

theorem norm_one_proximal
    (lasso : h = fun y => μ • ‖y‖₁)
    (x : EuclideanSpace ℝ (Fin n)) (xm : EuclideanSpace ℝ (Fin n)) (tpos : 0 < t) (μpos : 0 < μ)
    (minpoint : ∀ i : Fin n, xm i = Real.sign (x i) * (max (abs (x i) - t * μ) 0)):
    prox_prop (t • h) x xm := by
  let g := (t * μ) • (fun (x : EuclideanSpace ℝ (Fin n)) => ‖x‖₁)
  have geqth : g = t • h := by
    ext z; rw [Pi.smul_apply]; simp [g]; rw [lasso]; simp; rw [mul_assoc]
  rw [← geqth]
  show prox_prop ((t * μ) • (fun (x : EuclideanSpace ℝ (Fin n)) => ‖x‖₁)) x xm
  have tμpos : 0 < t * μ := by
    apply mul_pos; linarith [tpos]; linarith [μpos]
  rw [prox_iff_subderiv_smul (fun x : (EuclideanSpace ℝ (Fin n)) => ‖x‖₁) norm_one_convex tμpos]
  rw [← mem_SubderivAt, HasSubgradientAt]
  intro y
  rw [PiLp.inner_apply, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  simp only [PiLp.smul_apply, PiLp.sub_apply, Real.norm_eq_abs, smul_eq_mul]
  rw [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  simp only [RCLike.re_to_real]
  have hc : 1 / (t * μ) * (t * μ) = 1 := by field_simp
  have mp := minpoint i
  set c := 1 / (t * μ) with hc_def
  have cpos : 0 < c := by positivity
  rcases lt_trichotomy (x i) 0 with hx | hx | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx] at mp
    by_cases hle : -x i ≤ t * μ
    · rw [max_eq_right (by linarith), mul_zero] at mp
      rw [mp]
      have h1 : c * (-x i) ≤ 1 := by
        calc c * (-x i) ≤ c * (t * μ) := mul_le_mul_of_nonneg_left hle cpos.le
          _ = 1 := by rw [hc_def, hc]
      have h2 : c * (-x i) * (-y i) ≤ c * (-x i) * |y i| :=
        mul_le_mul_of_nonneg_left (neg_le_abs _) (by nlinarith)
      have h3 : c * (-x i) * |y i| ≤ |y i| := by nlinarith [abs_nonneg (y i)]
      simp only [abs_zero, sub_zero, zero_add]
      nlinarith
    · push Not at hle
      rw [max_eq_left (by linarith)] at mp
      have hxm : xm i = x i + t * μ := by rw [mp]; ring
      rw [hxm, abs_of_neg (by linarith)]
      have : (x i - (x i + t * μ)) * c = -1 := by
        rw [show x i - (x i + t * μ) = -(t * μ) by ring, neg_mul, mul_comm, hc_def, hc]
      rw [show c * (x i - (x i + t * μ)) = -1 by linarith [this]]
      linarith [neg_abs_le (y i)]
  · rw [hx, Real.sign_zero, zero_mul] at mp
    rw [mp, hx]
    simp
  · rw [Real.sign_of_pos hx, abs_of_pos hx] at mp
    by_cases hle : x i ≤ t * μ
    · rw [max_eq_right (by linarith), mul_zero] at mp
      rw [mp]
      have h1 : c * x i ≤ 1 := by
        calc c * x i ≤ c * (t * μ) := mul_le_mul_of_nonneg_left hle cpos.le
          _ = 1 := by rw [hc_def, hc]
      have h2 : c * x i * y i ≤ c * x i * |y i| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by nlinarith)
      have h3 : c * x i * |y i| ≤ |y i| := by nlinarith [abs_nonneg (y i)]
      simp only [abs_zero, sub_zero, zero_add]
      nlinarith
    · push Not at hle
      rw [max_eq_left (by linarith)] at mp
      have hxm : xm i = x i - t * μ := by rw [mp]; ring
      rw [hxm, abs_of_pos (by linarith)]
      have : (x i - (x i - t * μ)) * c = 1 := by
        rw [show x i - (x i - t * μ) = t * μ by ring, mul_comm, hc_def, hc]
      rw [show c * (x i - (x i - t * μ)) = 1 by linarith [this]]
      linarith [le_abs_self (y i)]

lemma Transpose_mul_self_eq_zero {A : Matrix (Fin m) (Fin n) ℝ} : Aᵀ * A = 0 ↔ A = 0 :=
  ⟨fun h => Matrix.ext fun i j =>
      (congr_fun <| dotProduct_self_eq_zero.1 <| Matrix.ext_iff.2 h j j) i,
    fun h => h ▸ Matrix.mul_zero _⟩

end property

noncomputable section LASSO

variable {n m : ℕ+}

local notation "‖" x "‖₂" =>
  @Norm.norm (EuclideanSpace ℝ (Fin m)) (PiLp.instNorm 2 fun _ ↦ ℝ) (WithLp.toLp 2 x)
local notation "‖" x "‖₁" => (Finset.sum Finset.univ (fun (i : Fin n) => ‖x i‖))

open Set Real Matrix Finset NNReal


structure LASSO (A : Matrix (Fin m) (Fin n) ℝ) (b : (Fin m) → ℝ) (μ : ℝ) (μpos : 0 < μ) (Ane0 : A ≠ 0)
    (x₀ : (EuclideanSpace ℝ (Fin n))) where
  (f h : (EuclideanSpace ℝ (Fin n)) → ℝ)
  (f' : (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n)))
  (L : ℝ≥0) (t : ℝ) (xm : (EuclideanSpace ℝ (Fin n))) (x y : ℕ → (EuclideanSpace ℝ (Fin n)))
  (feq : f = fun x : (EuclideanSpace ℝ (Fin n)) => (1 / 2) * ‖A *ᵥ x - b‖₂ ^ 2)
  (f'eq : f' = fun x : (EuclideanSpace ℝ (Fin n)) => WithLp.toLp 2 (Aᵀ *ᵥ (A *ᵥ x - b)))
  (heq : h = fun y => μ • ‖y‖₁) (teq : t = 1 / L)
  (Leq : L = ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) (Aᵀ * A)‖₊)
  (minphi : IsMinOn (f + h) Set.univ xm)
  (ori : x 0 = x₀)
  (update1 : ∀ (k : ℕ), y k = x k - t • f' (x k))
  (update2 : ∀ (k : ℕ), x (k + 1) =
    WithLp.toLp 2 (fun i : Fin n => (Real.sign (y k i) * (max (abs (y k i) - t * μ) 0))))

private lemma LASSO_L_pos {A : Matrix (Fin m) (Fin n) ℝ} {b : (Fin m) → ℝ} {μ : ℝ} {μpos : 0 < μ}
    {Ane0 : A ≠ 0} {x₀ : (EuclideanSpace ℝ (Fin n))} (p : LASSO A b μ μpos Ane0 x₀) :
    (0 : ℝ) < p.L := by
  rw [p.Leq, coe_nnnorm, norm_pos_iff, LinearEquiv.map_ne_zero_iff, Ne,
    Transpose_mul_self_eq_zero]
  exact Ane0

instance {A : Matrix (Fin m) (Fin n) ℝ} {b : (Fin m) → ℝ} {μ : ℝ} {μpos : 0 < μ} {Ane0 : A ≠ 0}
    {x₀ : (EuclideanSpace ℝ (Fin n))} (p : LASSO A b μ μpos Ane0 x₀) :
    proximal_gradient_method p.f p.h p.f' x₀ where
  xm := p.xm
  t := p.t
  x := p.x
  L := p.L
  fconv := by
    rw [p.feq]; apply affine_sq_convex
  hconv := by
    rw [p.heq]; apply ConvexOn.smul; linarith [μpos]; apply norm_one_convex
  h₁ : ∀ x₁ : (EuclideanSpace ℝ (Fin n)), HasGradientAt p.f (p.f' x₁) x₁ := by
    rw [p.feq, p.f'eq]
    exact (fun x => affine_sq_gradient x)
  h₂ : LipschitzWith p.L p.f' := by
    rw [lipschitzWith_iff_norm_sub_le]; intro x y
    have key : p.f' x - p.f' y
        = (EuclideanSpace.equiv (Fin n) ℝ).symm ((Aᵀ * A) *ᵥ (x - y).ofLp) := by
      rw [p.f'eq]
      ext i
      simp only [PiLp.sub_apply, WithLp.ofLp_sub, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      simp [EuclideanSpace.equiv]
    rw [key, p.Leq, coe_nnnorm]
    exact Matrix.l2_opNorm_mulVec (Aᵀ * A) (x - y)
  h₃ : ContinuousOn p.h univ := by
    rw [p.heq]
    apply Continuous.continuousOn
    fun_prop
  minphi : IsMinOn (p.f + p.h) Set.univ p.xm := p.minphi
  tpos : 0 < p.t := by
    rw [p.teq]; exact one_div_pos.mpr (LASSO_L_pos p)
  step : p.t ≤ 1 / p.L := by rw [p.teq]
  ori : p.x 0 = x₀ := p.ori
  hL : p.L > (0 : ℝ) := LASSO_L_pos p
  update : ∀ (k : ℕ), prox_prop (p.t • p.h) (p.x k - p.t • p.f' (p.x k)) (p.x (k + 1)) := by
    intro k
    apply norm_one_proximal
    · rw [p.heq]
    · rw [p.teq]; exact one_div_pos.mpr (LASSO_L_pos p)
    · linarith
    · intro i; rw [p.update2 k, ← p.update1 k]

/- convergence of LASSO -/

variable {A : Matrix (Fin m) (Fin n) ℝ} {b : (Fin m) → ℝ} {μ : ℝ} {μpos : 0 < μ} {Ane0 : A ≠ 0}
variable {x₀ : (EuclideanSpace ℝ (Fin n))}
variable {alg : LASSO A b μ μpos Ane0 x₀}

theorem LASSO_converge : ∀ (k : ℕ+), (alg.f (alg.x k) + alg.h (alg.x k)
    - alg.f alg.xm - alg.h alg.xm) ≤ alg.L / (2 * k) * ‖x₀ - alg.xm‖ ^ 2 := by
  intro k
  have h₁ : alg.f (alg.x k) + alg.h (alg.x k) - alg.f alg.xm - alg.h alg.xm =
      alg.f (proximal_gradient_method.x alg.f alg.h alg.f' x₀ k)
      + alg.h (proximal_gradient_method.x alg.f alg.h alg.f' x₀ k)
      - alg.f (proximal_gradient_method.xm alg.f alg.h alg.f' x₀)
      - alg.h (proximal_gradient_method.xm alg.f alg.h alg.f' x₀) := rfl
  have h₂ : 1 / (2 * k * alg.t) * ‖x₀ - alg.xm‖ ^ 2 =
      1 / (2 * k * proximal_gradient_method.t alg.f alg.h alg.f' x₀)
      * ‖x₀ - proximal_gradient_method.xm alg.f alg.h alg.f' x₀‖ ^ 2 := rfl
  have h₃ : alg.L / (2 * k) = 1 / (2 * k * alg.t) := by
    rw [alg.teq]; field_simp
  rw [h₁, h₃, h₂]
  apply proximal_gradient_method_converge k

end LASSO
