/-
Copyright (c) 2024 Zichen Wang, Yifan Bai, Pengfei Hao, Yuqing Gao, Anqing Shen.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Yifan Bai, Pengfei Hao, Yuqing Gao, Anqing Shen
-/
import ConvexAnalysis.Function.Proximal
import Mathlib.Topology.MetricSpace.Sequences

/-!
# The ADMM scheme

This file sets up the alternating direction method of multipliers for the problem of minimizing
`f₁ x₁ + f₂ x₂` subject to `A₁ x₁ + A₂ x₂ = b`. The main definitions are the problem data
`OptProblem`, the augmented Lagrangian `Augmented_Lagrangian_Function`, the iteration `ADMM`
(with the uniqueness condition `Admm_sub_Isunique` on its subproblems) and the KKT conditions
`Convex_KKT` of the convex problem.
-/

noncomputable section

open Set InnerProductSpace Topology Filter

variable (E₁ E₂ F : Type*)
   [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
   [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
   [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The basic form of the problem solved by ADMM: minimize `f₁ x₁ + f₂ x₂` subject to
`A₁ x₁ + A₂ x₂ = b`, with `f₁`, `f₂` convex and lower semicontinuous, `A₁`, `A₂` continuous
linear maps, and a feasible point at which the objective attains its minimum. -/
class OptProblem [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [FiniteDimensional ℝ F] where
   /-- The first term `f₁ : E₁ → ℝ` of the objective. -/
   f₁ : E₁ → ℝ
   /-- The second term `f₂ : E₂ → ℝ` of the objective. -/
   f₂ : E₂ → ℝ
   /-- The continuous linear map `A₁ : E₁ →L[ℝ] F` acting on `x₁` in the constraint. -/
   A₁ : E₁ →L[ℝ] F
   /-- The continuous linear map `A₂ : E₂ →L[ℝ] F` acting on `x₂` in the constraint. -/
   A₂ : E₂ →L[ℝ] F
   /-- The right-hand side `b : F` of the constraint `A₁ x₁ + A₂ x₂ = b`. -/
   b : F
   lscf₁ : LowerSemicontinuous f₁
   lscf₂ : LowerSemicontinuous f₂
   cf₁ : ConvexOn ℝ univ f₁
   cf₂ : ConvexOn ℝ univ f₂
   nonempty : ∃ x₁ x₂, (A₁ x₁) + (A₂ x₂) - b = 0 ∧
      IsMinOn (fun (x₁, x₂) ↦ f₁ x₁ + f₂ x₂) univ (x₁, x₂)

/-- The condition used for uniqueness of the solution of an ADMM subproblem: for a minimizer `x`
of `f` on `univ`, the proposition `∃ y, IsMinOn f univ y → x = y`. -/
def Admm_sub_Isunique {E : Type*} (f : E → ℝ) (x : E) (_h : IsMinOn f univ x) : Prop :=
   ∃ y, IsMinOn f univ y → x = y

/-- The augmented Lagrangian function of the problem `opt` with penalty parameter `ρ`:
`(x₁, x₂, y) ↦ f₁ x₁ + f₂ x₂ + ⟪y, A₁ x₁ + A₂ x₂ - b⟫ + ρ / 2 * ‖A₁ x₁ + A₂ x₂ - b‖ ^ 2`. -/
def Augmented_Lagrangian_Function (opt : OptProblem E₁ E₂ F) (ρ : ℝ) : E₁ × E₂ × F → ℝ :=
   fun (x₁, x₂, y) => (opt.f₁ x₁) + (opt.f₂ x₂) +
      inner ℝ y ((opt.A₁ x₁) + (opt.A₂ x₂) - opt.b) +
      ρ / 2 * ‖(opt.A₁ x₁) + (opt.A₂ x₂) - opt.b‖ ^ 2

/-- The basic iteration format of ADMM for an `OptProblem`: sequences `x₁`, `x₂`, `y` and
parameters `ρ > 0`, `0 < τ < (1 + √5) / 2` such that `x₁ (k + 1)` minimizes the augmented
Lagrangian in its first argument at `(x₂ k, y k)`, `x₂ (k + 1)` minimizes it in its second
argument at `(x₁ (k + 1), y k)`, and
`y (k + 1) = y k + (τ * ρ) • (A₁ (x₁ (k + 1)) + A₂ (x₂ (k + 1)) - b)`. -/
class ADMM extends (OptProblem E₁ E₂ F) where
   /-- The sequence of first primal iterates `x₁ : ℕ → E₁`. -/
   x₁ : ℕ → E₁
   /-- The sequence of second primal iterates `x₂ : ℕ → E₂`. -/
   x₂ : ℕ → E₂
   /-- The sequence of multipliers (dual iterates) `y : ℕ → F`. -/
   y : ℕ → F
   /-- The penalty parameter `ρ` of the augmented Lagrangian, assumed positive by `hrho`. -/
   ρ : ℝ
   /-- The step length `τ` of the multiplier update, assumed by `htau` to satisfy
   `0 < τ < (1 + √5) / 2`. -/
   τ : ℝ
   hrho : ρ > 0
   htau : 0 < τ ∧ τ < (1 + √5) / 2
   itex₁ : ∀ k, IsMinOn
      (fun x₁ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOptProblem ρ) (x₁, x₂ k, y k))
      univ (x₁ (k + 1))
   uitex₁ : ∀ k, Admm_sub_Isunique
      (fun x₁ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOptProblem ρ) (x₁, x₂ k, y k))
      (x₁ (k + 1)) (itex₁ k)
   itex₂ : ∀ k, IsMinOn
      (fun x₂ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOptProblem ρ) (x₁ (k + 1), x₂, y k))
      univ (x₂ (k + 1))
   uitex₂ : ∀ k, Admm_sub_Isunique
      (fun x₂ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOptProblem ρ) (x₁ (k + 1), x₂, y k))
      (x₂ (k + 1)) (itex₂ k)
   itey : ∀ k, y (k + 1) = y k + (τ * ρ) • ((A₁ <| x₁ (k + 1)) + (A₂ <| x₂ (k + 1)) - b)

variable {E₁ E₂ F} in
/-- The convex KKT conditions for `opt` at `(x₁, x₂)` with multiplier `y`:
`-A₁† y ∈ ∂f₁ x₁`, `-A₂† y ∈ ∂f₂ x₂` and `A₁ x₁ + A₂ x₂ = b`. -/
class Convex_KKT (x₁ : E₁) (x₂ : E₂) (y : F) (opt : OptProblem E₁ E₂ F) : Prop where
   subgrad₁ : -(ContinuousLinearMap.adjoint opt.A₁) y ∈ SubderivAt opt.f₁ x₁
   subgrad₂ : -(ContinuousLinearMap.adjoint opt.A₂) y ∈ SubderivAt opt.f₂ x₂
   eq : (opt.A₁ x₁) + (opt.A₂ x₂) = opt.b
