/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import ConvexAnalysis

/-!
# Statements of the main results

Each `example` restates one of the results listed under "Selected results" in `README.md`,
with all its hypotheses written out, and proves it by the library theorem. If a change to the
library alters the statement of one of these theorems (a new hypothesis, a weaker conclusion, a
renamed definition), this file stops compiling. Changing an `example` here is therefore a
breaking change, to be recorded in `CHANGELOG.md`.
-/

open Set InnerProductSpace Pointwise

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Sum rule for the subdifferential of convex functions (Moreau–Rockafellar). -/
example {f₁ f₂ : E → ℝ} (h₁ : ConvexOn ℝ univ f₁) (h₂ : ConvexOn ℝ univ f₂)
    (hc : ContinuousOn f₁ univ) (x : E) :
    SubderivAt f₁ x + SubderivAt f₂ x = SubderivAt (f₁ + f₂) x :=
  SubderivAt.add h₁ h₂ hc x

/-- First-order optimality condition for a differentiable convex function. -/
example {xm : E} {f : E → ℝ} {f' : E → E} (hf : ∀ x, HasGradientAt f (f' x) x)
    (hconv : ConvexOn ℝ univ f) (hc : ContinuousOn f' univ) :
    IsMinOn f univ xm ↔ f' xm = 0 :=
  first_order_convex_iff hf hconv hc

/-- Characterization of the proximal point: `u = prox_f(x)` iff `x - u ∈ ∂f(u)`. -/
example {x : E} (f : E → ℝ) (hf : ConvexOn ℝ univ f) (u : E) :
    prox_prop f x u ↔ x - u ∈ SubderivAt f u :=
  prox_iff_subderiv f hf u

end Hilbert

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The subdifferential of the norm at any point. -/
example {x z : E} : HasSubgradientAt (fun y ↦ ‖y‖) z x ↔ ‖z‖ ≤ 1 ∧ ⟪z, x⟫_ℝ = ‖x‖ :=
  hasSubgradientAt_norm_iff

/-- Fenchel's inequality. -/
example (s : Set E) (f : E → EReal) [ProperFunction s f] :
    ∀ x ∈ s, ∀ y ∈ s, (⟪x, y⟫_ℝ : EReal) ≤ f x + convex_conjugate s f y :=
  fenchel_inequality s f

end Inner

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Fenchel–Moreau: `f** = f` for a closed convex function [Rockafellar, Thm. 12.2]. -/
example {f : E → EReal} (hlsc : LowerSemicontinuous f) (hconv : ConvexOn ℝ univ f) :
    convex_conjugate univ (convex_conjugate univ f) = f :=
  bi_convex_conjugate_eq_self hlsc hconv

/-- `f** = cl f` for a convex function [Rockafellar, Thm. 12.2]. -/
example {f : E → EReal} (hconv : ConvexOn ℝ (dom univ f) f) :
    convex_conjugate univ (convex_conjugate univ f) = Function.closure f univ :=
  bi_convex_conjugate_eq_closure hconv

/-- A proper convex function has an affine minorant [Rockafellar, Cor. 12.1.2]. -/
example {f : E → EReal} (hp : ProperFunction univ f) (hconv : ConvexOn ℝ (dom univ f) f) :
    ∃ (a : E) (b : ℝ), ∀ x, f x ≥ (⟪x, a⟫_ℝ : EReal) - b :=
  exists_inner_minorant_of_proper_convex hp hconv

end FiniteDimensional

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First-order characterization of convexity. -/
example {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} {s : Set E} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasFDerivAt f (f' x) x) :
    ConvexOn ℝ s f ↔ ∀ x ∈ s, ∀ y ∈ s, f x + f' x (y - x) ≤ f y :=
  Convex_first_order_condition_iff hs hf

/-- `x ↦ ψ ‖x‖` is convex iff `ψ` is convex and nondecreasing on `[0, ∞)`. -/
example [Nontrivial E] (ψ : ℝ → ℝ) :
    ConvexOn ℝ univ (fun x : E ↦ ψ ‖x‖) ↔ ConvexOn ℝ (Ici 0) ψ ∧ MonotoneOn ψ (Ici 0) :=
  radial_convex_iff ψ

end Normed

/-- Farkas' lemma. -/
example {τ σ : Finset ℕ} {n : ℕ} {a b : ℕ → EuclideanSpace ℝ (Fin n)}
    {c : EuclideanSpace ℝ (Fin n)} :
    (∃ (lam : τ → ℝ) (mu : σ → ℝ), (∀ i, 0 ≤ mu i) ∧
        c = ∑ i, lam i • a i + ∑ i, mu i • b i) ↔
      ¬∃ z, (∀ i ∈ τ, ⟪a i, z⟫_ℝ = 0) ∧ (∀ i ∈ σ, ⟪b i, z⟫_ℝ ≥ 0) ∧ ⟪c, z⟫_ℝ < 0 :=
  Farkas
