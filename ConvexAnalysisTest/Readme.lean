/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import ConvexAnalysis

/-!
# The example of the README

Keep this file and the "Example" section of `README.md` identical, so that the code shown
there is known to compile.
-/

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A point minimizes `f` if and only if `0` is a subgradient of `f` there. -/
example (f : E → ℝ) (x : E) : IsMinOn f univ x ↔ 0 ∈ SubderivAt f x :=
  first_order_convex_iff_subgradient f x

/-- The subdifferential of the norm: `∂‖·‖(x) = {z | ‖z‖ ≤ 1, ⟪z, x⟫ = ‖x‖}`. -/
example (x : E) : SubderivAt (fun y ↦ ‖y‖) x = {z | ‖z‖ ≤ 1 ∧ ⟪z, x⟫_ℝ = ‖x‖} :=
  SubderivAt_norm x
