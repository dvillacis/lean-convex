/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import ConvexAnalysis.Convex.Subgradient
import ConvexAnalysis.Extended.ConvexConjugate

/-!
# Subgradients and the Fenchel–Young equality

This file links the subgradients of the library (`HasSubgradientAt`, `HasSubgradientWithinAt`
for real-valued functions, from `Convex/Subgradient`) with the convex conjugate
`convex_conjugate` of extended-real functions (`Extended/ConvexConjugate`).

## Real-valued functions

For `f : E → ℝ`, write `f*` for the conjugate of `x ↦ (f x : EReal)` over a set `s`.

* `conjugate_ge_of_mem`: Fenchel–Young, `⟪x, g⟫ - f x ≤ f* g` for `x ∈ s`.
* `hasSubgradientWithinAt_iff_conjugate_eq`: for `x ∈ s`, `g` is a subgradient of `f` at `x`
  relative to `s` iff equality holds, `f* g = ⟪x, g⟫ - f x`.
* `hasSubgradientAt_iff_conjugate_eq`, `SubderivAt_eq_conjugate`: the case `s = univ`.

## Extended-real functions

* `HasERealSubgradientAt f g x`: `f x + ⟪g, y - x⟫ ≤ f y` for all `y`, for `f : E → EReal`;
  it agrees with `HasSubgradientAt` for real-valued functions (`hasERealSubgradientAt_coe_iff`).
* `hasERealSubgradientAt_iff_conjugate_eq`: for finite `f x`, `g ∈ ∂f(x)` iff
  `f* g = ⟪x, g⟫ - f x`.
* `hasERealSubgradientAt_conjugate_iff` (Rockafellar, Thm 23.5): for a lower semicontinuous
  convex `f` on a finite-dimensional space and finite `f x`, `g ∈ ∂f(x)` iff `x ∈ ∂f*(g)`.
* `hasSubgradientAt_iff_mem_subgradient_conjugate`: the same for a continuous convex
  `f : E → ℝ`.
-/

open Set EReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

/-! ### Real-valued functions -/

section Real

variable {f : E → ℝ} {g x : E} {s : Set E}

/-- The conjugate of a real-valued function, as a supremum of real numbers. -/
lemma convex_conjugate_coe (s : Set E) (f : E → ℝ) (g : E) :
    convex_conjugate s (fun y => (f y : EReal)) g = ⨆ y ∈ s, ((⟪y, g⟫ - f y : ℝ) : EReal) := by
  simp only [convex_conjugate, EReal.coe_sub]

/-- Fenchel–Young: `⟪x, g⟫ - f x ≤ f* g` for `x ∈ s`. -/
lemma conjugate_ge_of_mem (hx : x ∈ s) :
    ((⟪x, g⟫ - f x : ℝ) : EReal) ≤ convex_conjugate s (fun y => (f y : EReal)) g := by
  rw [convex_conjugate_coe]
  exact le_iSup₂_of_le (f := fun y _ => ((⟪y, g⟫ - f y : ℝ) : EReal)) x hx le_rfl

/-- The subgradient inequality, rearranged: `g` is a subgradient of `f` at `x` relative to `s`
iff `x` maximizes `y ↦ ⟪y, g⟫ - f y` over `s`. -/
lemma hasSubgradientWithinAt_iff_forall_le :
    HasSubgradientWithinAt f g s x ↔ ∀ y ∈ s, ⟪y, g⟫ - f y ≤ ⟪x, g⟫ - f x := by
  refine forall₂_congr fun y _ => ?_
  rw [ge_iff_le, inner_sub_right, real_inner_comm g y, real_inner_comm g x]
  constructor <;> intro h <;> linarith

/-- **Fenchel–Young equality.** For `x ∈ s`, `g` is a subgradient of `f` at `x` relative to `s`
iff `f* g = ⟪x, g⟫ - f x`, where `f*` is the conjugate over `s`. -/
theorem hasSubgradientWithinAt_iff_conjugate_eq (hx : x ∈ s) :
    HasSubgradientWithinAt f g s x ↔
      convex_conjugate s (fun y => (f y : EReal)) g = ((⟪x, g⟫ - f x : ℝ) : EReal) := by
  rw [hasSubgradientWithinAt_iff_forall_le]
  constructor
  · intro h
    refine le_antisymm ?_ (conjugate_ge_of_mem hx)
    rw [convex_conjugate_coe]
    exact iSup₂_le fun y hy => EReal.coe_le_coe_iff.2 (h y hy)
  · intro h y hy
    have := (conjugate_ge_of_mem (f := f) (g := g) hy).trans h.le
    exact EReal.coe_le_coe_iff.1 this

/-- **Fenchel–Young equality** on the whole space: `g ∈ ∂f(x)` iff `f* g = ⟪x, g⟫ - f x`. -/
theorem hasSubgradientAt_iff_conjugate_eq :
    HasSubgradientAt f g x ↔
      convex_conjugate univ (fun y => (f y : EReal)) g = ((⟪x, g⟫ - f x : ℝ) : EReal) := by
  rw [← hasSubgradientWithinAt_univ]
  exact hasSubgradientWithinAt_iff_conjugate_eq (mem_univ x)

/-- The subdifferential as the set where the Fenchel–Young inequality is an equality. -/
theorem SubderivAt_eq_conjugate (f : E → ℝ) (x : E) :
    SubderivAt f x =
      {g | convex_conjugate univ (fun y => (f y : EReal)) g = ((⟪x, g⟫ - f x : ℝ) : EReal)} :=
  Set.ext fun _ => hasSubgradientAt_iff_conjugate_eq

end Real

/-! ### Extended-real functions -/

section Extended

/-- `g` is a subgradient of `f : E → EReal` at `x`: `f x + ⟪g, y - x⟫ ≤ f y` for all `y`.
As in Rockafellar, this is meant for points where `f x` is finite. -/
def HasERealSubgradientAt (f : E → EReal) (g x : E) : Prop :=
  ∀ y, f x + ⟪g, y - x⟫ ≤ f y

variable {g x : E}

/-- For a real-valued function, `HasERealSubgradientAt` is `HasSubgradientAt`. -/
lemma hasERealSubgradientAt_coe_iff {f : E → ℝ} :
    HasERealSubgradientAt (fun y => (f y : EReal)) g x ↔ HasSubgradientAt f g x := by
  refine forall_congr' fun y => ?_
  rw [ge_iff_le, ← EReal.coe_add, EReal.coe_le_coe_iff]

variable {f : E → EReal}

/-- **Fenchel–Young equality.** If `f x` is finite, `g ∈ ∂f(x)` iff `f* g = ⟪x, g⟫ - f x`. -/
theorem hasERealSubgradientAt_iff_conjugate_eq (hbot : f x ≠ ⊥) (htop : f x ≠ ⊤) :
    HasERealSubgradientAt f g x ↔ convex_conjugate univ f g = ⟪x, g⟫ - f x := by
  have hfy := fenchel_inequality' univ f x (mem_univ x) g (mem_univ g)
  obtain ⟨u, hu⟩ : ∃ u : ℝ, f x = u := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  rw [hu] at hfy ⊢
  constructor
  · intro h
    refine le_antisymm (iSup₂_le fun y _ => ?_) hfy
    have hy := h y
    rw [hu] at hy
    induction hfyv : f y with
    | bot => rw [hfyv, ← EReal.coe_add] at hy; exact absurd hy (by simp)
    | top => simp
    | coe w =>
      rw [hfyv, ← EReal.coe_add, EReal.coe_le_coe_iff] at hy
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff, inner_sub_right,
        real_inner_comm g y, real_inner_comm g x] at *
      linarith
  · intro h y
    have hy := (fenchel_inequality' univ f y (mem_univ y) g (mem_univ g)).trans h.le
    rw [hu]
    induction hfyv : f y with
    | bot =>
      rw [hfyv, EReal.sub_bot (EReal.coe_ne_bot _), top_le_iff, ← EReal.coe_sub] at hy
      exact absurd hy (EReal.coe_ne_top _)
    | top => exact le_top
    | coe w =>
      rw [hfyv, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hy
      rw [← EReal.coe_add, EReal.coe_le_coe_iff, inner_sub_right]
      have := real_inner_comm g y
      have := real_inner_comm g x
      linarith

/-- **Reciprocity of subgradients** (Rockafellar, Thm 23.5). For a lower semicontinuous convex
`f` on a finite-dimensional space and a point where `f x` is finite, `g ∈ ∂f(x)` iff
`x ∈ ∂f*(g)`. The proof uses `f** = f` (`bi_convex_conjugate_eq_self`). -/
theorem hasERealSubgradientAt_conjugate_iff [FiniteDimensional ℝ E]
    (hl : LowerSemicontinuous f) (hc : ConvexOn ℝ univ f) (hbot : f x ≠ ⊥) (htop : f x ≠ ⊤) :
    HasERealSubgradientAt f g x ↔ HasERealSubgradientAt (convex_conjugate univ f) x g := by
  have hff := bi_convex_conjugate_eq_self hl hc
  obtain ⟨u, hu⟩ : ∃ u : ℝ, f x = u := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  rw [hasERealSubgradientAt_iff_conjugate_eq hbot htop, hu]
  -- `f* g` is not `⊥`, by Fenchel–Young
  have hgb : convex_conjugate univ f g ≠ ⊥ := by
    have := fenchel_inequality' univ f x (mem_univ x) g (mem_univ g)
    rw [hu, ← EReal.coe_sub] at this
    exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) this
  constructor
  · intro h
    have hgt : convex_conjugate univ f g ≠ ⊤ := by rw [h, ← EReal.coe_sub]; exact EReal.coe_ne_top _
    rw [hasERealSubgradientAt_iff_conjugate_eq hgb hgt, hff, hu, h, ← EReal.coe_sub,
      ← EReal.coe_sub, real_inner_comm]
    congr 1
    ring
  · intro h
    -- `f* g` is finite: otherwise `f* ≡ ⊤`, so `f** ≡ ⊥`, contradicting `f** x = f x`
    have hgt : convex_conjugate univ f g ≠ ⊤ := by
      intro htop'
      have hall : ∀ y, convex_conjugate univ f y = ⊤ := fun y => by
        have := h y
        rw [htop', EReal.top_add_coe] at this
        exact top_le_iff.1 this
      have hbotx : convex_conjugate univ (convex_conjugate univ f) x = ⊥ := by
        show (⨆ y ∈ univ, (⟪y, x⟫ : EReal) - convex_conjugate univ f y) = ⊥
        refine le_bot_iff.1 (iSup₂_le fun y _ => ?_)
        rw [hall y]
        simp
      rw [hff, hu] at hbotx
      exact EReal.coe_ne_bot _ hbotx
    have h2 := (hasERealSubgradientAt_iff_conjugate_eq hgb hgt).1 h
    rw [hff, hu] at h2
    obtain ⟨c, hc'⟩ : ∃ c : ℝ, convex_conjugate univ f g = c :=
      ⟨_, (EReal.coe_toReal hgt hgb).symm⟩
    rw [hc', ← EReal.coe_sub, EReal.coe_eq_coe_iff] at h2
    rw [hc', ← EReal.coe_sub, EReal.coe_eq_coe_iff, real_inner_comm]
    linarith

/-- Reciprocity for a continuous convex `f : E → ℝ` on a finite-dimensional space:
`g ∈ ∂f(x)` iff `x ∈ ∂f*(g)`. -/
theorem hasSubgradientAt_iff_mem_subgradient_conjugate [FiniteDimensional ℝ E] {f : E → ℝ}
    (hl : Continuous f) (hc : ConvexOn ℝ univ f) :
    HasSubgradientAt f g x ↔
      HasERealSubgradientAt (convex_conjugate univ (fun y => (f y : EReal))) x g := by
  rw [← hasERealSubgradientAt_coe_iff]
  exact hasERealSubgradientAt_conjugate_iff
    (continuous_coe_real_ereal.comp hl).lowerSemicontinuous
    ((ProperFunctionConvexOn_iff_ConvexOn univ f).1 hc) (EReal.coe_ne_bot _) (EReal.coe_ne_top _)

end Extended
