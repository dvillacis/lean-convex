/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import ConvexAnalysis.Extended.FenchelYoung
import ConvexAnalysis.Extended.AffineMinorantExistence

/-!
# Subgradient calculus

Sum and chain rules for subgradients, all derived from one separation result.

* `exists_affine_sandwich`: if `F : E → ℝ` is convex, `G` is concave on a convex set `D`,
  `G ≤ F` on `D`, and `F x = G x` at some `x ∈ D`, then an affine function
  `y ↦ F x + ⟪t, y - x⟫` lies between them. The proof separates the open strict epigraph of
  `F` from the hypograph of `G` over `D`.
* `hasSubgradientWithinAt_iff_exists_normal` (constraint rule): for a convex `f : E → ℝ` and a
  convex set `B ∋ x`, `s` is a subgradient of `f` relative to `B` at `x` iff `s = s₁ + ν` with
  `s₁ ∈ ∂f(x)` and `ν` in the normal cone of `B` at `x`.
* `hasERealSubgradientAt_add_iff` (sum rule, Moreau–Rockafellar): for convex `f : E → ℝ` and
  convex `g : E → EReal` with `g x` finite, `∂(f + g)(x) = ∂f(x) + ∂g(x)`.
* `hasSubgradientAt_comp_iff` (chain rule): for a convex `h : F → ℝ` and a continuous linear
  `A : E → F`, `∂(h ∘ A)(x) = A† ∂h(A x)`.

Each result comes in two forms. The `_of_continuous` version holds on a Hilbert space and
assumes that the real-valued convex function (`F`, `f`, `h`, `φ i`) is continuous. The version
without suffix is the finite-dimensional case, where a convex function that is finite everywhere
is continuous (`ConvexOn.continuous_of_finiteDimensional`).
-/

open Set

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The sandwich theorem -/

section Sandwich

/-- **Sandwich theorem.** Let `F : E → ℝ` be convex and `G` concave on a convex set `D`, with
`G ≤ F` on `D` and `F x = G x` for some `x ∈ D`. Then there is `t : E` with
`F x + ⟪t, y - x⟫ ≤ F y` for all `y` and `G y ≤ G x + ⟪t, y - x⟫` for `y ∈ D`. -/
theorem exists_affine_sandwich_of_continuous [CompleteSpace E] {F G : E → ℝ} {D : Set E}
    (hF : ConvexOn ℝ univ F) (hFc : Continuous F) (hG : ConcaveOn ℝ D G)
    (hle : ∀ y ∈ D, G y ≤ F y) {x : E} (hx : x ∈ D) (hFG : F x = G x) :
    ∃ t : E, (∀ y, F x + ⟪t, y - x⟫ ≤ F y) ∧ (∀ y ∈ D, G y ≤ G x + ⟪t, y - x⟫) := by
  -- the open strict epigraph of `F` and the hypograph of `G` over `D`
  set C₁ : Set (E × ℝ) := {p | F p.1 < p.2}
  set C₂ : Set (E × ℝ) := {p | p.1 ∈ D ∧ p.2 ≤ G p.1}
  have hC₁c : Convex ℝ C₁ := by
    simpa [C₁] using hF.convex_strict_epigraph
  have hC₁o : IsOpen C₁ := isOpen_lt (hFc.comp continuous_fst) continuous_snd
  have hC₂c : Convex ℝ C₂ := hG.convex_hypograph
  have hdisj : Disjoint C₁ C₂ := by
    rw [Set.disjoint_left]
    rintro p hp ⟨hpD, hpG⟩
    exact absurd (hpG.trans (hle p.1 hpD)) (not_le.2 hp)
  obtain ⟨φ, c, hφ₁, hφ₂⟩ := geometric_hahn_banach_open hC₁c hC₁o hC₂c hdisj
  set α := φ (0, 1)
  set ℓ : E →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hℓ : ∀ y, ℓ y = φ (y, 0) := fun _ => rfl
  have hsplit : ∀ y μ, φ (y, μ) = ℓ y + μ * α := fun y μ => by
    rw [hℓ, φ.apply_prod_real (y, μ)]
  have h₁ : ∀ y μ, F y < μ → ℓ y + μ * α < c := fun y μ h => by
    simpa [hsplit] using hφ₁ (y, μ) h
  have h₂ : ∀ y ∈ D, c ≤ ℓ y + G y * α := fun y hy => by
    simpa [hsplit] using hφ₂ (y, G y) ⟨hy, le_rfl⟩
  -- the separating hyperplane is not vertical: `α < 0`
  have hα : α < 0 := by
    have := h₁ x (F x + 1) (by linarith)
    have := h₂ x hx
    rw [hFG] at *
    nlinarith
  -- `ℓ y + α F y ≤ c` for all `y`
  have h₁' : ∀ y, ℓ y + F y * α ≤ c := by
    intro y
    by_contra hcon
    push Not at hcon
    set δ := ℓ y + F y * α - c
    have := h₁ y (F y + δ / (-2 * α)) (by
      have : 0 < δ / (-2 * α) := div_pos (by linarith) (by linarith)
      linarith)
    have hαne : α ≠ 0 := hα.ne
    have e : ℓ y + (F y + δ / (-2 * α)) * α = ℓ y + F y * α - δ / 2 := by
      field_simp; ring
    linarith
  -- the affine function `a y = (c - ℓ y) / α`
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (-(α⁻¹) • ℓ), fun y => ?_, fun y hy => ?_⟩
  all_goals
    rw [InnerProductSpace.toDual_symm_apply, smul_apply, map_sub,
      smul_eq_mul]
  · have hy := h₁' y
    have hx' := h₂ x hx
    have hxx := h₁' x
    rw [← hFG] at hx'
    -- `c = ℓ x + α F x`
    have hc : c = ℓ x + F x * α := le_antisymm (by linarith) hxx
    have key : (F y - F x) * α ≤ -(ℓ y - ℓ x) := by linarith
    have : -α⁻¹ * (ℓ y - ℓ x) ≤ F y - F x := by
      rw [show -α⁻¹ * (ℓ y - ℓ x) = -(ℓ y - ℓ x) / α by ring]
      exact (div_le_iff_of_neg hα).2 key
    linarith
  · have hy' := h₂ y hy
    have hxx := h₁' x
    have hx' := h₂ x hx
    rw [← hFG] at hx'
    have hc : c = ℓ x + F x * α := le_antisymm (by linarith) hxx
    rw [hFG] at hc
    have key : -(ℓ y - ℓ x) ≤ (G y - G x) * α := by linarith
    have : G y - G x ≤ -α⁻¹ * (ℓ y - ℓ x) := by
      rw [show -α⁻¹ * (ℓ y - ℓ x) = -(ℓ y - ℓ x) / α by ring]
      exact (le_div_iff_of_neg hα).2 key
    linarith

/-- A convex function `E → ℝ` on a finite-dimensional space is continuous. -/
lemma ConvexOn.continuous_of_finiteDimensional [FiniteDimensional ℝ E] {F : E → ℝ}
    (hF : ConvexOn ℝ univ F) : Continuous F :=
  continuousOn_univ.1 (hF.continuousOn isOpen_univ)

/-- **Sandwich theorem** in finite dimension, where the continuity of `F` is automatic. -/
theorem exists_affine_sandwich [FiniteDimensional ℝ E] {F G : E → ℝ} {D : Set E}
    (hF : ConvexOn ℝ univ F) (hG : ConcaveOn ℝ D G) (hle : ∀ y ∈ D, G y ≤ F y) {x : E}
    (hx : x ∈ D) (hFG : F x = G x) :
    ∃ t : E, (∀ y, F x + ⟪t, y - x⟫ ≤ F y) ∧ (∀ y ∈ D, G y ≤ G x + ⟪t, y - x⟫) :=
  exists_affine_sandwich_of_continuous hF hF.continuous_of_finiteDimensional hG hle hx hFG

end Sandwich

/-! ### Affine shifts -/

section Shift

variable {D : Set E}

/-- An affine function `y ↦ c + ⟪s, y - x⟫` is concave. -/
lemma concaveOn_affine (hD : Convex ℝ D) (c : ℝ) (s x : E) :
    ConcaveOn ℝ D (fun y => c + ⟪s, y - x⟫) := by
  refine ⟨hD, fun y _ z _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, inner_sub_right, inner_add_right, real_inner_smul_right]
  have hx : ⟪s, x⟫ = a * ⟪s, x⟫ + b * ⟪s, x⟫ := by rw [← add_mul, hab, one_mul]
  have hc : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
  nlinarith

/-- Subtracting an affine function preserves convexity. -/
lemma ConvexOn.sub_affine {f : E → ℝ} (hf : ConvexOn ℝ D f) (c : ℝ) (s x : E) :
    ConvexOn ℝ D (fun y => f y - (c + ⟪s, y - x⟫)) :=
  hf.sub (concaveOn_affine hf.1 c s x)

/-- Subtracting an affine function preserves continuity. -/
lemma Continuous.sub_affine {f : E → ℝ} (hf : Continuous f) (c : ℝ) (s x : E) :
    Continuous (fun y => f y - (c + ⟪s, y - x⟫)) :=
  hf.sub (continuous_const.add (continuous_const.inner (continuous_id.sub continuous_const)))

/-- A constant minus a convex function is concave. -/
lemma ConvexOn.const_sub {f : E → ℝ} (hf : ConvexOn ℝ D f) (c : ℝ) :
    ConcaveOn ℝ D (fun y => c - f y) := by
  refine ⟨hf.1, fun y hy z hz a b ha hb hab => ?_⟩
  have := hf.2 hy hz ha hb hab
  simp only [smul_eq_mul] at this ⊢
  have hc : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
  nlinarith

end Shift

/-! ### Constraint rule -/

section Constraint

variable {f : E → ℝ} {B : Set E} {x s : E}

/-- **Constraint rule.** For a continuous convex `f : E → ℝ` on a Hilbert space and a convex set
`B ∋ x`, `s` is a subgradient of `f` at `x` relative to `B` iff `s = s₁ + ν` with `s₁ ∈ ∂f(x)`
and `ν` in the normal cone `N_B(x) = {ν | ∀ y ∈ B, ⟪ν, y - x⟫ ≤ 0}`. -/
theorem hasSubgradientWithinAt_iff_exists_normal_of_continuous [CompleteSpace E]
    (hf : ConvexOn ℝ univ f) (hfc : Continuous f) (hB : Convex ℝ B) (hx : x ∈ B) :
    HasSubgradientWithinAt f s B x ↔
      ∃ s₁ ν, HasSubgradientAt f s₁ x ∧ (∀ y ∈ B, ⟪ν, y - x⟫ ≤ 0) ∧ s = s₁ + ν := by
  constructor
  · intro h
    obtain ⟨t, ht₁, ht₂⟩ := exists_affine_sandwich_of_continuous (hf.sub_affine (f x) s x)
      (hfc.sub_affine (f x) s x) (concaveOn_const 0 hB) (fun y hy => by have := h y hy; linarith) hx
      (by simp)
    refine ⟨s + t, -t, fun y => ?_, fun y hy => ?_, by abel⟩
    · have := ht₁ y
      simp only [sub_self, inner_zero_right, add_zero, inner_add_left] at this ⊢
      linarith
    · have := ht₂ y hy
      simp only [zero_add, inner_neg_left] at this ⊢
      linarith
  · rintro ⟨s₁, ν, h₁, hν, rfl⟩ y hy
    have := h₁ y
    have := hν y hy
    simp only [ge_iff_le, inner_add_left] at *
    linarith

/-- **Constraint rule** in finite dimension: for a convex `f : E → ℝ` and a convex set `B ∋ x`,
`s` is a subgradient of `f` at `x` relative to `B` iff `s ∈ ∂f(x) + N_B(x)`. -/
theorem hasSubgradientWithinAt_iff_exists_normal [FiniteDimensional ℝ E]
    (hf : ConvexOn ℝ univ f) (hB : Convex ℝ B) (hx : x ∈ B) :
    HasSubgradientWithinAt f s B x ↔
      ∃ s₁ ν, HasSubgradientAt f s₁ x ∧ (∀ y ∈ B, ⟪ν, y - x⟫ ≤ 0) ∧ s = s₁ + ν :=
  hasSubgradientWithinAt_iff_exists_normal_of_continuous hf hf.continuous_of_finiteDimensional
    hB hx

end Constraint

/-! ### Sum rule -/

section Sum

variable {f : E → ℝ} {g : E → EReal} {x s : E}

/-- **Sum rule** (Moreau–Rockafellar). For a continuous convex `f : E → ℝ` on a Hilbert space
and a convex `g : E → EReal` with `g x` finite, `∂(f + g)(x) = ∂f(x) + ∂g(x)`. -/
theorem hasERealSubgradientAt_add_iff_of_continuous [CompleteSpace E] (hf : ConvexOn ℝ univ f)
    (hfc : Continuous f) (hg : ConvexOn ℝ (dom univ g) g) (hbot : g x ≠ ⊥) (htop : g x ≠ ⊤) :
    HasERealSubgradientAt (fun y => (f y : EReal) + g y) s x ↔
      ∃ s₁ s₂, HasSubgradientAt f s₁ x ∧ HasERealSubgradientAt g s₂ x ∧ s = s₁ + s₂ := by
  obtain ⟨v, hv⟩ : ∃ v : ℝ, g x = v := ⟨(g x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  constructor
  · intro h
    -- `g` is finite on its effective domain
    have hgb : ∀ y, g y ≠ ⊥ := fun y hy => by
      have := h y
      simp only at this
      rw [hv, hy, EReal.add_bot, ← EReal.coe_add, ← EReal.coe_add, le_bot_iff] at this
      exact EReal.coe_ne_bot _ this
    set D := dom univ g
    set gr : E → ℝ := fun y => (g y).toReal
    have hgr : ∀ y ∈ D, (gr y : EReal) = g y := fun y hy => EReal.coe_toReal hy.2.ne (hgb y)
    have hxD : x ∈ D := ⟨trivial, by rw [hv]; exact EReal.coe_lt_top v⟩
    have hgrc : ConvexOn ℝ D gr := by
      rw [ProperFunctionConvexOn_iff_ConvexOn]
      exact hg.congr fun y hy => (hgr y hy).symm
    have hgrx : gr x = v := by simp [gr, hv]
    -- the subgradient inequality in real form on `D`
    have hle : ∀ y ∈ D, f x + v + ⟪s, y - x⟫ ≤ f y + gr y := fun y hy => by
      have := h y
      simp only at this
      rw [hv, ← hgr y hy, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add,
        EReal.coe_le_coe_iff] at this
      exact this
    obtain ⟨t, ht₁, ht₂⟩ := exists_affine_sandwich_of_continuous (hf.sub_affine (f x) s x)
      (hfc.sub_affine (f x) s x) (hgrc.const_sub v)
      (fun y hy => by have := hle y hy; linarith) hxD (by simp [hgrx])
    refine ⟨s + t, -t, fun y => ?_, fun y => ?_, by abel⟩
    · have := ht₁ y
      simp only [sub_self, inner_zero_right, add_zero, inner_add_left] at this ⊢
      linarith
    · by_cases hy : y ∈ D
      · have := ht₂ y hy
        rw [hv, ← hgr y hy, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_neg_left]
        simp only [hgrx, sub_self, zero_add] at this
        linarith
      · have : g y = ⊤ := by
          by_contra hne
          exact hy ⟨trivial, lt_top_iff_ne_top.2 hne⟩
        rw [this]
        exact le_top
  · rintro ⟨s₁, s₂, h₁, h₂, rfl⟩ y
    have e : (↑(f x) + g x : EReal) + ⟪s₁ + s₂, y - x⟫ =
        (↑(f x) + ⟪s₁, y - x⟫ : EReal) + (g x + ⟪s₂, y - x⟫) := by
      rw [hv, inner_add_left]
      norm_cast
      ring
    rw [e]
    refine add_le_add ?_ (h₂ y)
    have := h₁ y
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith

/-- **Sum rule** in finite dimension: for a convex `f : E → ℝ` and a convex `g : E → EReal`
with `g x` finite, `∂(f + g)(x) = ∂f(x) + ∂g(x)`. -/
theorem hasERealSubgradientAt_add_iff [FiniteDimensional ℝ E] (hf : ConvexOn ℝ univ f)
    (hg : ConvexOn ℝ (dom univ g) g) (hbot : g x ≠ ⊥) (htop : g x ≠ ⊤) :
    HasERealSubgradientAt (fun y => (f y : EReal) + g y) s x ↔
      ∃ s₁ s₂, HasSubgradientAt f s₁ x ∧ HasERealSubgradientAt g s₂ x ∧ s = s₁ + s₂ :=
  hasERealSubgradientAt_add_iff_of_continuous hf hf.continuous_of_finiteDimensional hg hbot htop

end Sum

/-! ### Chain rule for linear maps -/

section Chain

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {h : F → ℝ} {x s : E}

/-- **Chain rule.** For a continuous convex `h : F → ℝ` and a continuous linear `A : E → F`
between Hilbert spaces, `s ∈ ∂(h ∘ A)(x)` iff `s = A† t` for some `t ∈ ∂h(A x)`. The range of
`A` need not be closed: `h - h (A x)` is sandwiched against `A y ↦ ⟪s, y - x⟫` on `range A`. -/
theorem hasSubgradientAt_comp_iff_of_continuous [CompleteSpace E] [CompleteSpace F]
    (hh : ConvexOn ℝ univ h) (hhc : Continuous h) (A : E →L[ℝ] F) :
    HasSubgradientAt (h ∘ A) s x ↔
      ∃ t, HasSubgradientAt h t (A x) ∧ s = ContinuousLinearMap.adjoint A t := by
  constructor
  · intro hs
    -- `s` vanishes on `ker A`
    have hker : ∀ k, A k = 0 → ⟪s, k⟫ = 0 := by
      intro k hAk
      have h1 := hs (x + k)
      have h2 := hs (x - k)
      simp only [Function.comp_apply, map_add, map_sub, hAk, add_zero, sub_zero,
        add_sub_cancel_left, sub_sub_cancel_left, inner_neg_right] at h1 h2
      linarith
    -- so `G (A y) = ⟪s, y - x⟫` is well defined on `range A`
    set D : Set F := Set.range A
    let G : F → ℝ := fun z => ⟪s, Classical.epsilon (fun y => A y = z) - x⟫
    have hGA : ∀ y, G (A y) = ⟪s, y - x⟫ := by
      intro y
      have hA : A (Classical.epsilon (fun y' => A y' = A y)) = A y :=
        Classical.epsilon_spec (p := fun y' => A y' = A y) ⟨y, rfl⟩
      have := hker (Classical.epsilon (fun y' => A y' = A y) - y) (by rw [map_sub, hA, sub_self])
      simp only [G, inner_sub_right] at this ⊢
      linarith
    have hG : ConcaveOn ℝ D G := by
      have hD : Convex ℝ D := by
        have := (LinearMap.range (A : E →ₗ[ℝ] F)).convex
        rwa [LinearMap.coe_range] at this
      refine ⟨hD, ?_⟩
      rintro _ ⟨y₁, rfl⟩ _ ⟨y₂, rfl⟩ a b ha hb hab
      have e : a • A y₁ + b • A y₂ = A (a • y₁ + b • y₂) := by simp
      rw [hGA y₁, hGA y₂, e, hGA]
      simp only [smul_eq_mul, inner_sub_right, inner_add_right, real_inner_smul_right]
      have hx : ⟪s, x⟫ = a * ⟪s, x⟫ + b * ⟪s, x⟫ := by rw [← add_mul, hab, one_mul]
      nlinarith
    obtain ⟨t, ht₁, ht₂⟩ := exists_affine_sandwich_of_continuous
      (hh.sub_affine (h (A x)) 0 (A x)) (hhc.sub_affine (h (A x)) 0 (A x)) hG
      (fun z hz => by
        obtain ⟨y, rfl⟩ := hz
        have h1 := hs y
        simp only [Function.comp_apply, inner_zero_left, add_zero] at h1 ⊢
        rw [hGA]
        linarith)
      (Set.mem_range_self x) (by simp [hGA])
    refine ⟨t, fun z => ?_, ?_⟩
    · have := ht₁ z
      simp only [sub_self, inner_zero_left, inner_zero_right, add_zero, zero_add] at this
      linarith
    · -- `⟪s - A† t, v⟫ ≤ 0` for all `v`, so `s = A† t`
      have hle : ∀ v, ⟪s - ContinuousLinearMap.adjoint A t, v⟫ ≤ 0 := by
        intro v
        have := ht₂ (A (x + v)) (Set.mem_range_self _)
        rw [hGA, hGA] at this
        simp only [map_add, add_sub_cancel_left, sub_self, inner_zero_right, zero_add] at this
        rw [inner_sub_left, ContinuousLinearMap.adjoint_inner_left]
        linarith
      have h0 : s - ContinuousLinearMap.adjoint A t = 0 := by
        have h1 := hle (s - ContinuousLinearMap.adjoint A t)
        rw [real_inner_self_eq_norm_sq] at h1
        exact norm_eq_zero.1
          (by nlinarith [norm_nonneg (s - ContinuousLinearMap.adjoint A t)])
      exact sub_eq_zero.1 h0
  · rintro ⟨t, ht, rfl⟩ y
    have := ht (A y)
    simp only [Function.comp_apply, ge_iff_le] at this ⊢
    rw [ContinuousLinearMap.adjoint_inner_left, map_sub]
    exact this

/-- **Chain rule** in finite dimension: for a convex `h : F → ℝ` and a linear `A : E → F`,
`s ∈ ∂(h ∘ A)(x)` iff `s = A† t` for some `t ∈ ∂h(A x)`. -/
theorem hasSubgradientAt_comp_iff [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hh : ConvexOn ℝ univ h) (A : E →L[ℝ] F) :
    HasSubgradientAt (h ∘ A) s x ↔
      ∃ t, HasSubgradientAt h t (A x) ∧ s = ContinuousLinearMap.adjoint A t :=
  hasSubgradientAt_comp_iff_of_continuous hh hh.continuous_of_finiteDimensional A

end Chain

/-! ### Finite sums -/

section FinsetSum

variable {ι : Type*} [DecidableEq ι]

/-- **Sum rule for finitely many continuous convex functions** `φ i : E → ℝ` on a Hilbert
space: `∂(∑ᵢ φ i)(x) = ∑ᵢ ∂(φ i)(x)`. -/
theorem hasSubgradientAt_finset_sum_iff_of_continuous [CompleteSpace E] (s : Finset ι)
    {φ : ι → E → ℝ} (hφ : ∀ i ∈ s, ConvexOn ℝ univ (φ i)) (hφc : ∀ i ∈ s, Continuous (φ i))
    {x g : E} :
    HasSubgradientAt (fun v => ∑ i ∈ s, φ i v) g x ↔
      ∃ gi : ι → E, (∀ i ∈ s, HasSubgradientAt (φ i) (gi i) x) ∧ g = ∑ i ∈ s, gi i := by
  induction s using Finset.induction_on generalizing g with
  | empty =>
    simp only [Finset.sum_empty, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
      true_and, exists_const]
    constructor
    · intro h
      have := h (x + g)
      simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq, ge_iff_le, zero_add] at this
      exact norm_eq_zero.1 (by nlinarith [norm_nonneg g])
    · rintro rfl y
      simp
  | insert a s ha ih =>
    have hφa := hφ a (Finset.mem_insert_self a s)
    have hφs : ∀ i ∈ s, ConvexOn ℝ univ (φ i) := fun i hi => hφ i (Finset.mem_insert_of_mem hi)
    have hφcs : ∀ i ∈ s, Continuous (φ i) := fun i hi => hφc i (Finset.mem_insert_of_mem hi)
    have hsum : ConvexOn ℝ univ (fun v => ∑ i ∈ s, φ i v) := ConvexOn.sum hφs convex_univ
    have hadd := SubderivAt.add hφa hsum (hφc a (Finset.mem_insert_self a s)).continuousOn x
    have e : (fun v => ∑ i ∈ insert a s, φ i v) = φ a + fun v => ∑ i ∈ s, φ i v := by
      funext v
      simp [Finset.sum_insert ha]
    rw [e, mem_SubderivAt, ← hadd, Set.mem_add]
    constructor
    · rintro ⟨g₁, hg₁, g₂, hg₂, rfl⟩
      obtain ⟨gi, hgi, rfl⟩ := (ih hφs hφcs).1 hg₂
      have hne : ∀ i ∈ s, i ≠ a := fun i hi h => ha (h ▸ hi)
      refine ⟨Function.update gi a g₁, fun i hi => ?_, ?_⟩
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · simpa using hg₁
        · rw [Function.update_of_ne (hne i hi)]
          exact hgi i hi
      · rw [Finset.sum_insert ha, Function.update_self]
        congr 1
        exact Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (hne i hi)]
    · rintro ⟨gi, hgi, rfl⟩
      refine ⟨gi a, hgi a (Finset.mem_insert_self a s), ∑ i ∈ s, gi i,
        (ih hφs hφcs).2 ⟨gi, fun i hi => hgi i (Finset.mem_insert_of_mem hi), rfl⟩, ?_⟩
      rw [Finset.sum_insert ha]

/-- **Sum rule for finitely many convex functions** `φ i : E → ℝ` in finite dimension:
`∂(∑ᵢ φ i)(x) = ∑ᵢ ∂(φ i)(x)`. -/
theorem hasSubgradientAt_finset_sum_iff [FiniteDimensional ℝ E] (s : Finset ι) {φ : ι → E → ℝ}
    (hφ : ∀ i ∈ s, ConvexOn ℝ univ (φ i)) {x g : E} :
    HasSubgradientAt (fun v => ∑ i ∈ s, φ i v) g x ↔
      ∃ gi : ι → E, (∀ i ∈ s, HasSubgradientAt (φ i) (gi i) x) ∧ g = ∑ i ∈ s, gi i :=
  hasSubgradientAt_finset_sum_iff_of_continuous s hφ
    (fun i hi => (hφ i hi).continuous_of_finiteDimensional)

end FinsetSum
