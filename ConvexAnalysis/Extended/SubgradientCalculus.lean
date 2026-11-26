/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import ConvexAnalysis.Extended.FenchelYoung
import ConvexAnalysis.Extended.AffineMinorantExistence
import ConvexAnalysis.Extended.IntrinsicInterior

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

## Extended-real functions with an interior point

* `exists_affine_sandwich_of_continuousAt`: the sandwich theorem for `F` convex on a set `C`,
  when `F` is continuous at a point of `int C ∩ D`. The other sandwich theorems follow from it.
* `hasERealSubgradientAt_add_iff_of_continuousAt` (sum rule): for convex `f, g : E → EReal`
  on a Hilbert space, `f` continuous at a point of `int (dom f) ∩ dom g`,
  `∂(f + g)(x) = ∂f(x) + ∂g(x)`.
* `hasERealSubgradientAt_comp_iff_of_continuousAt` (chain rule): for a convex `h : F → EReal`
  continuous at a point `A x₀ ∈ int (dom h)`, `∂(h ∘ A)(x) = A† ∂h(A x)`.
* `hasERealSubgradientAt_add_iff_of_mem_interior`, `hasERealSubgradientAt_comp_iff_of_mem_interior`:
  the finite-dimensional cases, where the continuity is automatic
  (`continuousAt_of_convexOn_of_mem_interior_dom`).

## Relative interiors (finite dimension)

* `exists_affine_sandwich_of_mem_intrinsicInterior`: the sandwich theorem when
  `ri C ∩ ri D ≠ ∅`. With `x₀` in both relative interiors, the interior-point theorem is applied
  inside `V = span (C - x₀)` and inside `W = span (D - x₀)`, and the two slopes are glued with
  `(V ⊓ W)ᗮ = Vᗮ ⊔ Wᗮ`.
* `hasERealSubgradientAt_add_iff_of_mem_intrinsicInterior` (Rockafellar, Thm 23.8): the sum rule
  for convex `f, g : E → EReal` with `ri (dom f) ∩ ri (dom g) ≠ ∅`.
* `hasERealSubgradientAt_comp_iff_of_mem_intrinsicInterior` (Rockafellar, Thm 23.9): the chain
  rule for a convex `h : F → EReal` when the range of `A` meets `ri (dom h)`.

The extended-real sum and chain rules share their proofs through
`hasERealSubgradientAt_add_iff_of_sandwich` and `hasERealSubgradientAt_comp_iff_of_sandwich`,
which take the sandwich theorem for the relevant pair of sets as a hypothesis.
-/

open Set Topology

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The sandwich theorem -/

section Sandwich

/-- **Sandwich theorem.** Let `F` be convex on `C` and `G` concave on `D`, with `G ≤ F` on
`C ∩ D` and `F x = G x` for some `x ∈ C ∩ D`. If `F` is continuous at some point of
`interior C ∩ D`, there is `t : E` with `F x + ⟪t, y - x⟫ ≤ F y` for `y ∈ C` and
`G y ≤ G x + ⟪t, y - x⟫` for `y ∈ D`. The proof separates the interior of the strict epigraph
of `F` from the hypograph of `G`. -/
theorem exists_affine_sandwich_of_continuousAt [CompleteSpace E] {F G : E → ℝ} {C D : Set E}
    (hF : ConvexOn ℝ C F) (hG : ConcaveOn ℝ D G) (hle : ∀ y ∈ C, y ∈ D → G y ≤ F y)
    {x₀ : E} (hx₀C : x₀ ∈ interior C) (hx₀D : x₀ ∈ D) (hFc : ContinuousAt F x₀)
    {x : E} (hxC : x ∈ C) (hxD : x ∈ D) (hFG : F x = G x) :
    ∃ t : E, (∀ y ∈ C, F x + ⟪t, y - x⟫ ≤ F y) ∧ (∀ y ∈ D, G y ≤ G x + ⟪t, y - x⟫) := by
  -- the strict epigraph of `F` over `C` and the hypograph of `G` over `D`
  set S : Set (E × ℝ) := {p | p.1 ∈ C ∧ F p.1 < p.2}
  set C₂ : Set (E × ℝ) := {p | p.1 ∈ D ∧ p.2 ≤ G p.1}
  have hSc : Convex ℝ S := hF.convex_strict_epigraph
  have hC₂c : Convex ℝ C₂ := hG.convex_hypograph
  -- `(x₀, F x₀ + 1)` is an interior point of the strict epigraph
  have hint : (x₀, F x₀ + 1) ∈ interior S := by
    have h1 : ∀ᶠ y in 𝓝 x₀, y ∈ C := mem_interior_iff_mem_nhds.1 hx₀C
    have h2 : ∀ᶠ y in 𝓝 x₀, F y < F x₀ + 1 / 2 :=
      hFc.eventually_lt continuousAt_const (by linarith)
    have ha : ∀ᶠ p : E × ℝ in 𝓝 (x₀, F x₀ + 1), p.1 ∈ C ∧ F p.1 < F x₀ + 1 / 2 :=
      (continuous_fst.tendsto (x₀, F x₀ + 1)).eventually (h1.and h2)
    have hb : ∀ᶠ p : E × ℝ in 𝓝 (x₀, F x₀ + 1), F x₀ + 1 / 2 < p.2 :=
      (continuous_snd.tendsto (x₀, F x₀ + 1)).eventually (lt_mem_nhds (by simp; linarith))
    refine mem_interior_iff_mem_nhds.2 ?_
    filter_upwards [ha, hb] with p hp hp'
    exact ⟨hp.1, hp.2.trans hp'⟩
  have hdisj : Disjoint (interior S) C₂ := by
    rw [Set.disjoint_left]
    rintro p hp ⟨hpD, hpG⟩
    have hpS := interior_subset hp
    exact absurd (hpG.trans (hle p.1 hpS.1 hpD)) (not_le.2 hpS.2)
  obtain ⟨φ, c, hφ₁, hφ₂⟩ :=
    geometric_hahn_banach_open hSc.interior isOpen_interior hC₂c hdisj
  -- `φ ≤ c` on the whole strict epigraph, which lies in the closure of its interior
  have hφS : ∀ p ∈ S, φ p ≤ c := by
    intro p hp
    have hcl : p ∈ closure (interior S) := by
      rw [hSc.closure_interior_eq_closure_of_nonempty_interior ⟨_, hint⟩]
      exact subset_closure hp
    exact closure_minimal (fun q hq => (hφ₁ q hq).le)
      (isClosed_le φ.continuous continuous_const) hcl
  set α := φ (0, 1)
  set ℓ : E →L[ℝ] ℝ := φ.comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hℓ : ∀ y, ℓ y = φ (y, 0) := fun _ => rfl
  have hsplit : ∀ y μ, φ (y, μ) = ℓ y + μ * α := fun y μ => by
    rw [hℓ, φ.apply_prod_real (y, μ)]
  have h₁ : ∀ y ∈ C, ∀ μ, F y < μ → ℓ y + μ * α ≤ c := fun y hy μ h => by
    simpa [hsplit] using hφS (y, μ) ⟨hy, h⟩
  have h₂ : ∀ y ∈ D, c ≤ ℓ y + G y * α := fun y hy => by
    simpa [hsplit] using hφ₂ (y, G y) ⟨hy, le_rfl⟩
  -- the separating hyperplane is not vertical: `α < 0`
  have hα : α < 0 := by
    have a := hφ₁ (x₀, F x₀ + 1) hint
    rw [hsplit] at a
    have b := h₂ x₀ hx₀D
    have d := hle x₀ (interior_subset hx₀C) hx₀D
    by_contra hneg
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ F x₀ + 1 - G x₀) (not_lt.1 hneg)
    nlinarith
  -- `ℓ y + α F y ≤ c` for all `y ∈ C`
  have h₁' : ∀ y ∈ C, ℓ y + F y * α ≤ c := by
    intro y hyC
    by_contra hcon
    push Not at hcon
    set δ := ℓ y + F y * α - c
    have := h₁ y hyC (F y + δ / (-2 * α)) (by
      have : 0 < δ / (-2 * α) := div_pos (by linarith) (by linarith)
      linarith)
    have hαne : α ≠ 0 := hα.ne
    have e : ℓ y + (F y + δ / (-2 * α)) * α = ℓ y + F y * α - δ / 2 := by
      field_simp; ring
    linarith
  have hxx := h₁' x hxC
  have hx' := h₂ x hxD
  rw [← hFG] at hx'
  -- `c = ℓ x + α F x`
  have hc : c = ℓ x + F x * α := le_antisymm (by linarith) hxx
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (-(α⁻¹) • ℓ), fun y hy => ?_, fun y hy => ?_⟩
  all_goals
    rw [InnerProductSpace.toDual_symm_apply, smul_apply, map_sub,
      smul_eq_mul]
  · have hy' := h₁' y hy
    have key : (F y - F x) * α ≤ -(ℓ y - ℓ x) := by linarith
    have : -α⁻¹ * (ℓ y - ℓ x) ≤ F y - F x := by
      rw [show -α⁻¹ * (ℓ y - ℓ x) = -(ℓ y - ℓ x) / α by ring]
      exact (div_le_iff_of_neg hα).2 key
    linarith
  · have hy' := h₂ y hy
    rw [hFG] at hc
    have key : -(ℓ y - ℓ x) ≤ (G y - G x) * α := by linarith
    have : G y - G x ≤ -α⁻¹ * (ℓ y - ℓ x) := by
      rw [show -α⁻¹ * (ℓ y - ℓ x) = -(ℓ y - ℓ x) / α by ring]
      exact (le_div_iff_of_neg hα).2 key
    linarith

/-- **Sandwich theorem** for a continuous convex `F : E → ℝ`. Let `G` be concave on a convex
set `D`, with `G ≤ F` on `D` and `F x = G x` for some `x ∈ D`. Then there is `t : E` with
`F x + ⟪t, y - x⟫ ≤ F y` for all `y` and `G y ≤ G x + ⟪t, y - x⟫` for `y ∈ D`. -/
theorem exists_affine_sandwich_of_continuous [CompleteSpace E] {F G : E → ℝ} {D : Set E}
    (hF : ConvexOn ℝ univ F) (hFc : Continuous F) (hG : ConcaveOn ℝ D G)
    (hle : ∀ y ∈ D, G y ≤ F y) {x : E} (hx : x ∈ D) (hFG : F x = G x) :
    ∃ t : E, (∀ y, F x + ⟪t, y - x⟫ ≤ F y) ∧ (∀ y ∈ D, G y ≤ G x + ⟪t, y - x⟫) := by
  obtain ⟨t, h1, h2⟩ := exists_affine_sandwich_of_continuousAt hF hG (fun y _ hy => hle y hy)
    (x₀ := x) (by simp) hx hFc.continuousAt (mem_univ x) hx hFG
  exact ⟨t, fun y => h1 y (mem_univ y), h2⟩

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

/-- Subtracting an affine function preserves continuity at a point. -/
lemma ContinuousAt.sub_affine {f : E → ℝ} {z : E} (hf : ContinuousAt f z) (c : ℝ) (s x : E) :
    ContinuousAt (fun y => f y - (c + ⟪s, y - x⟫)) z :=
  hf.sub (continuousAt_const.add
    (continuous_const.inner (continuous_id.sub continuous_const)).continuousAt)

/-- A constant minus a convex function is concave. -/
lemma ConvexOn.const_sub {f : E → ℝ} (hf : ConvexOn ℝ D f) (c : ℝ) :
    ConcaveOn ℝ D (fun y => c - f y) := by
  refine ⟨hf.1, fun y hy z hz a b ha hb hab => ?_⟩
  have := hf.2 hy hz ha hb hab
  simp only [smul_eq_mul] at this ⊢
  have hc : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
  nlinarith

end Shift

/-! ### The sandwich theorem with relative interiors -/

section RelativeInterior

variable [FiniteDimensional ℝ E]

/-- If `0 ∈ W`, `W` is convex and every `y ∈ W` can be prolonged through `0` inside `W`, then
`0` is an interior point of `W` relative to its linear span. -/
lemma zero_mem_interior_preimage_span {W : Set E} (hW : Convex ℝ W) (h0 : (0 : E) ∈ W)
    (hprol : ∀ y ∈ W, ∃ μ > (1 : ℝ), (1 - μ) • y ∈ W) :
    (0 : Submodule.span ℝ W) ∈ interior (((↑) : Submodule.span ℝ W → E) ⁻¹' W) := by
  set V := Submodule.span ℝ W
  set Ct : Set V := ((↑) : V → E) ⁻¹' W
  have hc : Convex ℝ Ct := hW.linear_preimage V.subtype
  have hne : (intrinsicInterior ℝ Ct).Nonempty :=
    Set.Nonempty.intrinsicInterior hc ⟨0, by simpa [Ct] using h0⟩
  rw [mem_interior_iff_forall_exists_pos_add_smul_mem hc hne]
  -- the cone generated by `W` is a subspace, hence contains `span W`
  have key : ∀ u ∈ V, ∃ ε > (0 : ℝ), ε • u ∈ W := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy => exact ⟨1, one_pos, by simpa using hy⟩
    | zero => exact ⟨1, one_pos, by simpa using h0⟩
    | add a b _ _ iha ihb =>
      obtain ⟨ε₁, h₁, ha⟩ := iha
      obtain ⟨ε₂, h₂, hb⟩ := ihb
      have hpos : 0 < ε₁ + ε₂ := by linarith
      refine ⟨ε₁ * ε₂ / (ε₁ + ε₂), by positivity, ?_⟩
      have := hW ha hb (a := ε₂ / (ε₁ + ε₂)) (b := ε₁ / (ε₁ + ε₂)) (by positivity)
        (by positivity) (by rw [← add_div, add_comm ε₂ ε₁, div_self hpos.ne'])
      have e1 : ε₂ / (ε₁ + ε₂) * ε₁ = ε₁ * ε₂ / (ε₁ + ε₂) := by ring
      have e2 : ε₁ / (ε₁ + ε₂) * ε₂ = ε₁ * ε₂ / (ε₁ + ε₂) := by ring
      rw [smul_smul, smul_smul, e1, e2, ← smul_add] at this
      exact this
    | smul c u _ ih =>
      obtain ⟨ε, hε, hu⟩ := ih
      rcases lt_trichotomy c 0 with hc | rfl | hc
      · obtain ⟨μ, hμ, hmem⟩ := hprol _ hu
        refine ⟨(μ - 1) * ε / (-c), div_pos (mul_pos (by linarith) hε) (by linarith), ?_⟩
        have e : ((μ - 1) * ε / (-c)) • c • u = (1 - μ) • ε • u := by
          rw [smul_smul, smul_smul]
          congr 1
          rw [div_mul_eq_mul_div, div_eq_iff (neg_ne_zero.2 hc.ne)]
          ring
        rw [e]
        exact hmem
      · exact ⟨1, one_pos, by simpa using h0⟩
      · refine ⟨ε / c, div_pos hε hc, ?_⟩
        rw [smul_smul, div_mul_cancel₀ _ hc.ne']
        exact hu
  intro v
  obtain ⟨ε, hε, h⟩ := key v v.2
  exact ⟨ε, hε, by simpa [Ct] using h⟩

/-- One half of the sandwich theorem with relative interiors: if `x₀ ∈ ri C ∩ D`, the
interior-point sandwich theorem applies inside the subspace `V = span (C - x₀)`, and gives the
inequality for `G` only on `D ∩ (x₀ + V)`. -/
lemma exists_affine_sandwich_aux {F G : E → ℝ} {C D : Set E}
    (hF : ConvexOn ℝ C F) (hG : ConcaveOn ℝ D G) (hle : ∀ y ∈ C, y ∈ D → G y ≤ F y)
    {x₀ : E} (hx₀C : x₀ ∈ intrinsicInterior ℝ C) (hx₀D : x₀ ∈ D)
    {x : E} (hxC : x ∈ C) (hxD : x ∈ D) (hFG : F x = G x) :
    ∃ t : E, (∀ y ∈ C, F x + ⟪t, y - x⟫ ≤ F y) ∧
      ∀ y ∈ D, y - x₀ ∈ Submodule.span ℝ ((fun v => x₀ + v) ⁻¹' C) →
        G y ≤ G x + ⟪t, y - x⟫ := by
  set W : Set E := (fun v => x₀ + v) ⁻¹' C
  have hW : Convex ℝ W := hF.1.translate_preimage_right x₀
  have h0 : (0 : E) ∈ W := by simpa [W] using intrinsicInterior_subset hx₀C
  have hprol : ∀ y ∈ W, ∃ μ > (1 : ℝ), (1 - μ) • y ∈ W := by
    intro y hy
    have hyC : x₀ + y ∈ C := hy
    obtain ⟨μ, hμ, hmem⟩ := intrinsicInterior_forall_exist_of_intrinsicInterior
      ⟨_, hyC⟩ hx₀C (x₀ + y) hyC
    refine ⟨μ, hμ, ?_⟩
    have e : (1 - μ) • (x₀ + y) + μ • x₀ = x₀ + (1 - μ) • y := by
      rw [smul_add, sub_smul, one_smul]
      abel
    rw [e] at hmem
    exact hmem
  set V := Submodule.span ℝ W
  set Ct : Set V := ((↑) : V → E) ⁻¹' W
  set Dt : Set V := V.subtype ⁻¹' ((fun z => x₀ + z) ⁻¹' D)
  have hFt : ConvexOn ℝ Ct (fun v : V => F (x₀ + v)) :=
    (hF.translate_right x₀).comp_linearMap V.subtype
  have hGt : ConcaveOn ℝ Dt (fun v : V => G (x₀ + v)) :=
    (hG.translate_right x₀).comp_linearMap V.subtype
  have h0int : (0 : V) ∈ interior Ct := zero_mem_interior_preimage_span hW h0 hprol
  have hcont : ContinuousAt (fun v : V => F (x₀ + v)) 0 :=
    ((hFt.subset interior_subset hFt.1.interior).continuousOn isOpen_interior).continuousAt
      (isOpen_interior.mem_nhds h0int)
  have hmemC : ∀ y ∈ C, x₀ + (y - x₀) ∈ C := fun y hy => by rwa [add_sub_cancel]
  have hmemD : ∀ y ∈ D, x₀ + (y - x₀) ∈ D := fun y hy => by rwa [add_sub_cancel]
  have hxV : x - x₀ ∈ V := Submodule.subset_span (hmemC x hxC)
  obtain ⟨tt, h1, h2⟩ := exists_affine_sandwich_of_continuousAt hFt hGt
    (x₀ := 0) (x := ⟨x - x₀, hxV⟩) (fun v hvC hvD => hle _ hvC hvD) h0int
    (show x₀ + ((0 : V) : E) ∈ D by simpa using hx₀D) hcont (hmemC x hxC) (hmemD x hxD)
    (by
      show F (x₀ + (x - x₀)) = G (x₀ + (x - x₀))
      rw [add_sub_cancel]
      exact hFG)
  have hinner : ∀ y (hyV : y - x₀ ∈ V),
      (⟪tt, (⟨y - x₀, hyV⟩ : V) - ⟨x - x₀, hxV⟩⟫ : ℝ) = ⟪(tt : E), y - x⟫ := by
    intro y hyV
    rw [Submodule.coe_inner]
    congr 1
    simp
  refine ⟨(tt : E), fun y hy => ?_, fun y hy hyV => ?_⟩
  · have hyV : y - x₀ ∈ V := Submodule.subset_span (hmemC y hy)
    have := h1 ⟨y - x₀, hyV⟩ (hmemC y hy)
    rw [hinner y hyV] at this
    simpa only [add_sub_cancel] using this
  · have := h2 ⟨y - x₀, hyV⟩ (hmemD y hy)
    rw [hinner y hyV] at this
    simpa only [add_sub_cancel] using this

/-- **Sandwich theorem with relative interiors** (finite dimension). Let `F` be convex on `C`
and `G` concave on `D`, with `G ≤ F` on `C ∩ D` and `F x = G x` for some `x ∈ C ∩ D`. If
`ri C ∩ ri D ≠ ∅`, there is `t : E` with `F x + ⟪t, y - x⟫ ≤ F y` for `y ∈ C` and
`G y ≤ G x + ⟪t, y - x⟫` for `y ∈ D`.

The interior-point theorem is applied twice, inside `V = span (C - x₀)` and inside
`W = span (D - x₀)`; the two slopes are glued with `(V ⊓ W)ᗮ = Vᗮ ⊔ Wᗮ`. -/
theorem exists_affine_sandwich_of_mem_intrinsicInterior {F G : E → ℝ} {C D : Set E}
    (hF : ConvexOn ℝ C F) (hG : ConcaveOn ℝ D G) (hle : ∀ y ∈ C, y ∈ D → G y ≤ F y)
    {x₀ : E} (hx₀C : x₀ ∈ intrinsicInterior ℝ C) (hx₀D : x₀ ∈ intrinsicInterior ℝ D)
    {x : E} (hxC : x ∈ C) (hxD : x ∈ D) (hFG : F x = G x) :
    ∃ t : E, (∀ y ∈ C, F x + ⟪t, y - x⟫ ≤ F y) ∧ (∀ y ∈ D, G y ≤ G x + ⟪t, y - x⟫) := by
  obtain ⟨t, ht₁, ht₂⟩ := exists_affine_sandwich_aux hF hG hle hx₀C
    (intrinsicInterior_subset hx₀D) hxC hxD hFG
  set V := Submodule.span ℝ ((fun v => x₀ + v) ⁻¹' C)
  set W := Submodule.span ℝ ((fun v => x₀ + v) ⁻¹' D)
  have hmemV : ∀ y ∈ C, y - x₀ ∈ V := fun y hy =>
    Submodule.subset_span (show x₀ + (y - x₀) ∈ C by rwa [add_sub_cancel])
  have hmemW : ∀ y ∈ D, y - x₀ ∈ W := fun y hy =>
    Submodule.subset_span (show x₀ + (y - x₀) ∈ D by rwa [add_sub_cancel])
  have hxV := hmemV x hxC
  have hxW := hmemW x hxD
  -- second application: `-(G - G x - ⟪t, · - x⟫)` on `D` against `0` on `x₀ + V`
  set D₂ : Set E := {y | y - x₀ ∈ V}
  have hD₂ : Convex ℝ D₂ := by
    intro a ha b hb α β _ _ hαβ
    have hx : x₀ = α • x₀ + β • x₀ := by rw [← add_smul, hαβ, one_smul]
    have e : α • a + β • b - x₀ = α • (a - x₀) + β • (b - x₀) := by
      rw [smul_sub, smul_sub]
      nth_rw 1 [hx]
      abel
    show α • a + β • b - x₀ ∈ V
    rw [e]
    exact V.add_mem (V.smul_mem α ha) (V.smul_mem β hb)
  obtain ⟨s', hs₁, hs₂⟩ := exists_affine_sandwich_aux
    (hG.neg.sub_affine (-(G x)) (-t) x) (concaveOn_const 0 hD₂)
    (fun y hy hy2 => by
      have := ht₂ y hy hy2
      simp only [Pi.neg_apply, inner_neg_left]
      linarith)
    hx₀D (show x₀ - x₀ ∈ V by simp) hxD hxV (by simp)
  -- `s'` is orthogonal to `V ⊓ W`
  have hperp : s' ∈ (V ⊓ W)ᗮ := by
    refine (Submodule.mem_orthogonal' _ _).2 fun d hd => ?_
    obtain ⟨hdV, hdW⟩ := Submodule.mem_inf.1 hd
    have h1 := hs₂ (x + d) (show x + d - x₀ ∈ V by
      rw [add_sub_right_comm]; exact V.add_mem hxV hdV)
      (by rw [add_sub_right_comm]; exact W.add_mem hxW hdW)
    have h2 := hs₂ (x - d) (show x - d - x₀ ∈ V by
      rw [sub_right_comm]; exact V.sub_mem hxV hdV)
      (by rw [sub_right_comm]; exact W.sub_mem hxW hdW)
    simp only [add_sub_cancel_left, sub_sub_cancel_left, inner_neg_right, zero_add] at h1 h2
    linarith
  have horth : (V ⊓ W)ᗮ = Vᗮ ⊔ Wᗮ := by
    rw [← Submodule.orthogonal_orthogonal (Vᗮ ⊔ Wᗮ), ← Submodule.inf_orthogonal,
      Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal]
  rw [horth] at hperp
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 hperp
  refine ⟨t - p, fun y hy => ?_, fun y hy => ?_⟩
  · have hyx : y - x ∈ V := by
      have := V.sub_mem (hmemV y hy) hxV
      rwa [sub_sub_sub_cancel_right] at this
    have h0 : ⟪p, y - x⟫ = 0 := Submodule.inner_left_of_mem_orthogonal hyx hp
    have := ht₁ y hy
    rw [inner_sub_left, h0]
    linarith
  · have hyx : y - x ∈ W := by
      have := W.sub_mem (hmemW y hy) hxW
      rwa [sub_sub_sub_cancel_right] at this
    have hq0 : ⟪q, y - x⟫ = 0 := Submodule.inner_left_of_mem_orthogonal hyx hq
    have := hs₁ y hy
    simp only [Pi.neg_apply, sub_self, inner_zero_right, add_zero, inner_neg_left,
      zero_add] at this
    rw [← hpq, inner_add_left, hq0] at this
    rw [inner_sub_left]
    linarith

end RelativeInterior

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

/-- A convex `f : E → EReal` on a finite-dimensional space that never takes the value `⊥` is
continuous at the interior points of its effective domain. -/
lemma continuousAt_of_convexOn_of_mem_interior_dom {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → EReal}
    (hf : ConvexOn ℝ (dom univ f) f) (hfb : ∀ y, f y ≠ ⊥) {x₀ : E}
    (hx₀ : x₀ ∈ interior (dom univ f)) : ContinuousAt f x₀ := by
  set fr : E → ℝ := fun y => (f y).toReal
  have hfr : ∀ y ∈ dom univ f, (fr y : EReal) = f y := fun y hy =>
    EReal.coe_toReal hy.2.ne (hfb y)
  have hfrc : ConvexOn ℝ (dom univ f) fr := by
    rw [ProperFunctionConvexOn_iff_ConvexOn]
    exact hf.congr fun y hy => (hfr y hy).symm
  have hc : ContinuousAt fr x₀ :=
    ((hfrc.subset interior_subset hfrc.1.interior).continuousOn isOpen_interior).continuousAt
      (isOpen_interior.mem_nhds hx₀)
  have hc' : ContinuousAt (fun y => (fr y : EReal)) x₀ :=
    continuous_coe_real_ereal.continuousAt.comp hc
  refine hc'.congr ?_
  filter_upwards [mem_interior_iff_mem_nhds.1 hx₀] with y hy using hfr y hy

/-- The sum rule for two extended-real convex functions, given a sandwich theorem for the pair
`(dom f, dom g)`: the hypothesis `hsw` provides a common slope for a convex `F` on `dom f`
(continuous wherever the real part of `f` is) and a concave `G` on `dom g` that touch at `x`.
The sum rules below supply `hsw` from an interior point or from a point of the relative
interiors. -/
theorem hasERealSubgradientAt_add_iff_of_sandwich {f g : E → EReal} {x s : E}
    (hf : ConvexOn ℝ (dom univ f) f) (hg : ConvexOn ℝ (dom univ g) g) (hfb : ∀ y, f y ≠ ⊥)
    (hfx : f x ≠ ⊤) (hbot : g x ≠ ⊥) (htop : g x ≠ ⊤)
    (hsw : ∀ F G : E → ℝ, ConvexOn ℝ (dom univ f) F →
      (∀ z, ContinuousAt (fun y => (f y).toReal) z → ContinuousAt F z) →
      ConcaveOn ℝ (dom univ g) G → (∀ y ∈ dom univ f, y ∈ dom univ g → G y ≤ F y) →
      x ∈ dom univ f → x ∈ dom univ g → F x = G x →
      ∃ t : E, (∀ y ∈ dom univ f, F x + ⟪t, y - x⟫ ≤ F y) ∧
        ∀ y ∈ dom univ g, G y ≤ G x + ⟪t, y - x⟫) :
    HasERealSubgradientAt (fun y => f y + g y) s x ↔
      ∃ s₁ s₂, HasERealSubgradientAt f s₁ x ∧ HasERealSubgradientAt g s₂ x ∧ s = s₁ + s₂ := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, f x = u := ⟨(f x).toReal, (EReal.coe_toReal hfx (hfb x)).symm⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, g x = v := ⟨(g x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  constructor
  · intro h
    have h' : ∀ y, (u : EReal) + v + ⟪s, y - x⟫ ≤ f y + g y := fun y => by
      simpa only [hu, hv] using h y
    have hgb : ∀ y, g y ≠ ⊥ := fun y hy => by
      have := h' y
      rw [hy, EReal.add_bot, ← EReal.coe_add, ← EReal.coe_add, le_bot_iff] at this
      exact EReal.coe_ne_bot _ this
    set Cf := dom univ f
    set Dg := dom univ g
    set fr : E → ℝ := fun y => (f y).toReal
    set gr : E → ℝ := fun y => (g y).toReal
    have hfr : ∀ y ∈ Cf, (fr y : EReal) = f y := fun y hy => EReal.coe_toReal hy.2.ne (hfb y)
    have hgr : ∀ y ∈ Dg, (gr y : EReal) = g y := fun y hy => EReal.coe_toReal hy.2.ne (hgb y)
    have hxC : x ∈ Cf := ⟨trivial, by rw [hu]; exact EReal.coe_lt_top u⟩
    have hxD : x ∈ Dg := ⟨trivial, by rw [hv]; exact EReal.coe_lt_top v⟩
    have hfrc : ConvexOn ℝ Cf fr := by
      rw [ProperFunctionConvexOn_iff_ConvexOn]
      exact hf.congr fun y hy => (hfr y hy).symm
    have hgrc : ConvexOn ℝ Dg gr := by
      rw [ProperFunctionConvexOn_iff_ConvexOn]
      exact hg.congr fun y hy => (hgr y hy).symm
    have hfrx : fr x = u := by simp [fr, hu]
    have hgrx : gr x = v := by simp [gr, hv]
    have hle : ∀ y ∈ Cf, y ∈ Dg → u + v + ⟪s, y - x⟫ ≤ fr y + gr y := fun y hyC hyD => by
      have := h' y
      rw [← hfr y hyC, ← hgr y hyD, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add,
        EReal.coe_le_coe_iff] at this
      exact this
    obtain ⟨t, ht₁, ht₂⟩ := hsw _ _ (hfrc.sub_affine u s x) (fun z hz => hz.sub_affine u s x)
      (hgrc.const_sub v) (fun y hyC hyD => by have := hle y hyC hyD; linarith) hxC hxD
      (by simp [hfrx, hgrx])
    refine ⟨s + t, -t, fun y => ?_, fun y => ?_, by abel⟩
    · by_cases hy : y ∈ Cf
      · have := ht₁ y hy
        rw [hu, ← hfr y hy, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_add_left]
        simp only [hfrx, sub_self, inner_zero_right, add_zero, zero_add] at this
        linarith
      · have : f y = ⊤ := by
          by_contra hne
          exact hy ⟨trivial, lt_top_iff_ne_top.2 hne⟩
        rw [this]
        exact le_top
    · by_cases hy : y ∈ Dg
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
    have e : (f x + g x : EReal) + ⟪s₁ + s₂, y - x⟫ =
        (f x + ⟪s₁, y - x⟫ : EReal) + (g x + ⟪s₂, y - x⟫) := by
      rw [hu, hv, inner_add_left]
      norm_cast
      ring
    show (f x + g x : EReal) + ⟪s₁ + s₂, y - x⟫ ≤ f y + g y
    rw [e]
    exact add_le_add (h₁ y) (h₂ y)

/-- **Sum rule** (Moreau–Rockafellar) for two extended-real functions. Let `f, g : E → EReal`
be convex on a Hilbert space, `f` never `⊥`, and let `f` be continuous at a point of
`int (dom f) ∩ dom g`. Then `∂(f + g)(x) = ∂f(x) + ∂g(x)` at every `x` where `f` and `g` are
finite. -/
theorem hasERealSubgradientAt_add_iff_of_continuousAt [CompleteSpace E] {f g : E → EReal}
    {x x₀ s : E} (hf : ConvexOn ℝ (dom univ f) f) (hg : ConvexOn ℝ (dom univ g) g)
    (hfb : ∀ y, f y ≠ ⊥) (hx₀f : x₀ ∈ interior (dom univ f)) (hx₀g : x₀ ∈ dom univ g)
    (hfc : ContinuousAt f x₀) (hfx : f x ≠ ⊤) (hbot : g x ≠ ⊥) (htop : g x ≠ ⊤) :
    HasERealSubgradientAt (fun y => f y + g y) s x ↔
      ∃ s₁ s₂, HasERealSubgradientAt f s₁ x ∧ HasERealSubgradientAt g s₂ x ∧ s = s₁ + s₂ :=
  hasERealSubgradientAt_add_iff_of_sandwich hf hg hfb hfx hbot htop
    fun _ _ hFc hcont hGc hle hxC hxD hFG =>
      exists_affine_sandwich_of_continuousAt hFc hGc hle hx₀f hx₀g
        (hcont x₀ ((EReal.tendsto_toReal (interior_subset hx₀f).2.ne (hfb x₀)).comp hfc))
        hxC hxD hFG

/-- **Sum rule** (Rockafellar, Thm 23.8) in finite dimension. Let `f, g : E → EReal` be
convex, `f` never `⊥`, and `ri (dom f) ∩ ri (dom g) ≠ ∅`. Then
`∂(f + g)(x) = ∂f(x) + ∂g(x)` at every `x` where `f` and `g` are finite. -/
theorem hasERealSubgradientAt_add_iff_of_mem_intrinsicInterior [FiniteDimensional ℝ E]
    {f g : E → EReal} {x x₀ s : E} (hf : ConvexOn ℝ (dom univ f) f)
    (hg : ConvexOn ℝ (dom univ g) g) (hfb : ∀ y, f y ≠ ⊥)
    (hx₀f : x₀ ∈ intrinsicInterior ℝ (dom univ f))
    (hx₀g : x₀ ∈ intrinsicInterior ℝ (dom univ g))
    (hfx : f x ≠ ⊤) (hbot : g x ≠ ⊥) (htop : g x ≠ ⊤) :
    HasERealSubgradientAt (fun y => f y + g y) s x ↔
      ∃ s₁ s₂, HasERealSubgradientAt f s₁ x ∧ HasERealSubgradientAt g s₂ x ∧ s = s₁ + s₂ :=
  hasERealSubgradientAt_add_iff_of_sandwich hf hg hfb hfx hbot htop
    fun _ _ hFc _ hGc hle hxC hxD hFG =>
      exists_affine_sandwich_of_mem_intrinsicInterior hFc hGc hle hx₀f hx₀g hxC hxD hFG

/-- **Sum rule** (Rockafellar, Thm 23.8, with an interior point) in finite dimension. Let
`f, g : E → EReal` be convex, `f` never `⊥`, and `int (dom f) ∩ dom g ≠ ∅`. Then
`∂(f + g)(x) = ∂f(x) + ∂g(x)` at every `x` where `f` and `g` are finite. -/
theorem hasERealSubgradientAt_add_iff_of_mem_interior [FiniteDimensional ℝ E] {f g : E → EReal}
    {x x₀ s : E} (hf : ConvexOn ℝ (dom univ f) f) (hg : ConvexOn ℝ (dom univ g) g)
    (hfb : ∀ y, f y ≠ ⊥) (hx₀f : x₀ ∈ interior (dom univ f)) (hx₀g : x₀ ∈ dom univ g)
    (hfx : f x ≠ ⊤) (hbot : g x ≠ ⊥) (htop : g x ≠ ⊤) :
    HasERealSubgradientAt (fun y => f y + g y) s x ↔
      ∃ s₁ s₂, HasERealSubgradientAt f s₁ x ∧ HasERealSubgradientAt g s₂ x ∧ s = s₁ + s₂ :=
  hasERealSubgradientAt_add_iff_of_continuousAt hf hg hfb hx₀f hx₀g
    (continuousAt_of_convexOn_of_mem_interior_dom hf hfb hx₀f) hfx hbot htop

end Sum

/-! ### Chain rule for linear maps -/

section Chain

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {h : F → ℝ} {x s : E}

omit [InnerProductSpace ℝ F] in
/-- If `s` vanishes on `ker A`, then `A y ↦ ⟪s, y - x⟫` is a well-defined concave (indeed
affine) function on `range A`. -/
lemma exists_concaveOn_range [NormedSpace ℝ F] (A : E →L[ℝ] F) (x : E) {s : E}
    (hker : ∀ k, A k = 0 → ⟪s, k⟫ = 0) :
    ∃ G : F → ℝ, ConcaveOn ℝ (Set.range A) G ∧ ∀ y, G (A y) = ⟪s, y - x⟫ := by
  let G : F → ℝ := fun z => ⟪s, Classical.epsilon (fun y => A y = z) - x⟫
  have hGA : ∀ y, G (A y) = ⟪s, y - x⟫ := by
    intro y
    have hA : A (Classical.epsilon (fun y' => A y' = A y)) = A y :=
      Classical.epsilon_spec (p := fun y' => A y' = A y) ⟨y, rfl⟩
    have := hker (Classical.epsilon (fun y' => A y' = A y) - y) (by rw [map_sub, hA, sub_self])
    simp only [G, inner_sub_right] at this ⊢
    linarith
  refine ⟨G, ⟨?_, ?_⟩, hGA⟩
  · have := (LinearMap.range (A : E →ₗ[ℝ] F)).convex
    rwa [LinearMap.coe_range] at this
  · rintro _ ⟨y₁, rfl⟩ _ ⟨y₂, rfl⟩ a b ha hb hab
    have e : a • A y₁ + b • A y₂ = A (a • y₁ + b • y₂) := by simp
    rw [hGA y₁, hGA y₂, e, hGA]
    simp only [smul_eq_mul, inner_sub_right, inner_add_right, real_inner_smul_right]
    have hx : ⟪s, x⟫ = a * ⟪s, x⟫ + b * ⟪s, x⟫ := by rw [← add_mul, hab, one_mul]
    nlinarith

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
    obtain ⟨G, hG, hGA⟩ := exists_concaveOn_range A x hker
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

/-- The chain rule for an extended-real convex `h`, given a sandwich theorem for the pair
`(dom h, range A)`; see `hasERealSubgradientAt_add_iff_of_sandwich`. -/
theorem hasERealSubgradientAt_comp_iff_of_sandwich [CompleteSpace E] [CompleteSpace F]
    {h : F → EReal} (hh : ConvexOn ℝ (dom univ h) h) (hhb : ∀ z, h z ≠ ⊥)
    (A : E →L[ℝ] F) (hx : h (A x) ≠ ⊤)
    (hsw : ∀ Φ G : F → ℝ, ConvexOn ℝ (dom univ h) Φ →
      (∀ z, ContinuousAt (fun y => (h y).toReal) z → ContinuousAt Φ z) →
      ConcaveOn ℝ (Set.range A) G → (∀ z ∈ dom univ h, z ∈ Set.range A → G z ≤ Φ z) →
      A x ∈ dom univ h → Φ (A x) = G (A x) →
      ∃ t : F, (∀ z ∈ dom univ h, Φ (A x) + ⟪t, z - A x⟫ ≤ Φ z) ∧
        ∀ z ∈ Set.range A, G z ≤ G (A x) + ⟪t, z - A x⟫) :
    HasERealSubgradientAt (fun y => h (A y)) s x ↔
      ∃ t, HasERealSubgradientAt h t (A x) ∧ s = ContinuousLinearMap.adjoint A t := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, h (A x) = u :=
    ⟨(h (A x)).toReal, (EReal.coe_toReal hx (hhb _)).symm⟩
  constructor
  · intro hs
    have hs' : ∀ y, (u : EReal) + ⟪s, y - x⟫ ≤ h (A y) := fun y => by
      simpa only [hu] using hs y
    -- `s` vanishes on `ker A`
    have hker : ∀ k, A k = 0 → ⟪s, k⟫ = 0 := by
      intro k hAk
      have h1 := hs' (x + k)
      have h2 := hs' (x - k)
      simp only [map_add, map_sub, hAk, add_zero, sub_zero, add_sub_cancel_left,
        sub_sub_cancel_left, inner_neg_right, hu] at h1 h2
      rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h1 h2
      linarith
    obtain ⟨G, hG, hGA⟩ := exists_concaveOn_range A x hker
    set Ch := dom univ h
    set hr : F → ℝ := fun z => (h z).toReal
    have hhr : ∀ z ∈ Ch, (hr z : EReal) = h z := fun z hz => EReal.coe_toReal hz.2.ne (hhb z)
    have hhrc : ConvexOn ℝ Ch hr := by
      rw [ProperFunctionConvexOn_iff_ConvexOn]
      exact hh.congr fun z hz => (hhr z hz).symm
    have hrx : hr (A x) = u := by simp [hr, hu]
    have hxC : A x ∈ Ch := ⟨trivial, by rw [hu]; exact EReal.coe_lt_top u⟩
    obtain ⟨t, ht₁, ht₂⟩ := hsw _ _
      (hhrc.sub_affine u 0 (A x)) (fun z hz => hz.sub_affine u 0 (A x)) hG
      (fun z hzC hz => by
        obtain ⟨y, rfl⟩ := hz
        have h1 := hs' y
        rw [← hhr _ hzC, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
        rw [hGA]
        simp only [inner_zero_left, add_zero]
        linarith)
      hxC (by simp [hGA, hrx])
    refine ⟨t, fun z => ?_, ?_⟩
    · by_cases hz : z ∈ Ch
      · have := ht₁ z hz
        rw [hu, ← hhr z hz, ← EReal.coe_add, EReal.coe_le_coe_iff]
        simp only [hrx, sub_self, inner_zero_left, inner_zero_right, add_zero, zero_add] at this
        linarith
      · have : h z = ⊤ := by
          by_contra hne
          exact hz ⟨trivial, lt_top_iff_ne_top.2 hne⟩
        rw [this]
        exact le_top
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
    show h (A x) + ⟪ContinuousLinearMap.adjoint A t, y - x⟫ ≤ h (A y)
    rw [ContinuousLinearMap.adjoint_inner_left, map_sub]
    exact this

/-- **Chain rule** for an extended-real function. Let `h : F → EReal` be convex and never `⊥`
on a Hilbert space, `A : E → F` continuous linear, and let `h` be continuous at a point
`A x₀ ∈ int (dom h)`. Then, where `h (A x)` is finite, `s ∈ ∂(h ∘ A)(x)` iff `s = A† t` for
some `t ∈ ∂h(A x)`. -/
theorem hasERealSubgradientAt_comp_iff_of_continuousAt [CompleteSpace E] [CompleteSpace F]
    {h : F → EReal} {x₀ : E} (hh : ConvexOn ℝ (dom univ h) h) (hhb : ∀ z, h z ≠ ⊥)
    (A : E →L[ℝ] F) (hx₀ : A x₀ ∈ interior (dom univ h)) (hhc : ContinuousAt h (A x₀))
    (hx : h (A x) ≠ ⊤) :
    HasERealSubgradientAt (fun y => h (A y)) s x ↔
      ∃ t, HasERealSubgradientAt h t (A x) ∧ s = ContinuousLinearMap.adjoint A t :=
  hasERealSubgradientAt_comp_iff_of_sandwich hh hhb A hx
    fun _ _ hΦc hcont hGc hle hxC hFG =>
      exists_affine_sandwich_of_continuousAt hΦc hGc hle hx₀ (Set.mem_range_self x₀)
        (hcont _ ((EReal.tendsto_toReal (interior_subset hx₀).2.ne (hhb _)).comp hhc))
        hxC (Set.mem_range_self x) hFG

/-- **Chain rule** (Rockafellar, Thm 23.9) in finite dimension. Let `h : F → EReal` be convex
and never `⊥`, `A : E → F` linear, and let the range of `A` meet `ri (dom h)`:
`A x₀ ∈ ri (dom h)`. Then, where `h (A x)` is finite, `s ∈ ∂(h ∘ A)(x)` iff `s = A† t` for
some `t ∈ ∂h(A x)`. -/
theorem hasERealSubgradientAt_comp_iff_of_mem_intrinsicInterior [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {h : F → EReal} {x₀ : E} (hh : ConvexOn ℝ (dom univ h) h)
    (hhb : ∀ z, h z ≠ ⊥) (A : E →L[ℝ] F)
    (hx₀ : A x₀ ∈ intrinsicInterior ℝ (dom univ h)) (hx : h (A x) ≠ ⊤) :
    HasERealSubgradientAt (fun y => h (A y)) s x ↔
      ∃ t, HasERealSubgradientAt h t (A x) ∧ s = ContinuousLinearMap.adjoint A t := by
  -- the range of `A` is a subspace, hence equal to its relative interior
  have hri : A x₀ ∈ intrinsicInterior ℝ (Set.range A) := by
    have e : Set.range A = ((LinearMap.range (A : E →ₗ[ℝ] F) : Submodule ℝ F) : Set F) :=
      (LinearMap.coe_range _).symm
    rw [e, intrinsicInterior_submodule_eq_self]
    exact LinearMap.mem_range_self _ x₀
  exact hasERealSubgradientAt_comp_iff_of_sandwich hh hhb A hx
    fun _ _ hΦc _ hGc hle hxC hFG =>
      exists_affine_sandwich_of_mem_intrinsicInterior hΦc hGc hle hx₀ hri hxC
        (Set.mem_range_self x) hFG

/-- **Chain rule** (Rockafellar, Thm 23.9, with an interior point) in finite dimension. Let
`h : F → EReal` be convex and never `⊥`, `A : E → F` linear, and `A x₀ ∈ int (dom h)`. Then,
where `h (A x)` is finite, `s ∈ ∂(h ∘ A)(x)` iff `s = A† t` for some `t ∈ ∂h(A x)`. -/
theorem hasERealSubgradientAt_comp_iff_of_mem_interior [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {h : F → EReal} {x₀ : E} (hh : ConvexOn ℝ (dom univ h) h)
    (hhb : ∀ z, h z ≠ ⊥) (A : E →L[ℝ] F) (hx₀ : A x₀ ∈ interior (dom univ h))
    (hx : h (A x) ≠ ⊤) :
    HasERealSubgradientAt (fun y => h (A y)) s x ↔
      ∃ t, HasERealSubgradientAt h t (A x) ∧ s = ContinuousLinearMap.adjoint A t :=
  hasERealSubgradientAt_comp_iff_of_continuousAt hh hhb A hx₀
    (continuousAt_of_convexOn_of_mem_interior_dom hh hhb hx₀) hx

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
