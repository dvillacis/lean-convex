/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.InnerProductSpace.Dual
import ConvexAnalysis.Extended.ProperFunction

/-!
# Existence of affine minorants of proper convex functions

We prove Rockafellar, *Convex Analysis*, Corollary 12.1.2: on a finite-dimensional real inner
product space `E`, every proper convex function `f : E → EReal` admits an affine minorant, i.e.
there are `a : E` and `b : ℝ` with `⟪x, a⟫ - b ≤ f x` for every `x : E`.

## Proof idea

* **Real-valued case with nonempty interior.** If `g : F → ℝ` is convex on a convex set `C` in a
  finite-dimensional normed space `F` and `v₁ ∈ interior C`, then `g` is continuous on
  `interior C`, so the strict epigraph `S = {(v, μ) | v ∈ interior C ∧ g v < μ}` is open and
  convex and does not contain `(v₁, g v₁)`. The Hahn–Banach separation theorem yields a
  continuous linear functional `φ (v, μ) = ℓ v + μ α` with `φ < φ (v₁, g v₁)` on `S`; necessarily
  `α < 0`, and `v ↦ g v₁ - α⁻¹ ℓ (v - v₁)` is an affine minorant of `g` on `interior C`
  (`ConvexOn.exists_affine_le_of_mem_interior`). Using the midpoints of `v₁` and `v ∈ C`, which
  lie in `interior C`, the minorant extends to all of `C` (`ConvexOn.exists_affine_le`).
* **Reduction.** Pick `x₀ ∈ dom univ f`, let `W = {y | x₀ + y ∈ dom univ f}` (a convex set
  containing `0`) and `V = span ℝ W`. The trace of `W` on `V` has nonempty interior in `V`
  (`interior_preimage_coe_span_nonempty`), and `v ↦ (f (x₀ + v)).toReal` is a real convex
  function on it. The affine minorant obtained on `V` is written through the Riesz representation
  on `V` as `v ↦ ⟪v, w⟫ + c` with `w ∈ V`, and this gives the minorant `x ↦ ⟪x - x₀, w⟫ + c` of
  `f` on `dom univ f`; outside the effective domain `f = ⊤`.

## Main statements

* `ConvexOn.exists_affine_le`: a real convex function on a convex set with nonempty interior in
  a finite-dimensional space has an affine minorant on that set.
* `exists_inner_minorant_of_proper_convex`: every proper convex `f : E → EReal` on a
  finite-dimensional inner product space has an affine minorant `x ↦ ⟪x, a⟫ - b`.
-/

open Set

section RealValued

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
/-- The strict epigraph of a function continuous on an open set `U`, restricted to `U`,
is open. -/
lemma isOpen_strictEpigraph_of_continuousOn {U : Set F} {g : F → ℝ} (hU : IsOpen U)
    (hg : ContinuousOn g U) : IsOpen {p : F × ℝ | p.1 ∈ U ∧ g p.1 < p.2} := by
  have h1 : ContinuousOn (fun p : F × ℝ => p.2 - g p.1) (U ×ˢ univ) :=
    continuousOn_snd.sub (hg.comp continuousOn_fst fun p hp => hp.1)
  have h2 := h1.isOpen_inter_preimage (hU.prod isOpen_univ) (isOpen_Ioi (a := (0 : ℝ)))
  convert h2 using 1
  ext p
  simp [sub_pos]

/-- A continuous linear functional on `F × ℝ` splits as `φ (v, μ) = φ (v, 0) + μ φ (0, 1)`. -/
lemma ContinuousLinearMap.apply_prod_real (φ : F × ℝ →L[ℝ] ℝ) (p : F × ℝ) :
    φ p = φ (p.1, 0) + p.2 * φ (0, 1) := by
  have hp : p = (p.1, 0) + p.2 • ((0 : F), (1 : ℝ)) := by ext <;> simp
  conv_lhs => rw [hp]
  rw [map_add, map_smul, smul_eq_mul]

/-- Supporting affine function at an interior point: if `g` is convex on `C` and
`v₁ ∈ interior C`, there is a continuous linear `ℓ` with `g v₁ + ℓ (v - v₁) ≤ g v`
for all `v ∈ interior C`. -/
lemma ConvexOn.exists_affine_le_of_mem_interior [FiniteDimensional ℝ F] {C : Set F}
    {g : F → ℝ} (hg : ConvexOn ℝ C g) {v₁ : F} (hv₁ : v₁ ∈ interior C) :
    ∃ ℓ : F →L[ℝ] ℝ, ∀ v ∈ interior C, g v₁ + ℓ (v - v₁) ≤ g v := by
  set S : Set (F × ℝ) := {p | p.1 ∈ interior C ∧ g p.1 < p.2}
  have hSc : Convex ℝ S := (hg.subset interior_subset hg.1.interior).convex_strict_epigraph
  have hSo : IsOpen S :=
    isOpen_strictEpigraph_of_continuousOn isOpen_interior hg.continuousOn_interior
  have hp₀ : (v₁, g v₁) ∉ S := fun h => lt_irrefl _ h.2
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hSc hSo hp₀
  have hsep : ∀ v ∈ interior C, ∀ μ, g v < μ →
      φ (v, 0) + μ * φ (0, 1) < φ (v₁, 0) + g v₁ * φ (0, 1) := by
    intro v hv μ hμ
    have h := hφ (v, μ) ⟨hv, hμ⟩
    rwa [φ.apply_prod_real, φ.apply_prod_real (v₁, g v₁)] at h
  have hα : φ (0, 1) < 0 := by
    have h := hsep v₁ hv₁ (g v₁ + 1) (by linarith)
    linarith
  refine ⟨-(φ (0, 1))⁻¹ • φ.comp (ContinuousLinearMap.inl ℝ F ℝ), fun v hv => ?_⟩
  have hℓ : ∀ u : F, φ.comp (ContinuousLinearMap.inl ℝ F ℝ) u = φ (u, 0) := fun _ => rfl
  simp only [smul_apply, hℓ, smul_eq_mul]
  have hsub : φ (v - v₁, 0) = φ (v, 0) - φ (v₁, 0) := by
    rw [← map_sub]; simp
  rw [hsub]
  by_contra hcon
  replace hcon := not_le.mp hcon
  set K := g v₁ + -(φ (0, 1))⁻¹ * (φ (v, 0) - φ (v₁, 0))
  have h := hsep v hv ((g v + K) / 2) (by linarith)
  -- multiply `K - (g v + K)/2 > 0` by `-α > 0`
  have hpos : 0 < (K - (g v + K) / 2) * -φ (0, 1) := mul_pos (by linarith) (by linarith)
  have hexp : (K - (g v + K) / 2) * -φ (0, 1) =
      -(g v₁ * φ (0, 1)) + (φ (v, 0) - φ (v₁, 0)) + (g v + K) / 2 * φ (0, 1) := by
    have hα0 : φ (0, 1) ≠ 0 := hα.ne
    simp only [K]
    field_simp
    ring
  linarith

/-- A real function convex on a convex set `C` with nonempty interior in a finite-dimensional
space has an affine minorant on `C`. -/
lemma ConvexOn.exists_affine_le [FiniteDimensional ℝ F] {C : Set F} {g : F → ℝ}
    (hg : ConvexOn ℝ C g) (hC : (interior C).Nonempty) :
    ∃ (ℓ : F →L[ℝ] ℝ) (c : ℝ), ∀ v ∈ C, ℓ v + c ≤ g v := by
  obtain ⟨v₁, hv₁⟩ := hC
  obtain ⟨ℓ, hℓ⟩ := hg.exists_affine_le_of_mem_interior hv₁
  refine ⟨ℓ, g v₁ - ℓ v₁, fun v hv => ?_⟩
  have hm : (1 / 2 : ℝ) • v₁ + (1 / 2 : ℝ) • v ∈ interior C :=
    hg.1.openSegment_interior_self_subset_interior hv₁ hv
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have h1 := hℓ _ hm
  have h2 := hg.2 (interior_subset hv₁) hv (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h2
  have hmid : (1 / 2 : ℝ) • v₁ + (1 / 2 : ℝ) • v - v₁ = (1 / 2 : ℝ) • (v - v₁) := by module
  rw [hmid, map_smul, map_sub, smul_eq_mul] at h1
  linarith

end RealValued

section Reduction

/-- A proper function is finite on its effective domain: there it equals the coercion of its
real part. -/
lemma coe_toReal_of_mem_dom {α : Type*} {f : α → EReal} (hfp : ProperFunction univ f) {x : α}
    (hx : x ∈ dom univ f) : ((f x).toReal : EReal) = f x :=
  EReal.coe_toReal hx.2.ne (hfp.1 x trivial).ne'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A convex set `W` containing `0` has nonempty interior relative to its linear span. -/
lemma interior_preimage_coe_span_nonempty [FiniteDimensional ℝ E] {W : Set E}
    (hW : Convex ℝ W) (h0 : (0 : E) ∈ W) :
    (interior (((↑) : Submodule.span ℝ W → E) ⁻¹' W)).Nonempty := by
  have hc : Convex ℝ (((↑) : Submodule.span ℝ W → E) ⁻¹' W) :=
    hW.linear_preimage (Submodule.span ℝ W).subtype
  have h0' : (0 : Submodule.span ℝ W) ∈ ((↑) : Submodule.span ℝ W → E) ⁻¹' W := by
    simpa using h0
  rw [hc.interior_nonempty_iff_affineSpan_eq_top,
    ← AffineSubspace.direction_eq_top_iff_of_nonempty ⟨0, subset_affineSpan ℝ _ h0'⟩,
    direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ h0']
  simp

/-- Rockafellar, Cor. 12.1.2: a proper convex function on a finite-dimensional inner product
space has an affine minorant `x ↦ ⟪x, a⟫ - b`. -/
theorem exists_inner_minorant_of_proper_convex [FiniteDimensional ℝ E] {f : E → EReal}
    (hfp : ProperFunction univ f) (hfc : ConvexOn ℝ (dom univ f) f) :
    ∃ (a : E) (b : ℝ), ∀ x : E, f x ≥ (inner ℝ x a : EReal) - b := by
  obtain ⟨x₀, -, hx₀⟩ : ∃ x ∈ univ, f x < ⊤ :=
    hfp.2.resolve_left univ_nonempty.ne_empty
  -- translate the effective domain so that it contains `0`
  set W : Set E := (fun y => x₀ + y) ⁻¹' dom univ f
  have hW : Convex ℝ W := hfc.1.translate_preimage_right x₀
  have h0 : (0 : E) ∈ W := by simp [W, hx₀]
  set V := Submodule.span ℝ W
  set C : Set V := ((↑) : V → E) ⁻¹' W
  -- the real-valued restriction of `f` to the translated domain inside `V`
  set g : V → ℝ := fun v => (f (x₀ + v)).toReal
  have hgc : ConvexOn ℝ C g := by
    have h1 : ConvexOn ℝ C (fun v : V => f (x₀ + v)) :=
      (hfc.translate_right x₀).comp_linearMap V.subtype
    rw [ProperFunctionConvexOn_iff_ConvexOn]
    exact h1.congr fun v hv => (coe_toReal_of_mem_dom hfp hv).symm
  obtain ⟨ℓ, c, hℓ⟩ := hgc.exists_affine_le (interior_preimage_coe_span_nonempty hW h0)
  -- Riesz representation of `ℓ` inside `V`
  set w : V := (InnerProductSpace.toDual ℝ V).symm ℓ
  refine ⟨(w : E), inner ℝ x₀ (w : E) - c, fun x => ?_⟩
  by_cases hx : f x < ⊤
  · have hxW : x - x₀ ∈ W := by simp [W, hx]
    have hxV : x - x₀ ∈ V := Submodule.subset_span hxW
    have hle := hℓ ⟨x - x₀, hxV⟩ hxW
    have hℓv : ℓ ⟨x - x₀, hxV⟩ = inner ℝ (x - x₀) (w : E) := by
      rw [← InnerProductSpace.toDual_symm_apply, real_inner_comm]
      rfl
    have hfx : f x = ((g ⟨x - x₀, hxV⟩ : ℝ) : EReal) := by
      simp only [g, add_sub_cancel]
      exact (coe_toReal_of_mem_dom hfp ⟨trivial, hx⟩).symm
    rw [hfx, ge_iff_le, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [hℓv, inner_sub_left] at hle
    linarith
  · rw [not_lt_top_iff.mp hx]
    exact le_top

end Reduction
