/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib

/-!
# Radial functions `x ↦ ψ ‖x‖`

Convexity and differentiability of functions of the norm, and of sums
`u ↦ β ∑ᵢ j ‖Kᵢ u‖` over a finite family of linear maps `Kᵢ` (e.g. the gradient blocks of a
discrete total variation).

## Convexity

* `radial_convexOn`: if `ψ` is convex and nondecreasing on `[0, ∞)`, then `x ↦ ψ ‖x‖` is convex.
* `radial_convex_iff`: on a nontrivial space the converse also holds.
* `sum_radial_convexOn`: `u ↦ β ∑ᵢ ψ ‖Kᵢ u‖` is convex for `β ≥ 0`.

## Differentiability

* `hasFDerivAt_norm_of_ne_zero`: the norm is differentiable away from the origin, with
  derivative `⟪x, ·⟫ / ‖x‖`.
* `radialGrad j' x = (j'(‖x‖)/‖x‖) x` (and `0` at the origin).
* `RadialC1 j j'`: `j` has right derivative `0` at the origin, derivative `j'` on `(0, ∞)`,
  `j' → 0` at `0⁺`, and `j'` is continuous on `(0, ∞)`. Under these hypotheses
  `RadialC1.hasFDerivAt` shows that `x ↦ j ‖x‖` is differentiable everywhere (including the
  origin) with gradient `radialGrad j' x`, and `RadialC1.continuous_radialGrad` that this
  gradient is continuous.
* `RadialC1.hasFDerivAt_H`, `RadialC1.hasGradientAt_H`, `RadialC1.contDiff_H`: the same for
  `H u = β ∑ᵢ j ‖Kᵢ u‖`, with `∇H(u) = ∑ᵢ Kᵢ† wᵢ(u)`, `wᵢ(u) = β radialGrad j' (Kᵢ u)`.
-/

open Set Filter Topology Asymptotics InnerProductSpace

/-! ### Convexity -/

section Convexity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `ψ` is convex and nondecreasing on `[0, ∞)`, then `x ↦ ψ ‖x‖` is convex. -/
theorem radial_convexOn {ψ : ℝ → ℝ} (hc : ConvexOn ℝ (Ici 0) ψ) (hm : MonotoneOn ψ (Ici 0)) :
    ConvexOn ℝ univ (fun x : E => ψ ‖x‖) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have htri : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  calc ψ ‖a • x + b • y‖ ≤ ψ (a * ‖x‖ + b * ‖y‖) :=
        hm (mem_Ici.2 (norm_nonneg _)) (mem_Ici.2 (by positivity)) htri
    _ ≤ a * ψ ‖x‖ + b * ψ ‖y‖ := by
        simpa [smul_eq_mul] using
          hc.2 (mem_Ici.2 (norm_nonneg x)) (mem_Ici.2 (norm_nonneg y)) ha hb hab

/-- On a nontrivial real normed space, `x ↦ ψ ‖x‖` is convex if and only if `ψ` is convex and
nondecreasing on `[0, ∞)`. -/
theorem radial_convex_iff [Nontrivial E] (ψ : ℝ → ℝ) :
    ConvexOn ℝ univ (fun x : E => ψ ‖x‖) ↔ ConvexOn ℝ (Ici 0) ψ ∧ MonotoneOn ψ (Ici 0) := by
  refine ⟨fun hN => ?_, fun h => radial_convexOn h.1 h.2⟩
  -- a unit vector `e`
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
  obtain ⟨e, he1⟩ : ∃ e : E, ‖e‖ = 1 := ⟨(‖x₀‖⁻¹ : ℝ) • x₀, norm_smul_inv_norm (𝕜 := ℝ) hx₀⟩
  have hψ : ∀ t, 0 ≤ t → ψ t = ψ ‖t • e‖ := fun t ht => by
    rw [norm_smul, he1, mul_one, Real.norm_of_nonneg ht]
  refine ⟨⟨convex_Ici 0, fun s hs t ht a b ha hb hab => ?_⟩, fun s hs t ht hst => ?_⟩
  · have hs' : (0 : ℝ) ≤ s := hs
    have ht' : (0 : ℝ) ≤ t := ht
    have := hN.2 (mem_univ (s • e)) (mem_univ (t • e)) ha hb hab
    simp only [smul_eq_mul] at this ⊢
    rw [hψ s hs', hψ t ht', hψ (a * s + b * t) (by positivity)]
    convert this using 3
    module
  · have hs' : (0 : ℝ) ≤ s := hs
    rcases eq_or_lt_of_le (hs'.trans hst) with h0 | htpos
    · have : s = t := le_antisymm hst (h0 ▸ hs')
      rw [this]
    -- `s • e` is a convex combination of `t • e` and `-(t • e)`
    set θ : ℝ := (t + s) / (2 * t)
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : 0 ≤ 1 - θ := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have hθs : θ * t - (1 - θ) * t = s := by
      simp only [θ]; field_simp; ring
    have hcomb : θ • (t • e) + (1 - θ) • (-(t • e)) = s • e := by
      calc θ • (t • e) + (1 - θ) • (-(t • e)) = (θ * t - (1 - θ) * t) • e := by module
        _ = s • e := by rw [hθs]
    have := hN.2 (mem_univ (t • e)) (mem_univ (-(t • e))) hθ0 hθ1 (by ring)
    simp only [smul_eq_mul, norm_neg, hcomb] at this
    rw [hψ s hs', hψ t htpos.le]
    linarith

variable {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite nonnegative combination of convex radial profiles composed with linear maps is
convex: `u ↦ β ∑ᵢ ψ ‖Kᵢ u‖` for `β ≥ 0` and `ψ` convex and nondecreasing on `[0, ∞)`. -/
theorem sum_radial_convexOn (s : Finset ι) (K : ι → E →ₗ[ℝ] F) {ψ : ℝ → ℝ}
    (hc : ConvexOn ℝ (Ici 0) ψ) (hm : MonotoneOn ψ (Ici 0)) {β : ℝ} (hβ : 0 ≤ β) :
    ConvexOn ℝ univ (fun u => β * ∑ i ∈ s, ψ ‖K i u‖) := by
  have hi : ∀ i, ConvexOn ℝ univ (fun u => ψ ‖K i u‖) := fun i => by
    simpa [Function.comp_def] using (radial_convexOn (E := F) hc hm).comp_linearMap (K i)
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have hsum : ∑ i ∈ s, ψ ‖K i (a • x + b • y)‖ ≤
      a * ∑ i ∈ s, ψ ‖K i x‖ + b * ∑ i ∈ s, ψ ‖K i y‖ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by
      simpa [smul_eq_mul] using (hi i).2 (mem_univ x) (mem_univ y) ha hb hab
  nlinarith [mul_le_mul_of_nonneg_left hsum hβ]

end Convexity

/-! ### Differentiability -/

section Differentiability

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The norm is differentiable away from the origin, with derivative `⟪x, ·⟫ / ‖x‖`. -/
lemma hasFDerivAt_norm_of_ne_zero {x : F} (hx : x ≠ 0) :
    HasFDerivAt (fun y : F => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  have hfun : (fun y : F => √(‖y‖ ^ 2)) = fun y => ‖y‖ :=
    funext fun y => Real.sqrt_sq (norm_nonneg y)
  rw [hfun] at this
  refine this.congr_fderiv ?_
  ext v
  simp [Real.sqrt_sq (norm_nonneg x), innerSL_apply_apply]
  field_simp

open Classical in
/-- The radial gradient `(j'(‖x‖)/‖x‖) x`, with value `0` at the origin. -/
noncomputable def radialGrad (j' : ℝ → ℝ) (x : F) : F :=
  if x = 0 then 0 else (j' ‖x‖ / ‖x‖) • x

lemma norm_radialGrad (j' : ℝ → ℝ) {x : F} (hx : x ≠ 0) : ‖radialGrad j' x‖ = |j' ‖x‖| := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [radialGrad, if_neg hx, norm_smul, Real.norm_eq_abs, abs_div, abs_norm,
    div_mul_cancel₀ _ hn.ne']

/-- Scalar hypotheses under which `x ↦ j ‖x‖` is `C¹`: right derivative `0` at the origin,
derivative `j'` on `(0, ∞)`, `j' → 0` at `0⁺`, and `j'` continuous on `(0, ∞)`. -/
structure RadialC1 (j j' : ℝ → ℝ) : Prop where
  deriv_zero : HasDerivWithinAt j 0 (Ici 0) 0
  deriv_pos : ∀ t > 0, HasDerivAt j (j' t) t
  tendsto_zero : Tendsto j' (𝓝[>] 0) (𝓝 0)
  cont : ContinuousOn j' (Ioi 0)

namespace RadialC1

variable {j j' : ℝ → ℝ} (h : RadialC1 j j')
include h

/-- `x ↦ j ‖x‖` is differentiable on `F`, with gradient `radialGrad j' x`; at the origin the
derivative is `0` because `j(s) - j(0) = o(s)`. -/
theorem hasFDerivAt (x : F) :
    HasFDerivAt (fun y : F => j ‖y‖) (innerSL ℝ (radialGrad j' x)) x := by
  by_cases hx : x = 0
  · subst hx
    rw [radialGrad, if_pos rfl, map_zero, hasFDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, norm_zero, zero_apply, sub_zero]
    have h0 := hasDerivWithinAt_iff_isLittleO.1 h.deriv_zero
    simp only [sub_zero, smul_zero] at h0
    have ht : Tendsto (fun y : F => ‖y‖) (𝓝 0) (𝓝[Ici 0] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨by simpa using (continuous_norm.tendsto (0 : F)),
        Eventually.of_forall fun y => norm_nonneg y⟩
    exact isLittleO_norm_right.1 (h0.comp_tendsto ht)
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    refine ((h.deriv_pos ‖x‖ hn).comp_hasFDerivAt x
      (hasFDerivAt_norm_of_ne_zero hx)).congr_fderiv ?_
    ext v
    simp [innerSL_apply_apply, radialGrad, hx]
    field_simp

/-- The radial gradient is continuous; at the origin this uses `j' → 0` at `0⁺`. -/
theorem continuous_radialGrad : Continuous (radialGrad (F := F) j') := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.tendsto_nhdsWithin_nhds.1 h.tendsto_zero ε hε
    refine ⟨δ, hδ, fun {y} hy => ?_⟩
    have h0 : radialGrad j' (0 : F) = 0 := by rw [radialGrad, if_pos rfl]
    rw [h0, dist_zero_right]
    by_cases hy0 : y = 0
    · rw [hy0, h0, norm_zero]; exact hε
    · have hn : 0 < ‖y‖ := norm_pos_iff.2 hy0
      have := hball (x := ‖y‖) hn (by rwa [dist_zero_right, norm_norm, ← dist_zero_right])
      rw [dist_zero_right, Real.norm_eq_abs] at this
      rwa [norm_radialGrad j' hy0]
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hc : ContinuousAt (fun y : F => (j' ‖y‖ / ‖y‖) • y) x :=
      (((h.cont.continuousAt (Ioi_mem_nhds hn)).comp continuous_norm.continuousAt).div
        continuous_norm.continuousAt hn.ne').smul continuousAt_id
    refine hc.congr ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y (hy : y ≠ 0)
    rw [radialGrad, if_neg hy]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι]

omit h in
/-- The vector field `wᵢ(u) = β j'(‖Kᵢ u‖) Kᵢ u / ‖Kᵢ u‖`. -/
noncomputable def wField (j' : ℝ → ℝ) (β : ℝ) (K : ι → E →L[ℝ] F) (u : E) (i : ι) : F :=
  β • radialGrad j' (K i u)

/-- `H u = β ∑ᵢ j(‖Kᵢ u‖)` is differentiable, with `H'(u) v = ∑ᵢ ⟪wᵢ(u), Kᵢ v⟫`. -/
theorem hasFDerivAt_H (K : ι → E →L[ℝ] F) (β : ℝ) (u : E) :
    HasFDerivAt (fun u => β * ∑ i, j ‖K i u‖)
      (∑ i, (innerSL ℝ (wField j' β K u i)).comp (K i)) u := by
  have hs : HasFDerivAt (fun u => ∑ i, j ‖K i u‖)
      (∑ i, (innerSL ℝ (radialGrad j' (K i u))).comp (K i)) u :=
    HasFDerivAt.fun_sum fun i _ => (h.hasFDerivAt (K i u)).comp u (K i).hasFDerivAt
  refine (hs.const_mul β).congr_fderiv ?_
  ext v
  simp [wField, Finset.mul_sum]

/-- Gradient form: `∇H(u) = ∑ᵢ Kᵢ† wᵢ(u)`. -/
theorem hasGradientAt_H [CompleteSpace E] [CompleteSpace F] (K : ι → E →L[ℝ] F) (β : ℝ)
    (u : E) :
    HasGradientAt (fun u => β * ∑ i, j ‖K i u‖)
      (∑ i, ContinuousLinearMap.adjoint (K i) (wField j' β K u i)) u := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (h.hasFDerivAt_H K β u).congr_fderiv ?_
  ext v
  simp [toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]

/-- `H u = β ∑ᵢ j(‖Kᵢ u‖)` is continuously differentiable. -/
theorem contDiff_H (K : ι → E →L[ℝ] F) (β : ℝ) :
    ContDiff ℝ 1 (fun u => β * ∑ i, j ‖K i u‖) := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨fun u => ∑ i, (innerSL ℝ (wField j' β K u i)).comp (K i), ?_, h.hasFDerivAt_H K β⟩
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((innerSL ℝ (E := F)).continuous.comp
    ((h.continuous_radialGrad.comp (K i).continuous).const_smul β)).clm_comp continuous_const

end RadialC1

end Differentiability
