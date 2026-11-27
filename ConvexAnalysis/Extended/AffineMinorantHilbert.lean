/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import ConvexAnalysis.Extended.AffineMinorant
import ConvexAnalysis.Extended.AffineMinorantExistence

/-!
# Continuous affine minorants in Hilbert spaces

`Extended/AffineMinorant` proves Rockafellar's Theorem 12.1 with affine minorants that are
algebraic affine maps, and passes to the form `⟪l, x⟫ + w` only in finite dimension. Here the
theorem is proved directly with continuous affine minorants, without any assumption on the
dimension.

* `exists_affine_lt_of_notMem_epi`: in a normed space, a point outside a closed convex
  epigraph-like set `S ⊆ E × ℝ` lies strictly below a continuous affine function that
  minorizes `S`.
* `exists_inner_minorant_gt`: for a proper lower semicontinuous convex `f` on a Hilbert space
  and `r < f x`, there is a minorant `y ↦ ⟪l, y⟫ + w` of `f` with `r < ⟪l, x⟫ + w`.
* `lsc_convex_eq_iSup_inner_minorant` (Theorem 12.1; Bauschke–Combettes, Thm 9.20): a lower
  semicontinuous convex `f : E → EReal` on a Hilbert space is the supremum of its minorants
  `y ↦ ⟪l, y⟫ + w`.
-/

open Set

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Let `S ⊆ E × ℝ` be closed, convex and closed upwards in the second coordinate, and let
`y₀` be a point over which `S` is neither empty nor the whole line. Then every point
`(x, r) ∉ S` lies strictly below a continuous affine function `y ↦ g y + w` that minorizes
`S`. If the separating hyperplane is vertical, it is tilted with the minorant obtained at
`y₀`. -/
theorem exists_affine_lt_of_notMem_epi {S : Set (E × ℝ)} (hSc : Convex ℝ S) (hScl : IsClosed S)
    (hup : ∀ y μ μ', (y, μ) ∈ S → μ ≤ μ' → (y, μ') ∈ S) {y₀ : E} {μ₀ ρ₀ : ℝ}
    (h₀ : (y₀, μ₀) ∈ S) (h₀' : (y₀, ρ₀) ∉ S) {x : E} {r : ℝ} (hx : (x, r) ∉ S) :
    ∃ (g : E →L[ℝ] ℝ) (w : ℝ), (∀ p ∈ S, g p.1 + w ≤ p.2) ∧ r < g x + w := by
  -- strict separation of a point from `S`, with a nonnegative coefficient on the last variable
  have sep : ∀ a ρ, (a, ρ) ∉ S → ∃ (ℓ : E →L[ℝ] ℝ) (α c : ℝ), 0 ≤ α ∧ ℓ a + ρ * α < c ∧
      ∀ y μ, (y, μ) ∈ S → c < ℓ y + μ * α := by
    intro a ρ ha
    obtain ⟨φ, c, h1, h2⟩ := geometric_hahn_banach_point_closed hSc hScl ha
    refine ⟨φ.comp (ContinuousLinearMap.inl ℝ E ℝ), φ (0, 1), c, ?_, ?_, ?_⟩
    · by_contra hneg
      push Not at hneg
      have hb := h2 (y₀, μ₀) h₀
      rw [φ.apply_prod_real] at hb
      dsimp only at hb
      set n := (φ (y₀, 0) + μ₀ * φ (0, 1) - c) / (-φ (0, 1)) with hn
      have hn0 : 0 ≤ n := div_nonneg (by linarith) (by linarith)
      have h := h2 (y₀, μ₀ + n) (hup y₀ μ₀ _ h₀ (by linarith))
      rw [φ.apply_prod_real] at h
      dsimp only at h
      have e : n * (-φ (0, 1)) = φ (y₀, 0) + μ₀ * φ (0, 1) - c :=
        div_mul_cancel₀ _ (by linarith : -φ (0, 1) ≠ 0)
      nlinarith
    · have h := h1
      rw [φ.apply_prod_real] at h
      exact h
    · intro y μ hy
      have h := h2 (y, μ) hy
      rw [φ.apply_prod_real] at h
      exact h
  have hρμ : ρ₀ < μ₀ := by
    by_contra h
    exact h₀' (hup y₀ μ₀ ρ₀ h₀ (not_lt.1 h))
  -- a first minorant, from the separation at `(y₀, ρ₀)`: it is not vertical
  obtain ⟨ℓ₀, α₀, c₀, hα₀, hs₀, hS₀⟩ := sep y₀ ρ₀ h₀'
  have hα₀' : 0 < α₀ := by
    have h := hS₀ y₀ μ₀ h₀
    by_contra hcon
    have h0 : α₀ = 0 := le_antisymm (not_lt.1 hcon) hα₀
    rw [h0] at h hs₀
    linarith
  obtain ⟨ℓ, α, c, hα, hs, hS⟩ := sep x r hx
  rcases hα.lt_or_eq with hpos | hzero
  · -- nonvertical hyperplane
    refine ⟨-(α⁻¹) • ℓ, c / α, fun p hp => ?_, ?_⟩
    · have h := hS p.1 p.2 hp
      simp only [smul_apply, smul_eq_mul]
      rw [show -α⁻¹ * ℓ p.1 + c / α = (c - ℓ p.1) / α by ring, div_le_iff₀ hpos]
      linarith
    · simp only [smul_apply, smul_eq_mul]
      rw [show -α⁻¹ * ℓ x + c / α = (c - ℓ x) / α by ring, lt_div_iff₀ hpos]
      linarith
  · -- vertical hyperplane `ℓ x < c < ℓ y`: add a large multiple of `c - ℓ` to the first minorant
    subst hzero
    simp only [mul_zero, add_zero] at hs hS
    have hcx : 0 < c - ℓ x := by linarith
    set lam := |r - (c₀ - ℓ₀ x) / α₀| / (c - ℓ x) + 1 with hlam
    have hlam0 : 0 ≤ lam := add_nonneg (div_nonneg (abs_nonneg _) hcx.le) zero_le_one
    have hlamx : r - (c₀ - ℓ₀ x) / α₀ < lam * (c - ℓ x) := by
      have e : lam * (c - ℓ x) = |r - (c₀ - ℓ₀ x) / α₀| + (c - ℓ x) := by
        rw [hlam, add_mul, div_mul_cancel₀ _ hcx.ne', one_mul]
      rw [e]
      linarith [le_abs_self (r - (c₀ - ℓ₀ x) / α₀)]
    refine ⟨-(α₀⁻¹) • ℓ₀ - lam • ℓ, c₀ / α₀ + lam * c, fun p hp => ?_, ?_⟩
    · have h1 := hS₀ p.1 p.2 hp
      have h2 := hS p.1 p.2 hp
      simp only [sub_apply, smul_apply, smul_eq_mul]
      have h3 : (c₀ - ℓ₀ p.1) / α₀ ≤ p.2 := by
        rw [div_le_iff₀ hα₀']
        linarith
      have h4 : lam * (c - ℓ p.1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam0 (by linarith)
      have e : -α₀⁻¹ * ℓ₀ p.1 - lam * ℓ p.1 + (c₀ / α₀ + lam * c) =
          (c₀ - ℓ₀ p.1) / α₀ + lam * (c - ℓ p.1) := by ring
      rw [e]
      linarith
    · simp only [sub_apply, smul_apply, smul_eq_mul]
      have e : -α₀⁻¹ * ℓ₀ x - lam * ℓ x + (c₀ / α₀ + lam * c) =
          (c₀ - ℓ₀ x) / α₀ + lam * (c - ℓ x) := by ring
      rw [e]
      linarith

end Normed

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → EReal}

local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

/-- For a proper lower semicontinuous convex `f` on a Hilbert space and a real `r < f x`,
there is a minorant `y ↦ ⟪l, y⟫ + w` of `f` whose value at `x` exceeds `r`. -/
theorem exists_inner_minorant_gt (hf : ConvexOn ℝ univ f) (hl : LowerSemicontinuous f)
    [hp : ProperFunction univ f] {x : E} {r : ℝ} (hr : (r : EReal) < f x) :
    ∃ (l : E) (w : ℝ), (∀ y, ((⟪l, y⟫ + w : ℝ) : EReal) ≤ f y) ∧ r < ⟪l, x⟫ + w := by
  set S := f.Epi univ
  have hSc : Convex ℝ S := EReal.convex_epigraph hf
  have hScl : IsClosed S :=
    epi_is_closed_of_lowersemicontinuous isClosed_univ (lowerSemicontinuousOn_univ_iff.mpr hl)
  have hmem : ∀ y (μ : ℝ), (y, μ) ∈ S ↔ f y ≤ (μ : EReal) := fun y μ => by
    simp [S, Function.Epi]
  obtain ⟨y₀, -, hy₀⟩ := exist_xs_lt_top (f := f) (s := univ) univ_nonempty.ne_empty
  obtain ⟨μ₀, hμ₀⟩ : ∃ μ₀ : ℝ, f y₀ = μ₀ :=
    ⟨_, (EReal.coe_toReal hy₀.ne (hp.uninfinity y₀ trivial).ne').symm⟩
  obtain ⟨g, w, hg, hgx⟩ := exists_affine_lt_of_notMem_epi hSc hScl
    (fun y μ μ' h hle => (hmem y μ').2 (((hmem y μ).1 h).trans (EReal.coe_le_coe_iff.2 hle)))
    (y₀ := y₀) (μ₀ := μ₀) (ρ₀ := μ₀ - 1) ((hmem _ _).2 hμ₀.le)
    (fun h => by
      have := (hmem _ _).1 h
      rw [hμ₀, EReal.coe_le_coe_iff] at this
      linarith)
    (x := x) (r := r) (fun h => not_le.2 hr ((hmem _ _).1 h))
  refine ⟨(InnerProductSpace.toDual ℝ E).symm g, w, fun y => ?_, ?_⟩
  · rw [InnerProductSpace.toDual_symm_apply]
    by_cases hy : f y = ⊤
    · rw [hy]
      exact le_top
    · obtain ⟨ν, hν⟩ : ∃ ν : ℝ, f y = ν :=
        ⟨_, (EReal.coe_toReal hy (hp.uninfinity y trivial).ne').symm⟩
      have := hg (y, ν) ((hmem _ _).2 hν.le)
      rw [hν, EReal.coe_le_coe_iff]
      exact this
  · rw [InnerProductSpace.toDual_symm_apply]
    exact hgx

/-- **Theorem 12.1 in Hilbert spaces.** A lower semicontinuous convex `f : E → EReal` is the
supremum of its continuous affine minorants `y ↦ ⟪l, y⟫ + w`. -/
theorem lsc_convex_eq_iSup_inner_minorant (hf : ConvexOn ℝ univ f) (hl : LowerSemicontinuous f)
    (x : E) :
    f x = ⨆ (l : E) (w : ℝ) (_ : ∀ x, ⟪l, x⟫ + w ≤ f x), (⟪l, x⟫ + w).toEReal := by
  apply le_antisymm
  · by_cases hp : ProperFunction univ f
    · refine le_of_forall_lt fun b hb => ?_
      obtain ⟨r, hbr, hrf⟩ := EReal.lt_iff_exists_real_btwn.1 hb
      obtain ⟨l, w, hlw, hx⟩ := exists_inner_minorant_gt hf hl hrf
      refine hbr.trans (lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 hx) ?_)
      exact le_iSup₂_of_le l w (le_iSup_of_le
        (fun y => by rw [← EReal.coe_add]; exact hlw y) le_rfl)
    · have himp := ProperFuntion.conveximproper_nonfinte (convexOn_dom_s_f_of_convexOn_s hf)
        (lowerSemicontinuousOn_univ_iff.mpr hl) hp
      by_cases hfex : ∃ y, f y = ⊥
      · rw [bot_of_exist_bot_of_convex_of_univ hf hfex x]
        exact bot_le
      · push Not at hfex
        have htop : ∀ y, f y = ⊤ := fun y => (himp y trivial).resolve_right (hfex y)
        have hle : ∀ c : ℝ, (c : EReal) ≤ ⨆ (l : E) (w : ℝ) (_ : ∀ y, ⟪l, y⟫ + w ≤ f y),
            ((⟪l, x⟫ + w : ℝ) : EReal) := fun c =>
          le_iSup₂_of_le (0 : E) c (le_iSup_of_le (fun y => by simp [htop y]) (by simp))
        refine le_of_forall_lt fun b hb => ?_
        rw [htop x] at hb
        induction b with
        | bot => exact lt_of_lt_of_le (EReal.bot_lt_coe 0) (hle 0)
        | top => exact absurd hb (lt_irrefl _)
        | coe c => exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (lt_add_one c)) (hle (c + 1))
  · refine iSup₂_le fun l w => iSup_le fun h => ?_
    rw [EReal.coe_add]
    exact h x

end Hilbert
