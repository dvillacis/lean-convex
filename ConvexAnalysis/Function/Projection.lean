/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Villacís
-/
import Mathlib

/-!
# Explicit projections onto balls and boxes

Closed-form projections, each characterized by its variational inequality
`⟪x - P x, b - P x⟫ ≤ 0` for all `b` in the set.

* `projBall λ z = (λ / max(λ, ‖z‖)) z`, the projection onto `{‖s‖ ≤ λ}`:
  `norm_projBall_le`, `projBall_vi`.
* The unit box `UnitBox.boxSet n = [0, 1]ⁿ ⊆ EuclideanSpace ℝ (Fin n)` with componentwise
  clipping `UnitBox.clip`: `clip_mem`, `clip_vi`, `isCompact_box`, `convex_box`, and its
  support function `σ(ξ) = ∑ⱼ max(ξⱼ, 0)` (`box_support`, attained; `continuous_boxSupport`).
-/

open Set WithLp
open scoped RealInnerProductSpace

/-! ### The closed ball `{‖s‖ ≤ λ}` -/

section Ball

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The projection `λ z / max(λ, ‖z‖)` onto the closed ball `{‖s‖ ≤ λ}`. -/
noncomputable def projBall (lam : ℝ) (z : F) : F := (lam / max lam ‖z‖) • z

/-- `projBall λ z` lies in `{‖s‖ ≤ λ}`. -/
theorem norm_projBall_le {lam : ℝ} (hlam : 0 ≤ lam) (z : F) : ‖projBall lam z‖ ≤ lam := by
  rw [projBall, norm_smul, Real.norm_of_nonneg (div_nonneg hlam (le_max_of_le_left hlam))]
  rcases eq_or_lt_of_le (le_max_of_le_left hlam : (0 : ℝ) ≤ max lam ‖z‖) with h0 | hpos
  · rw [← h0, div_zero, zero_mul]; exact hlam
  · rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hlam

/-- Variational inequality of the ball projection: `⟪z - P z, t - P z⟫ ≤ 0` for `‖t‖ ≤ λ`. -/
lemma projBall_vi {lam : ℝ} (hlam : 0 ≤ lam) (z : F) {t : F} (ht : ‖t‖ ≤ lam) :
    ⟪z - projBall lam z, t - projBall lam z⟫ ≤ 0 := by
  unfold projBall
  rcases le_or_gt ‖z‖ lam with hz | hz
  · rw [max_eq_left hz]
    rcases eq_or_lt_of_le hlam with h0 | hpos
    · have : z = 0 := norm_le_zero_iff.1 (h0 ▸ hz)
      simp [this]
    · rw [div_self hpos.ne', one_smul, sub_self, inner_zero_left]
  · have hzpos : 0 < ‖z‖ := hlam.trans_lt hz
    rw [max_eq_right hz.le]
    set c := lam / ‖z‖
    have hc1 : c ≤ 1 := (div_le_one hzpos).2 hz.le
    have e : z - c • z = (1 - c) • z := by rw [sub_smul, one_smul]
    rw [e, inner_smul_left, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    simp only [conj_trivial]
    have hcz : c * ‖z‖ ^ 2 = lam * ‖z‖ := by
      simp only [c]; field_simp
    have hzt : ⟪z, t⟫ ≤ ‖z‖ * lam :=
      (real_inner_le_norm z t).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg z))
    nlinarith

end Ball

/-! ### The unit box `[0, 1]ⁿ` -/

namespace UnitBox

variable {n : ℕ}

/-- The box `[0,1]ⁿ`. -/
def boxSet (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := {u | ∀ j, 0 ≤ u j ∧ u j ≤ 1}

/-- The projection onto the box: componentwise clipping to `[0, 1]`. -/
noncomputable def clip (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  toLp 2 (fun j => max 0 (min 1 (x j)))

lemma clip_mem (x : EuclideanSpace ℝ (Fin n)) : clip x ∈ boxSet n := fun _ =>
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- Variational inequality of clipping: `⟪x - clip x, b - clip x⟫ ≤ 0` for `b ∈ [0,1]ⁿ`. -/
lemma clip_vi (x : EuclideanSpace ℝ (Fin n)) (b : EuclideanSpace ℝ (Fin n)) (hb : b ∈ boxSet n) :
    ⟪x - clip x, b - clip x⟫ ≤ 0 := by
  simp only [PiLp.inner_apply, PiLp.sub_apply, RCLike.inner_apply, conj_trivial, clip]
  refine Finset.sum_nonpos fun j _ => ?_
  obtain ⟨h0, h1⟩ := hb j
  rcases le_total (x j) 0 with hx | hx
  · rw [min_eq_right (hx.trans zero_le_one), max_eq_left hx]; nlinarith
  rcases le_total (x j) 1 with hx' | hx'
  · rw [min_eq_right hx', max_eq_right hx, sub_self, mul_zero]
  · rw [min_eq_left hx', max_eq_right zero_le_one]; nlinarith

lemma box_eq : boxSet n = toLp 2 '' Set.pi univ (fun _ => Set.Icc (0 : ℝ) 1) := by
  ext u
  refine ⟨fun hu => ⟨ofLp u, fun j _ => hu j, rfl⟩, ?_⟩
  rintro ⟨w, hw, rfl⟩ j
  exact hw j (mem_univ j)

lemma isCompact_box : IsCompact (boxSet n) := by
  rw [box_eq]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

lemma convex_box : Convex ℝ (boxSet n) := by
  intro a ha b hb θ η hθ hη hθη j
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain ⟨ha0, ha1⟩ := ha j
  obtain ⟨hb0, hb1⟩ := hb j
  constructor <;> nlinarith

/-- **Support function of the box** `[0,1]ⁿ`: `σ(ξ) = ∑ⱼ max(ξⱼ, 0)`, and it is attained. -/
theorem box_support (ξ : EuclideanSpace ℝ (Fin n)) :
    IsGreatest ((fun u => ⟪ξ, u⟫) '' boxSet n) (∑ j, max (ξ j) 0) := by
  refine ⟨⟨toLp 2 (fun j => if 0 < ξ j then (1 : ℝ) else 0), fun j => ?_, ?_⟩, ?_⟩
  · dsimp only
    split_ifs <;> norm_num
  · simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [one_mul, max_eq_left h.le]
    · rw [zero_mul, max_eq_right (not_lt.1 h)]
  · rintro _ ⟨u, hu, rfl⟩
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    refine Finset.sum_le_sum fun j _ => ?_
    obtain ⟨h0, h1⟩ := hu j
    rcases le_total 0 (ξ j) with hξ | hξ
    · rw [max_eq_left hξ]; nlinarith
    · rw [max_eq_right hξ]; nlinarith

lemma continuous_boxSupport :
    Continuous fun ξ : EuclideanSpace ℝ (Fin n) => ∑ j, max (ξ j) 0 := by
  fun_prop

end UnitBox
