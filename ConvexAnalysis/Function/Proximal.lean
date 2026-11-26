/-
Copyright (c) 2024 Shengyang Xu, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengyang Xu, Chenyi Li
-/
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Convex.Basic
import ConvexAnalysis.Convex.Subgradient
import ConvexAnalysis.Function.Lsmooth
import ConvexAnalysis.Convex.StronglyConvex
import ConvexAnalysis.Function.MinimaClosedFunction

/-!
# Proximal operator

This file defines the proximal property `prox_prop`, the proximal set `prox_set` and the proximal
points `prox_point`, `prox_point_c` and `prox_point_c'` of a function `f : E → ℝ`.

The main results are the existence of proximal points (`prox_set_compact_of_lowersemi`,
`prox_set_compact_of_convex`, `prox_well_define`, `prox_well_define_convex`), uniqueness for convex
functions (`prox_unique_of_convex`), the calculus rules `proximal_shift`, `proximal_scale`,
`proximal_add_linear` and `proximal_add_sq`, and the characterizations `prox_iff_subderiv` and
`prox_iff_grad`.
-/

set_option linter.unusedVariables false

noncomputable section

open Set InnerProductSpace Topology Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {x y y₁ y₂ : E} {s : Set E} {f : E → ℝ}

/-- The proximal property: `xm` satisfies it for `f` at `x` if `xm` is a minimizer of
`u ↦ f u + ‖u - x‖² / 2` over the whole space. -/
def prox_prop (f : E → ℝ) (x : E) (xm : E) : Prop :=
  IsMinOn (fun u ↦ f u + ‖u - x‖ ^ 2 / 2) univ xm

/-- The proximal set of `f` at `x`: the set of minimizers of `u ↦ f u + ‖u - x‖² / 2`, i.e. of
all points that satisfy the proximal property `prox_prop f x`. -/
def prox_set (f : E → ℝ) (x : E) : Set E := {u | prox_prop f x u}

/-- A proximal point of `f` at `x`: a point of `prox_set f x` chosen by `Classical.choose` from
the hypothesis `h` that the proximal set is nonempty. -/
def prox_point (f : E → ℝ) (x : E) (h : ∃ y, prox_set f x y) : E :=
  Classical.choose h

variable [ProperSpace E]
/-
  The existence of the proximal for proper lower-semi-continuous function
-/
omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem prox_set_compact_of_lowersemi (f : E → ℝ) (hc : LowerSemicontinuous f)
    (lbdf : BddBelow (f '' univ)) :
    ∀ x, Nonempty (prox_set f x) ∧ IsCompact (prox_set f x) := by
  intro x
  let g := fun u ↦ f u + ‖u - x‖ ^ 2 / 2
  let epi := {p : (E × ℝ) | g p.1 ≤ p.2}
  let S := {y : E | g y ≤ g x}
  have eq : S = (g ⁻¹' Set.Iic (g x)) := by constructor
  let ImS := {g y | y ∈ S}
  have neImS : Set.Nonempty ImS := by
    use g x; simp [ImS]; use x; simp [S]
  rcases lbdf with ⟨L, Lbound⟩
  rw [mem_lowerBounds] at Lbound
  have boundg : ∀ (x : E), L ≤ g x := by
    intro z
    calc
      L ≤ f z := by
        specialize Lbound (f z); simp at Lbound; exact Lbound
      _ ≤ f z + ‖z - x‖ ^ 2 / 2 := by
        simp; linarith [sq_nonneg ‖z - x‖]
  have hg : LowerSemicontinuous g := by
    apply LowerSemicontinuous.add hc
    apply Continuous.lowerSemicontinuous
    fun_prop
  have S_bddbelow : BddBelow ImS := by
    use L; rw [mem_lowerBounds]
    rintro gy ⟨y0, _, gyeq⟩; rw [← gyeq]; exact boundg y0
  have epi_closed : IsClosed epi := by
    apply bounded_lowersemicontinuous_to_epi_closed
    · exact lowerSemicontinuousOn_univ_iff.2 hg
    use L
  have closeds : IsClosed S := by
    rw [eq]
    rw [lowerSemicontinuous_iff_isClosed_preimage] at hg
    exact hg (g x)
  have compacts : IsCompact S := by
    let B := Metric.closedBall x (f x - L + 1)
    have sinb : S ⊆ B := by
      intro u uin; simp [S] at uin
      apply mem_closedBall_iff_norm.2
      have norm_bound: ‖u - x‖ ≤ f x - L + 1 := by
        have ieq : L + ‖u - x‖ ^ 2 / 2 ≤ f x:= by
          calc
          L + ‖u - x‖ ^ 2 / 2 ≤ g u := by
            simp [g]; specialize Lbound (f u); simp at Lbound; exact Lbound
          _ ≤ f x := by simp [g] at uin; exact uin
        rw [← le_sub_iff_add_le'] at ieq
        have aux {a b : ℝ} (h1 : a ^ 2 / 2 ≤ b) (h2 : 0 ≤ a) : a ≤ b + 1 := by
          rw [div_le_iff₀] at h1; rw [← abs_eq_self] at h2; rw [← h2]
          apply abs_le_of_sq_le_sq; rw [add_sq]; simp
          calc
            a ^ 2 ≤ b * 2 := h1
            _ ≤ b ^ 2 + 2 * b + 1 := by
              rw [add_right_comm, mul_comm]; simp; linarith [sq_nonneg b]
          calc
            0 ≤ a ^ 2 / 2 := by linarith [sq_nonneg a]
            _ ≤ b * 2 / 2 := by linarith
            _ ≤ b + 1 := by simp
          linarith
        apply aux ieq
        apply norm_nonneg
      exact norm_bound
    have compactb : IsCompact B := isCompact_closedBall x (f x - L + 1)
    rw [← closure_eq_iff_isClosed] at closeds; rw [← closeds]
    apply IsCompact.closure_of_subset compactb sinb
  rcases exists_seq_tendsto_sInf neImS S_bddbelow with ⟨fx, _, cfx, fxs⟩
  choose xn xsub xeq using fxs
  rcases IsCompact.tendsto_subseq compacts xsub with ⟨x', _, k, mono, cxk⟩
  have cfxk : Filter.Tendsto (g ∘ xn ∘ k) Filter.atTop (𝓝 (sInf ImS)) := by
    have xkeq : ∀ (n : ℕ), (g ∘ xn ∘ k) n = (fx ∘ k) n := fun n => xeq <| k n
    rw [tendsto_congr xkeq]
    apply Tendsto.comp cfx (StrictMono.tendsto_atTop mono)
  have inepi : (x', sInf ImS) ∈ epi := by
    let p := fun c ↦ (((fun n ↦ xn n) ∘ k) c, (g ∘ xn ∘ k) c)
    have pnin :  ∀ c : ℕ, p c ∈ epi := by intro c; simp [epi, p]
    apply IsClosed.isSeqClosed epi_closed pnin
    change Tendsto (fun c ↦ (((fun n ↦ xn n) ∘ k) c, (g ∘ xn ∘ k) c)) atTop (𝓝 (x', sInf ImS))
    apply Tendsto.prodMk_nhds cxk cfxk
  have minima_ieq : g x' ≤ sInf ImS := inepi
  have minima : ∀ w : E, g x' ≤ g w := by
    intro w
    by_cases hw : w ∈ S
    · have gwin : g w ∈ ImS := by use w
      have legw : sInf ImS ≤ g w := by
        rw [Real.sInf_le_iff S_bddbelow neImS]
        intro _ epos; use g w; use gwin; linarith
      linarith
    · have gwnin : g x < g w := by
        simp [g, S] at hw; simp [g]; exact hw
      have gxin : g x ∈ ImS := by use x; simp [g, S]
      have legw : sInf ImS ≤ g w := by
        rw [Real.sInf_le_iff S_bddbelow neImS]
        intro _ epos; use g x; use gxin; linarith
      linarith
  constructor
  · use x'; simp [prox_set]; rw [prox_prop, isMinOn_iff]
    intro v _; exact minima v
  · have aux : prox_set f x = {x | IsMinOn g univ x} := by
      simp [prox_set]; ext y
      constructor
      · intro yin; simp [prox_prop] at yin; simp; exact yin
      · intro yin; simp; rw [prox_prop]
        simp at yin; exact yin
    have nes : Nonempty S := by use x; simp [S]
    rw [eq] at compacts; rw [eq] at nes
    rw [aux] -- apply IsCompact_isMinOn_of_isCompact_preimage hc nes compacts
    have seq : {x | IsMinOn g univ x} = (g ⁻¹' Set.Iic (g x')) := by
      ext y
      constructor
      · exact fun hxx => isMinOn_iff.mp hxx x' trivial
      · intro yin; simp at yin
        exact fun x xuniv => le_trans yin ((fun x _ => minima x) x xuniv)
    simp only [seq]
    apply IsCompact.of_isClosed_subset compacts (LowerSemicontinuous.isClosed_preimage hg (g x'))
    apply Set.preimage_mono
    simp only [Set.Iic_subset_Iic]
    exact minima x

theorem prox_set_compact_of_convex (f : E → ℝ) (hc : ContinuousOn f univ)
    (hconv : ConvexOn ℝ univ f) :
    ∀ x, Nonempty (prox_set f x) ∧ IsCompact (prox_set f x) := by
  intro x
  have subd: ∃ z : E, Nonempty (SubderivAt f z) := by
    use x; apply SubderivAt.nonempty hconv hc
  have hc : LowerSemicontinuous f :=
    Continuous.lowerSemicontinuous (continuousOn_univ.mp hc)
  rcases subd with ⟨z, a, ain⟩
  rw [← mem_SubderivAt, HasSubgradientAt] at ain
  let g := fun u ↦ f u + ‖u - x‖ ^ 2 / 2
  let epi := {p : (E × ℝ) | g p.1 ≤ p.2}
  have second_lower_bound (y : E) : g y ≥ f z + inner ℝ a (y - z) + ‖y - x‖ ^ 2 / 2 := by
    simp [g]
    specialize ain y; linarith
  have lower_bound (y : E) : f z + inner ℝ a (x - z) - ‖a‖ ^ 2 / 2 ≤ g y := by
    have : y - z = x - z + (y - x) := by simp
    specialize second_lower_bound y
    rw [this, inner_add_right, ← add_assoc, add_assoc] at second_lower_bound
    have : 0 ≤ ‖a‖ ^ 2 / 2 + inner ℝ a (y - x) + ‖y - x‖ ^ 2 / 2 := by
      linarith [norm_add_sq_real a (y - x), sq_nonneg ‖a + (y - x)‖]
    calc
      f z + inner ℝ a (x - z) - ‖a‖ ^ 2 / 2 ≤ f z + inner ℝ a (x - z) - ‖a‖ ^ 2 / 2 +
        (‖a‖ ^ 2 / 2 + inner ℝ a (y - x) + ‖y - x‖ ^ 2 / 2) := le_add_of_nonneg_right this
      _ = f z + inner ℝ a (x - z) + (inner ℝ a (y - x) + ‖y - x‖ ^ 2 / 2) := by ring
      _ ≤ g y := second_lower_bound
  have hg : LowerSemicontinuous g := by
    apply LowerSemicontinuous.add hc
    apply Continuous.lowerSemicontinuous
    fun_prop
  have epi_closed : IsClosed epi := by
    apply bounded_lowersemicontinuous_to_epi_closed
    · exact lowerSemicontinuousOn_univ_iff.2 hg
    use (f z + inner ℝ a (x - z) - ‖a‖ ^ 2 / 2)
  let S := {y : E| g y ≤ g z}
  have eq : S = (g ⁻¹' Set.Iic (g z)) := by constructor
  let ImS := {g y | y ∈ S}
  have neImS : Set.Nonempty ImS := by
    use g z; simp [ImS, S]; use z
  have S_bddbelow : BddBelow ImS := by
    use (f z + inner ℝ a (x - z) - ‖a‖ ^ 2 / 2)
    rw [mem_lowerBounds]
    rintro gy ⟨y0, _, gyeq⟩
    rw [← gyeq]; exact lower_bound y0
  have closeds : IsClosed S := by
    rw [eq]
    rw [lowerSemicontinuous_iff_isClosed_preimage] at hg
    exact hg (g z)
  have compacts : IsCompact S := by
    let B := Metric.closedBall (x - a) (‖z - (x - a)‖ + 2)
    have sinb : S ⊆ B := by
      intro u uin
      simp [S] at uin
      apply mem_closedBall_iff_norm.2
      have norm_bound: ‖u - (x - a)‖ ≤ ‖z - (x - a)‖ + 2 := by
        have ieq : f z + inner ℝ a (u - z) + ‖u - x‖ ^ 2 / 2 ≤ f z + ‖z - x‖ ^ 2 / 2 + 1 := by
          calc
            f z + inner ℝ a (u - z) + ‖u - x‖ ^ 2 / 2 ≤ g u := second_lower_bound u
            _ ≤ f z + ‖z - x‖ ^ 2 / 2 := uin
            _ ≤ f z + ‖z - x‖ ^ 2 / 2 + 1 := by linarith
        rw [add_assoc, add_assoc, add_le_add_iff_left] at ieq
        have eq : inner ℝ a (u - z) + ‖u - x‖ ^ 2 / 2 =
            (‖u - (x - a)‖ ^ 2 - ‖a‖ ^ 2 + 2 * inner ℝ (x - z) a) / 2 := by
          have h1 : u - (x - a) = (u - x) + a := by abel
          have h2 : inner ℝ a (u - z) = inner ℝ (u - x) a + inner ℝ (x - z) a := by
            rw [real_inner_comm, ← inner_add_left]; congr 1; abel
          rw [h1, norm_add_sq_real, h2]; ring
        rw [eq] at ieq
        have ieq2 : ‖u - (x - a)‖ ^ 2 ≤ ‖z - (x - a)‖ ^ 2 + 2 := by
          have h3 : ‖z - (x - a)‖ ^ 2 = ‖z - x‖ ^ 2 + 2 * inner ℝ (z - x) a + ‖a‖ ^ 2 := by
            rw [show z - (x - a) = (z - x) + a by abel, norm_add_sq_real]
          have h4 : inner ℝ (x - z) a = - inner ℝ (z - x) a := by
            rw [← inner_neg_left, neg_sub]
          rw [h3]; linarith
        have : |‖z - (x - a)‖ + 2| = ‖z - (x - a)‖ + 2 := by
          apply abs_of_pos; apply add_pos_of_nonneg_of_pos (norm_nonneg (z - (x - a)))
          simp
        rw [← abs_norm, ← this, ← sq_le_sq, add_sq]
        calc
          ‖u - (x - a)‖ ^ 2 ≤ ‖z - (x - a)‖ ^ 2 + 2 := ieq2
          _ ≤ ‖z - (x - a)‖ ^ 2 + 2 * ‖z - (x - a)‖ * 2 + 2 ^ 2 := by
            rw [add_assoc, add_le_add_iff_left]; apply le_add_of_nonneg_of_le
            simp; norm_num
      exact norm_bound
    have compactb : IsCompact B := isCompact_closedBall (x - a) (‖z - (x - a)‖ + 2)
    rw [← closure_eq_iff_isClosed] at closeds; rw [← closeds]
    apply IsCompact.closure_of_subset compactb sinb
  rcases exists_seq_tendsto_sInf neImS S_bddbelow with ⟨fx, _, cfx, fxs⟩
  choose xn xsub xeq using fxs
  rcases IsCompact.tendsto_subseq compacts xsub with ⟨x', _, k, mono, cxk⟩
  have cfxk : Filter.Tendsto (g ∘ xn ∘ k) Filter.atTop (𝓝 (sInf ImS)) := by
    have xkeq : ∀ (n : ℕ), (g ∘ xn ∘ k) n = (fx ∘ k) n := fun n => xeq <| k n
    rw [tendsto_congr xkeq]
    apply Tendsto.comp cfx (StrictMono.tendsto_atTop mono)
  have inepi : (x', sInf ImS) ∈ epi := by
    let p := fun c ↦ (((fun n ↦ xn n) ∘ k) c, (g ∘ xn ∘ k) c)
    have pnin :  ∀ c : ℕ, p c ∈ epi := by intro c; simp [epi, p]
    apply IsClosed.isSeqClosed epi_closed pnin
    change Tendsto (fun c ↦ (((fun n ↦ xn n) ∘ k) c, (g ∘ xn ∘ k) c)) atTop (𝓝 (x', sInf ImS))
    apply Tendsto.prodMk_nhds cxk cfxk
  have minima_ieq : g x' ≤ sInf ImS := inepi
  have minima : ∀ w : E, g x' ≤ g w := by
      intro w
      by_cases hw : w ∈ S
      · have gwin : g w ∈ ImS := by use w
        have legw : sInf ImS ≤ g w := by
          rw [Real.sInf_le_iff S_bddbelow neImS]
          intro _ epos; use g w; use gwin; linarith
        linarith
      · have gwnin : g z < g w := by
          simp [S] at hw; simp [g]; exact hw
        have gzin : g z ∈ ImS := by use z; simp [S]
        have legw : sInf ImS ≤ g w := by
          rw [Real.sInf_le_iff S_bddbelow neImS]
          intro _ epos; use g z; use gzin; linarith
        linarith
  constructor
  · use x'; simp [prox_set]; rw [prox_prop, isMinOn_iff]
    intro v _; exact minima v
  · have aux : prox_set f x = {x | IsMinOn g univ x} := by
      simp [prox_set]; ext y
      constructor
      · intro yin; simp [prox_prop] at yin; simp; exact yin
      · intro yin; simp; rw [prox_prop]
        simp at yin; exact yin
    have nes : Nonempty S := by use z; simp [S]
    rw [eq] at compacts; rw [eq] at nes
    rw [aux] -- apply IsCompact_isMinOn_of_isCompact_preimage hc nes compacts
    have seq : {x | IsMinOn g univ x} = (g ⁻¹' Set.Iic (g x')) := by
      ext y
      constructor
      · exact fun hxx => isMinOn_iff.mp hxx x' trivial
      · intro yin; simp at yin
        exact fun x xuniv => le_trans yin ((fun x _ => minima x) x xuniv)
    simp only [seq]
    apply IsCompact.of_isClosed_subset compacts (LowerSemicontinuous.isClosed_preimage hg (g x'))
    apply Set.preimage_mono
    simp only [Set.Iic_subset_Iic]
    exact minima z

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem prox_well_define (f : E → ℝ) (hc : LowerSemicontinuous f) (lbdf : BddBelow (f '' univ)) :
    ∀ x, ∃ y, prox_prop f x y := by
  intro x
  rcases (prox_set_compact_of_lowersemi f hc lbdf x).1 with ⟨y, yprop⟩
  use y; simp [prox_set] at yprop; exact yprop

theorem prox_well_define_convex (f : E → ℝ) (hc : ContinuousOn f univ)
    (hconv : ConvexOn ℝ univ f) :
  ∀ x, ∃ y, prox_prop f x y := by
  intro x
  rcases (prox_set_compact_of_convex f hc hconv x).1 with ⟨y, yprop⟩
  use y; simp [prox_set] at yprop; exact yprop

/-- A proximal point of `f` at `x` for `f` lower semicontinuous and bounded below: a point of
`prox_set f x`, chosen by `Classical.choose` from `prox_well_define`. -/
def prox_point_c (f : E → ℝ) (x : E) (hc : LowerSemicontinuous f)
    (lbdf : BddBelow (f '' univ)) : E :=
  have h : ∃ y, prox_set f x y := by
    apply prox_well_define f hc lbdf x
  Classical.choose h

/-- A proximal point of `f` at `x` for `f` continuous and convex on the whole space: a point of
`prox_set f x`, chosen by `Classical.choose` from `prox_well_define_convex`. -/
def prox_point_c' (f : E → ℝ) (x : E) (hc : ContinuousOn f univ)
    (hconv : ConvexOn ℝ univ f) : E :=
  have h : ∃ y, prox_set f x y := by
    apply prox_well_define_convex f hc hconv x
  Classical.choose h

section properties

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {s : Set E} {f : E → ℝ} {u x y₁ y₂ : E} {t : ℝ}

open Set InnerProductSpace

/-
  The uniqueness of the proximal for proper convex function
-/
theorem prox_unique_of_convex (f : E → ℝ) (x : E) (hfun : ConvexOn ℝ univ f)
    (h₁ : prox_prop f x y₁) (h₂ : prox_prop f x y₂) : y₁ = y₂ := by
  let g := fun u ↦ f u + ‖u - x‖ ^ 2 / 2
  let m := (1 : ℝ)
  have gsconv : StrongConvexOn univ m g := by
    apply strongconvex_of_convex_add_sq
    show ConvexOn ℝ univ f; apply hfun
  rw [prox_prop] at h₁
  rw [prox_prop] at h₂
  apply Strongly_Convex_Unique_Minima gsconv
  apply h₁; apply h₂; simp; simp; norm_num
/-
   The square of norm is convex on a convex set
-/
lemma convex_of_norm_sq {s : Set E} (x : E) (conv : Convex ℝ s) :
    ConvexOn ℝ s (fun (u : E) ↦ ‖u - x‖ ^ 2 / 2) := by
  rw [ConvexOn]; use conv
  intro y _ z _ a b anneg bnneg absum1
  have eq1 : a • y + b • z - x = a • (y - x) + b • (z - x) := by
    rw [smul_sub, smul_sub, add_comm_sub, sub_sub, ← add_smul, add_comm b a]
    rw [absum1, one_smul, ← add_sub]
  have key (u v : E) : ‖a • u + b • v‖ ^ 2 ≤ a * ‖u‖ ^ 2 + b * ‖v‖ ^ 2 := by
    have h1 : ‖a • u + b • v‖ ≤ a * ‖u‖ + b * ‖v‖ := by
      calc
        ‖a • u + b • v‖ ≤ ‖a • u‖ + ‖b • v‖ := norm_add_le _ _
        _ = a * ‖u‖ + b * ‖v‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg anneg, Real.norm_of_nonneg bnneg]
    have h2 : (a * ‖u‖ + b * ‖v‖) ^ 2 = a * ‖u‖ ^ 2 + b * ‖v‖ ^ 2
        - a * b * (‖u‖ - ‖v‖) ^ 2 := by
      linear_combination (a * ‖u‖ ^ 2 + b * ‖v‖ ^ 2) * absum1
    calc
      ‖a • u + b • v‖ ^ 2 ≤ (a * ‖u‖ + b * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ a * ‖u‖ ^ 2 + b * ‖v‖ ^ 2 := by
        rw [h2]; linarith [mul_nonneg (mul_nonneg anneg bnneg) (sq_nonneg (‖u‖ - ‖v‖))]
  simp only [smul_eq_mul]
  rw [eq1]
  linarith [key (y - x) (z - x)]

/-
  Sub-derivative at x equal to sub-derivative within univ at x
-/
lemma Subderivat_eq_SubderivWithinAt_univ (f : E → ℝ) :
    SubderivWithinAt f univ u = SubderivAt f u := by
    apply subset_antisymm
    · intro p pin
      rw [SubderivWithinAt] at pin
      rw [← mem_SubderivAt, ← hasSubgradientWithinAt_univ]
      apply pin
    · intro p pin
      rw [← mem_SubderivAt, ← hasSubgradientWithinAt_univ] at pin;
      rw [SubderivWithinAt]
      apply pin

/-
  relation of proximal between a function and its shift
-/
theorem proximal_shift (a : E) {t : ℝ} (tnz : t ≠ 0) (f : E → ℝ) :
    ∀ z : E, prox_prop (fun x ↦ f (t • x + a)) x z ↔
      prox_prop (t ^ 2 • f) (t • x + a) (t • z + a) := by
  intro z
  simp only [prox_prop, isMinOn_univ_iff, Pi.smul_apply, smul_eq_mul]
  have hk (w : E) : ‖t • w + a - (t • x + a)‖ ^ 2 = t ^ 2 * ‖w - x‖ ^ 2 := by
    rw [add_sub_add_right_eq_sub, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hy (y : E) : t • (t⁻¹ • (y - a)) + a = y := by
    rw [smul_smul, mul_inv_cancel₀ tnz, one_smul, sub_add_cancel]
  have tsq : 0 < t ^ 2 := by positivity
  constructor
  · intro cond y
    obtain ⟨w, rfl⟩ : ∃ w, t • w + a = y := ⟨_, hy y⟩
    specialize cond w
    rw [hk, hk]
    have := mul_le_mul_of_nonneg_left cond tsq.le
    linarith
  · intro cond w
    specialize cond (t • w + a)
    rw [hk, hk] at cond
    have h : t ^ 2 * (f (t • z + a) + ‖z - x‖ ^ 2 / 2) ≤
        t ^ 2 * (f (t • w + a) + ‖w - x‖ ^ 2 / 2) := by linarith
    exact le_of_mul_le_mul_left h tsq

/-
  relation of proximal between a function and its scale
-/
theorem proximal_scale {t : ℝ} (tpos : 0 < t) (f : E → ℝ) :
    ∀ z : E, prox_prop (fun x ↦ t • f (t⁻¹ • x)) x z ↔
      prox_prop (t⁻¹ • f) (t⁻¹ • x) (t⁻¹ • z) := by
  intro z
  simp only [prox_prop, isMinOn_univ_iff, Pi.smul_apply, smul_eq_mul]
  have tne : t ≠ 0 := tpos.ne'
  have hk (w : E) : ‖t⁻¹ • w - t⁻¹ • x‖ ^ 2 = t⁻¹ ^ 2 * ‖w - x‖ ^ 2 := by
    rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have e (A B : ℝ) : t⁻¹ ^ 2 * (t * A + B / 2) = t⁻¹ * A + t⁻¹ ^ 2 * B / 2 := by
    field_simp
  have ssq : 0 < t⁻¹ ^ 2 := by positivity
  constructor
  · intro cond y
    obtain ⟨w, rfl⟩ : ∃ w, t⁻¹ • w = y := ⟨t • y, by rw [smul_smul, inv_mul_cancel₀ tne, one_smul]⟩
    specialize cond w
    rw [hk, hk]
    have := mul_le_mul_of_nonneg_left cond ssq.le
    rw [e, e] at this
    linarith
  · intro cond y
    specialize cond (t⁻¹ • y)
    rw [hk, hk] at cond
    have h : t⁻¹ ^ 2 * (t * f (t⁻¹ • z) + ‖z - x‖ ^ 2 / 2) ≤
        t⁻¹ ^ 2 * (t * f (t⁻¹ • y) + ‖y - x‖ ^ 2 / 2) := by
      rw [e, e]; linarith
    exact le_of_mul_le_mul_left h ssq

/-
  change of proximal when added a linear components
-/
theorem proximal_add_linear (a : E) (f : E → ℝ) :
    ∀ z : E, prox_prop (fun x ↦ f x + inner ℝ a x) x z ↔
      prox_prop f (x - a) z := by
  intro z
  rw [prox_prop, prox_prop, isMinOn_univ_iff, isMinOn_univ_iff]
  have aux (v : E) : ‖v - (x - a)‖ ^ 2 / 2 =
      ‖v - x‖ ^ 2 / 2 + inner ℝ a v + (‖a‖ ^ 2 / 2 - inner ℝ a x) := by
    rw [← sub_add, norm_add_sq_real, real_inner_comm, inner_sub_right]; ring_nf
  constructor
  · intro cond y
    specialize cond y
    rw [aux, aux, add_comm _ (inner ℝ a z), add_comm _ (inner ℝ a y)]
    linarith
  · intro cond y
    specialize cond y
    rw [aux, aux, add_comm _ (inner ℝ a z), add_comm _ (inner ℝ a y)] at cond
    linarith

/-
  change of proximal when added a square components
-/
theorem proximal_add_sq (a : E) {l : ℝ} (lpos : 0 < l) (f : E → ℝ) :
    ∀ z : E, prox_prop (fun x ↦ f x + l / 2 * ‖x - a‖ ^ 2) x z ↔
      prox_prop ((1 / (l + 1)) • f) ((1 / (l + 1)) • (x + l • a)) z := by
  intro z
  rw [prox_prop, prox_prop, isMinOn_univ_iff, isMinOn_univ_iff]
  have aux (v : E) : ‖v - (1 / (l + 1)) • (x + l • a)‖ ^ 2 / 2 =
      (l + 1)⁻¹ * (l / 2 * ‖v - a‖ ^ 2 + ‖v - x‖ ^ 2 / 2 + (((l + 1)⁻¹ * (‖x + l • a‖ ^ 2)
        - ‖x‖ ^ 2 - l * ‖a‖ ^ 2) / 2)) := by
    have hl : l + 1 ≠ 0 := by linarith
    rw [norm_sub_sq_real v, norm_sub_sq_real v a, norm_sub_sq_real v x]
    simp only [inner_smul_right, inner_add_right]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  have hc : 0 < (l + 1)⁻¹ := by positivity
  simp only [Pi.smul_apply, smul_eq_mul, one_div] at aux ⊢
  constructor
  · intro cond y
    specialize cond y
    rw [aux, aux]
    have := mul_le_mul_of_nonneg_left cond hc.le
    linarith
  · intro cond y
    specialize cond y
    rw [aux, aux] at cond
    have h : (l + 1)⁻¹ * (f z + l / 2 * ‖z - a‖ ^ 2 + ‖z - x‖ ^ 2 / 2) ≤
        (l + 1)⁻¹ * (f y + l / 2 * ‖y - a‖ ^ 2 + ‖y - x‖ ^ 2 / 2) := by linarith
    have := le_of_mul_le_mul_left h hc
    linarith

end properties

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {s : Set E} {f : E → ℝ} {u x : E} {t : ℝ}

/-
  u minimize the proximal at x iff x - u is subgradient
-/
theorem prox_iff_subderiv (f : E → ℝ) (hfun : ConvexOn ℝ univ f) :
    ∀ u : E, prox_prop f x u ↔ x - u ∈ SubderivAt f u := by
  intro u; rw [prox_prop, ← HasSubgradientAt_zero_iff_isMinOn, mem_SubderivAt]
  let g := fun u ↦ ‖u - x‖ ^ 2 / 2
  have hg : ConvexOn ℝ Set.univ g := by apply convex_of_norm_sq x (convex_univ)
  have hcg : ContinuousOn g univ := by
    change ContinuousOn (fun u ↦ ‖u - x‖ ^ 2 / 2) univ
    fun_prop
  change 0 ∈ SubderivAt (f + g) u ↔ x - u ∈ SubderivAt f u
  have : SubderivAt (f + g) u = SubderivAt (g + f) u := by
    unfold SubderivAt; ext z; rw [Set.mem_ofPred, Set.mem_ofPred];
    constructor
    repeat
    unfold HasSubgradientAt; intro hy y; specialize hy y; simp at hy ⊢; linarith
  rw [this, ← SubderivAt.add hg hfun hcg]
  have subg : SubderivAt g u = {u - x} := by
    let g' := fun u ↦ u - x
    have gderiv : ∀ x, HasGradientAt g (g' x) x := gradient_of_sq
    have : SubderivWithinAt g univ u = {g' u} := by
      apply SubderivWithinAt_eq_gradient; simp
      have gconv : ConvexOn ℝ univ g := by
        rcases hfun with ⟨conv, _⟩
        apply convex_of_norm_sq
        apply conv
      apply gconv; apply gderiv
    rw [← Subderivat_eq_SubderivWithinAt_univ, this]
  rw [subg]; simp

/-
  If f is differentiable and convex on E, then u minimize the proximal at x iff ∇f(u) = x - u
-/
theorem prox_iff_grad (f : E → ℝ) {f' : E → E} (hfun : ConvexOn ℝ univ f)
    (hdiff : ∀ x, HasGradientAt f (f' x) x) :
    ∀ u : E, prox_prop f x u ↔ f' u = x - u := by
  intro u
  have iff_subderiv : ∀ u : E, prox_prop f x u ↔ x - u ∈ SubderivAt f u := by
    apply prox_iff_subderiv
    apply hfun
  specialize iff_subderiv u
  rw [iff_subderiv, ← Subderivat_eq_SubderivWithinAt_univ]
  have subderiv_eq_gradient : SubderivWithinAt f univ u = {f' u} := by
    apply SubderivWithinAt_eq_gradient; simp
    apply hfun; apply hdiff
  rw [subderiv_eq_gradient]; simp
  apply eq_comm

/-
  If f is differentiable and convex on E, then u minimize the proximal for t*f at x iff
  t ∇f(u) = x - u
-/
theorem prox_iff_grad_smul (f : E → ℝ) {f' : E → E} (t : ℝ) (hfun : ConvexOn ℝ univ f)
    (hdiff : ∀ x, HasGradientAt f (f' x) x) (tnonneg : 0 ≤ t) :
    ∀ u : E, prox_prop (t • f) x u ↔ t • f' u = x - u := by
  intro u
  let g := fun u ↦ (t • f) u
  let g' := fun u ↦ t • f' u
  have gconv : ConvexOn ℝ univ g := by
    apply ConvexOn.smul tnonneg hfun
  have gderiv : ∀ x, HasGradientAt g (g' x) x := by
    intro x
    simp only [Pi.smul_apply, g, g']
    apply HasGradientAt.const_smul'
    exact hdiff x
  rw [prox_iff_subderiv]
  have : SubderivWithinAt g univ u = {g' u} := by
      apply SubderivWithinAt_eq_gradient; simp
      apply gconv; apply gderiv
  rw [← Subderivat_eq_SubderivWithinAt_univ, this]; simp
  apply eq_comm
  apply gconv

/-
  u minimize the proximal for t*f at x iff (x - u)/t is subgradient
-/
theorem prox_iff_subderiv_smul (f : E → ℝ) {t : ℝ} (hfun : ConvexOn ℝ univ f) (ht : 0 < t) :
    ∀ u : E, prox_prop (t • f) x u ↔ (1 / t) • (x - u) ∈ (SubderivAt f u) := by
  intro u
  let g := fun u ↦ (t • f) u
  have tnonneg : 0 ≤ t := by linarith
  have gconv : ConvexOn ℝ univ g := by
    apply ConvexOn.smul tnonneg hfun
  rw [prox_iff_subderiv, ← mem_SubderivAt, ← mem_SubderivAt]
  rw [HasSubgradientAt, HasSubgradientAt]
  simp only [Pi.smul_apply, smul_eq_mul, inner_smul_left, one_div, conj_trivial]
  constructor
  · intro cond y
    specialize cond y
    have e : f y - (f u + t⁻¹ * inner ℝ (x - u) (y - u)) =
        t⁻¹ * (t * f y - (t * f u + inner ℝ (x - u) (y - u))) := by
      field_simp
    have := mul_nonneg (inv_nonneg.2 ht.le) (sub_nonneg.2 cond)
    rw [ge_iff_le, ← sub_nonneg, e]; exact this
  · intro cond y
    specialize cond y
    have := mul_le_mul_of_nonneg_left cond ht.le
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at this
    linarith
  exact gconv

end
