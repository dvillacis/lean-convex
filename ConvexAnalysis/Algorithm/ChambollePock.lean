/-
Copyright (c) 2026 David Villacís. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Villacís
-/
import Mathlib

/-!
# The primal–dual method of Chambolle and Pock

PDHGM with extrapolation `θ = 1`, for `min_x max_y ⟪L x, y⟫ + Gf x - Ff y` over convex sets.

Setting: real inner product spaces `X`, `Y`, a linear map `L : X → Y` with `‖L x‖² ≤ M ‖x‖²`,
steps `τ, σ > 0` with `τ σ M < 1`, convex-analytic data `Gf : X → ℝ` on `C ⊆ X` and
`Ff : Y → ℝ` on `D ⊆ Y`, and the Lagrangian
`Lag x y = ⟪L x, y⟫ + Gf x - Ff y`. A run of the method (`Run`) is given by the variational
inequalities that characterize its two proximal steps
    `x_{n+1} = prox_{τ Gf}(x_n - τ L* y_{n+1})`,  `y_{n+1} = prox_{σ Ff}(y_n + σ L x̄_n)`,
with `x̄_n = x_n + (x_n - x_{n-1})` (`x̄_0 = x_0`).

* `young` — `⟪L a, b⟫ ≤ κ (‖a‖²/(2τ) + ‖b‖²/(2σ))`, `κ = √(τ σ M)`.
* `Run.energy_step` — for a saddle point `(x*, y*)`, the energy
  `V_n = ‖x* - x_n‖²/(2τ) + ‖y* - y_n‖²/(2σ) - ⟪L d_n, y* - y_n⟫ + κ ‖d_n‖²/(2τ)`,
  `d_n = x_n - x_{n-1}`, satisfies `V_{n+1} + (1-κ)(‖d_{n+1}‖²/(2τ) + ‖y_{n+1}-y_n‖²/(2σ)) ≤ V_n`.
* `Run.summable_step`, `Run.tendsto_dx`, `Run.tendsto_dy` — the steps are square-summable.
* `Run.bounded` — the iterates are bounded.
* `Run.cluster_saddle` — every cluster point of `(x_{n+1}, y_{n+1})` is a saddle point.
* `Run.energy_bound` — Theorem 1(a) of Chambolle–Pock:
  `‖x* - x_n‖²/(2τ) + (1-κ) ‖y* - y_n‖²/(2σ) ≤ ‖x* - x_0‖²/(2τ) + ‖y* - y_0‖²/(2σ)`.
* `Run.energy_step_gap`, `Run.sum_gap_le` — the energy inequality at an arbitrary
  `(x, y) ∈ C × D`, with the partial gap `Lag(x_{n+1}, y) - Lag(x, y_{n+1})`, and its telescoped
  form.
* `Run.ergodic_gap` — Theorem 1(b) of Chambolle–Pock: for convex `Gf`, `Ff` the averages
  `x̄_N`, `ȳ_N` of the iterates satisfy
  `Lag(x̄_N, y) - Lag(x, ȳ_N) ≤ (‖x - x_0‖²/(2τ) + ‖y - y_0‖²/(2σ)) / N` on `C × D`.
* `Run.tendsto_saddle` — Theorem 1(c) of Chambolle–Pock: in finite dimension the whole
  sequence `(x_n, y_n)` converges to a saddle point.
* `Run.exists_le` — a continuous function that vanishes at saddle points is `≤ ε` at some
  iterate, for every `ε > 0`.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

namespace ChambollePock

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Successive differences `d_0 = 0`, `d_{n+1} = x_{n+1} - x_n`. -/
def dseq (x : ℕ → X) : ℕ → X
  | 0 => 0
  | n + 1 => x (n + 1) - x n

omit [InnerProductSpace ℝ X] in
@[simp] lemma dseq_zero (x : ℕ → X) : dseq x 0 = 0 := rfl
omit [InnerProductSpace ℝ X] in
@[simp] lemma dseq_succ (x : ℕ → X) (n : ℕ) : dseq x (n + 1) = x (n + 1) - x n := rfl

/-- Young-type bound for the coupling: `⟪L a, b⟫ ≤ √(τσM) (‖a‖²/(2τ) + ‖b‖²/(2σ))`. -/
lemma young (L : X →ₗ[ℝ] Y) {M τ σ : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, ‖L x‖ ^ 2 ≤ M * ‖x‖ ^ 2)
    (hτ : 0 < τ) (hσ : 0 < σ) (a : X) (b : Y) :
    ⟪L a, b⟫ ≤ Real.sqrt (τ * σ * M) * (‖a‖ ^ 2 / (2 * τ) + ‖b‖ ^ 2 / (2 * σ)) := by
  set κ := Real.sqrt (τ * σ * M) with hκ
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hκ2 : κ ^ 2 = τ * σ * M := Real.sq_sqrt (by positivity)
  set p := ‖L a‖
  set α := ‖a‖
  set β := ‖b‖
  have hp : p ^ 2 ≤ M * α ^ 2 := hM a
  have hcs : ⟪L a, b⟫ ≤ p * β := real_inner_le_norm _ _
  set P := κ * α ^ 2 / (2 * τ)
  set Q := κ * β ^ 2 / (2 * σ)
  have hP0 : 0 ≤ P := by positivity
  have hQ0 : 0 ≤ Q := by positivity
  have h4 : 4 * P * Q = M * α ^ 2 * β ^ 2 := by
    simp only [P, Q]
    field_simp
    rw [hκ2]
    ring
  have hR : p * β ≤ P + Q := by
    have hpb0 : 0 ≤ p * β := by positivity
    have hsq : (p * β) ^ 2 ≤ (P + Q) ^ 2 := by
      have : (p * β) ^ 2 ≤ M * α ^ 2 * β ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right hp (by positivity)
      nlinarith [sq_nonneg (P - Q)]
    exact (pow_le_pow_iff_left₀ hpb0 (by positivity) two_ne_zero).1 hsq
  calc ⟪L a, b⟫ ≤ p * β := hcs
    _ ≤ P + Q := hR
    _ = κ * (α ^ 2 / (2 * τ) + β ^ 2 / (2 * σ)) := by simp only [P, Q]; ring

lemma one_sub_kappa_pos {t : ℝ} (hκ : t < 1) : 0 < 1 - Real.sqrt t := by
  have : Real.sqrt t < 1 := (Real.sqrt_lt' one_pos).2 (by simpa using hκ)
  linarith

lemma tendsto_zero_of_sq_div {Z : Type*} [NormedAddCommGroup Z] {v : ℕ → Z} {c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun n => ‖v n‖ ^ 2 / c) atTop (𝓝 0)) : Tendsto v atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have := (h.const_mul c).sqrt
  simp only [mul_zero, Real.sqrt_zero] at this
  refine this.congr fun n => ?_
  rw [mul_div_cancel₀ _ hc.ne', Real.sqrt_sq (norm_nonneg _)]

variable (L : X →ₗ[ℝ] Y) (Gf : X → ℝ) (Ff : Y → ℝ) (C : Set X) (D : Set Y) (τ σ : ℝ)

/-- The Lagrangian `⟪L x, y⟫ + Gf x - Ff y`. -/
def Lag (x : X) (y : Y) : ℝ := ⟪L x, y⟫ + Gf x - Ff y

/-- `(xs, ys)` is a saddle point of `Lag` on `C × D`. -/
def IsSaddle (xs : X) (ys : Y) : Prop :=
  xs ∈ C ∧ ys ∈ D ∧ (∀ y ∈ D, Lag L Gf Ff xs y ≤ Lag L Gf Ff xs ys) ∧
    ∀ x ∈ C, Lag L Gf Ff xs ys ≤ Lag L Gf Ff x ys

/-- A run of the method, given by the variational inequalities of its proximal steps. -/
structure Run where
  /-- The sequence of primal iterates. -/
  x : ℕ → X
  /-- The sequence of dual iterates. -/
  y : ℕ → Y
  x_mem : ∀ n, x (n + 1) ∈ C
  y_mem : ∀ n, y (n + 1) ∈ D
  prox_x : ∀ n, ∀ x' ∈ C,
    ⟪x n - x (n + 1), x' - x (n + 1)⟫ / τ - ⟪y (n + 1), L (x' - x (n + 1))⟫ ≤
      Gf x' - Gf (x (n + 1))
  prox_y : ∀ n, ∀ y' ∈ D,
    ⟪y n - y (n + 1), y' - y (n + 1)⟫ / σ + ⟪L (x n + dseq x n), y' - y (n + 1)⟫ ≤
      Ff y' - Ff (y (n + 1))

namespace Run

variable {L Gf Ff C D τ σ} (run : Run L Gf Ff C D τ σ) {M : ℝ}

/-- The energy `V_n`. -/
noncomputable def V (M : ℝ) (xs : X) (ys : Y) (n : ℕ) : ℝ :=
  ‖xs - run.x n‖ ^ 2 / (2 * τ) + ‖ys - run.y n‖ ^ 2 / (2 * σ) -
    ⟪L (dseq run.x n), ys - run.y n⟫ + Real.sqrt (τ * σ * M) * ‖dseq run.x n‖ ^ 2 / (2 * τ)

/-- The step size `s_n = ‖d_{n+1}‖²/(2τ) + ‖y_{n+1} - y_n‖²/(2σ)`. -/
noncomputable def step (n : ℕ) : ℝ :=
  ‖dseq run.x (n + 1)‖ ^ 2 / (2 * τ) + ‖run.y (n + 1) - run.y n‖ ^ 2 / (2 * σ)

/-- The ergodic average `(x_1 + ⋯ + x_N) / N` of the primal iterates. -/
noncomputable def xavg (N : ℕ) : X := ∑ i ∈ Finset.range N, (N : ℝ)⁻¹ • run.x (i + 1)

/-- The ergodic average `(y_1 + ⋯ + y_N) / N` of the dual iterates. -/
noncomputable def yavg (N : ℕ) : Y := ∑ i ∈ Finset.range N, (N : ℝ)⁻¹ • run.y (i + 1)

variable (hM0 : 0 ≤ M) (hM : ∀ x, ‖L x‖ ^ 2 ≤ M * ‖x‖ ^ 2) (hτ : 0 < τ) (hσ : 0 < σ)
  {xs : X} {ys : Y} (hs : IsSaddle L Gf Ff C D xs ys)
include hM0 hM hτ hσ hs

omit hs in
/-- **One-step energy inequality with the partial gap.** For any `(x, y) ∈ C × D`, not
necessarily a saddle point,
`V_{n+1} + (1-κ) s_n + Lag(x_{n+1}, y) - Lag(x, y_{n+1}) ≤ V_n`. -/
theorem energy_step_gap (hxs : xs ∈ C) (hys : ys ∈ D) (n : ℕ) :
    run.V M xs ys (n + 1) + (1 - Real.sqrt (τ * σ * M)) * run.step n +
      (Lag L Gf Ff (run.x (n + 1)) ys - Lag L Gf Ff xs (run.y (n + 1))) ≤ run.V M xs ys n := by
  set κ := Real.sqrt (τ * σ * M)
  have hP := run.prox_x n xs hxs
  have hD := run.prox_y n ys hys
  -- polarization identities
  have px := norm_sub_sq_real (run.x n - run.x (n + 1)) (xs - run.x (n + 1))
  have py := norm_sub_sq_real (run.y n - run.y (n + 1)) (ys - run.y (n + 1))
  rw [show run.x n - run.x (n + 1) - (xs - run.x (n + 1)) = run.x n - xs by abel] at px
  rw [show run.y n - run.y (n + 1) - (ys - run.y (n + 1)) = run.y n - ys by abel] at py
  -- Young for the cross term
  have hy := young L hM0 hM hτ hσ (dseq run.x n) (run.y (n + 1) - run.y n)
  -- linear algebra of the coupling
  have e1 : ⟪run.y (n + 1), L (xs - run.x (n + 1))⟫ =
      ⟪L xs, run.y (n + 1)⟫ - ⟪L (run.x (n + 1)), run.y (n + 1)⟫ := by
    rw [map_sub, real_inner_comm, inner_sub_left]
  have e2 : ⟪L (run.x n + dseq run.x n), ys - run.y (n + 1)⟫ =
      ⟪L (run.x (n + 1)), ys - run.y (n + 1)⟫ - ⟪L (dseq run.x (n + 1)), ys - run.y (n + 1)⟫ +
        ⟪L (dseq run.x n), ys - run.y n⟫ -
        ⟪L (dseq run.x n), run.y (n + 1) - run.y n⟫ := by
    have : run.x n + dseq run.x n = run.x (n + 1) - dseq run.x (n + 1) + dseq run.x n := by
      simp only [dseq_succ]; abel
    rw [this, map_add, map_sub, inner_add_left, inner_sub_left]
    have : ys - run.y (n + 1) = (ys - run.y n) - (run.y (n + 1) - run.y n) := by abel
    rw [this, inner_sub_right (L (dseq run.x n))]
    ring
  have e3 : ⟪L (run.x (n + 1)), ys - run.y (n + 1)⟫ =
      ⟪L (run.x (n + 1)), ys⟫ - ⟪L (run.x (n + 1)), run.y (n + 1)⟫ := inner_sub_right _ _ _
  have nx : ‖run.x n - run.x (n + 1)‖ = ‖dseq run.x (n + 1)‖ := by
    rw [dseq_succ, norm_sub_rev]
  have ny : ‖run.y n - run.y (n + 1)‖ = ‖run.y (n + 1) - run.y n‖ := norm_sub_rev _ _
  have nx' : ‖run.x n - xs‖ = ‖xs - run.x n‖ := norm_sub_rev _ _
  have ny' : ‖run.y n - ys‖ = ‖ys - run.y n‖ := norm_sub_rev _ _
  rw [nx, nx'] at px
  rw [ny, ny'] at py
  have hτ' : τ ≠ 0 := hτ.ne'
  have hσ' : σ ≠ 0 := hσ.ne'
  have hi1 : ⟪run.x n - run.x (n + 1), xs - run.x (n + 1)⟫ / τ =
      ‖dseq run.x (n + 1)‖ ^ 2 / (2 * τ) + ‖xs - run.x (n + 1)‖ ^ 2 / (2 * τ) -
        ‖xs - run.x n‖ ^ 2 / (2 * τ) := by
    rw [show ⟪run.x n - run.x (n + 1), xs - run.x (n + 1)⟫ =
      (‖dseq run.x (n + 1)‖ ^ 2 + ‖xs - run.x (n + 1)‖ ^ 2 - ‖xs - run.x n‖ ^ 2) / 2 by linarith]
    field_simp
  have hi2 : ⟪run.y n - run.y (n + 1), ys - run.y (n + 1)⟫ / σ =
      ‖run.y (n + 1) - run.y n‖ ^ 2 / (2 * σ) + ‖ys - run.y (n + 1)‖ ^ 2 / (2 * σ) -
        ‖ys - run.y n‖ ^ 2 / (2 * σ) := by
    rw [show ⟪run.y n - run.y (n + 1), ys - run.y (n + 1)⟫ =
      (‖run.y (n + 1) - run.y n‖ ^ 2 + ‖ys - run.y (n + 1)‖ ^ 2 - ‖ys - run.y n‖ ^ 2) / 2 by
        linarith]
    field_simp
  rw [hi1, e1] at hP
  rw [hi2, e2, e3] at hD
  have hk1 : κ * ‖dseq run.x (n + 1)‖ ^ 2 / (2 * τ) =
      κ * (‖dseq run.x (n + 1)‖ ^ 2 / (2 * τ)) := by ring
  have hk0 : κ * ‖dseq run.x n‖ ^ 2 / (2 * τ) = κ * (‖dseq run.x n‖ ^ 2 / (2 * τ)) := by ring
  simp only [V, step, Lag]
  rw [hk1, hk0]
  nlinarith [hP, hD, hy]

/-- **One-step energy inequality.** At a saddle point the partial gap is nonnegative. -/
theorem energy_step (n : ℕ) :
    run.V M xs ys (n + 1) + (1 - Real.sqrt (τ * σ * M)) * run.step n ≤ run.V M xs ys n := by
  obtain ⟨hxs, hys, hsy, hsx⟩ := hs
  have h := run.energy_step_gap hM0 hM hτ hσ hxs hys n
  have hg1 := hsy (run.y (n + 1)) (run.y_mem n)
  have hg2 := hsx (run.x (n + 1)) (run.x_mem n)
  linarith

omit hs in
/-- Lower bound for the energy: `V_n ≥ ‖x* - x_n‖²/(2τ) + (1-κ) ‖y* - y_n‖²/(2σ)`. -/
theorem V_lower (n : ℕ) :
    ‖xs - run.x n‖ ^ 2 / (2 * τ) + (1 - Real.sqrt (τ * σ * M)) * (‖ys - run.y n‖ ^ 2 / (2 * σ)) ≤
      run.V M xs ys n := by
  have hy := young L hM0 hM hτ hσ (dseq run.x n) (ys - run.y n)
  have hk : Real.sqrt (τ * σ * M) * ‖dseq run.x n‖ ^ 2 / (2 * τ) =
      Real.sqrt (τ * σ * M) * (‖dseq run.x n‖ ^ 2 / (2 * τ)) := by ring
  simp only [V]
  rw [hk]
  nlinarith [hy]

omit hs in
/-- Upper bound for the energy:
`V_n ≤ ‖x* - x_n‖²/(2τ) + (1+κ) ‖y* - y_n‖²/(2σ) + 2κ ‖d_n‖²/(2τ)`. -/
theorem V_upper (n : ℕ) :
    run.V M xs ys n ≤ ‖xs - run.x n‖ ^ 2 / (2 * τ) +
      (1 + Real.sqrt (τ * σ * M)) * (‖ys - run.y n‖ ^ 2 / (2 * σ)) +
      2 * Real.sqrt (τ * σ * M) * (‖dseq run.x n‖ ^ 2 / (2 * τ)) := by
  have hy := young L hM0 hM hτ hσ (-dseq run.x n) (ys - run.y n)
  rw [map_neg, inner_neg_left, norm_neg] at hy
  have hk : Real.sqrt (τ * σ * M) * ‖dseq run.x n‖ ^ 2 / (2 * τ) =
      Real.sqrt (τ * σ * M) * (‖dseq run.x n‖ ^ 2 / (2 * τ)) := by ring
  simp only [V]
  rw [hk]
  nlinarith [hy]

omit hM0 hM hτ hσ hs in
lemma V_zero : run.V M xs ys 0 = ‖xs - run.x 0‖ ^ 2 / (2 * τ) + ‖ys - run.y 0‖ ^ 2 / (2 * σ) := by
  simp [V]

omit hM0 hM hs in
lemma step_nonneg (n : ℕ) : 0 ≤ run.step n := by
  simp only [step]; positivity

/-- Telescoped energy inequality. -/
theorem sum_step_le (n : ℕ) :
    (1 - Real.sqrt (τ * σ * M)) * ∑ i ∈ Finset.range n, run.step i ≤
      run.V M xs ys 0 - run.V M xs ys n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add]
    linarith [run.energy_step hM0 hM hτ hσ hs n]

/-- The energy is nonincreasing: `V_n ≤ V_0`. -/
theorem V_le_V_zero (hκ : τ * σ * M < 1) (n : ℕ) : run.V M xs ys n ≤ run.V M xs ys 0 := by
  have h := run.sum_step_le hM0 hM hτ hσ hs n
  have h0 : 0 ≤ ∑ i ∈ Finset.range n, run.step i :=
    Finset.sum_nonneg fun i _ => run.step_nonneg hτ hσ i
  nlinarith [one_sub_kappa_pos hκ]

/-- The steps are summable: `∑ (‖x_{n+1} - x_n‖²/(2τ) + ‖y_{n+1} - y_n‖²/(2σ)) < ∞`. -/
theorem summable_step (hκ : τ * σ * M < 1) : Summable run.step := by
  have hk := one_sub_kappa_pos hκ
  refine summable_of_sum_range_le (fun n => run.step_nonneg hτ hσ n)
    (c := run.V M xs ys 0 / (1 - Real.sqrt (τ * σ * M))) fun n => ?_
  rw [le_div_iff₀ hk]
  have h1 := run.sum_step_le hM0 hM hτ hσ hs n
  have h2 := run.V_lower hM0 hM hτ hσ n (xs := xs) (ys := ys)
  have h3 : 0 ≤ ‖xs - run.x n‖ ^ 2 / (2 * τ) + (1 - Real.sqrt (τ * σ * M)) *
      (‖ys - run.y n‖ ^ 2 / (2 * σ)) := by positivity
  linarith

/-- `x_{n+1} - x_n → 0`. -/
theorem tendsto_dx (hκ : τ * σ * M < 1) :
    Tendsto (fun n => run.x (n + 1) - run.x n) atTop (𝓝 0) := by
  refine tendsto_zero_of_sq_div (by positivity : (0 : ℝ) < 2 * τ) ?_
  refine squeeze_zero (fun n => by positivity) (fun n => ?_)
    (run.summable_step hM0 hM hτ hσ hs hκ).tendsto_atTop_zero
  have : 0 ≤ ‖run.y (n + 1) - run.y n‖ ^ 2 / (2 * σ) := by positivity
  simp only [step, dseq_succ]
  linarith

/-- `y_{n+1} - y_n → 0`. -/
theorem tendsto_dy (hκ : τ * σ * M < 1) :
    Tendsto (fun n => run.y (n + 1) - run.y n) atTop (𝓝 0) := by
  refine tendsto_zero_of_sq_div (by positivity : (0 : ℝ) < 2 * σ) ?_
  refine squeeze_zero (fun n => by positivity) (fun n => ?_)
    (run.summable_step hM0 hM hτ hσ hs hκ).tendsto_atTop_zero
  have : 0 ≤ ‖dseq run.x (n + 1)‖ ^ 2 / (2 * τ) := by positivity
  simp only [step]
  linarith

/-- The iterates are bounded. -/
theorem bounded (hκ : τ * σ * M < 1) :
    Bornology.IsBounded (Set.range fun n => (run.x n, run.y n)) := by
  have hk := one_sub_kappa_pos hκ
  set V0 := run.V M xs ys 0
  refine (Metric.isBounded_closedBall (x := (xs, ys))
    (r := Real.sqrt (2 * τ * V0) + Real.sqrt (2 * σ * V0 / (1 - Real.sqrt (τ * σ * M))))).subset ?_
  rintro _ ⟨n, rfl⟩
  have h1 := run.V_lower hM0 hM hτ hσ n (xs := xs) (ys := ys)
  have h2 := run.V_le_V_zero hM0 hM hτ hσ hs hκ n
  have ha : 0 ≤ ‖xs - run.x n‖ ^ 2 / (2 * τ) := by positivity
  have hb : 0 ≤ ‖ys - run.y n‖ ^ 2 / (2 * σ) := by positivity
  have hbx : ‖xs - run.x n‖ ≤ Real.sqrt (2 * τ * V0) := by
    rw [← abs_norm]; apply Real.abs_le_sqrt
    have : ‖xs - run.x n‖ ^ 2 / (2 * τ) ≤ V0 := by nlinarith
    rw [div_le_iff₀ (by positivity)] at this; linarith
  have hby : ‖ys - run.y n‖ ≤ Real.sqrt (2 * σ * V0 / (1 - Real.sqrt (τ * σ * M))) := by
    rw [← abs_norm]; apply Real.abs_le_sqrt
    have : (1 - Real.sqrt (τ * σ * M)) * (‖ys - run.y n‖ ^ 2 / (2 * σ)) ≤ V0 := by linarith
    rw [le_div_iff₀ hk]
    rw [mul_div_assoc', div_le_iff₀ (by positivity)] at this
    linarith
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff, dist_eq_norm, dist_eq_norm,
    norm_sub_rev, norm_sub_rev (run.y n)]
  exact ⟨hbx.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _)),
    hby.trans (le_add_of_nonneg_left (Real.sqrt_nonneg _))⟩

omit hs in
/-- Telescoped partial gaps: for any `(x, y) ∈ C × D`,
`∑_{i<N} (Lag(x_{i+1}, y) - Lag(x, y_{i+1})) ≤ ‖x - x_0‖²/(2τ) + ‖y - y_0‖²/(2σ)`. -/
theorem sum_gap_le (hκ : τ * σ * M < 1) (hxs : xs ∈ C) (hys : ys ∈ D) (N : ℕ) :
    ∑ i ∈ Finset.range N, (Lag L Gf Ff (run.x (i + 1)) ys - Lag L Gf Ff xs (run.y (i + 1))) ≤
      ‖xs - run.x 0‖ ^ 2 / (2 * τ) + ‖ys - run.y 0‖ ^ 2 / (2 * σ) := by
  have hk := one_sub_kappa_pos hκ
  have key : ∀ n, ∑ i ∈ Finset.range n,
      (Lag L Gf Ff (run.x (i + 1)) ys - Lag L Gf Ff xs (run.y (i + 1))) ≤
        run.V M xs ys 0 - run.V M xs ys n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h := run.energy_step_gap hM0 hM hτ hσ hxs hys n
      have := mul_nonneg hk.le (run.step_nonneg hτ hσ n)
      linarith
  have h1 := run.V_lower hM0 hM hτ hσ N (xs := xs) (ys := ys)
  have h2 : 0 ≤ ‖xs - run.x N‖ ^ 2 / (2 * τ) := by positivity
  have h3 : 0 ≤ (1 - Real.sqrt (τ * σ * M)) * (‖ys - run.y N‖ ^ 2 / (2 * σ)) :=
    mul_nonneg hk.le (by positivity)
  have h4 := key N
  rw [run.V_zero] at h4
  linarith

omit hs in
/-- **Ergodic rate** (Chambolle–Pock, Theorem 1(b)). For convex `Gf` on `C` and `Ff` on `D`,
the averages `x̄_N = (x_1 + ⋯ + x_N)/N`, `ȳ_N = (y_1 + ⋯ + y_N)/N` satisfy, for every
`(x, y) ∈ C × D` and `N ≥ 1`,
`Lag(x̄_N, y) - Lag(x, ȳ_N) ≤ (‖x - x_0‖²/(2τ) + ‖y - y_0‖²/(2σ)) / N`. No saddle point is
needed. -/
theorem ergodic_gap (hκ : τ * σ * M < 1) (hGc : ConvexOn ℝ C Gf) (hFc : ConvexOn ℝ D Ff)
    (hxs : xs ∈ C) (hys : ys ∈ D) {N : ℕ} (hN : 0 < N) :
    Lag L Gf Ff (run.xavg N) ys - Lag L Gf Ff xs (run.yavg N) ≤
      (‖xs - run.x 0‖ ^ 2 / (2 * τ) + ‖ys - run.y 0‖ ^ 2 / (2 * σ)) / N := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.2 hN0.le
  have hNN : (N : ℝ)⁻¹ * N = 1 := inv_mul_cancel₀ hN0.ne'
  have hw : ∑ _i ∈ Finset.range N, (N : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm, hNN]
  set a := ∑ i ∈ Finset.range N, ⟪L (run.x (i + 1)), ys⟫
  set b := ∑ i ∈ Finset.range N, Gf (run.x (i + 1))
  set c := ∑ i ∈ Finset.range N, ⟪L xs, run.y (i + 1)⟫
  set d := ∑ i ∈ Finset.range N, Ff (run.y (i + 1))
  -- Jensen for `Gf` and `Ff`, linearity for the coupling
  have hG : Gf (run.xavg N) ≤ (N : ℝ)⁻¹ * b := by
    have := hGc.map_sum_le (t := Finset.range N) (w := fun _ => (N : ℝ)⁻¹)
      (p := fun i => run.x (i + 1)) (fun _ _ => hinv) hw (fun i _ => run.x_mem i)
    simpa only [xavg, smul_eq_mul, ← Finset.mul_sum] using this
  have hF : Ff (run.yavg N) ≤ (N : ℝ)⁻¹ * d := by
    have := hFc.map_sum_le (t := Finset.range N) (w := fun _ => (N : ℝ)⁻¹)
      (p := fun i => run.y (i + 1)) (fun _ _ => hinv) hw (fun i _ => run.y_mem i)
    simpa only [yavg, smul_eq_mul, ← Finset.mul_sum] using this
  have ha : ⟪L (run.xavg N), ys⟫ = (N : ℝ)⁻¹ * a := by
    simp only [xavg, a, map_sum, map_smul, sum_inner, real_inner_smul_left, Finset.mul_sum]
  have hc : ⟪L xs, run.yavg N⟫ = (N : ℝ)⁻¹ * c := by
    simp only [yavg, c, inner_sum, real_inner_smul_right, Finset.mul_sum]
  -- the telescoped gaps
  have hsum := run.sum_gap_le hM0 hM hτ hσ hκ hxs hys N
  have hsplit : ∑ i ∈ Finset.range N,
      (Lag L Gf Ff (run.x (i + 1)) ys - Lag L Gf Ff xs (run.y (i + 1))) =
        a + b - N * Ff ys - c - N * Gf xs + d := by
    simp only [Lag, a, b, c, d, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  rw [hsplit] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum hinv
  have e1 : (N : ℝ)⁻¹ * (N * Ff ys) = Ff ys := by rw [← mul_assoc, hNN, one_mul]
  have e2 : (N : ℝ)⁻¹ * (N * Gf xs) = Gf xs := by rw [← mul_assoc, hNN, one_mul]
  rw [div_eq_inv_mul]
  simp only [Lag]
  rw [ha, hc]
  nlinarith [hmul, hG, hF, e1, e2]

/-- **Energy bound** (Chambolle–Pock, Theorem 1(a)): for every `n`,
`‖x* - x_n‖²/(2τ) + (1-κ) ‖y* - y_n‖²/(2σ) ≤ ‖x* - x_0‖²/(2τ) + ‖y* - y_0‖²/(2σ)`. -/
theorem energy_bound (hκ : τ * σ * M < 1) (n : ℕ) :
    ‖xs - run.x n‖ ^ 2 / (2 * τ) + (1 - Real.sqrt (τ * σ * M)) * (‖ys - run.y n‖ ^ 2 / (2 * σ)) ≤
      ‖xs - run.x 0‖ ^ 2 / (2 * τ) + ‖ys - run.y 0‖ ^ 2 / (2 * σ) := by
  rw [← run.V_zero (M := M) (xs := xs) (ys := ys)]
  exact (run.V_lower hM0 hM hτ hσ n).trans (run.V_le_V_zero hM0 hM hτ hσ hs hκ n)

/-- **Cluster points are saddle points.** Along a subsequence, `(x_{n+1}, y_{n+1})` converges to
a saddle point of the Lagrangian. -/
theorem cluster_saddle [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] (hκ : τ * σ * M < 1)
    (hC : IsClosed C) (hDc : IsClosed D) (hG : Continuous Gf) (hF : Continuous Ff) :
    ∃ xh yh, IsSaddle L Gf Ff C D xh yh ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => (run.x (φ k + 1), run.y (φ k + 1))) atTop (𝓝 (xh, yh)) := by
  have hbdd : Bornology.IsBounded (Set.range fun n => (run.x (n + 1), run.y (n + 1))) :=
    (run.bounded hM0 hM hτ hσ hs hκ).subset (by rintro _ ⟨n, rfl⟩; exact ⟨n + 1, rfl⟩)
  obtain ⟨p, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbdd (fun n => Set.mem_range_self n)
  have hLc : Continuous L := LinearMap.continuous_of_finiteDimensional L
  have hφt := hφ.tendsto_atTop
  have hx1 : Tendsto (fun k => run.x (φ k + 1)) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hlim
  have hy1 : Tendsto (fun k => run.y (φ k + 1)) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hlim
  have hdx := (run.tendsto_dx hM0 hM hτ hσ hs hκ).comp hφt
  have hdy := (run.tendsto_dy hM0 hM hτ hσ hs hκ).comp hφt
  have hx0 : Tendsto (fun k => run.x (φ k)) atTop (𝓝 p.1) := by
    have := hx1.sub hdx
    simp only [sub_zero] at this
    exact this.congr fun k => by simp
  have hy0 : Tendsto (fun k => run.y (φ k)) atTop (𝓝 p.2) := by
    have := hy1.sub hdy
    simp only [sub_zero] at this
    exact this.congr fun k => by simp
  have hd : Tendsto (fun k => dseq run.x (φ k)) atTop (𝓝 0) := by
    have : Tendsto (dseq run.x) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).1 (run.tendsto_dx hM0 hM hτ hσ hs hκ)
    exact this.comp hφt
  have hxm : p.1 ∈ C := hC.mem_of_tendsto hx1 (Eventually.of_forall fun k => run.x_mem _)
  have hym : p.2 ∈ D := hDc.mem_of_tendsto hy1 (Eventually.of_forall fun k => run.y_mem _)
  refine ⟨p.1, p.2, ⟨hxm, hym, fun y' hy' => ?_, fun x' hx' => ?_⟩, φ, hφ, hlim⟩
  · -- limit of the dual variational inequality
    have hl : Tendsto (fun k => ⟪run.y (φ k) - run.y (φ k + 1), y' - run.y (φ k + 1)⟫ / σ +
        ⟪L (run.x (φ k) + dseq run.x (φ k)), y' - run.y (φ k + 1)⟫) atTop
        (𝓝 (⟪p.2 - p.2, y' - p.2⟫ / σ + ⟪L (p.1 + 0), y' - p.2⟫)) :=
      (((hy0.sub hy1).inner (tendsto_const_nhds.sub hy1)).div_const σ).add
        (((hLc.tendsto _).comp (hx0.add hd)).inner (tendsto_const_nhds.sub hy1))
    have hr : Tendsto (fun k => Ff y' - Ff (run.y (φ k + 1))) atTop (𝓝 (Ff y' - Ff p.2)) :=
      tendsto_const_nhds.sub ((hF.tendsto _).comp hy1)
    have := le_of_tendsto_of_tendsto' hl hr fun k => run.prox_y (φ k) y' hy'
    simp only [sub_self, inner_zero_left, zero_div, zero_add, add_zero, inner_sub_right] at this
    simp only [Lag]
    linarith
  · -- limit of the primal variational inequality
    have hl : Tendsto (fun k => ⟪run.x (φ k) - run.x (φ k + 1), x' - run.x (φ k + 1)⟫ / τ -
        ⟪run.y (φ k + 1), L (x' - run.x (φ k + 1))⟫) atTop
        (𝓝 (⟪p.1 - p.1, x' - p.1⟫ / τ - ⟪p.2, L (x' - p.1)⟫)) :=
      (((hx0.sub hx1).inner (tendsto_const_nhds.sub hx1)).div_const τ).sub
        (hy1.inner ((hLc.tendsto _).comp (tendsto_const_nhds.sub hx1)))
    have hr : Tendsto (fun k => Gf x' - Gf (run.x (φ k + 1))) atTop (𝓝 (Gf x' - Gf p.1)) :=
      tendsto_const_nhds.sub ((hG.tendsto _).comp hx1)
    have := le_of_tendsto_of_tendsto' hl hr fun k => run.prox_x (φ k) x' hx'
    simp only [sub_self, inner_zero_left, zero_div, zero_sub, map_sub, inner_sub_right] at this
    simp only [Lag]
    have e1 := real_inner_comm (L x') p.2
    have e2 := real_inner_comm (L p.1) p.2
    linarith

/-- **Convergence** (Chambolle–Pock, Theorem 1(c)). The whole sequence `(x_n, y_n)` converges
to a saddle point of the Lagrangian. The energy `V_n` relative to the cluster saddle point of
`cluster_saddle` is nonincreasing and tends to `0` along a subsequence, hence tends to `0`. -/
theorem tendsto_saddle [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] (hκ : τ * σ * M < 1)
    (hC : IsClosed C) (hDc : IsClosed D) (hG : Continuous Gf) (hF : Continuous Ff) :
    ∃ xh yh, IsSaddle L Gf Ff C D xh yh ∧
      Tendsto (fun n => (run.x n, run.y n)) atTop (𝓝 (xh, yh)) := by
  obtain ⟨xh, yh, hsad, φ, hφ, hlim⟩ := run.cluster_saddle hM0 hM hτ hσ hs hκ hC hDc hG hF
  refine ⟨xh, yh, hsad, ?_⟩
  have hk := one_sub_kappa_pos hκ
  have hx1 : Tendsto (fun k => run.x (φ k + 1)) atTop (𝓝 xh) :=
    (continuous_fst.tendsto (xh, yh)).comp hlim
  have hy1 : Tendsto (fun k => run.y (φ k + 1)) atTop (𝓝 yh) :=
    (continuous_snd.tendsto (xh, yh)).comp hlim
  have hd : Tendsto (fun k => dseq run.x (φ k + 1)) atTop (𝓝 0) :=
    (run.tendsto_dx hM0 hM hτ hσ hs hκ).comp hφ.tendsto_atTop
  -- the upper bound of `V` tends to `0` along the subsequence
  have hU : Tendsto (fun k => ‖xh - run.x (φ k + 1)‖ ^ 2 / (2 * τ) +
      (1 + Real.sqrt (τ * σ * M)) * (‖yh - run.y (φ k + 1)‖ ^ 2 / (2 * σ)) +
      2 * Real.sqrt (τ * σ * M) * (‖dseq run.x (φ k + 1)‖ ^ 2 / (2 * τ))) atTop (𝓝 0) := by
    have a := ((tendsto_const_nhds (x := xh)).sub hx1).norm.pow 2 |>.div_const (2 * τ)
    have b := (((tendsto_const_nhds (x := yh)).sub hy1).norm.pow 2 |>.div_const (2 * σ)).const_mul
      (1 + Real.sqrt (τ * σ * M))
    have c := (hd.norm.pow 2 |>.div_const (2 * τ)).const_mul (2 * Real.sqrt (τ * σ * M))
    have := (a.add b).add c
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div, mul_zero, add_zero] at this
    exact this
  have hV0 : ∀ n, 0 ≤ run.V M xh yh n := fun n => by
    have h1 := run.V_lower hM0 hM hτ hσ n (xs := xh) (ys := yh)
    have h2 : 0 ≤ ‖xh - run.x n‖ ^ 2 / (2 * τ) := by positivity
    have h3 : 0 ≤ (1 - Real.sqrt (τ * σ * M)) * (‖yh - run.y n‖ ^ 2 / (2 * σ)) :=
      mul_nonneg hk.le (by positivity)
    linarith
  have hanti : Antitone fun n => run.V M xh yh n := antitone_nat_of_succ_le fun n => by
    have h1 := run.energy_step hM0 hM hτ hσ hsad n
    have h2 := mul_nonneg hk.le (run.step_nonneg hτ hσ n)
    linarith
  have hsub : Tendsto (fun k => run.V M xh yh (φ k + 1)) atTop (𝓝 0) :=
    squeeze_zero (fun k => hV0 _) (fun k => run.V_upper hM0 hM hτ hσ _) hU
  have hVlim : Tendsto (fun n => run.V M xh yh n) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n => ha.trans_le (hV0 n),
      fun a ha => ?_⟩
    obtain ⟨k, hk'⟩ := ((tendsto_order.1 hsub).2 a ha).exists
    filter_upwards [eventually_ge_atTop (φ k + 1)] with n hn
    exact (hanti hn).trans_lt hk'
  have hxn : Tendsto (fun n => ‖xh - run.x n‖ ^ 2 / (2 * τ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hVlim
    have h1 := run.V_lower hM0 hM hτ hσ n (xs := xh) (ys := yh)
    have h3 : 0 ≤ (1 - Real.sqrt (τ * σ * M)) * (‖yh - run.y n‖ ^ 2 / (2 * σ)) :=
      mul_nonneg hk.le (by positivity)
    linarith
  have hyn : Tendsto (fun n => ‖yh - run.y n‖ ^ 2 / (2 * σ)) atTop (𝓝 0) := by
    have hdiv := hVlim.div_const (1 - Real.sqrt (τ * σ * M))
    rw [zero_div] at hdiv
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hdiv
    have h1 := run.V_lower hM0 hM hτ hσ n (xs := xh) (ys := yh)
    have h2 : 0 ≤ ‖xh - run.x n‖ ^ 2 / (2 * τ) := by positivity
    rw [le_div_iff₀ hk]
    linarith
  have hx := tendsto_zero_of_sq_div (by positivity : (0 : ℝ) < 2 * τ) hxn
  have hy := tendsto_zero_of_sq_div (by positivity : (0 : ℝ) < 2 * σ) hyn
  have hx' : Tendsto run.x atTop (𝓝 xh) := by
    simpa using (tendsto_const_nhds (x := xh)).sub hx
  have hy' : Tendsto run.y atTop (𝓝 yh) := by
    simpa using (tendsto_const_nhds (x := yh)).sub hy
  exact hx'.prodMk_nhds hy'

/-- **Finite termination of a continuous stopping test.** If `Φ` is continuous and `Φ ≤ 0` at
every saddle point, then for every `ε > 0` some iterate satisfies `Φ(x_{n+1}, y_{n+1}) ≤ ε`. -/
theorem exists_le [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] (hκ : τ * σ * M < 1)
    (hC : IsClosed C) (hDc : IsClosed D) (hG : Continuous Gf) (hF : Continuous Ff)
    (Φ : X → Y → ℝ) (hΦc : Continuous fun p : X × Y => Φ p.1 p.2)
    (hΦ : ∀ xh yh, IsSaddle L Gf Ff C D xh yh → Φ xh yh ≤ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, Φ (run.x (n + 1)) (run.y (n + 1)) ≤ ε := by
  obtain ⟨xh, yh, hsad, φ, -, hlim⟩ := run.cluster_saddle hM0 hM hτ hσ hs hκ hC hDc hG hF
  have h := (hΦc.tendsto (xh, yh)).comp hlim
  have hlt : Φ xh yh < ε := (hΦ xh yh hsad).trans_lt hε
  obtain ⟨k, hk⟩ := ((tendsto_order.1 h).2 ε hlt).exists
  exact ⟨φ k, hk.le⟩

end Run

end ChambollePock
