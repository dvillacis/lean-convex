/-
Copyright (c) 2024 Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li
-/
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.Convex.Deriv
import ConvexAnalysis.Function.KL
import ConvexAnalysis.Function.Proximal
import ConvexAnalysis.Differential.Subdifferential
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Block Coordinate Descent

## Main results

This file mainly concentrates on the scheme of the block coordinate descent method.

- We give the definition of gradient on prod space.
- We define the problem type of BCD method and the update scheme of BCD method.
- We prove the Lipschitz continuity of the gradient of the coordinates.

-/

section diff

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {H : WithLp 2 (E × F) → ℝ}

lemma diff_from_l2 (h : Differentiable ℝ H) :
    Differentiable ℝ (fun p : E × F ↦ H (WithLp.toLp 2 p)) := by
  apply Differentiable.comp h
  apply IsBoundedLinearMap.differentiable
  exact instIsBoundedLinearMapL2equiv

theorem diff_prod₁ (h : Differentiable ℝ H) (y : F) :
    Differentiable ℝ (fun x ↦ H (WithLp.toLp 2 (x, y))) := by
  apply Differentiable.comp (diff_from_l2 h)
  exact Differentiable.prodMk differentiable_id (differentiable_const y)

theorem diff_prod₂ (h : Differentiable ℝ H) (x : E) :
    Differentiable ℝ (fun y ↦ H (WithLp.toLp 2 (x, y))) := by
  apply Differentiable.comp (diff_from_l2 h)
  exact Differentiable.prodMk (differentiable_const x) differentiable_id

end diff

noncomputable section prod_grad

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {H : WithLp 2 (E × F) → ℝ} {x : E} {y : F} {z : WithLp 2 (E × F)} {l : NNReal}

open Set Bornology Filter BigOperators Topology

/-- The partial gradient of `H` in the first variable: the gradient of `t ↦ H (t, y)`. -/
def grad_fst (H : WithLp 2 (E × F) → ℝ) (y : F) : E → E :=
  gradient (fun t ↦ H (WithLp.toLp 2 (t, y)))

/-- The map `(x, y) ↦ grad_fst H y x` on `E × F`. -/
def grad_fun_fst (H : WithLp 2 (E × F) → ℝ) := fun (x, y) ↦ (grad_fst H y x)

/-- The partial gradient of `H` in the second variable: the gradient of `t ↦ H (x, t)`. -/
def grad_snd (H : WithLp 2 (E × F) → ℝ) (x : E) : F → F :=
  gradient (fun t ↦ H (WithLp.toLp 2 (x, t)))

/-- The map `(x, y) ↦ grad_snd H x y` on `E × F`. -/
def grad_fun_snd (H : WithLp 2 (E × F) → ℝ) := fun (x, y) ↦ (grad_snd H x y)

/-- The vector `(grad_fst H z.snd z.fst, grad_snd H z.fst z.snd)` of the two partial gradients
of `H` at `z`, as an element of `WithLp 2 (E × F)`. -/
def grad_comp (H : WithLp 2 (E × F) → ℝ) (z : WithLp 2 (E × F)) : WithLp 2 (E × F) :=
    WithLp.toLp 2 (grad_fst H z.snd z.fst, grad_snd H z.fst z.snd)

/-- The map `z ↦ grad_comp H z`. -/
def grad_fun_comp (H : WithLp 2 (E × F) → ℝ) := fun z ↦ (grad_comp H z)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] in
private lemma toLp_fst_snd (z : WithLp 2 (E × F)) : WithLp.toLp 2 (z.fst, z.snd) = z := rfl

theorem grad_fst_eq (h : Differentiable ℝ H) (z : WithLp 2 (E × F)) :
    (gradient H z).fst = grad_fst H z.snd z.fst := by
  have h₁ : HasGradientAt (fun x ↦ H (WithLp.toLp 2 (x, z.snd)))
      (grad_fst H z.snd z.fst) z.fst := by
    apply DifferentiableAt.hasGradientAt
    apply diff_prod₁ h
  have h₂ : HasGradientAt (fun x ↦ H (WithLp.toLp 2 (x, z.snd))) (gradient H z).fst z.fst := by
    have h₃ : HasGradientAt H (gradient H z) z := DifferentiableAt.hasGradientAt (h z)
    rw [hasGradientAt_iff_isLittleO, Asymptotics.isLittleO_iff] at h₃ ⊢
    intro c hc
    have ht : Tendsto (fun t : E ↦ WithLp.toLp 2 (t, z.snd)) (𝓝 z.fst) (𝓝 z) := by
      have hc : Continuous (fun t : E ↦ WithLp.toLp 2 (t, z.snd)) := by fun_prop
      simpa [toLp_fst_snd] using hc.tendsto z.fst
    filter_upwards [ht.eventually (h₃ hc)] with t ht'
    have e : WithLp.toLp 2 (t, z.snd) - z = WithLp.toLp 2 (t - z.fst, (0 : F)) := by
      rw [← toLp_fst_snd z, ← WithLp.toLp_sub]; simp
    rw [e, norm_prod_right_zero, WithLp.prod_inner_apply] at ht'
    simpa [toLp_fst_snd] using ht'
  exact HasGradientAt.unique h₂ h₁

theorem grad_snd_eq (h : Differentiable ℝ H) (z : WithLp 2 (E × F)) :
    (gradient H z).snd = grad_snd H z.fst z.snd := by
  have h₁ : HasGradientAt (fun y ↦ H (WithLp.toLp 2 (z.fst, y)))
      (grad_snd H z.fst z.snd) z.snd := by
    apply DifferentiableAt.hasGradientAt
    apply diff_prod₂ h
  have h₂ : HasGradientAt (fun y ↦ H (WithLp.toLp 2 (z.fst, y))) (gradient H z).snd z.snd := by
    have h₃ : HasGradientAt H (gradient H z) z := DifferentiableAt.hasGradientAt (h z)
    rw [hasGradientAt_iff_isLittleO, Asymptotics.isLittleO_iff] at h₃ ⊢
    intro c hc
    have ht : Tendsto (fun t : F ↦ WithLp.toLp 2 (z.fst, t)) (𝓝 z.snd) (𝓝 z) := by
      have hc : Continuous (fun t : F ↦ WithLp.toLp 2 (z.fst, t)) := by fun_prop
      simpa [toLp_fst_snd] using hc.tendsto z.snd
    filter_upwards [ht.eventually (h₃ hc)] with t ht'
    have e : WithLp.toLp 2 (z.fst, t) - z = WithLp.toLp 2 ((0 : E), t - z.snd) := by
      rw [← toLp_fst_snd z, ← WithLp.toLp_sub]; simp
    rw [e, norm_prod_left_zero, WithLp.prod_inner_apply] at ht'
    simpa [toLp_fst_snd] using ht'
  exact HasGradientAt.unique h₂ h₁

theorem grad_eq_block_grad (h : Differentiable ℝ H) : gradient H = grad_fun_comp H := by
  ext z
  calc
    gradient H z = WithLp.toLp 2 ((gradient H z).fst, (gradient H z).snd) := rfl
    _ = WithLp.toLp 2 (grad_fst H z.snd z.fst, grad_snd H z.fst z.snd) := by
      rw [← grad_fst_eq h, ← grad_snd_eq h]
    _ = grad_fun_comp H z := rfl

theorem lip_grad_fst_of_lip (h : Differentiable ℝ H) (hl : LipschitzWith l (gradient H)) :
    LipschitzWith l (fun (z : WithLp 2 (E × F)) ↦ grad_fst H z.snd z.fst) := by
  rw [lipschitzWith_iff_norm_sub_le] at *
  intro z z'
  calc
    _ = ‖(gradient H z).fst - (gradient H z').fst‖ := by rw [grad_fst_eq h, grad_fst_eq h]
    _ = ‖(gradient H z - gradient H z').fst‖ := rfl
    _ ≤ ‖(gradient H z - gradient H z')‖ := fst_norm_le_prod_L2 _
    _ ≤ _ := hl z z'

theorem lip_grad_snd_of_lip (h : Differentiable ℝ H) (hl : LipschitzWith l (gradient H)) :
    LipschitzWith l (fun (z : WithLp 2 (E × F)) ↦ grad_snd H z.fst z.snd) := by
  rw [lipschitzWith_iff_norm_sub_le] at *
  intro z z'
  calc
    _ = ‖(gradient H z).snd - (gradient H z').snd‖ := by rw [grad_snd_eq h, grad_snd_eq h]
    _ = ‖(gradient H z - gradient H z').snd‖ := rfl
    _ ≤ ‖(gradient H z - gradient H z')‖ := snd_norm_le_prod_L2 _
    _ ≤ _ := hl z z'

end prod_grad

noncomputable section algorithm

open Set Bornology Filter BigOperators Topology

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [ProperSpace F]
variable {f : E → ℝ} {g : F → ℝ}
variable {H : (WithLp 2 (E × F)) → ℝ} {x0 : E} {y0 : F} {l : NNReal}

instance Proper_Prod : ProperSpace (WithLp 2 (E × F)) where
  isCompact_closedBall := by
    intro z r
    obtain h := IsCompact.prod (isCompact_closedBall z.fst r) (isCompact_closedBall z.snd r)
    have {a b : ℝ} : a ≤ √(a ^ 2 + b ^ 2) := by apply Real.le_sqrt_of_sq_le; linarith [sq_nonneg b]
    have hsub : Metric.closedBall z r
        ⊆ WithLp.toLp 2 '' (Metric.closedBall z.fst r ×ˢ Metric.closedBall z.snd r) := by
      intro w hball
      refine ⟨WithLp.ofLp w, ?_, WithLp.toLp_ofLp 2 w⟩
      rw [mem_prod]
      simp only [mem_closedBall_iff_norm, WithLp.prod_norm_eq_of_L2, WithLp.sub_fst,
        WithLp.sub_snd, WithLp.ofLp_fst, WithLp.ofLp_snd] at *
      constructor
      · exact le_trans this hball
      · exact le_trans this ((add_comm (‖w.fst - z.fst‖ ^ 2) _) ▸ hball)
    have hc : Continuous (WithLp.toLp 2 : E × F → WithLp 2 (E × F)) := by fun_prop
    exact IsCompact.of_isClosed_subset (h.image hc) Metric.isClosed_closedBall hsub

/--
Assumption: f and g are lower semicontinuous, H is continuously differentiable
∇ H is l- Lipschitz continuous, f and g are lower bounded
-/
class ProblemData (f : E → ℝ) (g : F → ℝ) (H : (WithLp 2 (E × F)) → ℝ) (l : NNReal) : Prop where
  lbdf : BddBelow (f '' univ)
  lbdg : BddBelow (g '' univ)
  hf : LowerSemicontinuous f
  hg : LowerSemicontinuous g
  conf : ContDiff ℝ 1 H
  lpos : l > (0 : ℝ)
  lip : LipschitzWith l (gradient H)

/--
The definition of block coordinate descent
-/
structure BCD (f : E → ℝ) (g : F → ℝ) (H : (WithLp 2 (E × F)) → ℝ) (l : NNReal)
    (x0 : E) (y0 : F) extends ProblemData f g H l where
  /-- The sequence of iterates in the first block. -/
  x : ℕ → E
  /-- The sequence of iterates in the second block. -/
  y : ℕ → F
  x0 : x 0 = x0
  y0 : y 0 = y0
  /-- The step sizes of the proximal step in the first block. -/
  c : ℕ → ℝ
  /-- The step sizes of the proximal step in the second block. -/
  d : ℕ → ℝ
  s₁ : ∀ k, prox_prop (c k • f) (x k - c k • (grad_fst H (y k) (x k))) (x (k + 1))
  s₂ : ∀ k, prox_prop (d k • g) (y k - d k • (grad_snd H (x (k + 1)) (y k))) (y (k + 1))

open BCD

/-- The sequence of iterates `z n = (x n, y n)` of the algorithm in `WithLp 2 (E × F)`. -/
def BCD.z {self : BCD f g H l x0 y0} : ℕ → WithLp 2 (E × F) :=
  fun n ↦ WithLp.toLp 2 (self.x n, self.y n)

/-- The objective function `ψ z = f z.fst + g z.snd + H z` of the algorithm. -/
def BCD.ψ {_ : BCD f g H l x0 y0} := fun z : WithLp 2 (E × F) ↦ f z.fst + g z.snd + H z

variable {alg : BCD f g H l x0 y0}

omit [ProperSpace E] [ProperSpace F] in
lemma BCD.Hdiff {self : BCD f g H l x0 y0} : Differentiable ℝ H :=
    self.conf.differentiable one_ne_zero

omit [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]
  [InnerProductSpace ℝ F] [CompleteSpace F] [ProperSpace F] in
lemma comp_norm_le (x : E) (y : F) : (‖x‖ ≤ ‖(x,y)‖) ∧ (‖y‖ ≤ ‖(x,y)‖) :=
  ⟨le_max_left ‖x‖ ‖y‖, le_max_right ‖x‖ ‖y‖⟩

omit [ProperSpace E] [ProperSpace F] in
lemma BCD.cpos (γ : ℝ) (hγ : γ > 1) (ck : ∀ k, alg.c k = 1 / (γ * l)) : ∀ k, 0 < (alg.c k) := by
  intro k
  specialize ck k; rw [ck]
  apply div_pos; norm_num
  apply mul_pos; linarith[hγ]; apply alg.lpos

omit [ProperSpace E] [ProperSpace F] in
lemma BCD.dpos (γ : ℝ) (hγ : γ > 1) (dk : ∀ k, alg.d k = 1 / (γ * l)) : ∀ k, 0 < (alg.d k) := by
  intro k
  specialize dk k; rw [dk]
  apply div_pos; norm_num
  apply mul_pos; linarith[hγ]; apply alg.lpos

omit [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]
  [InnerProductSpace ℝ F] [CompleteSpace F] [ProperSpace F] in
private lemma sub_prod (x x1 : E) (y y1 : F) :
    WithLp.toLp 2 (x, y) - WithLp.toLp 2 (x1, y1) = WithLp.toLp 2 (x - x1, y - y1) := rfl

/-- The vector `A_kx k = (c k)⁻¹ • (x k - x (k + 1)) - grad_fst H (y k) (x k)`. -/
def BCD.A_kx k := (alg.c k)⁻¹ • (alg.x k - alg.x (k + 1)) - (grad_fst H (alg.y k) (alg.x k))

/-- The vector `A_ky k = (d k)⁻¹ • (y k - y (k + 1)) - grad_snd H (x (k + 1)) (y k)`. -/
def BCD.A_ky k := (alg.d k)⁻¹ • (alg.y k - alg.y (k + 1)) - (grad_snd H (alg.x (k + 1)) (alg.y k))

/-- The vector `A_k k = (A_kx k, A_ky k)` in `WithLp 2 (E × F)`. -/
def BCD.A_k (k : ℕ) : WithLp 2 (E × F) := WithLp.toLp 2 (alg.A_kx k, alg.A_ky k)

/-- The vector `A_k k + ∇ H (x (k + 1), y (k + 1))`. -/
def BCD.subdiff k := alg.A_k k + gradient H (WithLp.toLp 2 (alg.x (k + 1), alg.y (k + 1)))

end algorithm

section Assumption

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {f : E → ℝ} {g : F → ℝ}
variable {H : (WithLp 2 (E × F)) → ℝ} {x0 : E} {y0 : F} {l : NNReal}

theorem BCD.lip₁ {self : BCD f g H l x0 y0} : LipschitzWith l (grad_fun_comp H) := by
  obtain lip := self.lip
  rwa [grad_eq_block_grad self.Hdiff] at lip

/- coordinate Lipschitz continuous -/
theorem BCD.coordinate_lip {self : BCD f g H l x0 y0} : (∀ y, LipschitzWith l (grad_fst H y))
    ∧ (∀ x, LipschitzWith l (grad_snd H x)) := by
  have h : LipschitzWith l (grad_fun_comp H) := self.lip₁
  rw [lipschitzWith_iff_norm_sub_le] at h
  constructor
  · intro y
    rw [lipschitzWith_iff_norm_sub_le]
    intro x1 x2
    have h' := h (WithLp.toLp 2 (x1, y)) (WithLp.toLp 2 (x2, y))
    have e : grad_fun_comp H (WithLp.toLp 2 (x1, y)) - grad_fun_comp H (WithLp.toLp 2 (x2, y))
        = WithLp.toLp 2 (grad_fst H y x1 - grad_fst H y x2, grad_snd H x1 y - grad_snd H x2 y) :=
      rfl
    rw [e, sub_prod, sub_self, norm_prod_right_zero] at h'
    have := fst_norm_le_prod_L2
      (WithLp.toLp 2 (grad_fst H y x1 - grad_fst H y x2, grad_snd H x1 y - grad_snd H x2 y))
    simp only [WithLp.toLp_fst] at this
    exact le_trans this h'
  intro x
  rw [lipschitzWith_iff_norm_sub_le]
  intro y1 y2
  have h' := h (WithLp.toLp 2 (x, y1)) (WithLp.toLp 2 (x, y2))
  have e : grad_fun_comp H (WithLp.toLp 2 (x, y1)) - grad_fun_comp H (WithLp.toLp 2 (x, y2))
      = WithLp.toLp 2 (grad_fst H y1 x - grad_fst H y2 x, grad_snd H x y1 - grad_snd H x y2) :=
    rfl
  rw [e, sub_prod, sub_self, norm_prod_left_zero] at h'
  have := snd_norm_le_prod_L2
    (WithLp.toLp 2 (grad_fst H y1 x - grad_fst H y2 x, grad_snd H x y1 - grad_snd H x y2))
  simp only [WithLp.toLp_snd] at this
  exact le_trans this h'

end Assumption
