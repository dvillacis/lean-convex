# ConvexAnalysis

Convex analysis and subdifferential calculus for Lean 4 / Mathlib (v4.33.1),
starting from a port of the theory part of [OptLib](https://github.com/optsuite/optlib)
(see `NOTICE`).

## Contents

| Area | Files |
|---|---|
| Differential calculus helpers | `Differential/Calculation`, `Differential/Lemmas`, `Differential/GradientDiv` |
| Convex functions | `Convex/ConvexFunction`, `Convex/StronglyConvex`, `Convex/QuasiConvexFirstOrder`, `Convex/FiniteDimensionalConvexFunctionsLocallyLipschitz`, `Convex/Radial`\* |
| Subgradients | `Convex/Subgradient`, `Convex/BanachSubgradient`, `Convex/ImageSubgradientClosed`, `Convex/NormSubgradient`\* |
| Nonsmooth subdifferential | `Differential/Subdifferential` |
| Cones and Farkas | `Convex/ConicCaratheodory`, `Convex/ClosedCone`, `Convex/Farkas` |
| Functions | `Function/Lsmooth`, `Function/MinimaClosedFunction`, `Function/Proximal`, `Function/KL`, `Function/L1Space`, `Function/Projection`\* |
| Optimality | `Optimality/OptimalityConditionOfUnconstrainedProblem`, `Optimality/Constrained_Problem` (KKT), `Optimality/Weak_Duality`, `Optimality/FeasibleCone`\* |
| Extended-real convex analysis (Rockafellar ch. 1–13, Thm 23.5, 23.8, 23.9) | `Extended/EReal`, `Extended/ProperFunction`, `Extended/Epigraph`, `Extended/ConvexIndicator`, `Extended/IntrinsicInterior`, `Extended/ClosedFunction_Closure`, `Extended/AffineMinorant`, `Extended/AffineMinorantExistence`, `Extended/AffineMinorantHilbert`\*, `Extended/ConvexConjugate`, `Extended/ConvexSupport`†, `Extended/FenchelYoung`\*, `Extended/SubgradientCalculus`\* |
| Algorithms | `Algorithm/GD` (gradient descent, strongly convex case), `Algorithm/Nesterov` (accelerated methods), `Algorithm/SubgradientMethod`, `Algorithm/ProximalGradient`, `Algorithm/LASSO`, `Algorithm/BCD` (block coordinate descent with KL), `Algorithm/ADMM`, `Algorithm/ChambollePock`\* |

\* Not from OptLib; see *Additions* below. † Ported from Reaslib (OptLib's `Optlib-v4.24` branch); see *Extended-real functions* below.

Functions are real-valued, with domains given by sets, as in Mathlib's `ConvexOn s f`, except
in `Extended/`.

## Extended-real functions

The files in `Extended/` treat functions `f : E → EReal`, following Rockafellar's *Convex
Analysis*:

| File | Contents |
|---|---|
| `EReal` | arithmetic and `iSup`/`iInf` lemmas for `EReal` |
| `ProperFunction` | `ProperFunction s f` (never `⊥`, somewhere `< ⊤`), effective domain `dom s f`, sums and scalings of proper convex functions |
| `Epigraph` | `f.Epi s`; convex function ⟺ convex epigraph; closedness of the `EReal` and real epigraphs; epigraph of a pointwise sup |
| `ConvexIndicator` | the indicator `s.convex_indicator` (`0` on `s`, `⊤` off it): convex for convex `s`, lower semicontinuous for closed `s` |
| `IntrinsicInterior` | relative interior (Mathlib's `intrinsicInterior`) of products and of convex sets, line segments into the relative interior |
| `ClosedFunction_Closure` | lower semicontinuous hull and closure `f.closure s`; `epi (cl f) = closure (epi f)`; `cl f = liminf f`; lsc ⟺ closed epigraph |
| `AffineMinorant` | Thm 12.1: a closed proper convex function is the sup of its affine minorants |
| `AffineMinorantExistence` | Cor 12.1.2: a proper convex function has an affine minorant (`exists_inner_minorant_of_proper_convex`); a real convex function on a set with nonempty interior has an affine minorant (`ConvexOn.exists_affine_le`) |
| `AffineMinorantHilbert`\* | Thm 12.1 without finite dimension: a lower semicontinuous convex `f : E → EReal` on a Hilbert space is the supremum of its continuous affine minorants `⟪l, ·⟫ + w` (`lsc_convex_eq_iSup_inner_minorant`); the separation step holds in any normed space (`exists_affine_lt_of_notMem_epi`) |
| `ConvexConjugate` | conjugate `convex_conjugate s f`; Fenchel's inequality; `f*` is convex and lsc; `f*` is proper when `f` is proper and convex; Thm 12.2 (Fenchel–Moreau): `f** = cl f` for convex `f` (`bi_convex_conjugate_eq_closure`), `f** = f` for closed convex `f` on any Hilbert space (`bi_convex_conjugate_eq_self`; Bauschke–Combettes Thm 13.37); `f ↦ f*` is injective on closed proper convex functions, also on any Hilbert space; Cor 12.2.2: `f*` can be computed over `ri (dom f)`; Thm 12.3: conjugate of `x ↦ g (A (x - a)) + ⟪x, a'⟫ + α` |
| `ConvexSupport` | support function `s.convex_support`; `σ_C = σ_D ⟺ C = D` for closed convex sets; bounded `C` ⟺ finite `σ_C`; `cl f` of a convex `f` is convex; Thm 13.2: for a positively homogeneous convex `f ≠ ⊤`, `cl f = σ_C` with `C = {x | f* x ≤ 0}` |
| `FenchelYoung`\* | links the two halves of the library. For real-valued `f`, `g ∈ ∂f(x)` (`HasSubgradientAt`, `HasSubgradientWithinAt`) iff `f* g = ⟪x, g⟫ - f x` (`hasSubgradientAt_iff_conjugate_eq`); a subgradient `HasERealSubgradientAt` for `E → EReal` with the same characterization; Thm 23.5 reciprocity `g ∈ ∂f(x) ⟺ x ∈ ∂f*(g)` for convex `f` with `(cl f)(x) = f x` (`hasERealSubgradientAt_conjugate_iff_of_closure_eq`), for lsc convex `f` on a Hilbert space (`hasERealSubgradientAt_conjugate_iff`), for continuous convex `f : E → ℝ` on a Hilbert space and for convex `f : E → ℝ` in finite dimension |
| `SubgradientCalculus`\* | every rule is stated twice: on a Hilbert space for continuous convex functions (suffix `_of_continuous`, as in Clason–Valkonen Thm 4.14 and 4.17) and in finite dimension, where continuity is automatic. Sandwich theorem: an affine function between a convex `F` and a concave `G ≤ F` that touch at a point (`exists_affine_sandwich`). Constraint rule: for convex `f : E → ℝ` and convex `B ∋ x`, `s` is a subgradient of `f` relative to `B` at `x` iff `s ∈ ∂f(x) + N_B(x)` (`hasSubgradientWithinAt_iff_exists_normal`). Sum rule (Moreau–Rockafellar): `∂(f + g)(x) = ∂f(x) + ∂g(x)` for convex `f : E → ℝ` and convex `g : E → EReal` finite at `x` (`hasERealSubgradientAt_add_iff`). Chain rule: `∂(h ∘ A)(x) = A† ∂h(A x)` for convex `h : F → ℝ` and linear `A` (`hasSubgradientAt_comp_iff`). Finite sums: `∂(∑ᵢ φᵢ)(x) = ∑ᵢ ∂φᵢ(x)` (`hasSubgradientAt_finset_sum_iff`). Extended-real versions under an interior-point qualification: sandwich theorem for `F` convex on `C` and continuous at a point of `int C ∩ D` (`exists_affine_sandwich_of_continuousAt`); sum rule for convex `f, g : E → EReal` with `int (dom f) ∩ dom g ≠ ∅` (`hasERealSubgradientAt_add_iff_of_mem_interior`, and `_of_continuousAt` on a Hilbert space); chain rule for convex `h : F → EReal` with `A x₀ ∈ int (dom h)` (`hasERealSubgradientAt_comp_iff_of_mem_interior`, and `_of_continuousAt`). Relative-interior versions in finite dimension: sandwich theorem when `ri C ∩ ri D ≠ ∅` (`exists_affine_sandwich_of_mem_intrinsicInterior`); Rockafellar Thm 23.8, the sum rule when `ri (dom f) ∩ ri (dom g) ≠ ∅` (`hasERealSubgradientAt_add_iff_of_mem_intrinsicInterior`); Rockafellar Thm 23.9, the chain rule when the range of `A` meets `ri (dom h)` (`hasERealSubgradientAt_comp_iff_of_mem_intrinsicInterior`) |

Upstream left six proofs as `sorry`; all six are proved here. Two needed their statement
corrected: Thm 12.3 takes `α : ℝ` rather than `EReal`, and Cor 12.2.2 assumes finite
dimension. See `PORTING.md`.

## Additions

Files marked \* were moved here from the formalization of the DC–TVq paper
(`~/papers/TVQ/paper_DC_TVq/lean`), which now imports them from this library:

| File | Contents |
|---|---|
| `Convex/NormSubgradient` | `∂‖·‖(x) = {z : ‖z‖ ≤ 1, ⟪z, x⟫ = ‖x‖}` at every `x` (`mem_subdiff_norm_iff`, `hasSubgradientAt_norm_iff`, `SubderivAt_norm`); Fenchel–Young for `λ‖·‖` and `½‖· - f‖²`; `∂(λ‖·‖)(w) = λ ∂‖·‖(w)` for `λ ≥ 0` (`hasSubgradientAt_const_mul_norm_iff`); convexity and gradient `A†(Au - f)` of `½‖A · - f‖²` |
| `Convex/Radial` | `x ↦ ψ ‖x‖` is convex iff `ψ` is convex and nondecreasing on `[0, ∞)` (`radial_convex_iff`); convexity of `u ↦ β ∑ᵢ ψ ‖Kᵢ u‖`; derivative of `‖·‖` away from `0`; `C¹` regularity and gradient `∑ᵢ Kᵢ† wᵢ(u)` of `u ↦ β ∑ᵢ j ‖Kᵢ u‖` under `RadialC1 j j'` |
| `Optimality/FeasibleCone` | cone of feasible directions of a convex set; its closure contains the polar of the normal cone (`mem_closure_feasCone`). DCTVq no longer uses it: its optimality proof now goes through `Extended/SubgradientCalculus` |
| `Function/Projection` | projection onto `{‖s‖ ≤ λ}` (`projBall`, `projBall_vi`) and onto `[0,1]ⁿ` (`UnitBox.clip`, `clip_vi`); support function of `[0,1]ⁿ` (`UnitBox.box_support`) |
| `Algorithm/ChambollePock` | PDHGM (`θ = 1`) for `min_x max_y ⟪Lx, y⟫ + G(x) - F(y)` over convex sets, `τσ‖L‖² < 1`: energy inequality, square-summable steps, bounded iterates (`energy_bound`, Thm 1(a) of Chambolle–Pock), cluster points are saddle points, the ergodic rate `Lag(x̄_N, y) - Lag(x, ȳ_N) ≤ (‖x - x_0‖²/(2τ) + ‖y - y_0‖²/(2σ)) / N` for the averaged iterates (`ergodic_gap`, Thm 1(b)), and in finite dimension convergence of the whole sequence to a saddle point (`tendsto_saddle`, Thm 1(c)) |

## Build

```
lake exe cache get && lake build
```

## Status

All 36 ported OptLib files (theory and algorithms), the 9 ported Reaslib files and the 7
added files compile against Mathlib v4.33.1 with no `sorry`. All 790 original OptLib
declarations are kept; all Reaslib declarations of the ported files are kept, two with a corrected
statement (see `PORTING.md`). Run `lake env lean scripts/AuditAxioms.lean` to check that no declaration depends on an
axiom beyond `propext`, `Classical.choice`, `Quot.sound`. See `PORTING.md` for the per-file
log and the (forced) statement changes.
