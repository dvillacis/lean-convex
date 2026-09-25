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
| Extended-real convex analysis (Rockafellar ch. 1–12) | `Extended/EReal`, `Extended/ProperFunction`, `Extended/Epigraph`, `Extended/ConvexIndicator`, `Extended/IntrinsicInterior`, `Extended/ClosedFunction_Closure`, `Extended/AffineMinorant`, `Extended/AffineMinorantExistence`, `Extended/ConvexConjugate`, `Extended/ConvexSupport`† |
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
| `ConvexConjugate` | conjugate `convex_conjugate s f`; Fenchel's inequality; `f*` is convex and lsc; `f*` is proper when `f` is proper and convex; Thm 12.2 (Fenchel–Moreau): `f** = cl f` for convex `f` (`bi_convex_conjugate_eq_closure`), `f** = f` for closed convex `f` (`bi_convex_conjugate_eq_self`); `f ↦ f*` is injective on closed proper convex functions; Cor 12.2.2: `f*` can be computed over `ri (dom f)`; Thm 12.3: conjugate of `x ↦ g (A (x - a)) + ⟪x, a'⟫ + α` |
| `ConvexSupport` | support function `s.convex_support`; `σ_C = σ_D ⟺ C = D` for closed convex sets; bounded `C` ⟺ finite `σ_C`; `cl f` of a convex `f` is convex; Thm 13.2: for a positively homogeneous convex `f ≠ ⊤`, `cl f = σ_C` with `C = {x | f* x ≤ 0}` |

Upstream left six proofs as `sorry`; all six are proved here. Two needed their statement
corrected: Thm 12.3 takes `α : ℝ` rather than `EReal`, and Cor 12.2.2 assumes finite
dimension. See `PORTING.md`.

## Additions

Files marked \* were moved here from the formalization of the DC–TVq paper
(`~/papers/TVQ/paper_DC_TVq/lean`), which now imports them from this library:

| File | Contents |
|---|---|
| `Convex/NormSubgradient` | `∂‖·‖(x) = {z : ‖z‖ ≤ 1, ⟪z, x⟫ = ‖x‖}` at every `x` (`mem_subdiff_norm_iff`, `hasSubgradientAt_norm_iff`, `SubderivAt_norm`); Fenchel–Young for `λ‖·‖` and `½‖· - f‖²` |
| `Convex/Radial` | `x ↦ ψ ‖x‖` is convex iff `ψ` is convex and nondecreasing on `[0, ∞)` (`radial_convex_iff`); convexity of `u ↦ β ∑ᵢ ψ ‖Kᵢ u‖`; derivative of `‖·‖` away from `0`; `C¹` regularity and gradient `∑ᵢ Kᵢ† wᵢ(u)` of `u ↦ β ∑ᵢ j ‖Kᵢ u‖` under `RadialC1 j j'` |
| `Optimality/FeasibleCone` | cone of feasible directions of a convex set; its closure contains the polar of the normal cone (`mem_closure_feasCone`) |
| `Function/Projection` | projection onto `{‖s‖ ≤ λ}` (`projBall`, `projBall_vi`) and onto `[0,1]ⁿ` (`UnitBox.clip`, `clip_vi`); support function of `[0,1]ⁿ` (`UnitBox.box_support`) |
| `Algorithm/ChambollePock` | PDHGM (`θ = 1`) for `min_x max_y ⟪Lx, y⟫ + G(x) - F(y)` over convex sets, `τσ‖L‖² < 1`: energy inequality, square-summable steps, bounded iterates, cluster points are saddle points |

## Build

```
lake exe cache get && lake build
```

## Status

All 36 ported OptLib files (theory and algorithms), the 9 ported Reaslib files and the 6
added files compile against Mathlib v4.33.1 with no `sorry`. All 790 original OptLib
declarations are kept; all Reaslib declarations of the ported files are kept, two with a corrected
statement (see `PORTING.md`). Run `lake env lean scripts/AuditAxioms.lean` to check that no declaration depends on an
axiom beyond `propext`, `Classical.choice`, `Quot.sound`. See `PORTING.md` for the per-file
log and the (forced) statement changes.
