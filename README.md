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
| Algorithms | `Algorithm/GD` (gradient descent, strongly convex case), `Algorithm/Nesterov` (accelerated methods), `Algorithm/SubgradientMethod`, `Algorithm/ProximalGradient`, `Algorithm/LASSO`, `Algorithm/BCD` (block coordinate descent with KL), `Algorithm/ADMM`, `Algorithm/ChambollePock`\* |

\* Not from OptLib; see *Additions* below.

Functions are real-valued, with domains given by sets, as in Mathlib's `ConvexOn s f`.

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

All 36 ported files (theory and algorithms) and the 5 added files compile against Mathlib
v4.33.1 with no `sorry`; all 790 original declarations are kept. Run `lake env lean scripts/AuditAxioms.lean` to check that no declaration depends on an
axiom beyond `propext`, `Classical.choice`, `Quot.sound`. See `PORTING.md` for the per-file
log and the (forced) statement changes.
