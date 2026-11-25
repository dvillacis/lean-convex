# ConvexAnalysis

[![CI](https://github.com/dvillacis/lean-convex/actions/workflows/ci.yml/badge.svg)](https://github.com/dvillacis/lean-convex/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/dvillacis/lean-convex)](https://github.com/dvillacis/lean-convex/releases)
[![Documentation](https://img.shields.io/badge/docs-API-blue)](https://david.villacis.net/lean-convex/docs/)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue)](LICENSE)

A Lean 4 / Mathlib library of convex analysis and subdifferential calculus: convex functions,
subgradients, conjugates, proximal maps, optimality conditions and first-order algorithms. It
starts from a port of [OptLib](https://github.com/optsuite/optlib) to Mathlib v4.33.1 (see
[`NOTICE`](NOTICE) and [`PORTING.md`](PORTING.md)), and adds proofs that OptLib left open and
some new files.

- **Verified.** The library compiles against Mathlib v4.33.1 with no `sorry`, and no declaration
  depends on an axiom beyond `propext`, `Classical.choice`, `Quot.sound`. CI checks both on every
  change.
- **Faithful to OptLib.** All 790 declarations of the 36 ported OptLib files are kept under
  their original names, and all declarations of the 9 ported Reaslib files. The statement
  changes forced by Mathlib, and the two corrected statements, are listed in `PORTING.md`.
- **Complete.** The six proofs that upstream left as `sorry` are proved here.

[`VariationalAnalysis`](https://github.com/dvillacis/lean-variational) builds on this library.

## Example

Declarations are in the root namespace, as in OptLib:

```lean
import ConvexAnalysis

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A point minimizes `f` if and only if `0` is a subgradient of `f` there. -/
example (f : E → ℝ) (x : E) : IsMinOn f univ x ↔ 0 ∈ SubderivAt f x :=
  first_order_convex_iff_subgradient f x

/-- The subdifferential of the norm: `∂‖·‖(x) = {z | ‖z‖ ≤ 1, ⟪z, x⟫ = ‖x‖}`. -/
example (x : E) : SubderivAt (fun y ↦ ‖y‖) x = {z | ‖z‖ ≤ 1 ∧ ⟪z, x⟫_ℝ = ‖x‖} :=
  SubderivAt_norm x
```

## Selected results

| Result | Lean name |
|---|---|
| Minimizers of any `f`: `x` minimizes `f` iff `0 ∈ ∂f(x)` | [`first_order_convex_iff_subgradient`](https://david.villacis.net/lean-convex/docs/ConvexAnalysis/Convex/Subgradient.html#first_order_convex_iff_subgradient) |
| Sum rule `∂f₁(x) + ∂f₂(x) = ∂(f₁ + f₂)(x)` for convex functions | [`SubderivAt.add`](https://david.villacis.net/lean-convex/docs/ConvexAnalysis/Convex/Subgradient.html#SubderivAt.add) |
| Subdifferential of the norm at every point | [`SubderivAt_norm`](https://david.villacis.net/lean-convex/docs/ConvexAnalysis/Convex/NormSubgradient.html#SubderivAt_norm) |
| First-order characterization of convexity | [`Convex_first_order_condition_iff`](https://david.villacis.net/lean-convex/docs/ConvexAnalysis/Convex/ConvexFunction.html#Convex_first_order_condition_iff) |
| Optimality condition `∇f(x) = 0` for differentiable convex `f` | [`first_order_convex_iff`](https://david.villacis.net/lean-convex/docs/ConvexAnalysis/Optimality/OptimalityConditionOfUnconstrainedProblem.html#first_order_convex_iff) |
| Proximal point: `u = prox_f(x)` iff `x - u ∈ ∂f(u)` | [`prox_iff_subderiv`](https://david.villacis.net/lean-convex/docs/ConvexAnalysis/Function/Proximal.html#prox_iff_subderiv) |
| Farkas' lemma | [`Farkas`](https://david.villacis.net/lean-convex/docs/ConvexAnalysis/Convex/Farkas.html#Farkas) |
| Fenchel's inequality | [`fenchel_inequality`](https://david.villacis.net/lean-convex/docs/ConvexAnalysis/Extended/ConvexConjugate.html#fenchel_inequality) |
| Fenchel–Moreau: `f** = f` for closed convex `f` (Rockafellar, Thm. 12.2) | [`bi_convex_conjugate_eq_self`](https://david.villacis.net/lean-convex/docs/ConvexAnalysis/Extended/ConvexConjugate.html#bi_convex_conjugate_eq_self) |
| `f** = cl f` for convex `f` (Rockafellar, Thm. 12.2) | [`bi_convex_conjugate_eq_closure`](https://david.villacis.net/lean-convex/docs/ConvexAnalysis/Extended/ConvexConjugate.html#bi_convex_conjugate_eq_closure) |
| A proper convex function has an affine minorant (Rockafellar, Cor. 12.1.2) | [`exists_inner_minorant_of_proper_convex`](https://david.villacis.net/lean-convex/docs/ConvexAnalysis/Extended/AffineMinorantExistence.html#exists_inner_minorant_of_proper_convex) |
| `x ↦ ψ ‖x‖` is convex iff `ψ` is convex and nondecreasing on `[0, ∞)` | [`radial_convex_iff`](https://david.villacis.net/lean-convex/docs/ConvexAnalysis/Convex/Radial.html#radial_convex_iff) |

Rockafellar = R. T. Rockafellar, *Convex Analysis*, Princeton University Press, 1970.

## Installation

Add the library to the `lakefile.toml` of a project that uses the same Lean toolchain
(`leanprover/lean4:v4.33.1`):

```toml
[[require]]
name = "convexanalysis"
git = "https://github.com/dvillacis/lean-convex"
rev = "v0.1.2"
```

and run

```
lake update convexanalysis
lake exe cache get
lake build
```

At a tagged `rev`, Lake downloads the compiled library from the GitHub release instead of
compiling it (Linux x86_64 and macOS arm64; on other platforms it is compiled locally). Mathlib comes as a transitive dependency.

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

Files marked \* are not from OptLib. They were written for the formalization of a paper on
DC programming for TVq regularization, and moved here:

| File | Contents |
|---|---|
| `Convex/NormSubgradient` | `∂‖·‖(x) = {z : ‖z‖ ≤ 1, ⟪z, x⟫ = ‖x‖}` at every `x` (`mem_subdiff_norm_iff`, `hasSubgradientAt_norm_iff`, `SubderivAt_norm`); Fenchel–Young for `λ‖·‖` and `½‖· - f‖²` |
| `Convex/Radial` | `x ↦ ψ ‖x‖` is convex iff `ψ` is convex and nondecreasing on `[0, ∞)` (`radial_convex_iff`); convexity of `u ↦ β ∑ᵢ ψ ‖Kᵢ u‖`; derivative of `‖·‖` away from `0`; `C¹` regularity and gradient `∑ᵢ Kᵢ† wᵢ(u)` of `u ↦ β ∑ᵢ j ‖Kᵢ u‖` under `RadialC1 j j'` |
| `Optimality/FeasibleCone` | cone of feasible directions of a convex set; its closure contains the polar of the normal cone (`mem_closure_feasCone`) |
| `Function/Projection` | projection onto `{‖s‖ ≤ λ}` (`projBall`, `projBall_vi`) and onto `[0,1]ⁿ` (`UnitBox.clip`, `clip_vi`); support function of `[0,1]ⁿ` (`UnitBox.box_support`) |
| `Algorithm/ChambollePock` | PDHGM (`θ = 1`) for `min_x max_y ⟪Lx, y⟫ + G(x) - F(y)` over convex sets, `τσ‖L‖² < 1`: energy inequality, square-summable steps, bounded iterates, cluster points are saddle points |

## Development

```
lake exe cache get && lake build
```

Every pull request is checked by CI (`.github/workflows/ci.yml`), which runs

| Check | Command |
|---|---|
| Build, with no warnings from this package (including Mathlib's style linters) | `lake build` |
| The root file imports every module | `lake exe mk_all --check` (`lake exe mk_all` to fix) |
| The statements of the main results and the README example are unchanged | `lake test`, `python3 scripts/check_readme.py` |
| Every definition has a docstring | `lake env lean scripts/LintDocs.lean` |
| No axiom beyond `propext`, `Classical.choice`, `Quot.sound` | `lake env lean scripts/AuditAxioms.lean` |

Mathlib's standard set of style linters is enabled in `lakefile.toml`, except the two that
would require rewriting the ported proofs (`linter.flexible`, `linter.style.multiGoal`). The
ported theorems keep the names OptLib gave them, so Mathlib's naming conventions and the
environment linters of Batteries are not enforced, and theorems are not required to have a
docstring.

See [`CONTRIBUTING.md`](CONTRIBUTING.md) for how to propose a change.

## Versions and compatibility

- **Lean and Mathlib.** Each release is built against one Lean toolchain and one Mathlib version,
  listed in [`CHANGELOG.md`](CHANGELOG.md). A project that depends on this library must use the
  same toolchain, and gets Mathlib at the pinned version.
- **Version numbers.** While the version is `0.y.z`, a new `y` may rename declarations or change
  statements, and the changelog marks these changes as breaking. A new `z` only adds
  declarations or changes proofs and documentation.

To make a release: update `version` in `lakefile.toml`, `version` and `date-released` in
`CITATION.cff`, and `CHANGELOG.md`; merge; then push a tag `vX.Y.Z`.
`.github/workflows/release.yml` creates the GitHub release and attaches the compiled library.

## Citing

Use "Cite this repository" on GitHub, which reads [`CITATION.cff`](CITATION.cff). Since most of
the library is a port, please also cite [OptLib](https://github.com/optsuite/optlib).

## License

Apache 2.0; see [LICENSE](LICENSE). The ported files keep the copyright of the OptLib authors;
see [NOTICE](NOTICE).
