# Porting log (OptLib, Mathlib v4.13.0 → v4.33.1)

Legend: ✓ ported (compiles, no `sorry`), statement changes listed per file.

| File | Status | Errors fixed | Statement changes | Notes |
|---|---|---|---|---|
| Differential/Calculation | ✓ | 9 | none (only `∑ i in` → `∑ i ∈`) | `HasFDerivAtFilter` now uses `L ×ˢ pure x`; `fun_sum`, `fderiv_fun_neg` |
| Convex/ConicCaratheodory | ✓ | 2 (+1 deprecation) | none | `field_simp` behaviour; one extra `Nonempty` goal |
| Function/MinimaClosedFunction | ✓ | 7 causes | `LinearOrderedRing 𝕜` → `[Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]` (class removed from Mathlib; same meaning) | import `Topology.Semicontinuity.Basic`; renames `prodMk_nhds`, `not_le_of_gt`, `sInf_le_sInf_of_isCoinitialFor` |
| Convex/BanachSubgradient | ✓ | 9 | none | imports `LocallyConvex.Separation`, `LinearAlgebra.Dual.Lemmas`; `ContinuousOn.prodMk` |
| Convex/ClosedCone | ✓ | 5 | none | `EuclideanSpace` is a structure: `F` goes through `WithLp.linearEquiv`; `Topology.IsClosedEmbedding` |
| Function/L1Space | ✓ | ~24 (5 causes) | definition `f`: body wrapped in `WithLp.toLp 1` (PiLp is a structure; same meaning) | `Basis` → `Module.Basis`; `Fin.val_castSucc`; `match` no longer reduces on variables |
| Convex/Farkas | ✓ | ~35 | `Farkas`: `inner x y` → `inner ℝ x y` (Mathlib's `inner` now takes the field explicitly; same meaning) | imports `LinearAlgebra.Matrix.Rank`, `LinearAlgebra.FiniteDimensional.Basic`; `push Not` gives `.Nonempty` |
| Differential/Lemmas | ✓ | ~25 (15 causes) | `inner a b` → `inner ℝ a b`; ProdL2 lemmas use `z.fst`/`z.snd` and `WithLp.toLp 2 (x, 0)` (WithLp is a structure); `instIsBoundedLinearMapL2equiv` is now a `theorem` about `WithLp.toLp 2` (IsBoundedLinearMap is no longer a class) | `LowerSemicontinuousWithinAt` is an abbrev; `hasFDerivAt_iff_isLittleO`; `norm_pos_iff`, `div_le_div_iff_of_pos_right` |
| Convex/FiniteDimensionalConvexFunctionsLocallyLipschitz | ✓ | 8 | none | `LipschitzOnWith.of_dist_le_mul`; `norm_pos_iff'` now multiplicative; `mul_le_mul_left` no longer an iff; `Module.Basis` |
| Convex/ConvexFunction | ✓ | 39 | `inner a b` → `inner ℝ a b` in the first-order and monotone-gradient theorems (same meaning) | `toDual_apply_apply`; `_root_.sub_apply`; `mul_le_mul_of_nonneg_right` |
| Convex/QuasiConvexFirstOrder | ✓ | 2 | none | `Real.mul_pos` removed → `mul_pos` |
| Differential/GradientDiv | ✓ | ~32 | none | `div_le_div_iff₀`; `div_add_div_same` → `(add_div _ _ _).symm` |
| Optimality/OptimalityConditionOfUnconstrainedProblem | ✓ | 9 | `DescentDirection`: `inner ℝ` (same meaning) | `simp` turns `ContinuousOn g univ` into `Continuous g` |
| Convex/Subgradient | ✓ | 57 | none (defs already used `⟪x, y⟫` notation) | `hasFDerivAt_iff_tendsto`; `mul_lt_mul_of_pos_right`; `Set.nonempty_iff_ne_empty`; on ℝ `inner ℝ a b = b * a` |
| Function/Lsmooth | ✓ | ~25 | `inner ℝ` in 6 theorems (same meaning) | `field_simp` stronger; `add_le_add_right` argument order |
| Convex/StronglyConvex | ✓ | 9 | `inner ℝ` in 4 theorems (same meaning) | uses Mathlib's `StrongConvexOn`; `module` tactic |
| Optimality/Constrained_Problem | ✓ | ~47 | `inner ℝ` in `IsLinear*`, `LinearCQ_linear_constraint_*`; `LICQ_Axfullrank`, `LICQ_existZ`, `LICQ_strictfderiv_Ax_elem`: gradients enter the matrix via `WithLp.ofLp`; `mulVec_eq_toEuclidean` with `.ofLp`; `LICQ_implicit_f`: `Mx.range = ⊤`; `structure … where` syntax. New helper lemma `mem_posTangentConeAt_of_seq'` | `posTangentConeAt` is now `tangentConeAt NNReal` (irreducible); `IsLocalMinOn.hasFDerivWithinAt_nonneg` |
| Function/Proximal | ✓ | ~30 | `proximal_add_linear`: `inner ℝ` (same meaning) | `continuousOn_univ`; `pow_le_pow_left₀`; `fun_prop` for continuity |
| Optimality/Weak_Duality | ✓ | 6 | helper `ConcaveOn.sum`: `OrderedSemiring 𝕜` → `[Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]` (class removed; same meaning) | `DifferentiableAt.fun_sum` |
| Convex/ImageSubgradientClosed | ✓ | 2 causes (7 messages) | none | import `Topology.Instances.EReal.Lemmas`; a def's continuation line needed indentation |
| Differential/Subdifferential | ✓ | 17 | `differential_fun` body and `has_f_subdiff_iff`: `inner ℝ` (same meaning) | import `Data.EReal.Basic`; `lt_iff_not_ge`; `mul_le_mul_iff_right₀` |
| Function/KL | ✓ | 17 | none in meaning (`EMetric.infEdist` → `Metric.infEDist`, same function) | `deriv_fun_sum`; `tendsto_finsetSum`; `Finset.tsum_subtype`; the commented-out `uniformly_KL_property'` block of the original is kept as a comment |

## Summary

- 36 of 36 files ported (22 theory + 14 algorithm files, ~16,600 lines); `lake build`
  succeeds with no errors.
- All 790 declarations of the original files are present under their original names
  (checked by comparing declaration lists with the OptLib sources).
- `lake env lean scripts/AuditAxioms.lean`: 1264 declarations checked (including generated
  ones), none depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound`.
- Statement changes are all forced by Mathlib and keep the mathematical meaning:
  explicit `inner ℝ`; `WithLp`/`PiLp`/`EuclideanSpace` being structures (`toLp`, `ofLp`,
  `.fst`, `.snd`); removed bundled order classes (`LinearOrderedRing`, `OrderedSemiring`);
  `IsBoundedLinearMap` no longer a class; `Mx.range` for continuous linear maps.
- Helper lemmas added: `mem_posTangentConeAt_of_seq'` (Constrained_Problem, because Mathlib
  redefined `posTangentConeAt` via `tangentConeAt`), private `toLp_fst_snd` (BCD/Scheme) and
  private `LASSO_L_pos` (LASSO).

## Algorithm files

| File | Status | Errors fixed | Statement changes | Notes |
|---|---|---|---|---|
| Algorithm/ProximalGradient | ✓ | ~21 | none (`class … where` syntax) | |
| Algorithm/GD/GradientDescent | ✓ | 19 | `convex_function`: `inner ℝ` (same meaning) | `induction'` removed → structured `induction`/`cases` |
| Algorithm/Nesterov/NesterovSmooth | ✓ | ~36 | none | `PNat.caseStrongInductionOn` with structured cases |
| Algorithm/Nesterov/NesterovAccelerationFirst | ✓ | 17 | none | `add_le_add_left`/`_right` swapped meanings; `mul_le_mul_iff_right₀` |
| Algorithm/Nesterov/NesterovAccelerationSecond | ✓ | 17 | none | `contrapose!`; instance needs field `z` explicitly |
| Algorithm/ADMM/Scheme | ✓ | ~11 | `Augmented_Lagrangian_Function`: `inner ℝ` (same meaning) | column-0 continuation lines in `variable` blocks |
| Algorithm/ADMM/Inv_bounded | ✓ | ~5 | `KerA_bot`, `KerA_eq_KerA'A`, `KerA'A_bot`: `ker A` → `A.ker` (no `ker` on continuous linear maps; same submodule) | |
| Algorithm/SubgradientMethod | ✓ | ~41 | none | `mul_lt_mul_iff_right₀`; `div_lt_div_iff_of_pos_right`; `pow_le_pow_left₀`; simp `∃ i < k+1` → `∃ i ≤ k` |
| Algorithm/BCD/Scheme | ✓ | 53 | `WithLp 2 (E × F)` is a structure: `diff_from_l2` states differentiability of `p ↦ H (WithLp.toLp 2 p)`; `diff_prod₁/₂`, `grad_fst/snd`, `BCD.subdiff`, `BCD.A_k`, `BCD.z` pass pairs as `WithLp.toLp 2 (x, y)`; `.1/.2` → `.fst/.snd` (same meaning). New private helper `toLp_fst_snd` | `Differentiable.prodMk`; `ContDiff.differentiable (hn : n ≠ 0)` |
| Algorithm/GD/GradientDescentStronglyConvex | ✓ | 7 (then proofs rewritten) | `inner ℝ` only (same meaning) | proofs of all three results rewritten |
| Algorithm/ADMM/Lemma | ✓ | 93 reported (19 real) | `inner ℝ` in `M` and ~15 lemma statements (same meaning) | `HasFDerivAt.add_const c`; `pow_le_one₀`; `one_lt_pow₀`; `inv_strictAnti₀`; `real_inner_self_eq_norm_sq` |
| Algorithm/LASSO | ✓ | ~20 | `EuclideanSpace` is a structure: `‖x‖₂` notation, the gradient lemmas and the `LASSO` fields `f'eq`, `update2` wrap vectors with `WithLp.toLp 2`; `real_inner_eq_dot`: `inner ℝ` (same meaning). New private helper `LASSO_L_pos` | `Matrix.l2_opNorm_mulVec` |
| Algorithm/ADMM/Theroem_converge | ✓ | 15 | none (only indentation of continuation lines) | `dist_eq_norm`; `Summable.of_nonneg_of_le` |
| Algorithm/BCD/Convergence | ✓ | 89 | `f_subdiff_block` with `WithLp.toLp 2 (u, v)` and `z.fst`/`z.snd`; `fconv`/`gconv`: `.fst`/`.snd`; `infEdist_bound`, `limitset_property_2`: `Metric.infEDist` (same function); `∑ k in` → `∑ k ∈` (same meaning) | `MapClusterPt.of_comp`; `not_bddBelow_of_tendsto_atBot`; `tendsto_atTop_of_antitone` |

# Porting log (Reaslib, OptLib branch `Optlib-v4.24` → Mathlib v4.33.1)

Source: commit `1ab89cf2c1c46bee690b7a13f0fdf697a491ba38` of the `Optlib-v4.24` branch
(Lean `v4.24.0-rc1`, Mathlib `v4.24.0`). Files are under `ConvexAnalysis/Extended/` with their
upstream names; `Reaslib.Basic.*` and `Reaslib.ConvexAnalysis.*` imports became
`ConvexAnalysis.Extended.*`.

Changes common to all files, not listed per file:

- **Auto-bound implicits.** The upstream lakefile allows them; ours sets `autoImplicit = false`.
  The missing binders (`{E : Type*}`, `{x : E}`, `universe u`, …) were added explicitly in the
  position Lean would have given them, so the elaborated statements are unchanged.
- **Instances that can never fire.** Current Lean rejects an `instance` with an argument that
  instance search cannot fill (e.g. `hs : s.Nonempty`), with no option to turn the check off.
  Such declarations became `theorem`s with the same name and statement (listed per file).
  Anonymous ones now carry their auto-generated name.
- **Renamed Mathlib modules.** `Topology.Semicontinuous` → `Topology.Semicontinuity.Basic`;
  `Analysis.NormedSpace.HahnBanach.Separation` → `Analysis.LocallyConvex.Separation`.

| File | Status | Errors fixed | Statement changes | Notes |
|---|---|---|---|---|
| Basic/EReal → Extended/EReal | ✓ | 4 | none | `add_le_add_left` argument order; `CompleteSemilatticeInf.sInf_le` removed |
| Basic/ProperFunction → Extended/ProperFunction | ✓ | 9 | instance → theorem: `ProperFun_of_subset`, `ProperFunction.add`, `ProperFunction.sum`, `ProperFunction.congr`, and the two anonymous instances, now `instProperFunctionHSMulRealForallERealOfGeOfNat` (`m • f` proper) and `instProperFunctionOfForallMemSetAndLtERealBotTop` | simp now collapses `Fin 1` intersections and leaves `Finset.image` sums |
| ConvexAnalysis/Epigraph → Extended/Epigraph | ✓ | 1 | none | a `simp` that no longer makes progress |
| ConvexAnalysis/ConvexIndicator → Extended/ConvexIndicator | ✓ | 2 | instance → theorem: `ConvexIndicator_is_proper_on_univ` | `LowerSemicontinuous` is an abbrev of `Semicontinuous` (cannot be unfolded) |
| ConvexAnalysis/IntrinsicInterior → Extended/IntrinsicInterior | ✓ | ~140 (37 under `lake env lean`, the rest under `lake build`) | `D_eq_projection`: `… '' C` → `… '' (WithLp.toLp 2 '' C)` (`WithLp` is a structure). Rename: `inv_eq_self` → `inv_eq_self'` (clashes with Mathlib's root `inv_eq_self`, a different statement) | `AffineSubspace.smul_vsub_vadd_mem` → `smul_vsub_vadd_mem'`; `WithLp.fst`, `WithLp.continuous_fst`; changed simp normal forms (`Fin.forall_fin_two`, product pairs) |
| ConvexAnalysis/ClosedFunction_Closure → Extended/ClosedFunction_Closure | ✓ | not counted | Rename: `lowerSemicontinuousOn_iff` → `lowerSemicontinuousOn_iff'` (clashes with Mathlib's `lowerSemicontinuousOn_iff`, a different statement) | `lowerSemicontinuousWithinAt_iff`, `lowerSemicontinuousAt_iff` in place of unfolding; `Set.restrict_eq` deprecated |
| ConvexAnalysis/AffineMinorant → Extended/AffineMinorant | ✓ | not counted | instance → theorem: `Nonempempty_of_empty`, `Nonempty_affine_minorant`, `empty_affine_minorant` | |
| ConvexAnalysis/ConvexConjugate → Extended/ConvexConjugate | ✓ (four upstream `sorry`s proved, see below) | not counted | instance → theorem: `proper_convex_proper_conjugate` (commented out), `univ_convex_closure_proper'` (commented out) | import of `ClosedFunction_Closure_Proper` dropped (no declaration of it is used); `ContinuousLinearMap.adjoint_id` |
| ConvexAnalysis/ConvexSupport → Extended/ConvexSupport | ✓ (two upstream `sorry`s proved, see below) | not counted | instance → theorem: `convex_support_is_proper_of_nonempty` | `iSup_subtype`; simp now rewrites `⟪x, x⟫` to `‖x‖ ^ 2` |

Not ported: `ClosedFunction_Closure_Proper(_2)`, `affineset`, `LevelSet`, `seperationlaw` and
`intrinsicInterior_Epigraph` (all contain unfinished proofs), `Reaslib/NumericalAlgebra`, and
`Reaslib/Optlib/Algorithm/ADMM/Real_liminf` (a liminf for real sequences that nothing uses;
Mathlib has `Filter.liminf`). The `Reaslib/Optlib` copy of OptLib is the one already ported
above.

## Proofs supplied for upstream `sorry`s

Upstream left six proofs as `sorry`. All six are now proved here; two of them needed their
statement corrected because it was false as written. The 11 declarations that depended on
them are restored with their upstream proofs unchanged:

| Declaration | File | How |
|---|---|---|
| `CCP_lower_bounded_by_affine` (Cor 12.1.2: a proper convex `f` has an affine minorant) | ConvexConjugate | new file `Extended/AffineMinorantExistence` (`exists_inner_minorant_of_proper_convex`). The domain is translated to contain `0` and restricted to its span `V`, where it has nonempty interior. `f` is real-valued and convex there, hence continuous on the interior (`ConvexOn.continuousOn_interior`). Separating a point below the graph from the open strict epigraph gives a minorant on the interior (`ConvexOn.exists_affine_le_of_mem_interior`), which extends to the whole domain through midpoints (`ConvexOn.exists_affine_le`) and is written as an inner product by Riesz on `V`. Upstream's sketch went through `cl f` being proper, which in turn used this lemma. |
| `bi_convex_conjugate_eq_closure` (Thm 12.2, `f** = cl f`) | ConvexConjugate | For proper `f`: every affine minorant is continuous and `≤ f`, so it is `≤` the lsc hull (`affine_le_closure_of_proper`). Conversely, `cl f` is proper (`closure_proper_of_proper_convex`, from Cor 12.1.2), convex (`closure_convexOn_univ_of_proper`) and lsc, so Thm 12.1 (`closed_convex_function_is_sup_of_affine_bound_univ'`) writes it as the sup of its affine minorants, which are minorants of `f` since `cl f ≤ f`. If `f` takes `⊥`, both sides are `⊥`; otherwise, if `f` is not proper, `f ≡ ⊤` and both sides are `⊤`. |
| `univ_convex_closure_convex` | ConvexSupport | proper case: `closure_convexOn_univ_of_proper`; otherwise `cl f` is constant `⊥` or `⊤` |
| `exist_f_bot_of_cl_bot` | ConvexSupport | if `f` is proper, `cl f` is proper, so it is not `⊥`; otherwise `f ≡ ⊤` unless it takes `⊥`. This no longer uses `univ_convex_closure_intrinsicInterior` from the unported `ClosedFunction_Closure_Proper`. |
| `linearMap_convex_conjugate` (Thm 12.3: `(x ↦ g (A (x - a)) + ⟪x, a'⟫ + α)* y = g* ((A*)⁻¹ (y - a')) + ⟪y, a⟫ - α - ⟪a, a'⟫`) | ConvexConjugate | change of variables `z = A (x - a)` (`Equiv.iSup_comp`), a termwise identity checked separately for `g z = ⊥`, `⊤` and real, and `biSup_add_coe_const`. **Statement changed:** `α : EReal` → `α : ℝ`, because the upstream statement is false for `α = ⊥`, `g ≡ ⊤`, `A = id`, `a = a' = 0` (in `EReal`, `⊤ + ⊥ = ⊥`, so the left side is `⊤` and the right side `⊥`; checked in Lean). The hypothesis `ConvexOn ℝ (dom univ g) g` was dropped because the proof does not use it. Rockafellar also has `α ∈ ℝ`. |
| `convex_conjugate_in_ri` (Cor 12.2.2: `f* y = sup_{x ∈ ri (dom f)} (⟪x, y⟫ - f x)`) | ConvexConjugate | For `x ∈ dom f` and `z ∈ ri (dom f)`, the points `t z + (1 - t) x`, `t ∈ (0, 1)`, lie in `ri (dom f)` (`openSegment_sub_intrinsicInterior`). Convexity bounds their value below by an affine function of `t`, which tends to `⟪x, y⟫ - f x` as `t → 0⁺`. If `f` takes `⊥`, both sides are `⊤`. **Statement changed:** added `[FiniteDimensional ℝ E]`. Without it the statement is false: in `ℓ²` the nonnegative cone has empty relative interior (not checked in Lean). Rockafellar works in `ℝⁿ`. |

Restored with their upstream proofs: `bi_convex_conjugate_eq_self` (`f** = f` for closed convex
`f`), `convex_conjugate_congr_iff`, `proper_convex_proper_conjugate`,
`univ_convex_closure_proper'`, `convex_conjugate_closure_eq_convex_conjugate`,
`convex_conjugate_equiv`, `ccp_convex_conjugate_bijective`,
`ccp_zero_or_inf_iff_conjugate_is_positive_homogeneous`, `closure_ccp_or_bot_of_convex_ne_top`,
`conjugate_ccp_if_ccp`, `closure_eq_conjugate_of_positive_homogeneous_of_convex_ne_top`.

Changes to the file layout:

- `dom_univ_convex_closure_convex` was moved from ConvexSupport to ConvexConjugate (section
  `closure_of_proper_convex`), with the same statement and proof, because the proof of Thm 12.2
  needs it.
- New helper lemmas in that section: `affine_le_lowerSemicontinuousHull`,
  `affine_le_closure_of_proper`, `closure_proper_of_proper_convex` and
  `closure_convexOn_univ_of_proper`.

Generalizations after the port (statements made stronger, names kept):

- `bi_convex_conjugate_eq_self` (`f** = f` for lower semicontinuous convex `f`),
  `convex_conjugate_congr_iff` and `ccp_convex_conjugate_bijective` now assume `[CompleteSpace E]`
  instead of `[FiniteDimensional ℝ E]`. The proof of `bi_convex_conjugate_eq_self` no longer goes
  through `f** = cl f`; it uses the new file `Extended/AffineMinorantHilbert`, which proves
  Thm 12.1 with continuous affine minorants `⟪l, ·⟫ + w` directly.
- `bi_convex_conjugate_eq_closure` (`f** = cl f` for convex `f`) keeps `[FiniteDimensional ℝ E]`:
  its proof needs the lower semicontinuous hull of a proper convex function to be proper
  (Cor 12.1.2), which uses finite dimension.
