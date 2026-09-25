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
