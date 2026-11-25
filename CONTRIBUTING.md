# Contributing

Contributions are welcome: new results, corrections, simpler proofs, and reports of statements
that are wrong or hard to use. For anything larger than a small fix, open an issue first to
agree on the statement and on where it goes.

## Setting up

```
git clone https://github.com/dvillacis/lean-convex
cd lean-convex
lake exe cache get
lake build
```

`lake exe cache get` downloads the compiled Mathlib; without it, Mathlib is compiled locally,
which takes hours. The Lean version is fixed by `lean-toolchain`.

## What a change must satisfy

Changes go through pull requests against `main`. CI runs the checks below, and each can be run
locally.

| Check | Command |
|---|---|
| The library builds with no warnings | `lake build` |
| The root file imports every module | `lake exe mk_all --check` (`lake exe mk_all` to fix) |
| The tests build | `lake test` |
| The README example is the tested one | `python3 scripts/check_readme.py` |
| No `sorry` and no new axiom | `lake env lean scripts/AuditAxioms.lean` |

No `sorry` is merged, and no declaration may depend on an axiom beyond `propext`,
`Classical.choice` and `Quot.sound`.

## Ported files

Most files are ported from OptLib and Reaslib (see [`NOTICE`](NOTICE)). For these files:

- keep the copyright header and the authors of the original;
- keep the names and statements of the original declarations, so that the library can be
  compared with upstream. Proofs may change freely;
- if a statement has to change (because Mathlib changed, or because it was false), record it in
  [`PORTING.md`](PORTING.md) and mark it as breaking in the changelog.

New declarations in a ported file, and new files, follow the
[Mathlib style guide](https://leanprover-community.github.io/contribute/style.html) and
[naming conventions](https://leanprover-community.github.io/contribute/naming.html), and have a
docstring.

## Conventions

- Functions are real-valued, with domains given by sets, as in Mathlib's `ConvexOn s f`. The
  files in `Extended/` treat functions `E → EReal`, following Rockafellar's *Convex Analysis*.
- Subgradients are vectors of an inner product space (`HasSubgradientAt`, `SubderivAt`);
  `Convex/BanachSubgradient` has the version with continuous linear functionals.
- Declarations are in the root namespace, as in OptLib.

## Bookkeeping

A pull request that adds or changes results also updates:

- the tables of [`README.md`](README.md), if a file is added or its contents change;
- [`CHANGELOG.md`](CHANGELOG.md), under "Unreleased". Renaming a declaration or changing the
  statement of a theorem is a breaking change and is marked as such.

## Tests

`ConvexAnalysisTest/Statements.lean` restates the main results with all their hypotheses
written out and proves each by the library theorem. If one of these `example`s stops compiling,
the statement of a main result has changed: either restore it, or change the `example` and
record a breaking change. Add an `example` there for a new result that users are likely to rely
on.

`ConvexAnalysisTest/Readme.lean` contains the example of the README; keep the two identical.

## License

By contributing you agree that your contribution is licensed under the Apache 2.0 license of
the project (see [LICENSE](LICENSE)). Add yourself to the authors line of the files you change
substantially.
