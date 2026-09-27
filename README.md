# jinaga-spec

A formal specification of Jinaga's specification language and the algorithms
that transform it, with a machine-checked proof that the specification split is
correct, and conformance vectors that any implementation can run.

**Status: a spike.** It covers one algorithm end to end (`splitBeforeFirstSuccessor`)
to find out whether this approach keeps the definitions readable, the proofs
tractable, and the ports checkable. The answer so far is yes. Nothing in `jinaga.js` or `jinaga.net` depends on it.

## What is here

| | |
|---|---|
| `JinagaSpec/Syntax.lean`, `Semantics.lean`, `Split.lean` | The definitions: the language, what it means over a fact graph, and the split. 343 lines, written to be read next to the TypeScript. |
| `JinagaSpec/Proofs/` | The proof that the split preserves meaning. About 1,200 lines. `Main.lean` has the theorem. |
| `JinagaSpec/Cases.lean`, `Vectors.lean` | Seventeen named specifications, and the program that writes them out with the split the oracle computes. |
| `vectors/` | The generated conformance vectors: `split/` for the split, `well-formed/` for the check. Any port can read them. |
| `ports/typescript/` | Runs the vectors against `jinaga.js`, holds a reference `isWellFormed`, and audits `jinaga.js`'s parser against the well-formedness vectors. |
| `Check.lean` | Randomized test of the theorem, with mutation checks. Runs before proving, and still useful after. |
| `docs/findings.md` | What the spike turned up. Read this after the theorem. |
| `docs/contracts.md` | What the split expects, who must provide it, and how to check a sequence of steps. |
| `JinagaSpec/WellFormed.lean` | `isWellFormed`: an executable check of the split's preconditions, proved to agree with `WellFormed`. |

## Try it

```
scripts/verify.sh
```

That builds and checks the proofs, confirms the vectors are current, runs the
randomized check, and runs the TypeScript port if it finds `../jinaga.js` (or
`JINAGA_JS`). It needs [`elan`](https://github.com/leanprover/elan); the
toolchain is pinned in `lean-toolchain`, and there is no other Lean dependency
(no Mathlib).

## The theorem

An authorization rule is a specification. To evaluate one, `jinaga.js` cuts it
at its first match that the in-memory graph cannot run. The *head* before the
cut walks predecessors on the graph. The *tail* after it runs against the
store, once per head result, seeded with only the facts the tail is given.

```lean
theorem split_correct (s : Specification) (hwf : WellFormed s) (g : Graph) (env : Env)
    (r : List (Option FactId)) :
    r ∈ (splitBeforeFirstSuccessor s).evaluate g env ↔ r ∈ s.evaluate g env
```

For every well-formed specification, every graph, and every assignment of the
givens, the split and the whole specification return the same results. It
depends only on Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`).

`WellFormed` is what the parser and validator already guarantee:

1. **Scoped.** Every label a path condition names is in scope: a given, an
   earlier match, or, inside an existential condition, the enclosing unknown.
2. **Unshadowed.** No match re-declares a label that is already in scope.
   `SpecificationParser.parseMatch` rejects this with "The name ... has already
   been used".
3. **Projected.** The projection names only givens and top-level unknowns.

The theorem is about sets of results. It does not claim the split returns them
in the same order or with the same multiplicity, which authorization does not
need (it asks whether any result is the user).

## Reading the definitions

`Split.lean` is in a deliberately **portable subset**: inductive types, total
pure functions, structural recursion, and lists. No tactics, no dependent types.
A port should read line for line. Names match TypeScript, with these exceptions:

| Lean | TypeScript |
|---|---|
| `matchList` (`matches` is reserved) | `matches` |
| `Match.mk unknown conditions` | `{ unknown, conditions }` |
| `Condition.existential «exists» matchList` | `ExistentialCondition` |
| `Env` | `ReferencesByName` |
| `evalMatches` | `FactGraph.executeMatches` |
| `Split.evaluate` | the head-then-tail evaluation in `AuthorizationRuleSpecification` |
| `Env.restrictTo names` | `startReferences(tuple, tail)` |
| `tailGivenAt` | `referencedLabels(tailMatches, allLabels, projection)` |
| `splitPaths` | the loop over the pivot's path conditions, with `allocateLabels` |
| `WellFormed` | what `SpecificationParser` and `validateSpecification` enforce |

One deliberate difference in shape: `splitPaths` threads the labels taken so far
through its walk, where TypeScript allocates them up front and indexes into the
list. The names produced are identical.

## Conformance vectors

Each file in `vectors/split/` holds a specification, the split the Lean oracle
computes, and both in Jinaga's text form. A port passes when its split of the
same specification equals `expected`. See `vectors/README.md`.

Run against each layer of the three stacked pull requests (#308, #309, #311),
every vector flips in exactly the layer whose issue it names:

| layer | main | #308 | #309 | #311 |
|---|---|---|---|---|
| vectors passing | 7 | 9 | 12 | 17 of 17 |

## What is modelled, and what is not

Modelled: path conditions, positive and negative existential conditions,
multi-valued predecessor roles, fact and composite projections, several givens.

Not yet: conditions on givens, `field`/`hash`/`time` projections, and nested
specification projections. The split's handling of a given's conditions
(`declaredLabelsInGivens`, added in the review of #311) has no counterpart here.
See `docs/findings.md`.

## The limit of the guarantee

The proof covers the model in `JinagaSpec/`. The TypeScript is a separate
artifact. What connects them is the conformance corpus and a reading of the two
side by side. The randomized check and the mutation check make a divergence
harder to hide, but they are not a proof about the TypeScript.

## Next

1. Wire `isWellFormed` into the `AuthorizationRuleSpecification` constructors in
   `jinaga.js` and `jinaga.net` (`docs/contracts.md`).
2. Given conditions and the remaining projections, and a .NET runner for the vectors.
3. Vectors that check evaluation (a specification, a graph, and the expected
   results), so a port is checked on meaning as well as on shape.
4. `buildFeeds`, then skeleton canonicity, then distribution soundness.

## License

MIT. See `LICENSE`.
