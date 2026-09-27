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
| `JinagaSpec/Syntax.lean`, `Semantics.lean`, `Split.lean` | The definitions: the language, what it means over a fact graph, and the split. 350 lines with the check, written to be read next to the TypeScript. |
| `JinagaSpec/Proofs/` | The proof that the split preserves meaning. About 1,200 lines. `Main.lean` has the theorem. |
| `JinagaSpec/Cases.lean`, `Vectors.lean` | Named specifications, and the program that writes them out with the split the oracle computes. |
| `vectors/` | The generated conformance vectors: `split/` for the split, `well-formed/` for the check. Any port can read them. |
| `ports/typescript/` | Runs the vectors against `jinaga.js`, holds a reference `isWellFormed`, and audits `jinaga.js`'s parser against the well-formedness vectors. |
| `Check.lean` | Randomized test of the theorem, with mutation checks. Runs before proving, and still useful after. |
| `docs/findings.md` | What the spike turned up. Read this after the theorem. |
| `docs/contracts.md` | What the split expects, who must provide it, and how to check a sequence of steps. |
| `JinagaSpec/WellFormed.lean` | `isWellFormed`: an executable check of the split's preconditions, proved to agree with `WellFormed`. |
| `JinagaSpec/Store.lean`, `JinagaSpec/Proofs/Store.lean` | The graph a rule runs on while its fact is under authorization, and the boundary theorem `tailReadsGiven` decides. |
| `JinagaSpec/Hoist.lean`, `JinagaSpec/Proofs/Hoist.lean` | `hoist`: the fix for formulation D of #231, proved sound for every well-formed specification. |

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

`WellFormed` is what a library checks once, where a specification enters (`docs/contracts.md`):

1. **Scoped.** Every label a path condition names is in scope: a given, an
   earlier match, or, inside an existential condition, the enclosing unknown.
2. **Well-named.** Every declared label is new, not already in scope, and ordinary,
   not reserved: a label that begins with `__` belongs to the split.
3. **Projected.** The projection names only givens and top-level unknowns.

The theorem is about sets of results. It does not claim the split returns them
in the same order or with the same multiplicity, which authorization does not
need (it asks whether any result is the user).

`split_correct` runs the head and the tail on the same graph. A rule does not:
it runs while its fact is being authorized, before that fact is saved, so the
store the tail runs on does not have it. `JinagaSpec/Store.lean` models this —
`Split.evaluateStore` is the runner's behaviour, and `tailReadsGiven` is the
model's name for exactly the shape that denies everyone — and two theorems say
the boundary is exact:

```lean
theorem store_denies (hwf : WellFormed s) (hg : s.given = [g0]) (hord : OrdinaryTypes s)
    (hclosed : store.closed) (hfnotin : ¬ InStore store f.id)
    (hfpred : ∀ p ∈ f.predecessors, InStore store p.2) (henv : env g0.name = some f.id)
    (h : tailReadsGiven (splitBeforeFirstSuccessor s) g0.name = true) :
    (splitBeforeFirstSuccessor s).evaluateStore store f env = []

theorem store_correct (hwf : WellFormed s) (hg : s.given = [g0]) (hord : OrdinaryTypes s)
    (hclosed : store.closed) (hfnotin : ¬ InStore store f.id)
    (hfpred : ∀ p ∈ f.predecessors, InStore store p.2) (henv : env g0.name = some f.id)
    (h : tailReadsGiven (splitBeforeFirstSuccessor s) g0.name = false) (r : List (Option FactId)) :
    r ∈ (splitBeforeFirstSuccessor s).evaluateStore store f env ↔
      r ∈ s.evaluate (Graph.authGraph store f) env
```

A rule with one given, whose tail reads that given, admits nobody
(`store_denies`). One that does not means, on the store, exactly what the whole
specification means on the graph that holds the given (`store_correct`). See
`docs/findings.md` for the retyping trick both proofs lean on.

`jinaga.js` refuses this shape where a rule is written:
`AuthorizationRuleSpecification`'s constructor throws `AuthorizationRuleError`
when the tail is given the rule's own given
([jinaga/jinaga.js#324](https://github.com/jinaga/jinaga.js/pull/324)). The
TypeScript port checks that it throws exactly when `tailReadsGiven` is true of
the split it runs, which is `hoist`, below.

`hoist` (`JinagaSpec/Hoist.lean`) is the split `jinaga.js` runs
([jinaga/jinaga.js#325](https://github.com/jinaga/jinaga.js/pull/325)). It
admits formulation D of jinaga/jinaga.js#231, which `splitBeforeFirstSuccessor`
leaves with a tail that reads the given: it reaches into the tail's existential
conditions, at any depth, not only the pivot's own top level, for a
predecessor walk of a label already in scope, hoisting it only where doing so
is sound. `hoist_correct` proves
this sound for every well-formed specification, with no hypothesis beyond
`WellFormed s` — the same shape as `split_correct` — and `store_denies_hoist`/
`store_correct_hoist` carry the store boundary theorems over to it. Where
hoisting stops being sound, and the argument the general proof turns on, are
in `docs/findings.md` — including a second unsoundness the randomized check
found in an earlier version of the rule, one level of nesting deeper than the
first.

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
| `tailGivenAt` | `referencedLabels(tailMatches, inScope, projection)` |
| `splitPaths`, `splitLabel` | none, since `jinaga.js` runs `hoist`, which subsumes it; and `splitLabel(i)` |
| `WellFormed` | what `SpecificationParser` and `validateSpecification` enforce |
| `Graph.authGraph` | the in-memory write batch, with the fact under authorization added |
| `Split.evaluateStore` | `AuthorizationRuleSpecification.isAuthorized`/`getAuthorizedPopulation`, running the tail on the store |
| `tailReadsGiven` | the check in `AuthorizationRuleSpecification`'s constructor that throws `AuthorizationRuleError` (jinaga/jinaga.js#324) |
| `hoist`, `hoistMatches`, `hoistCondition` | `splitBeforeFirstSuccessor`, `hoistMatches`, `hoistCondition` (jinaga/jinaga.js#325); the Lean index is the length of the list of hoisted matches |


## Conformance vectors

Each file in `vectors/split/` holds a specification, the split the Lean oracle
computes, and both in Jinaga's text form. A port passes when its split of the
same specification equals `expected`. See `vectors/README.md`.

The TypeScript in `jinaga.js` passes every vector (`scripts/verify.sh` runs it).

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
   `jinaga.net` (`docs/contracts.md`); `jinaga.js` now does this
   (jinaga/jinaga.js#308, #311).
2. Given conditions and the remaining projections, and a .NET runner for the vectors.
3. Vectors that check evaluation (a specification, a graph, and the expected
   results), so a port is checked on meaning as well as on shape.
4. Make `hoist` the specification's split: regenerate the vectors so
   `expected` is the hoisted split, and drop the separate `hoisted` envelope.
   `jinaga.js` runs it (jinaga/jinaga.js#325), and `jinaga.net` should adopt it
   with the boundary check in item 1.
5. `buildFeeds`, then skeleton canonicity, then distribution soundness.

## License

MIT. See `LICENSE`.
