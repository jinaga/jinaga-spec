# Contracts between algorithms

An algorithm is correct only for the inputs it expects. `split_correct` is a
theorem about **well-formed** specifications. This document says what the split
expects, who is responsible for providing it, and how to check a sequence of
steps that ends in the split. Where a postcondition is proved, it says where.
Where it is not, it says so, and the obligation stays with whoever composes the
steps.

## The split's contract

**Precondition** (`WellFormed`, `JinagaSpec/Proofs/Scoped.lean`):

1. **Scoped.** Every label a path condition names is in scope: a given, an
   earlier match, or, inside an existential condition, the enclosing unknown.
   In particular, a match never joins its own unknown.
2. **Unshadowed.** No match declares a label that is already in scope.
   (Lexical: sibling existential conditions may reuse a name.)
3. **Projected.** The projection names only givens and top-level unknowns.

**Postconditions.**

| | Status |
|---|---|
| The split returns the same results as the whole specification (as sets). | Proved: `split_correct`. |
| The tail's path conditions and projection name only the tail's givens or labels the tail declares earlier. | Proved: `tail_scoped`. |
| Every split label is distinct from every label the specification declares. | Proved: `splitPaths_names`, `freshLabel_not_mem`. |
| The head is deterministic (the graph can run it). | True by construction, **not proved**. |
| The head and tail are themselves `WellFormed`, so they can be split or transformed again. | **Not stated, not proved.** |

The last two matter only if a head or tail is fed to another algorithm that
assumes well-formedness. Nothing does today.

## Who can hand the split a specification

Traced in `jinaga.js` and the local `jinaga.net` checkout:

- **`splitBeforeFirstSuccessor` has one caller in `jinaga.js`**, the class
  `AuthorizationRuleSpecification` (`src/authorization/authorizationRules.ts`),
  in `isAuthorized` and `getAuthorizedPopulation`. `jinaga.net` has the same
  shape (`Authorization/AuthorizationRuleSpecification.cs`). The other local
  checkouts (`jinaga-server`, `jinaga-replicator`, and the rest) do not call it.
- **The class is not exported,** but the function is
  (`src/index.ts`), so any package can call it with any `Specification`.
- **The class is constructed in three places:** the model builder
  (`typeFromDefinition`), the predecessor-selector builder
  (`typeFromPredecessorSelector`), and the parser (`parseAuthorizationRules`,
  reached from `AuthorizationRules.loadFromDescription`).
- **Its constructor runs `validateSpecificationOrThrow`,** which checks only that
  each match is *rooted* (begins with a path condition). It checks none of the
  three conditions above.

## Which producer establishes which condition

| | Scoped | Unshadowed | Projected |
|---|---|---|---|
| **Parser** | Enforced: a path's joined label must be in `labels` ("has not been defined"), and `labels` excludes the match's own unknown. Nested matches are parsed with `[...labels, unknown]`. | Enforced: `parseMatch` rejects a name already in `labels` ("has already been used"). Nested labels are discarded on the way out, so scope is lexical. | **Not enforced.** `parseProjection` and `parseComponent` read an identifier and never look it up. |
| **Model builder** | By construction, unverified. Labels come from the lambdas' parameters. | By construction, unverified. Not read. | By construction, unverified. |
| **`validateSpecification`** | Not checked. | Not checked. | Not checked. |
| **Any other caller of the exported function** | No guarantee. | No guarantee. | No guarantee. |

### A gap that exists today

The parser accepts, and `validateSpecification` passes,

```
(p1: Employee) {
    u1: Office [ u1 = p1->office: Office ]
    u2: President [ u2->office: Office = u1 ]
} => nosuchlabel
```

and the split returns a tail whose projection is `nosuchlabel`, a label nothing
defines. `npm run audit` in `ports/typescript` reproduces this for every
specification in `vectors/well-formed`: the parser rejects every scoping and
shadowing violation, accepts every well-formed one (sibling-name reuse included),
and accepts all three projection violations, which `validateSpecification` also
passes. `split_correct` does not apply, because `Projected` fails. The rule loads
and fails only when it runs. (Reproduced against the branch carrying #308, #309
and #311.) The other two conditions are enforced by the parser, so a rule
loaded from text meets them.

## Other algorithms that produce or transform specifications

These are exported from `jinaga.js` and are not modelled here:
`alphaTransform`, `intersectSpecificationWithDistribution`, `reduceSpecification`,
`buildFeeds`, and the inverse-specification builders. **None feeds the split in
the current code.** If any ever does, it must preserve `WellFormed`, and today
there is no statement, and no proof, that it does.

## Checking a sequence of steps

For a pipeline `s0 → f1 → ... → fn → split`, the split's precondition holds if

1. the producer of `s0` establishes `WellFormed s0`,
2. each `fi` preserves it: `WellFormed x → WellFormed (fi x)`, and
3. so `WellFormed (fn (... (f1 s0)))` holds when the split runs.

Record each pipeline in a table like this. An unproved cell is a runtime
obligation.

| step | establishes or preserves | how it is known |
|---|---|---|
| producer | Scoped, Unshadowed, Projected | proved / enforced in code / **unverified** |
| `f1` | ... | ... |

Until a step is proved, verify the sequence by running the check on the
specification immediately before it reaches the split, and treating failure as
an authoring error.

## The check

`isWellFormed` (`JinagaSpec/WellFormed.lean`) is that check. It is written in the
portable subset and reports the three conditions separately (`isScoped`,
`isUnshadowed`, `isProjected`), so a port can name the one a specification
violates.

- **It decides the hypothesis exactly:** `isWellFormed_iff` proves
  `isWellFormed s = true ↔ WellFormed s`. So a specification that passes is split
  correctly (`split_correct_of_check`), and one the theorem covers is never
  rejected.
- **It has vectors:** `vectors/well-formed/` holds 16 specifications, well-formed
  and violating each condition, with the expected verdict. Each case states the
  verdict a reader of the rules expects, and the generator refuses to write a
  vector where the oracle disagrees. All 17 specifications in `vectors/split/`
  are checked to be well-formed.
- **It has a reference port:** `ports/typescript/well-formed.ts` mirrors the Lean
  and depends on nothing, so it can be lifted into `jinaga.js` as it stands. It
  passes all 16 vectors, and mutants that skip the scope check or the shadowing
  check are each caught by the vectors written for them.

### Putting it to use in `jinaga.js`

Not done here, because it changes `jinaga.js`. The change is small:

1. Add `well-formed.ts` under `src/specification/`.
2. In the `AuthorizationRuleSpecification` constructor, after
   `validateSpecificationOrThrow`, throw an `AuthorizationRuleError` naming the
   violated condition if `checkWellFormed` fails. That closes the projection gap
   at the point a rule is stored, for the parser, the builders, and any future
   producer, without relying on any of them.
3. Decide whether the exported `splitBeforeFirstSuccessor` should check too, or
   whether its documentation should state the precondition. Throwing there
   changes a public function's behavior for callers outside this repository.

`jinaga.net` needs the same check, run against the same vectors.

## Remaining work

1. **Wire the check into the constructors** in `jinaga.js` and `jinaga.net`
   (above).
2. **State `WellFormed` postconditions** for `alphaTransform`,
   `intersectSpecificationWithDistribution`, `reduceSpecification` and
   `buildFeeds`, and prove them or list them here as obligations, before any of
   them feeds the split.
3. **Prove the split's own output well-formed**, so a head or tail can be passed
   on.
4. **Model conditions on givens and the remaining projections**, which the check
   ignores today.
