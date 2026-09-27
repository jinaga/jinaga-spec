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
defines. `split_correct` does not apply, because `Projected` fails. The rule loads
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

Until a step is proved, the way to verify the sequence is to check the
precondition at the boundary: run a `wellFormed` check on the specification
immediately before it reaches the split, and treat failure as an authoring error.
That check does not exist yet.

## Recommended next steps

1. **An executable `isWellFormed`** in `JinagaSpec/`, in the portable subset, with
   a soundness theorem (`isWellFormed s = true → WellFormed s`). Ports run the
   same check.
2. **Vectors for it:** specifications that are well-formed, and one violating each
   condition, with the expected verdict.
3. **Call the check at the choke point:** the `AuthorizationRuleSpecification`
   constructor, and the exported `splitBeforeFirstSuccessor`.
4. **Close the projection gap** in the parser, or accept it as the reason for (3).
5. **State `WellFormed` postconditions** for `alphaTransform`,
   `intersectSpecificationWithDistribution`, `reduceSpecification` and
   `buildFeeds`, and prove them or list them here as obligations, before any of
   them feeds the split.
