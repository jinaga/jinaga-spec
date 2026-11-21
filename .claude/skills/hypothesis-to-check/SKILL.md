---
name: hypothesis-to-check
description: "For every hypothesis a new or changed jinaga-spec theorem assumes, produce the executable check that enforces it: a Bool function in Lean, a proof that it equals the hypothesis, the same check in the TypeScript port, and a negative vector. Use when stating a theorem with a hypothesis on its input (WellFormed, DistinctLabels, RootedMatches, a per-descendant quantifier), or when generalizing one to a new scope."
---

# From hypothesis to check

A theorem with a hypothesis says nothing about input that breaks it. If no
layer rejects that input, a well-formed-looking specification gets output that
no theorem covers. PR #43's feed theorems assumed `∀ d ∈ s.descendants,
WellFormed d` while `isWellFormed`, the port and jinaga.js all ignored child
specifications; the reviewer found it.

Do this when stating the theorem, not after review.

## For each hypothesis `H s` on the input

1. **Is it already enforced?** Look for an existing `isX` with an `isX_iff`
   lemma (`isWellFormed_iff`, `isWellFormedDeep_iff`). If one exists and has the
   same scope as the hypothesis, cite it and stop. A check over the top level
   only does not enforce a hypothesis quantified over descendants.

2. **Prefer to drop it.** If the proof never reads it, delete it (see
   `CLAUDE.md`). If it holds by construction for every output of the algorithm
   (`buildFeeds_feedShape` needs nothing), prove that instead.

3. **Write the Lean check** next to the hypothesis's definition:
   `def isX (s : Specification) : Bool`. Reuse existing checks
   (`isWellFormedDeep s := s.descendants.all isWellFormed`) rather than writing
   a new traversal.

4. **Prove `isX_iff : isX s = true ↔ H s`** and add it to the axioms list in
   `scripts/verify.sh`.

5. **Port it.** Add the same check to `ports/typescript/` (usually
   `well-formed.ts`), and call it from the port of the algorithm that needs it,
   so the port rejects what the theorem does not cover. Seed scope checks with
   everything in scope (given labels included) — PR #43's first port started a
   repeated-label check from `[]`, so a child could redeclare a given.

6. **Add a negative vector** in `vectors/well-formed/` (or the algorithm's own
   vector directory) that breaks exactly this hypothesis, with `violates`
   naming it. Make the vector check use `isX`. If jinaga.js accepts it, list it
   as a known jinaga.js miss in the runner, so the runner says when jinaga.js
   starts agreeing.

7. **Name the check in the docs.** `docs/contracts.md` says which check a
   caller runs before calling the algorithm. Never write "the caller checks X"
   unless a function named there does.

## Hand-back

List each hypothesis with its check, its `_iff` lemma, its port function, and
its negative vector — or why it needs none.
