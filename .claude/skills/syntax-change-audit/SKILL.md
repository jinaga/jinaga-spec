---
name: syntax-change-audit
description: "Audit every consumer of a changed definition in JinagaSpec/Syntax.lean or Semantics.lean before proving anything about the change. Use whenever a change adds a constructor, a field, or a case to Specification, Match, Condition, Projection, Component or another core type, or changes what a shared helper such as Projection.labels or usedInMatches returns — even when the change is motivated by one algorithm (feeds) and the others still compile."
---

# Syntax change audit

A new case in a core type compiles everywhere a function falls through to a
default (`| _ => []`, a `match` that ignores the new constructor, a helper that
recurses only into the old cases). The theorems about those functions often stay
true, because they compare rows rather than everything the function touches, so
neither the compiler nor `verify.sh` notices. PR #43 shipped this way at first:
child specifications made `Projection.labels` return `[]` for a child, which
silently changed the split's tail givens and the given-condition fresh label.
The theorems held; the behavior had diverged from jinaga.js.

Run this audit right after changing the type, before writing proofs.

## Steps

1. **Name what changed.** The type, the new constructor or field, and every
   helper whose result now differs on new inputs (for a new `Component` case:
   `Projection.labels`, anything that folds over components).

2. **List every consumer.** Pattern matches on the type and callers of each
   changed helper, transitively, across `JinagaSpec/`, the `Check*.lean` files,
   `Vectors.lean` and `ports/typescript/`:

   ```bash
   grep -rn "\.labels\b\|Projection\.\|\.components\|| \.composite\|| \.fact" JinagaSpec Check*.lean Vectors.lean
   grep -rn "components\|projection\.type" ports/typescript/*.ts
   ```

   Adjust the pattern to the names that changed. Include functions that use a
   wildcard; they are the likeliest to be wrong.

3. **Fill in the table** for each consumer, in your working notes:

   | Lean function | jinaga.js counterpart (file:line) | New case handled the same? | Theorem that would notice a difference | Vector that exercises the new case |
   |---|---|---|---|---|

   Find the counterpart in `../jinaga.js/src/specification/` (and
   `../jinaga-server/src/` for SQL and feeds). "Handled the same" means the
   Lean function returns what jinaga.js returns on an input that uses the new
   case, not merely that it terminates.

4. **Act on every row that is not "same, covered":**
   - Different from jinaga.js: fix it, or record in `docs/findings.md` why the
     spec deliberately differs.
   - Same, but no theorem would notice a change: add a vector whose input uses
     the new case, so the port runners compare it against jinaga.js. One vector
     per consumer, each testing one thing (`docs/findings.md`, "A vector should
     exercise one thing").
   - When several consumers need the same new helper (the split and the
     given-condition label both needed every label a projection names), write
     one shared helper (`Projection.allLabels`), not one per caller.

5. **Say which algorithms stay out of scope.** If an algorithm deliberately
   ignores the new case (the inverses don't model `invertProjection`), state it
   in that module's doc comment and in `docs/findings.md` "Not covered", in
   words that say what is and isn't ignored.

6. **Report the table** in your hand-back, so the reviewer can check it rather
   than rediscover it.
