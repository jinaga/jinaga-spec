import JinagaSpec.Semantics

/-!
# Maintaining a result as facts arrive

A stream holds a set of results and updates it as facts arrive. A replica
saves facts in batches (a `/load` response, a feed page, a WebSocket frame, or
a local fact with its new predecessors), so a step adds a batch `B`, and a
single fact is the batch `[f]`. The stream does not trust whatever told it
which results might have changed. It treats those as *candidates*, and keeps or
drops each one by reading the specification on the graph that now holds the
batch. A result that is not a candidate is left alone. This is the design of
jinaga/jinaga.js#336.

`Proofs/Maintain.lean` proves that the held set then equals `evaluate` after
every batch, provided each step's candidates `Cover` the change. Where the
candidates come from is a separate question (jinaga/jinaga-spec#7, #11).
-/
namespace JinagaSpec

abbrev Row := List (Option FactId)

/-- The candidates include every result that the batch `B` adds or removes. -/
def Covers (s : Specification) (env : Env) (g : Graph) (B : List Fact) (candidates : List Row) : Prop :=
  ∀ r, (r ∈ s.evaluate g env ↔ r ∈ s.evaluate (g ++ B) env) ∨ r ∈ candidates

/-- After facts arrive in `g`: keep each candidate exactly when it is a result
on `g`, and leave every other held result as it was. -/
def recheck (s : Specification) (env : Env) (g : Graph) (candidates held : List Row) : List Row :=
  held.filter (!candidates.contains ·) ++ candidates.filter ((s.evaluate g env).contains ·)

/-- One batch: extend the graph, then re-check the candidates the producer
names for this graph and batch. -/
def maintainStep (s : Specification) (env : Env) (candidates : Graph → List Fact → List Row) :
    Graph × List Row → List Fact → Graph × List Row
  | (g, held), B => (g ++ B, recheck s env (g ++ B) (candidates g B) held)

end JinagaSpec
