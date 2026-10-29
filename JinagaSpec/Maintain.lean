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

`Proofs/Maintain.lean` proves that the held set then equals the result after
every batch, provided each step's candidates `Cover` the change. Where the
candidates come from is a separate question (jinaga/jinaga-spec#7, #11).

The result is any function of the graph: a stream maintains
`(s.read · env)`, what a replica reads, and the randomized check also
maintains `(s.evaluate · env)`. Nothing here depends on which.
-/
namespace JinagaSpec

abbrev Row := List (Option FactId)

/-- The candidates include every result that the batch `B` adds or removes. -/
def Covers (result : Graph → List Row) (g : Graph) (B : List Fact) (candidates : List Row) : Prop :=
  ∀ r, (r ∈ result g ↔ r ∈ result (g ++ B)) ∨ r ∈ candidates

/-- After facts arrive in `g`: keep each candidate exactly when it is a result
on `g`, and leave every other held result as it was. -/
def recheck (result : Graph → List Row) (g : Graph) (candidates held : List Row) : List Row :=
  held.filter (!candidates.contains ·) ++ candidates.filter ((result g).contains ·)

/-- One batch: extend the graph, and update the held results for the graph
before and the batch. -/
def advance (update : Graph → List Fact → List Row → List Row) :
    Graph × List Row → List Fact → Graph × List Row
  | (g, held), B => (g ++ B, update g B held)

/-- One batch: extend the graph, then re-check the candidates the producer
names for this graph and batch. -/
def maintainStep (result : Graph → List Row) (candidates : Graph → List Fact → List Row) :
    Graph × List Row → List Fact → Graph × List Row :=
  advance fun g B => recheck result (g ++ B) (candidates g B)

end JinagaSpec
