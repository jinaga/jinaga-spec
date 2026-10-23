import JinagaSpec.Semantics

/-!
# Maintaining a result as facts arrive

A stream holds a set of results and updates it as each fact arrives. It does
not trust whatever told it which results might have changed. It treats those as
*candidates*, and keeps or drops each one by reading the specification on the
graph that now holds the fact. A result that is not a candidate is left alone.
This is the design of jinaga/jinaga.js#336.

`Proofs/Maintain.lean` proves that the held set then equals `evaluate` after
every insertion, provided each step's candidates `Cover` the change. Where the
candidates come from is a separate question (jinaga/jinaga-spec#7).
-/
namespace JinagaSpec

abbrev Row := List (Option FactId)

/-- The candidates include every result that `f` adds or removes. -/
def Covers (s : Specification) (env : Env) (g : Graph) (f : Fact) (candidates : List Row) : Prop :=
  ∀ r, (r ∈ s.evaluate g env ↔ r ∈ s.evaluate (g ++ [f]) env) ∨ r ∈ candidates

/-- After a fact arrives in `g`: keep each candidate exactly when it is a result
on `g`, and leave every other held result as it was. -/
def recheck (s : Specification) (env : Env) (g : Graph) (candidates held : List Row) : List Row :=
  held.filter (!candidates.contains ·) ++ candidates.filter ((s.evaluate g env).contains ·)

/-- One insertion: extend the graph, then re-check the candidates the producer
names for this graph and fact. -/
def maintainStep (s : Specification) (env : Env) (candidates : Graph → Fact → List Row) :
    Graph × List Row → Fact → Graph × List Row
  | (g, held), f => (g ++ [f], recheck s env (g ++ [f]) (candidates g f) held)

end JinagaSpec
