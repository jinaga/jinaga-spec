import JinagaSpec.Semantics

/-!
# Paging a feed by bookmark

jinaga-server pages a feed (`src/postgres/specification-sql.ts`): a tuple's
position is the ids of its facts, largest first
(`sort(array[f1.fact_id, ...], 'desc')`), positions compare lexicographically,
as Postgres compares arrays, and a page is the tuples after the bookmark, in
order, up to a limit. The bookmark then moves to the last position on the
page, and a replica stores it (`saveBookmark`) after it has saved the facts.

`Proofs/Cursor.lean` proves that a replica that pages a feed this way, while the
replicator's graph grows, has every tuple's facts once a page comes back empty.
It needs one thing of the replicator: a fact saved after a tuple was read has a
larger id than every fact of the graph that read saw (`IdsIncrease`).
jinaga-server assigns `fact_id` from a sequence before commit, and two saves
may commit out of id order, so today it does not always hold
(jinaga/jinaga-server#203).
-/
namespace JinagaSpec

/-- A tuple's position in its feed: the ids of its facts, largest first. -/
def position (t : List FactId) : List Nat := t.mergeSort fun a b => decide (b ≤ a)

/-- `P` is a page of the tuples `T` after bookmark `b`: tuples beyond the
bookmark, none left out below a position the page holds, and empty only when
there is nothing beyond the bookmark. `ORDER BY bookmark ASC LIMIT n` returns
one, whatever `n` is; so does a page of every tuple beyond the bookmark. -/
structure IsPage (T P : List (List FactId)) (b : List Nat) : Prop where
  beyond : ∀ t ∈ P, t ∈ T ∧ b < position t
  noGap : ∀ t ∈ T, b < position t → t ∉ P → ∀ p ∈ P, position p ≤ position t
  progress : (∃ t ∈ T, b < position t) → P ≠ []

/-- The bookmark after a page: its last position, which is its largest. -/
def nextBookmark (b : List Nat) (P : List (List FactId)) : List Nat :=
  P.foldl (fun m t => if position t ≤ m then m else position t) b

/-- What the replica has caught up on: the facts of every tuple at or before
the bookmark are among those it has delivered. -/
def Caught (T : List (List FactId)) (b : List Nat) (D : List FactId) : Prop :=
  ∀ t ∈ T, position t ≤ b → ∀ id ∈ t, id ∈ D

/-- Every fact of `B` has a larger id than every fact of `g`. -/
def IdsIncrease (g : Graph) (B : List Fact) : Prop := ∀ x ∈ g, ∀ y ∈ B, x.id < y.id

end JinagaSpec
