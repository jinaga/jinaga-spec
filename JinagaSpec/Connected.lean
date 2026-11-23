import JinagaSpec.Feeds
import JinagaSpec.Inverse

/-!
# Connected descendants

A feed is one query that a replicator answers from its givens. If its labels
fall into two chains that no path condition joins, the store has to answer it
as a product of the two, which jinaga-server cannot do
(jinaga/jinaga-server#233). `buildFeeds` keeps each descendant's matches in
written order, so a feed cut at a negative condition or at a child
specification can be such a product even when the whole specification is
connected. A specification like that is refused (jinaga/jinaga-spec#55). This
file defines the check.

`ConnectedDescendants s` holds when

1. each descendant, taken as a feed (its matches with the givens they use),
   passes `isConnected`;
2. every given is used by some descendant; and
3. every feed `buildFeeds` emits is joined (`isJoined`): its path conditions
   alone join its matches and the givens it uses, and it passes `isConnected`.

Clause 3 is the one (A) of jinaga-spec#55 needs, and it says no feed is a
product: a feed's matches are joined by its path conditions, not by a negative
condition. An excluding feed holds a condition's matches as matches, joined to
the rest by their own path conditions. A filtered feed holds the condition as
a filter (`addLast`), and `isConnected` counts every label a filter names as
joined to the match it is on (`negative-condition-joins-two-chains`), so the
filters are dropped before the check (`Match.paths`). The givens are then the
ones the path conditions use: a given only a filter names is a parameter of
the filter, not a factor of a product (`two-givens`). Dropping the filters
also drops the check that a filter's matches are joined to the feed
(`negative-condition-joined-only-inside-its-own`), so the feed must pass
`isConnected` as well. The clause is stated over the emitted feeds rather than
over the prefixes where `buildFeeds` cuts, because those prefixes are exactly
the feeds; restating the cuts as a second walk would copy `levelFeeds` and
`negFeeds`.

Clauses 1 and 2 are refusal policy. No theorem here needs clause 2, which is
jinaga-spec#45's rule and matches jinaga.js, or clause 1 at a child
specification; clause 1 at the specification itself makes the check at least
as strict as `isConnected` when the top-level matches use every given
(`isConnected_asFeed`).

`isConnected` is the check `invertSpecification` runs (`Inverse.lean`). It
reads only a specification's givens and its top-level matches.
-/
namespace JinagaSpec

/-- A feed is joined when its path conditions alone, its negative conditions'
filters dropped, join its matches and the givens it uses, so it is not a
product; and it passes `isConnected`, so each filter's matches are joined to
it. -/
def isJoined (f : Specification) : Bool :=
  isConnected f && isConnected (asFeed f.given (f.matchList.map Match.paths))

/-- Every descendant is connected over the givens it uses, every given is used
by some descendant, and every feed is joined. -/
def ConnectedDescendants (s : Specification) : Prop :=
  (∀ d ∈ s.descendants, isConnected (asFeed d.given d.matchList) = true) ∧
  (∀ l ∈ s.given, ∃ d ∈ s.descendants, l ∈ usedGivens d.given d.matchList) ∧
  ∀ f ∈ buildFeeds s, isJoined f = true

/-- The check that decides `ConnectedDescendants` (`isConnectedDeep_iff`). -/
def isConnectedDeep (s : Specification) : Bool :=
  s.descendants.all (fun d => isConnected (asFeed d.given d.matchList)) &&
  s.given.all (fun l => s.descendants.any fun d => (usedGivens d.given d.matchList).contains l) &&
  (buildFeeds s).all isJoined

end JinagaSpec
