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

* each descendant, taken as a feed (its matches with the givens they use), is
  connected;
* every given is used by some descendant; and
* every feed `buildFeeds` emits is connected.

The last clause is the one (A) of jinaga-spec#55 needs. It is stated over the
emitted feeds rather than over the prefixes where `buildFeeds` cuts, because
those prefixes are exactly the feeds: an excluding feed is the written prefix
followed by the condition's matches, a restoring feed goes on through the
canceller's matches, and each of them is checked as it is emitted. A
condition's matches are joined into the feed with path conditions only, so
`isConnected` does not count the link it adds from a condition's labels to the
match it is written on. Restating the cuts as a second walk would copy
`levelFeeds` and `negFeeds`.

`isConnected` is the check `invertSpecification` runs (`Inverse.lean`). It
reads only a specification's givens and its top-level matches.
-/
namespace JinagaSpec

/-- A list of matches as a feed of `given`: with the givens it uses, and no
projection. -/
def asFeed (given : List Label) (ms : List Match) : Specification :=
  { given := usedGivens given ms, matchList := ms, projection := .composite [] }

/-- Every descendant is connected over the givens it uses, every given is used
by some descendant, and every feed is connected. The feeds theorems
`buildFeeds_connected` and `isConnected_of_connectedDescendants` assume it. -/
def ConnectedDescendants (s : Specification) : Prop :=
  (∀ d ∈ s.descendants, isConnected (asFeed d.given d.matchList) = true) ∧
  (∀ l ∈ s.given, ∃ d ∈ s.descendants, l ∈ usedGivens d.given d.matchList) ∧
  ∀ f ∈ buildFeeds s, isConnected f = true

/-- The check that decides `ConnectedDescendants` (`isConnectedDeep_iff`). -/
def isConnectedDeep (s : Specification) : Bool :=
  s.descendants.all (fun d => isConnected (asFeed d.given d.matchList)) &&
  s.given.all (fun l => s.descendants.any fun d => (usedGivens d.given d.matchList).contains l) &&
  (buildFeeds s).all isConnected

end JinagaSpec
