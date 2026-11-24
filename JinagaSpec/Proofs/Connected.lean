import JinagaSpec.Connected
import JinagaSpec.Proofs.Children

/-!
# Connected descendants

* `isConnectedDeep_iff`: the check decides `ConnectedDescendants`.
* `isConnected_asFeed`: a specification is connected exactly when its
  matches, as a feed, are. So clause 1 of `ConnectedDescendants`, at the
  specification itself, is `isConnected`.

Clause 2, that every feed is joined, is a definition with no theorem behind
it: `isJoined` is what "not a product" means here. `feeds_cover` and
`feeds_defer` (`Proofs/Children.lean`) need no new hypothesis: `buildFeeds` is
unchanged, and the check only refuses.
-/
namespace JinagaSpec

/-- The check decides `ConnectedDescendants`. -/
theorem isConnectedDeep_iff (s : Specification) : isConnectedDeep s = true ↔ ConnectedDescendants s := by
  simp [isConnectedDeep, ConnectedDescendants]

/-- `isConnected` reads only the matches and the givens they use, which are a
feed's givens, so a specification is connected exactly when its matches, as a
feed, are. -/
theorem isConnected_asFeed (s : Specification) :
    isConnected (asFeed s.given s.matchList) = isConnected s := by
  simp [isConnected, asFeed, usedGivens]

end JinagaSpec
