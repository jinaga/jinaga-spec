import JinagaSpec.Connected
import JinagaSpec.Proofs.Children

/-!
# Connected descendants

* `isConnectedDeep_iff`: the check decides `ConnectedDescendants`.
* `isConnected_asFeed`: a specification whose top-level matches use every
  given is connected exactly when its matches, as a feed, are. So clause 1 of
  `ConnectedDescendants`, at the specification itself, makes the check at
  least as strict as `isConnected` on such a specification.

Clause 3, that every feed is joined, is a definition with no theorem behind
it: `isJoined` is what "not a product" means here. `feeds_cover` and
`feeds_defer` (`Proofs/Children.lean`) need no new hypothesis: `buildFeeds` is
unchanged, and the check only refuses.
-/
namespace JinagaSpec

/-- The check decides `ConnectedDescendants`. -/
theorem isConnectedDeep_iff (s : Specification) : isConnectedDeep s = true ↔ ConnectedDescendants s := by
  simp [isConnectedDeep, ConnectedDescendants, and_assoc]

/-- `isConnected` reads only the givens and the matches, so a specification
whose top-level matches use every given is connected exactly when its matches,
as a feed, are. A given that only a child specification uses is allowed
(`child-uses-a-given`), and `isConnected` refuses it. -/
theorem isConnected_asFeed {s : Specification} (hu : usedGivens s.given s.matchList = s.given) :
    isConnected (asFeed s.given s.matchList) = isConnected s := by
  rw [asFeed, hu]; rfl

end JinagaSpec
