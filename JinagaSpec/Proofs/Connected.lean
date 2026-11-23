import JinagaSpec.Connected
import JinagaSpec.Proofs.Children

/-!
# Connected descendants

* `isConnectedDeep_iff`: the check decides `ConnectedDescendants`.
* `buildFeeds_connected`: every feed of a specification that passes it is
  connected, with the givens it uses.
* `isConnected_of_connectedDescendants`: a specification that passes it, and
  whose top-level matches use every given, passes `isConnected`, the check
  the inverse runs.

`feeds_cover` and `feeds_defer` (`Proofs/Children.lean`) need no new
hypothesis: `buildFeeds` is unchanged, and the check only refuses.
-/
namespace JinagaSpec

/-- The check decides `ConnectedDescendants`. -/
theorem isConnectedDeep_iff (s : Specification) : isConnectedDeep s = true ↔ ConnectedDescendants s := by
  simp [isConnectedDeep, ConnectedDescendants, and_assoc]

/-- **Every feed is connected.** Each feed of a specification that passes the
check is connected, and its givens are the specification's givens it uses. -/
theorem buildFeeds_connected {s : Specification} (h : ConnectedDescendants s) :
    ∀ f ∈ buildFeeds s, isConnected f = true ∧ f.given = usedGivens s.given f.matchList := by
  intro f hf
  refine ⟨h.2.2 f hf, ?_⟩
  obtain ⟨F, -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hf).1
  rfl

/-- **At least as strict as `isConnected`**, for a specification whose
top-level matches use every given. A given that only a child specification
uses is allowed (`child-uses-a-given`), and `isConnected` refuses it. -/
theorem isConnected_of_connectedDescendants {s : Specification} (h : ConnectedDescendants s)
    (hu : usedGivens s.given s.matchList = s.given) : isConnected s = true := by
  have := h.1 _ (List.mem_map.mpr ⟨_, mem_paths.mpr (Or.inl rfl), rfl⟩)
  simp only [asFeed, List.append_nil, hu] at this
  exact this

end JinagaSpec
