import JinagaSpec.Build
import JinagaSpec.Semantics

/-!
# Named cases for feeds

Each is a specification, the subscription's givens, and a graph a replicator
holds. `lake exe vectors` writes one feed vector per case (`vectors/feeds/`):
the feeds `buildFeeds` makes, the facts they deliver on the graph, and the
results, which a replica holding those facts and their predecessors reads
(`feeds_cover`). `check-feeds` checks each. Several are where `jinaga.js`'s
`buildFeeds` misses a result (`docs/findings.md`).
-/
namespace JinagaSpec

open Build

structure FeedCase where
  name : String
  description : String
  source : String
  spec : Specification
  givens : List (Name × FactId)
  graph : Graph

private def r (n t : Name) : Role := role n t

/-- An event, unless it has a delete that is not cancelled. `cancel` lists the
negative conditions on the delete. -/
private def eventSpec (cancel : List Condition) : Specification :=
  spec [("t", "Tenant")]
    [unknown "e" "Event" [path [r "tenant" "Tenant"] "t",
      notExists [unknown "d" "Delete" ([path [r "event" "Event"] "e"] ++ cancel)]],
     unknown "n" "Name" [path [r "event" "Event"] "e"]]
    (.composite [.fact "event" "e", .fact "name" "n"])

private def restored : Condition := notExists [unknown "x" "Restore" [path [r "delete" "Delete"] "d"]]
private def undone : Condition := notExists [unknown "u" "Undo" [path [r "delete" "Delete"] "d"]]

def feedCases : List FeedCase := [
  { name := "not-exists-excludes"
    description := "One notExists. The ordinary feed is filtered by it; the excluding feed delivers the Done that removes a task, and stops."
    source := "jinaga-server feeds"
    spec := spec [("p1", "Root")]
      [unknown "t" "Task" [path [r "root" "Root"] "p1",
        notExists [unknown "d" "Done" [path [r "task" "Task"] "t"]]]]
      (fact "t")
    givens := [("p1", 0)]
    graph := [⟨0, "Root", []⟩, ⟨1, "Task", [("root", 0)]⟩, ⟨2, "Done", [("task", 1)]⟩,
      ⟨3, "Task", [("root", 0)]⟩] },
  { name := "not-exists-restored"
    description := "notExists { notExists }: an event with a delete that has been restored. The ordinary feed withholds the event; the restoring feed, through the delete and the restore, delivers it and its name."
    source := "jinaga-server docs/analysis/feed-builder-nested-existential-bug.md"
    spec := eventSpec [restored]
    givens := [("t", 0)]
    graph := [⟨0, "Tenant", []⟩, ⟨1, "Event", [("tenant", 0)]⟩, ⟨2, "Delete", [("event", 1)]⟩,
      ⟨3, "Restore", [("delete", 2)]⟩, ⟨4, "Name", [("event", 1)]⟩] },
  { name := "not-exists-cancelled-twice"
    description := "A delete that is both restored and undone. A restoring feed drops the other negative conditions of the delete it restores. jinaga.js's restoring feed for the restore also asks the delete to have no undo, and the one for the undo no restore, so neither delivers the name."
    source := "check-feeds"
    spec := eventSpec [restored, undone]
    givens := [("t", 0)]
    graph := [⟨0, "Tenant", []⟩, ⟨1, "Event", [("tenant", 0)]⟩, ⟨2, "Delete", [("event", 1)]⟩,
      ⟨3, "Restore", [("delete", 2)]⟩, ⟨4, "Undo", [("delete", 2)]⟩, ⟨5, "Name", [("event", 1)]⟩] },
  { name := "not-exists-cancelled-by-second"
    description := "A delete undone, whose restore was revoked. The restoring feed for the undo drops the filter on restores. jinaga.js's keeps it, and delivers no name."
    source := "check-feeds"
    spec := eventSpec
      [notExists [unknown "x" "Restore" [path [r "delete" "Delete"] "d",
        notExists [unknown "v" "Revoke" [path [r "restore" "Restore"] "x"]]]], undone]
    givens := [("t", 0)]
    graph := [⟨0, "Tenant", []⟩, ⟨1, "Event", [("tenant", 0)]⟩, ⟨2, "Delete", [("event", 1)]⟩,
      ⟨3, "Restore", [("delete", 2)]⟩, ⟨4, "Revoke", [("restore", 3)]⟩, ⟨5, "Undo", [("delete", 2)]⟩,
      ⟨6, "Name", [("event", 1)]⟩] },
  { name := "not-exists-cancelled-by-first"
    description := "A delete restored, whose undo was revoked. The restoring feed for the restore delivers the name; a feed through the undo, its revocation, and a feed for the undo's restoring delivers nothing more."
    source := "check-feeds"
    spec := eventSpec
      [restored, notExists [unknown "u" "Undo" [path [r "delete" "Delete"] "d",
        notExists [unknown "v" "Revoke" [path [r "undo" "Undo"] "u"]]]]]
    givens := [("t", 0)]
    graph := [⟨0, "Tenant", []⟩, ⟨1, "Event", [("tenant", 0)]⟩, ⟨2, "Delete", [("event", 1)]⟩,
      ⟨3, "Restore", [("delete", 2)]⟩, ⟨4, "Undo", [("delete", 2)]⟩, ⟨5, "Revoke", [("undo", 4)]⟩,
      ⟨6, "Name", [("event", 1)]⟩] },
  { name := "restore-revoked-and-unrevoked"
    description := "A delete restored, whose restore is revoked twice, one revocation itself undone. The event stays deleted, but the restoring feed through the undone revocation still delivers its name: withholding it would need a nested negative condition, which append-only forbids. Deferral is guaranteed only when no witness of the exclusion has a cancelling fact."
    source := "feeds_defer"
    spec := spec [("t", "Tenant")]
      [unknown "e" "Event" [path [r "tenant" "Tenant"] "t",
        notExists [unknown "d" "Delete" [path [r "event" "Event"] "e",
          notExists [unknown "x" "Restore" [path [r "delete" "Delete"] "d",
            notExists [unknown "v" "Revoke" [path [r "restore" "Restore"] "x",
              notExists [unknown "z" "Unrevoke" [path [r "revoke" "Revoke"] "v"]]]]]]]]],
       unknown "n" "Name" [path [r "event" "Event"] "e"]]
      (fact "n")
    givens := [("t", 0)]
    graph := [⟨0, "Tenant", []⟩, ⟨1, "Event", [("tenant", 0)]⟩, ⟨2, "Delete", [("event", 1)]⟩,
      ⟨3, "Restore", [("delete", 2)]⟩, ⟨4, "Revoke", [("restore", 3)]⟩, ⟨5, "Revoke", [("restore", 3)]⟩,
      ⟨6, "Unrevoke", [("revoke", 5)]⟩, ⟨7, "Name", [("event", 1)]⟩] },
  { name := "exists-inside-not-exists"
    description := "notExists { exists }: an event with no approved delete. The filter is the delete's level, with the approval joined in. jinaga.js replaces the condition with its positive one, which names a label it does not bind."
    source := "check-feeds"
    spec := spec [("t", "Tenant")]
      [unknown "e" "Event" [path [r "tenant" "Tenant"] "t",
        notExists [unknown "d" "Delete" [path [r "event" "Event"] "e",
          exists' [unknown "a" "Approval" [path [r "delete" "Delete"] "d"]]]]]]
      (fact "e")
    givens := [("t", 0)]
    graph := [⟨0, "Tenant", []⟩, ⟨1, "Event", [("tenant", 0)]⟩, ⟨2, "Delete", [("event", 1)]⟩,
      ⟨3, "Event", [("tenant", 0)]⟩, ⟨4, "Delete", [("event", 3)]⟩, ⟨5, "Approval", [("delete", 4)]⟩] },
  { name := "sibling-conditions"
    description := "An account with no unthawed freeze and a mirror that is not retired. The mirror joins the account; the restoring feed for a thawed freeze goes on to the mirror's condition."
    source := "jinaga/jinaga.js#368"
    spec := spec [("p1", "Tenant")]
      [unknown "a" "Account" [path [r "tenant" "Tenant"] "p1",
        notExists [unknown "f" "Freeze" [path [r "account" "Account"] "a",
          notExists [unknown "u" "Unfreeze" [path [r "freeze" "Freeze"] "f"]]]],
        exists' [unknown "m" "Mirror" [path [r "account" "Account"] "a",
          notExists [unknown "x" "Retired" [path [r "mirror" "Mirror"] "m"]]]]]]
      (fact "a")
    givens := [("p1", 0)]
    graph := [⟨0, "Tenant", []⟩, ⟨1, "Account", [("tenant", 0)]⟩, ⟨2, "Freeze", [("account", 1)]⟩,
      ⟨3, "Unfreeze", [("freeze", 2)]⟩, ⟨4, "Mirror", [("account", 1)]⟩] },
  { name := "predecessors-only"
    description := "Every match walks to predecessors. The feed is dropped: a replica holding the given holds the results."
    source := "jinaga.js traversesSuccessors"
    spec := spec [("p", "Post")]
      [unknown "a" "Author" [path [] "p" [r "author" "Author"]]]
      (fact "a")
    givens := [("p", 1)]
    graph := [⟨0, "Author", []⟩, ⟨1, "Post", [("author", 0)]⟩] },
  { name := "two-givens"
    description := "Messages in a channel that a user has not read. The excluding feed takes both givens."
    source := "jinaga/jinaga-spec#8"
    spec := spec [("p1", "User"), ("p2", "Channel")]
      [unknown "m" "Message" [path [r "channel" "Channel"] "p2",
        notExists [unknown "rd" "Read" [path [r "message" "Message"] "m", path [r "user" "User"] "p1"]]]]
      (fact "m")
    givens := [("p1", 0), ("p2", 1)]
    graph := [⟨0, "User", []⟩, ⟨1, "Channel", []⟩, ⟨2, "Message", [("channel", 1)]⟩,
      ⟨3, "Message", [("channel", 1)]⟩, ⟨4, "Read", [("message", 2), ("user", 0)]⟩] }]

def FeedCase.env (c : FeedCase) : Env := c.spec.bindGivens (c.spec.given.map fun l => (c.givens.lookup l.name).getD 0)

end JinagaSpec
