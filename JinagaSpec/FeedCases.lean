import JinagaSpec.Build
import JinagaSpec.Semantics
import JinagaSpec.DistinctLabelsCases

/-!
# Named cases for feeds

Each is a specification, the subscription's givens, and a graph a replicator
holds. `lake exe vectors` writes one feed vector per case (`vectors/feeds/`):
the feeds `buildFeeds` makes, the facts they deliver on the graph, and the
results, which a replica holding those facts and their predecessors reads
(`feeds_cover`), child specifications' included. `check-feeds` checks each. Several are where `jinaga.js`'s
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

/-- A mutable property, the latest of its values: `label` of type `type`, of the
fact `owner`, with no `next` that replaces it. -/
private def latest (label type ownerRole ownerType owner : Name) : Match :=
  unknown label type [path [r ownerRole ownerType] owner,
    notExists [unknown "next" type [path [r "prior" type] label]]]

/-- Chapter 12's Entity List: a restaurant's servers, unless terminated and not
rehired, each with its current names and rates. -/
def serversSpec : Specification :=
  spec [("r", "Restaurant")]
    [unknown "s" "Server" [path [r "restaurant" "Restaurant"] "r",
      notExists [unknown "st" "Terminated" [path [r "server" "Server"] "s",
        notExists [unknown "sr" "Rehired" [path [r "terminated" "Terminated"] "st"]]]]]]
    (.composite [.fact "server" "s",
      .specification "names" [latest "sn" "Name" "server" "Server" "s"] (fact "sn"),
      .specification "rates" [latest "rt" "Rate" "server" "Server" "s"] (fact "rt")])

/-- An event's names, unless its delete stands: a delete stands unless restored,
a restore unless revoked, and a revoke unless unrevoked. Four levels of negative
condition, where an exclusion can be contested: a restore revoked twice, one
revocation undone. No feeds that page by bookmark withhold its names exactly
(`exact_deferral_impossible`, `Proofs/Contested.lean`). -/
def contested : Specification :=
  spec [("t", "Tenant")]
    [unknown "e" "Event" [path [r "tenant" "Tenant"] "t",
      notExists [unknown "d" "Delete" [path [r "event" "Event"] "e",
        notExists [unknown "x" "Restore" [path [r "delete" "Delete"] "d",
          notExists [unknown "v" "Revoke" [path [r "restore" "Restore"] "x",
            notExists [unknown "z" "Unrevoke" [path [r "revoke" "Revoke"] "v"]]]]]]]]],
     unknown "n" "Name" [path [r "event" "Event"] "e"]]
    (fact "n")

def feedCases : List FeedCase := [
  { name := "sibling-conditions-share-a-name"
    description := "An account with no freeze and with a mirror, each condition declaring y. The feeds are those of the renamed specification (withDistinctLabels), whose second y is y2."
    source := "jinaga/jinaga-spec#71"
    spec := siblingConditionsShareName
    givens := [("p1", 0)]
    graph := [⟨0, "Tenant", []⟩, ⟨1, "Account", [("tenant", 0)]⟩, ⟨2, "Mirror", [("account", 1)]⟩,
      ⟨3, "Account", [("tenant", 0)]⟩, ⟨4, "Freeze", [("account", 3)]⟩, ⟨5, "Mirror", [("account", 3)]⟩] },
  { name := "condition-and-later-match-share-a-name"
    description := "An event with no delete, and its names, the condition and the match both declaring n. The feeds are those of the renamed specification, whose match is n2."
    source := "jinaga/jinaga-spec#71"
    spec := conditionAndMatchShareName
    givens := [("t", 0)]
    graph := [⟨0, "Tenant", []⟩, ⟨1, "Event", [("tenant", 0)]⟩, ⟨2, "Name", [("event", 1)]⟩,
      ⟨3, "Event", [("tenant", 0)]⟩, ⟨4, "Delete", [("event", 3)]⟩, ⟨5, "Name", [("event", 3)]⟩] },
  { name := "repeated-label-with-next"
    description := "jinaga.js's vector: servers not terminated unless rehired, and their current rates. The negative condition and the child specification both declare sr; the child's is sr2 in the renamed specification."
    source := "jinaga/jinaga.js#387, jinaga/jinaga.js#426"
    spec := rehiredServerRates true
    givens := [("r", 0)]
    graph := [⟨0, "Restaurant", []⟩, ⟨1, "Server", [("restaurant", 0)]⟩, ⟨2, "Terminated", [("server", 1)]⟩,
      ⟨3, "Rehired", [("terminated", 2)]⟩, ⟨4, "Rate", [("server", 1)]⟩, ⟨5, "Rate", [("server", 1), ("prior", 4)]⟩,
      ⟨6, "Server", [("restaurant", 0)]⟩, ⟨7, "Terminated", [("server", 6)]⟩, ⟨8, "Rate", [("server", 6)]⟩] },
  { name := "repeated-label-without-next"
    description := "jinaga.js's vector: servers not terminated unless rehired, and their rates. The negative condition and the child specification both declare sr; the child's is sr2 in the renamed specification."
    source := "jinaga/jinaga.js#387, jinaga/jinaga.js#426"
    spec := rehiredServerRates false
    givens := [("r", 0)]
    graph := [⟨0, "Restaurant", []⟩, ⟨1, "Server", [("restaurant", 0)]⟩, ⟨2, "Terminated", [("server", 1)]⟩,
      ⟨3, "Rehired", [("terminated", 2)]⟩, ⟨4, "Rate", [("server", 1)]⟩,
      ⟨6, "Server", [("restaurant", 0)]⟩, ⟨7, "Terminated", [("server", 6)]⟩, ⟨8, "Rate", [("server", 6)]⟩] },
  { name := "candidate-taken"
    description := "Two conditions declare y and a match declares y2, so the renamed specification's second y is y3."
    source := "jinaga/jinaga-spec#71"
    spec := candidateTaken
    givens := [("p1", 0)]
    graph := [⟨0, "Tenant", []⟩, ⟨1, "Account", [("tenant", 0)]⟩, ⟨2, "Mirror", [("account", 1)]⟩,
      ⟨3, "Owner", [("account", 1)]⟩, ⟨4, "Account", [("tenant", 0)]⟩, ⟨5, "Freeze", [("account", 4)]⟩,
      ⟨6, "Mirror", [("account", 4)]⟩, ⟨7, "Owner", [("account", 4)]⟩] },
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
    description := "A delete restored, whose restore is revoked twice, one revocation itself undone. The event stays deleted, but the restoring feed through the undone revocation still delivers its name. No consistent, append-only feeds withhold it on every such graph (exact_deferral_impossible). Deferral is guaranteed only when no witness of the exclusion has a cancelling fact."
    source := "feeds_defer"
    spec := contested
    givens := [("t", 0)]
    graph := [⟨0, "Tenant", []⟩, ⟨1, "Event", [("tenant", 0)]⟩, ⟨2, "Delete", [("event", 1)]⟩,
      ⟨3, "Restore", [("delete", 2)]⟩, ⟨4, "Revoke", [("restore", 3)]⟩, ⟨5, "Revoke", [("restore", 3)]⟩,
      ⟨6, "Unrevoke", [("revoke", 5)]⟩, ⟨7, "Name", [("event", 1)]⟩] },
  { name := "restore-revoked-and-both-unrevoked"
    description := "restore-revoked-and-unrevoked with the other revocation undone too. The restore stands, the delete is cancelled, and the name is a result, delivered through the restoring feed. Its tuple binds an unrevoke. A tuple that binds no unrevoke would have been there before the last one arrived, while the event was deleted, so withholding the name in restore-revoked-and-unrevoked would take a tuple binding every unrevoke (exact_deferral_impossible)."
    source := "exact_deferral_impossible"
    spec := contested
    givens := [("t", 0)]
    graph := [⟨0, "Tenant", []⟩, ⟨1, "Event", [("tenant", 0)]⟩, ⟨2, "Delete", [("event", 1)]⟩,
      ⟨3, "Restore", [("delete", 2)]⟩, ⟨4, "Revoke", [("restore", 3)]⟩, ⟨5, "Revoke", [("restore", 3)]⟩,
      ⟨6, "Unrevoke", [("revoke", 5)]⟩, ⟨7, "Name", [("event", 1)]⟩, ⟨8, "Unrevoke", [("revoke", 4)]⟩] },
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
      ⟨3, "Message", [("channel", 1)]⟩, ⟨4, "Read", [("message", 2), ("user", 0)]⟩] },
  { name := "child-of-excluded"
    description := "Chapter 12's Entity List. A server's names and rates are child specifications, each the latest of a mutable property. The filtered and restoring feeds of the server go on to them; the excluding feed does not, so the name of a terminated server is deferred until it is rehired. The sibling child specifications both declare next, which only one feed at a time binds."
    source := "The Art of Immutable Architecture, chapter 12, Projections"
    spec := serversSpec
    givens := [("r", 0)]
    graph := [⟨0, "Restaurant", []⟩, ⟨1, "Server", [("restaurant", 0)]⟩, ⟨2, "Name", [("server", 1)]⟩,
      ⟨3, "Name", [("server", 1), ("prior", 2)]⟩, ⟨4, "Rate", [("server", 1)]⟩,
      ⟨5, "Server", [("restaurant", 0)]⟩, ⟨6, "Terminated", [("server", 5)]⟩, ⟨7, "Name", [("server", 5)]⟩,
      ⟨8, "Server", [("restaurant", 0)]⟩, ⟨9, "Terminated", [("server", 8)]⟩, ⟨10, "Rehired", [("terminated", 9)]⟩,
      ⟨11, "Name", [("server", 8)]⟩, ⟨12, "Rate", [("server", 8)]⟩] },
  { name := "grandchild"
    description := "A child specification with a child specification of its own: each event's names, and each name's notes that are not retracted. The grandchild's feeds go on from the child's positive feeds, and its negative condition makes an excluding feed of its own."
    source := "The Art of Immutable Architecture, chapter 12: recursively produce feeds from the projections of those child specifications"
    spec := spec [("t", "Tenant")]
      [unknown "e" "Event" [path [r "tenant" "Tenant"] "t"]]
      (.composite [.fact "event" "e",
        .specification "names" [unknown "n" "Name" [path [r "event" "Event"] "e"]]
          (.composite [.fact "name" "n",
            .specification "notes" [unknown "x" "Note" [path [r "name" "Name"] "n",
              notExists [unknown "rx" "Retract" [path [r "note" "Note"] "x"]]]] (fact "x")])])
    givens := [("t", 0)]
    graph := [⟨0, "Tenant", []⟩, ⟨1, "Event", [("tenant", 0)]⟩, ⟨2, "Name", [("event", 1)]⟩,
      ⟨3, "Note", [("name", 2)]⟩, ⟨4, "Note", [("name", 2)]⟩, ⟨5, "Retract", [("note", 4)]⟩,
      ⟨6, "Name", [("event", 1)]⟩, ⟨7, "Event", [("tenant", 0)]⟩] },
  { name := "child-uses-a-given"
    description := "Chapter 12's comments for a user: every post of a blog, and the user's own comments on each. The post feed takes only the blog; the comment feed, a child specification's, takes the blog and the user."
    source := "The Art of Immutable Architecture, chapter 12, Unused Givens"
    spec := spec [("b", "Blog"), ("u", "User")]
      [unknown "p" "Post" [path [r "blog" "Blog"] "b"]]
      (.composite [.fact "post" "p",
        .specification "myComments" [unknown "c" "Comment" [path [r "post" "Post"] "p", path [r "author" "User"] "u"]]
          (fact "c")])
    givens := [("b", 0), ("u", 1)]
    graph := [⟨0, "Blog", []⟩, ⟨1, "User", []⟩, ⟨2, "User", []⟩, ⟨3, "Post", [("blog", 0)]⟩,
      ⟨4, "Comment", [("post", 3), ("author", 1)]⟩, ⟨5, "Comment", [("post", 3), ("author", 2)]⟩,
      ⟨6, "Post", [("blog", 0)]⟩] }]

def FeedCase.env (c : FeedCase) : Env := c.spec.bindGivens (c.spec.given.map fun l => (c.givens.lookup l.name).getD 0)

end JinagaSpec
