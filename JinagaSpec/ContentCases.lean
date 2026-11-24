import JinagaSpec.Build
import JinagaSpec.Content

/-!
# Named cases for the content store

Each is a history of saves, uploads and reads on one model, documents in
groups: `(g: Group) { d: Document [ d->group: Group = g ] } => d`, or the same
documents as a child specification of their group. `lake exe
vectors` writes one content vector per case (`vectors/content/`): every
upload's and read's response from `Replicator.write` and `Replicator.read`, and
the objects stored at the end. The cached replicator (`ContentCache.lean`)
must give the same responses (`cached_read`), so every vector checks a cache
too. Each case names the mutants of `ContentMutants.lean` it must catch, the
handlers' and the cache's, and the generator refuses a case that does not
catch them, or a set of cases that leaves a mutant uncaught.

A save is a batch of facts, stored only if it is fresh (`isFresh`) and names
no predecessor outside the store and the batch (`isClosed`).

The policy is data, so that a port's harness can supply it in place of its
model, rules and hash function:

* the hash of bytes is `"#"` followed by the bytes;
* a content fact's content hash and maximum size are listed in `content`; a
  fact not listed is not content-bearing;
* the authorization rules let a user create exactly the facts `writers` pairs
  them with;
* the distribution rules are one rule, `rule`: the specification has one
  feed, which a user may read when `rule`, run with the proof's givens, names
  them (`Policy.distributes`). The rule is membership in the document's group,
  which a `Removal` revokes and a `Restore` of that removal gives back
  (`groupMembers`, `documentGroupMembers`).

Every case starts from the same store: the users' facts, both groups, Alice a
member of group A and Mallory of group B. Eve is a member of neither.
-/
namespace JinagaSpec

open Build

inductive ContentStep where
  | event (e : Event)
  | read (user : Option User) (key : FactId) (givens : List FactId)

def documentsInGroup : Specification :=
  spec [("g", "Group")] [unknown "d" "Document" [path [role "group" "Group"] "g"]] (fact "d")

/-- The same documents, as a child specification of their group:
`(g: Group) { } => { documents = { d: Document [ d->group: Group = g ] } => d }`. -/
def groupWithDocuments : Specification :=
  spec [("g", "Group")] []
    (.composite [.specification "documents" [unknown "d" "Document" [path [role "group" "Group"] "g"]] (fact "d")])

/-- `(g: Group) { d: Document [ d->group: Group = g ] } => { group = g, document = d }`:
a given and an unknown, both projected. -/
def groupAndDocument : Specification :=
  spec [("g", "Group")] [unknown "d" "Document" [path [role "group" "Group"] "g"]]
    (.composite [.fact "group" "g", .fact "document" "d"])

/-- The documents not deleted: `(g: Group) { d: Document [ d->group: Group = g,
!E { x: Deleted [ x->document: Document = d ] } ] } => d`. -/
def liveDocumentsInGroup : Specification :=
  spec [("g", "Group")] [unknown "d" "Document" [path [role "group" "Group"] "g",
    notExists [unknown "x" "Deleted" [path [role "document" "Document"] "d"]]]] (fact "d")

/-- `(g: Group) { } => g`. -/
def theGroup : Specification := spec [("g", "Group")] [] (fact "g")

/-- `(d: Document) { } => d`: the content fact as its own given. -/
def theDocument : Specification := spec [("d", "Document")] [] (fact "d")

/-- A child specification that declares its parent's unknown again:
`(g: Group) { d: Document [ d->group: Group = g ] } => { again = { d: Document [ d->group: Group = g ] } => d }`.
The top level is well formed; the child, as a descendant, is not. -/
def redeclaringChild : Specification :=
  let documents := [unknown "d" "Document" [path [role "group" "Group"] "g"]]
  spec [("g", "Group")] documents (.composite [.specification "again" documents (fact "d")])

/-- A specification that declares the label the replicator pins the content
fact to: `(g: Group) { __f: Document [ __f->group: Group = g ] } => __f`. -/
def declaresPinLabel : Specification :=
  spec [("g", "Group")] [unknown pinLabel "Document" [path [role "group" "Group"] "g"]] (fact pinLabel)

/-- The current members of a group, the distribution rule for its documents:
`(g: Group) { m: Member [ m->group: Group = g->groupOf, !E { r: Removal [ r->member: Member = m,
!E { s: Restore [ s->removal: Removal = r ] } ] } ] u: Jinaga.User [ u = m->user: Jinaga.User ] } => u`.
The group is a fact of type `group`, reached from the given by `groupOf`. A
`Removal` of the membership revokes it, and a `Restore` of the removal gives it
back. -/
def membersOf (given : Name × Name) (group : Name) (groupOf : List Role) : Specification :=
  spec [given] [
    unknown "m" "Member" [path [role "group" group] given.1 groupOf,
      notExists [unknown "r" "Removal" [path [role "member" "Member"] "m",
        notExists [unknown "s" "Restore" [path [role "removal" "Removal"] "r"]]]]],
    unknown "u" "Jinaga.User" [path [] "m" [role "user" "Jinaga.User"]]] (fact "u")

/-- The current members of the given group. -/
def groupMembers : Specification := membersOf ("g", "Group") "Group" []

/-- The current members of the given document's group. -/
def documentGroupMembers : Specification := membersOf ("d", "Document") "Group" [role "group" "Group"]

structure ContentCase where
  name : String
  description : String
  source : String
  /-- Content key, content hash, maximum size in characters. -/
  content : List (FactId × Hash × Nat)
  writers : List (User × FactId)
  /-- The distribution rule, run with the proof's givens. -/
  rule : Specification := groupMembers
  /-- The specification every read's proof runs. -/
  spec : Specification := documentsInGroup
  steps : List ContentStep
  /-- Labels of the mutants (`ContentMutants.lean`) this case must catch. -/
  catches : List String

def ContentCase.policy (c : ContentCase) : Policy where
  hash b := "#" ++ b
  contentHash f := (c.content.find? (·.1 == f.id)).map (·.2.1)
  fits f b := (c.content.find? (·.1 == f.id)).any (b.length ≤ ·.2.2)
  mayCreate u _ f := c.writers.contains (u, f.id)
  distribution _ gs := [[{ spec := c.rule, givens := gs }]]

namespace ContentCases

def alice : User := 100
def mallory : User := 101
def eve : User := 102

def groupA : Fact := { id := 1, type := "Group", predecessors := [] }
def groupB : Fact := { id := 2, type := "Group", predecessors := [] }
/-- Alice's plan, in group A. -/
def plan : Fact := { id := 10, type := "Document", predecessors := [("group", 1)] }
/-- Mallory's document in group B, naming the same content hash as `plan`. -/
def spoof : Fact := { id := 11, type := "Document", predecessors := [("group", 2)] }
/-- A document in group A whose maximum size is four characters. -/
def notes : Fact := { id := 12, type := "Document", predecessors := [("group", 1)] }
/-- The plan, deleted. -/
def planDeleted : Fact := { id := 30, type := "Deleted", predecessors := [("document", 10)] }
/-- A fact of a type that is not content-bearing. -/
def comment : Fact := { id := 20, type := "Comment", predecessors := [("document", 10)] }

def content : List (FactId × Hash × Nat) :=
  [(10, "#plan", 100), (11, "#plan", 100), (12, "#notes!", 4), (13, "#minutes", 100)]
def writers : List (User × FactId) := [(alice, 10), (alice, 12), (alice, 13), (alice, 20), (mallory, 11)]

def save (f : Fact) : ContentStep := .event (.save [f])
def saveAll (B : List Fact) : ContentStep := .event (.save B)

def user (u : User) : Fact := { id := u, type := "Jinaga.User", predecessors := [] }
def member (id : FactId) (group : Fact) (u : User) : Fact :=
  { id, type := "Member", predecessors := [("group", group.id), ("user", u)] }
def removal (id : FactId) (m : Fact) : Fact := { id, type := "Removal", predecessors := [("member", m.id)] }
def restore (id : FactId) (r : Fact) : Fact := { id, type := "Restore", predecessors := [("removal", r.id)] }

def aliceInA : Fact := member 40 groupA alice
def malloryInB : Fact := member 41 groupB mallory
/-- Alice's membership of group A, removed. -/
def aliceRemoved : Fact := removal 42 aliceInA
/-- The removal, undone. -/
def aliceRestored : Fact := restore 43 aliceRemoved

/-- Group C, its minutes, and Alice's membership of it, which arrive together. -/
def groupC : Fact := { id := 3, type := "Group", predecessors := [] }
def minutes : Fact := { id := 13, type := "Document", predecessors := [("group", 3)] }
def aliceInC : Fact := member 44 groupC alice

/-- The store every case starts from, saved as one batch. -/
def initial : List ContentStep :=
  [saveAll [user alice, user mallory, user eve, groupA, groupB, aliceInA, malloryInB]]
def write (u : Option User) (key : FactId) (o : Bytes) : ContentStep := .event (.write u key o)

/-- Alice's plan saved and uploaded. -/
def planStored : List ContentStep := [save plan, write alice 10 "plan"]

def make (name description source : String) (steps : List ContentStep) (catches : List String := [])
    (spec : Specification := documentsInGroup) (rule : Specification := groupMembers) : ContentCase :=
  { name, description, source, content, writers, rule, spec, steps := initial ++ steps, catches }

end ContentCases

open ContentCases in
def contentCases : List ContentCase := [
  make "upload-then-read"
    "Before the upload an admitted reader gets 404 not_uploaded; the upload is stored; a repeat is accepted and changes nothing; then the reader gets the bytes."
    "RW-8, RR-7, SEC-1"
    [save plan, .read alice 10 [1], write alice 10 "plan", write alice 10 "plan", .read alice 10 [1]],
  make "no-token"
    "Without a valid token both endpoints answer 401, and nothing is stored."
    "RW-1, RR-2"
    [save plan, write none 10 "plan", .read none 10 [1]],
  make "writer-not-authorized"
    "Eve may not create the plan, so her upload of the right bytes is refused and nothing is stored."
    "RW-4, SEC-3"
    [save plan, write eve 10 "plan", .read alice 10 [1]]
    ["SEC-3: authorize the fact's presence, not the writer"],
  make "bytes-do-not-match"
    "Bytes whose hash is not the content hash are refused with 422, and nothing is stored."
    "RW-5, SEC-2"
    [save plan, write alice 10 "plam", .read alice 10 [1]]
    ["SEC-2: store bytes without hashing them"],
  make "too-large"
    "Bytes that match the content hash but exceed the declared maximum are refused with 413."
    "MD-2, RW-6"
    [save notes, write alice 12 "notes!", .read alice 12 [1]],
  make "not-content-bearing"
    "A fact whose type is not declared content-bearing takes no object: 422."
    "RW-3"
    (planStored ++ [save comment, write alice 20 "x"]),
  make "fact-missing"
    "An upload for a fact the store does not hold yet is refused, and accepted once the fact is saved."
    "RW-2, CW-8"
    [write alice 10 "plan", save plan, write alice 10 "plan", .read alice 10 [1]],
  make "spoof-same-hash"
    "Mallory, who knows the plan's hash, mints a document in her own group naming it. Her read of that document is admitted, and gets 404: no object was ever uploaded under its key. Her read of the plan is 403."
    "ST-1, SEC-4"
    (planStored ++ [save spoof, .read mallory 11 [2], .read mallory 10 [2]])
    ["SEC-4: look an object up by its content hash"],
  make "hash-shortcut"
    "Mallory uploads no bytes for her document, counting on the replicator already holding bytes of that hash. Refused with 422; her read stays 404."
    "ST-3, SEC-3"
    (planStored ++ [save spoof, write mallory 11 "", .read mallory 11 [2]])
    ["SEC-3: map a key to stored bytes of the same hash"],
  make "repeat-by-refused-writer"
    "Eve, who may create neither document, uploads to one that holds an object and one that does not. Both are 403: a refused writer does not learn which is stored."
    "RW-4, RW-8, SEC-5"
    (planStored ++ [save notes, write eve 10 "plan", write eve 12 "x"])
    ["SEC-5: answer a repeat upload before checking the writer"],
  make "reader-not-distributed"
    "Eve's proof yields the plan, but the distribution rules do not let her run it: 403."
    "RR-3, SEC-1"
    (planStored ++ [.read eve 10 [1]])
    ["SEC-1: no distribution check"],
  make "proof-does-not-yield"
    "Mallory may run the specification for group B, but it does not yield the plan, which is in group A: 403."
    "RR-4, SEC-1"
    (planStored ++ [.read mallory 10 [2]])
    ["SEC-1: no yields check"],
  make "no-existence-leak"
    "To a reader the rules do not admit, a stored object and a missing one get the same 403."
    "RR-5, SEC-5"
    (planStored ++ [save notes, .read eve 10 [1], .read eve 12 [1]])
    ["SEC-5: answer 404 before checking the proof"],
  make "child-specification-yields"
    "Alice's proof reaches the plan through a child specification of its group, as a client's nested query does. It yields the plan, so she gets the bytes; the same proof for group B does not."
    "RR-4, CR-1"
    (planStored ++ [.read alice 10 [1], .read mallory 10 [2]])
    ["read_admitted: yields ignores child specifications"]
    groupWithDocuments,
  make "unbound-given"
    "A proof that binds fewer givens, or more, than the specification declares is refused with 400."
    "RR-1"
    (planStored ++ [.read alice 10 [], .read alice 10 [1, 1]]),
  make "ill-formed-child-specification"
    "The proof's child specification declares `d` again, which its parent declares. The top level is well formed, but the child, as a specification of its own, is not: 400."
    "RR-1"
    (planStored ++ [.read alice 10 [1]])
    ["RR-1: check only the top-level specification"]
    redeclaringChild,
  make "reserved-label"
    "The proof's specification declares `__f`, the label the replicator pins the content fact to: 400."
    "RR-1"
    (planStored ++ [.read alice 10 [1]]) [] declaresPinLabel,
  make "given-and-unknown-projected"
    "The proof projects the group, a given, and the document, an unknown. The plan is confirmed through the second label, by pinning `d` to it. The group is confirmed by its given alone; it has no object, so 404."
    "RR-4"
    (planStored ++ [.read alice 10 [1], .read alice 1 [1]])
    ["read_admitted: bind only the first projected label"]
    groupAndDocument,
  make "pinned-match-keeps-conditions"
    "The proof's document match also asks that the document is not deleted. Pinning `d` to the plan keeps that condition: Alice gets the bytes until the plan is deleted, then 403."
    "RR-4"
    (planStored ++ [.read alice 10 [1], save planDeleted, .read alice 10 [1]])
    ["SEC-1: drop the pinned match's own conditions"]
    liveDocumentsInGroup,
  make "given-not-held"
    "The proof binds its Group given to the plan, a Document. The store does not hold it as a Group, so the specification reads nothing: 403, though its projected label is bound to the plan."
    "RR-4"
    (planStored ++ [.read alice 10 [10]])
    ["confirms_eq_yields: skip the check that the givens are held"]
    theGroup documentGroupMembers,
  make "content-fact-as-given"
    "`(d: Document) { } => d` with `d` bound to the plan yields the plan on every store that holds it. Here SEC-1 is only as strong as the distribution rules."
    "RR-4, SEC-1"
    (planStored ++ [.read alice 10 [10]]) [] theDocument documentGroupMembers,
  make "given-not-in-store"
    "Alice's proof names a group the store does not hold: neither the proof nor the rule run with it reads anything, so 403."
    "RR-4"
    (planStored ++ [.read alice 10 [3]]),
  make "membership-revoked"
    "Alice reads the plan; then her membership of group A is removed, and her next read is 403. A cache must drop her entry on the removal: a fact of neither the plan's type nor any type the reader's proof names, which the rule's negative existential condition reads."
    "NF-2, SEC-7"
    (planStored ++ [.read alice 10 [1], save aliceRemoved, .read alice 10 [1]])
    ["cached_read: invalidate only on a fact of the content fact's type",
     "cached_read: never invalidate on a revocation",
     "cached_read: invalidate on the reader's proof only, never the rules"],
  make "membership-restored"
    "Alice's membership is removed and she is refused; then the removal is undone, and she gets the plan again. SEC-7 as written would forbid that second answer; a cache must drop the refusal."
    "NF-2, SEC-7"
    (planStored ++ [save aliceRemoved, .read alice 10 [1], save aliceRestored, .read alice 10 [1]])
    ["cached_read: keep the entries the rules refused"],
  make "given-arrives"
    "Alice's proof is the plan itself, `(d: Document) { } => d`, and the rule the members of its group. Before the plan is saved she is refused; once it is, she is admitted. Only the plan arriving as both proofs' given changes either."
    "NF-2, RR-4"
    [.read alice 10 [10], save plan, write alice 10 "plan", .read alice 10 [10]]
    ["cached_read: ignore a given arriving in the batch"]
    theDocument documentGroupMembers,
  make "batch-arrives-together"
    "Group C, its minutes and Alice's membership of it arrive in one batch. Before it Alice is refused the minutes; after it she is admitted, and told nothing is uploaded. No fact of the batch read without the others finds the change."
    "NF-2, CR-3"
    [.read alice 13 [3], saveAll [groupC, minutes, aliceInC], .read alice 13 [3]]
    ["cached_read: read each fact of a batch alone"],
  make "batch-not-fresh"
    "A batch that repeats a fact the store holds is not fresh, and is not stored: the plan in it is not saved, so its upload is refused. A replicator first drops the facts it already holds; the plan alone is fresh, and is stored."
    "NF-2, RW-2"
    [saveAll [groupA, plan], write alice 10 "plan", save plan, write alice 10 "plan", .read alice 10 [1]]
    ["save_fresh: store a batch without checking it is fresh"],
  make "batch-not-closed"
    "A batch that names a predecessor neither the store nor the batch holds is not stored: Alice's membership of group C, saved before group C, is refused. Stored, it would name group C, so no batch holding group C, and the minutes in it, would be fresh again. Saved after group C, the membership is stored, and Alice reads the minutes."
    "NF-2"
    [save aliceInC, saveAll [groupC, minutes], save aliceInC, write alice 13 "minutes", .read alice 13 [3]]
    ["run_closed: store a batch that names a predecessor not stored"]
]

end JinagaSpec
