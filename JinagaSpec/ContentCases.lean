import JinagaSpec.Build
import JinagaSpec.Content

/-!
# Named cases for the content store

Each is a history of saves, uploads and reads on one model, documents in
groups: `(g: Group) { d: Document [ d->group: Group = g ] } => d`, or the same
documents as a child specification of their group. `lake exe
vectors` writes one content vector per case (`vectors/content/`): every
upload's and read's response from `Replicator.write` and `Replicator.read`, and
the objects stored at the end. Each case names the mutants of
`ContentMutants.lean` it must catch, and the generator refuses a case that does
not catch them, or a set of cases that leaves a mutant uncaught.

The policy is data, so that a port's harness can supply it in place of its
model, rules and hash function:

* the hash of bytes is `"#"` followed by the bytes;
* a content fact's content hash and maximum size are listed in `content`; a
  fact not listed is not content-bearing;
* the authorization rules let a user create exactly the facts `writers` pairs
  them with;
* the distribution rules let a user run the specification with exactly the
  givens `readers` pairs them with: for those givens, one feed, authorized by
  the rule proofs `(u: Jinaga.User) { } => u` run with each such reader `u`.
  Each user's fact is saved first, so that the rule yields them.
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

structure ContentCase where
  name : String
  description : String
  source : String
  /-- Content key, content hash, maximum size in characters. -/
  content : List (FactId × Hash × Nat)
  writers : List (User × FactId)
  readers : List (User × List FactId)
  /-- The specification every read's proof runs. -/
  spec : Specification := documentsInGroup
  steps : List ContentStep
  /-- Labels of the mutants (`ContentMutants.lean`) this case must catch. -/
  catches : List String

/-- A distribution rule that names one user: `(u: Jinaga.User) { } => u`. -/
def theUser : Specification := spec [("u", "Jinaga.User")] [] (fact "u")

def ContentCase.policy (c : ContentCase) : Policy where
  hash b := "#" ++ b
  contentHash f := (c.content.find? (·.1 == f.id)).map (·.2.1)
  fits f b := (c.content.find? (·.1 == f.id)).any (b.length ≤ ·.2.2)
  mayCreate u _ f := c.writers.contains (u, f.id)
  distribution _ gs := [(c.readers.filter (·.2 == gs)).map fun (u, _) => { spec := theUser, givens := [u] }]

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

def content : List (FactId × Hash × Nat) := [(10, "#plan", 100), (11, "#plan", 100), (12, "#notes!", 4)]
def writers : List (User × FactId) := [(alice, 10), (alice, 12), (alice, 20), (mallory, 11)]
def readers : List (User × List FactId) := [(alice, [1]), (alice, [3]), (mallory, [2])]

def save (f : Fact) : ContentStep := .event (.save [f])

/-- The users' own facts, which the distribution rules name. -/
def users : List ContentStep := [alice, mallory, eve].map fun u => save { id := u, type := "Jinaga.User", predecessors := [] }
def write (u : Option User) (key : FactId) (o : Bytes) : ContentStep := .event (.write u key o)

/-- Alice's plan saved and uploaded. -/
def planStored : List ContentStep := [save groupA, save plan, write alice 10 "plan"]

def make (name description source : String) (steps : List ContentStep) (catches : List String := [])
    (spec : Specification := documentsInGroup) (moreReaders : List (User × List FactId) := []) : ContentCase :=
  { name, description, source, content, writers, readers := readers ++ moreReaders, spec, steps := users ++ steps, catches }

end ContentCases

open ContentCases in
def contentCases : List ContentCase := [
  make "upload-then-read"
    "Before the upload an admitted reader gets 404 not_uploaded; the upload is stored; a repeat is accepted and changes nothing; then the reader gets the bytes."
    "RW-8, RR-7, SEC-1"
    [save groupA, save plan, .read alice 10 [1], write alice 10 "plan", write alice 10 "plan", .read alice 10 [1]],
  make "no-token"
    "Without a valid token both endpoints answer 401, and nothing is stored."
    "RW-1, RR-2"
    [save groupA, save plan, write none 10 "plan", .read none 10 [1]],
  make "writer-not-authorized"
    "Eve may not create the plan, so her upload of the right bytes is refused and nothing is stored."
    "RW-4, SEC-3"
    [save groupA, save plan, write eve 10 "plan", .read alice 10 [1]]
    ["SEC-3: authorize the fact's presence, not the writer"],
  make "bytes-do-not-match"
    "Bytes whose hash is not the content hash are refused with 422, and nothing is stored."
    "RW-5, SEC-2"
    [save groupA, save plan, write alice 10 "plam", .read alice 10 [1]]
    ["SEC-2: store bytes without hashing them"],
  make "too-large"
    "Bytes that match the content hash but exceed the declared maximum are refused with 413."
    "MD-2, RW-6"
    [save groupA, save notes, write alice 12 "notes!", .read alice 12 [1]],
  make "not-content-bearing"
    "A fact whose type is not declared content-bearing takes no object: 422."
    "RW-3"
    (planStored ++ [save comment, write alice 20 "x"]),
  make "fact-missing"
    "An upload for a fact the store does not hold yet is refused, and accepted once the fact is saved."
    "RW-2, CW-8"
    [save groupA, write alice 10 "plan", save plan, write alice 10 "plan", .read alice 10 [1]],
  make "spoof-same-hash"
    "Mallory, who knows the plan's hash, mints a document in her own group naming it. Her read of that document is admitted, and gets 404: no object was ever uploaded under its key. Her read of the plan is 403."
    "ST-1, SEC-4"
    (planStored ++ [save groupB, save spoof, .read mallory 11 [2], .read mallory 10 [2]])
    ["SEC-4: look an object up by its content hash"],
  make "hash-shortcut"
    "Mallory uploads no bytes for her document, counting on the replicator already holding bytes of that hash. Refused with 422; her read stays 404."
    "ST-3, SEC-3"
    (planStored ++ [save groupB, save spoof, write mallory 11 "", .read mallory 11 [2]])
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
    (planStored ++ [save groupB, .read mallory 10 [2]])
    ["SEC-1: no yields check"],
  make "no-existence-leak"
    "To a reader the rules do not admit, a stored object and a missing one get the same 403."
    "RR-5, SEC-5"
    (planStored ++ [save notes, .read eve 10 [1], .read eve 12 [1]])
    ["SEC-5: answer 404 before checking the proof"],
  make "child-specification-yields"
    "Alice's proof reaches the plan through a child specification of its group, as a client's nested query does. It yields the plan, so she gets the bytes; the same proof for group B does not."
    "RR-4, CR-1"
    (planStored ++ [save groupB, .read alice 10 [1], .read mallory 10 [2]])
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
    theGroup [(alice, [10])],
  make "content-fact-as-given"
    "`(d: Document) { } => d` with `d` bound to the plan yields the plan on every store that holds it. Here SEC-1 is only as strong as the distribution rules."
    "RR-4, SEC-1"
    (planStored ++ [.read alice 10 [10]]) [] theDocument [(alice, [10])],
  make "given-not-in-store"
    "The distribution rules admit a proof whose given the store does not hold; it yields nothing, so 403."
    "RR-4"
    (planStored ++ [.read alice 10 [3]])
]

end JinagaSpec
