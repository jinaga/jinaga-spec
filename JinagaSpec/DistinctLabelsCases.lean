import JinagaSpec.Build
import JinagaSpec.GivenConditions

/-!
# Named cases for renaming reused labels

Each is a specification. `lake exe vectors` writes one vector per case
(`vectors/distinct-labels/`): the specification's text, and the text
`withDistinctLabels` makes of it. The specifications that reuse a label are
also feed cases (`FeedCases.lean`), with a graph.
-/
namespace JinagaSpec

open Build

structure DistinctLabelsCase where
  name : String
  description : String
  source : String
  spec : Specification

private def r (n t : Name) : Role := role n t

/-- An account with no freeze and with a mirror, each condition declaring `y`. -/
def siblingConditionsShareName : Specification :=
  spec [("p1", "Tenant")]
    [unknown "a" "Account" [path [r "tenant" "Tenant"] "p1",
      notExists [unknown "y" "Freeze" [path [r "account" "Account"] "a"]],
      exists' [unknown "y" "Mirror" [path [r "account" "Account"] "a"]]]]
    (fact "a")

/-- An event with no delete, and its names: the condition and the match after it
declare `n`. -/
def conditionAndMatchShareName : Specification :=
  spec [("t", "Tenant")]
    [unknown "e" "Event" [path [r "tenant" "Tenant"] "t",
      notExists [unknown "n" "Delete" [path [r "event" "Event"] "e"]]],
     unknown "n" "Name" [path [r "event" "Event"] "e"]]
    (.composite [.fact "event" "e", .fact "name" "n"])

/-- jinaga.js's `rehiredServerRates` (jinaga/jinaga.js#426): a server that is
not terminated unless rehired, and its rates. The child specification declares
`sr` again, which the negative condition declared. -/
def rehiredServerRates (withNext : Bool) : Specification :=
  spec [("r", "Restaurant")]
    [unknown "s" "Server" [path [r "restaurant" "Restaurant"] "r",
      notExists [unknown "st" "Terminated" [path [r "server" "Server"] "s",
        notExists [unknown "sr" "Rehired" [path [r "terminated" "Terminated"] "st"]]]]]]
    (.composite [.specification "rates"
      [unknown "sr" "Rate" ([path [r "server" "Server"] "s"] ++
        if withNext then [notExists [unknown "next" "Rate" [path [r "prior" "Rate"] "sr"]]] else [])]
      (fact "sr")])

/-- Two conditions declare `y`, and the specification already declares `y2`, so
the second `y` becomes `y3`. -/
def candidateTaken : Specification :=
  spec [("p1", "Tenant")]
    [unknown "a" "Account" [path [r "tenant" "Tenant"] "p1",
      notExists [unknown "y" "Freeze" [path [r "account" "Account"] "a"]],
      exists' [unknown "y" "Mirror" [path [r "account" "Account"] "a"]]],
     unknown "y2" "Owner" [path [r "account" "Account"] "a"]]
    (.composite [.fact "account" "a", .fact "owner" "y2"])

/-- Two chains, from `p` and from `q`, each with a condition that declares `y`.
Only the shared name joins them. -/
def twoChainsShareName : Specification :=
  spec [("p", "Project"), ("q", "Queue")]
    [unknown "a" "Assignment" [path [r "project" "Project"] "p",
      exists' [unknown "y" "Approval" [path [r "assignment" "Assignment"] "a"]]],
     unknown "b" "Batch" [path [r "queue" "Queue"] "q",
      exists' [unknown "y" "Approval" [path [r "batch" "Batch"] "b"]]]]
    (.composite [.fact "assignment" "a", .fact "batch" "b"])

/-- A project that is not archived, and its tasks: the condition on the given
and the match both declare `a`. -/
def givenConditionShared : ConditionedSpecification :=
  { given := [({ name := "p", type := "Project" },
      [(false, [unknown "a" "Archive" [path [r "project" "Project"] "p"]])])]
    matchList := [unknown "a" "Task" [path [r "project" "Project"] "p"]]
    projection := fact "a" }

def distinctLabelsCases : List DistinctLabelsCase := [
  { name := "sibling-conditions-share-a-name"
    description := "Two existential conditions of one match both declare y. Neither is in scope of the other, so the specification is well formed, but a feed joins the positive one's level with the negative one's matches. The second y is renamed."
    source := "jinaga/jinaga-spec#71"
    spec := siblingConditionsShareName },
  { name := "condition-and-later-match-share-a-name"
    description := "A negative condition declares n, and so does the match after it. The match is renamed, and so is the projection's reference to it; the component keeps its name."
    source := "jinaga/jinaga-spec#71"
    spec := conditionAndMatchShareName },
  { name := "repeated-label-with-next"
    description := "jinaga.js's vector: a negative condition declares sr, and so does the child specification, whose own condition names it. The child's sr is renamed, with every reference to it."
    source := "jinaga/jinaga.js#387, jinaga/jinaga.js#426"
    spec := rehiredServerRates true },
  { name := "repeated-label-without-next"
    description := "jinaga.js's vector: a negative condition declares sr, and so does the child specification. The child's sr is renamed."
    source := "jinaga/jinaga.js#387, jinaga/jinaga.js#426"
    spec := rehiredServerRates false },
  { name := "sibling-children-share-a-name"
    description := "Two child specifications declare n. They are separate descendants, and no feed binds both, so neither is renamed."
    source := "jinaga/jinaga-spec#71"
    spec := spec [("r", "Restaurant")]
      [unknown "s" "Server" [path [r "restaurant" "Restaurant"] "r"]]
      (.composite [.fact "server" "s",
        .specification "names" [unknown "n" "Name" [path [r "server" "Server"] "s"]] (fact "n"),
        .specification "rates" [unknown "n" "Rate" [path [r "server" "Server"] "s"]] (fact "n")]) },
  { name := "repeated-reserved-name"
    description := "Two conditions declare __x, a name reserved for the split, so the specification is not well formed. The second loses its leading underscores, so that a new name is never reserved."
    source := "jinaga.js distinct-labels.ts"
    spec := spec [("p1", "Tenant")]
      [unknown "a" "Account" [path [r "tenant" "Tenant"] "p1",
        notExists [unknown "__x" "Freeze" [path [r "account" "Account"] "a"]],
        exists' [unknown "__x" "Mirror" [path [r "account" "Account"] "a"]]]]
      (fact "a") },
  { name := "candidate-taken"
    description := "Two conditions declare y, and a match declares y2, so the second y skips y2 and becomes y3."
    source := "jinaga.js distinct-labels.ts"
    spec := candidateTaken },
  { name := "two-chains-share-a-name"
    description := "Two chains, from p and from q, whose conditions both declare y. The connectivity check reads a label by name, so before renaming it counts the two ys as one and joins the chains; the feed is a product, and binds y twice. After renaming it refuses the specification."
    source := "jinaga/jinaga-spec#71"
    spec := twoChainsShareName },
  { name := "given-condition-shares-a-name"
    description := "The reduction of (p: Project [!E { a: Archive [...] }]) { a: Task [...] }: the condition on the given and the match both declare a, which is no reuse in scope. Reducing moves the condition onto a first match, so the descendant then declares a twice, and the match's a is renamed. Conditions on givens are reduced before renaming."
    source := "jinaga/jinaga-spec#71"
    spec := reduceGivenConditions (givenConditionsLabel givenConditionShared) givenConditionShared },
  { name := "nothing-repeated"
    description := "No descendant declares a label twice, so nothing is renamed."
    source := "jinaga/jinaga-spec#71"
    spec := spec [("p1", "Tenant")]
      [unknown "a" "Account" [path [r "tenant" "Tenant"] "p1",
        notExists [unknown "f" "Freeze" [path [r "account" "Account"] "a"]],
        exists' [unknown "m" "Mirror" [path [r "account" "Account"] "a"]]]]
      (fact "a") }]

end JinagaSpec
