import JinagaSpec.Build
import JinagaSpec.WellFormed

/-!
# Cases

Named specifications for the conformance vectors and for the checks. Each
records where it came from. The `#NNN` numbers are issues in `jinaga/jinaga.js`.
-/
namespace JinagaSpec

open Build

structure Case where
  name : String
  description : String
  source : String
  spec : Specification

def cases : List Case :=
  let office := role "office" "Office"
  let company := role "company" "Company"
  let author := role "author" "Jinaga.User"
  let post := role "post" "Post"
  let blog := role "blog" "Blog"
  let creator := role "creator" "Jinaga.User"
  let workspace := role "workspace" "Workspace"
  let item := role "item" "Item"
  let parent := role "parent" "Item"
  let user := role "user" "Jinaga.User"
  [
  { name := "only-predecessors"
    description := "Every match walks predecessors, so the graph can run the whole specification."
    source := "splitSpecificationSpec: should put all in head if only predecessor joins"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "Office" [path [] "p1" [office]]] (fact "u1") },
  { name := "several-predecessor-conditions-in-one-match"
    description := "A match joins its unknown to two predecessor paths of the given. It is deterministic, so nothing splits."
    source := "#299, the comment rule"
    spec := spec [("p1", "Comment")]
      [unknown "u1" "Jinaga.User" [path [] "p1" [author], path [] "p1" [post, blog, creator]]]
      (fact "u1") },
  { name := "predecessor-match-of-two-conditions-then-successor"
    description := "A predecessor-only match of two conditions, then a successor match. The split falls after the first match, which keeps both conditions."
    source := "#299"
    spec := spec [("p1", "Comment")]
      [unknown "u1" "Jinaga.User" [path [] "p1" [author], path [] "p1" [post, blog, creator]],
       unknown "u2" "Blog" [path [creator] "u1"]]
      (fact "u2") },
  { name := "only-successors"
    description := "The first match walks successors of the given, so the head has no matches and the tail is the whole specification."
    source := "splitSpecificationSpec: should put all in tail if only successor joins"
    spec := spec [("p1", "Company")]
      [unknown "u1" "Office" [path [company] "p1"]] (fact "u1") },
  { name := "predecessor-then-successor"
    description := "A predecessor match, then a match that seeks successors of it. The pivot joins directly to a label the head binds."
    source := "splitSpecificationSpec: should split if predecessor and then successor"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "Office" [path [] "p1" [office]],
       unknown "u2" "President" [path [office] "u1"]]
      (fact "u2") },
  { name := "predecessor-and-successor-in-one-match"
    description := "One condition walks predecessors and then successors. The predecessor walk becomes a head match bound to a split label."
    source := "splitSpecificationSpec: should split if predecessor and then successor, but in one match"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "President" [path [office] "p1" [office]]] (fact "u1") },
  { name := "existential-on-the-pivot"
    description := "The pivot carries a negative existential. It stays with the tail."
    source := "splitSpecificationSpec: should split path when existential condition exists"
    spec := spec [("p1", "Administrator")]
      [unknown "u1" "Administrator"
        [path [company] "p1" [company],
         notExists [unknown "u2" "Administrator.Revoked" [path [role "administrator" "Administrator"] "u1"]]]]
      (fact "u1") },
  { name := "existential-with-only-successor-joins"
    description := "A predecessor match, then a pivot with successors and a negative existential."
    source := "splitSpecificationSpec: should split when existential appears with only successor joins"
    spec := spec [("p1", "Administrator")]
      [unknown "u1" "Company" [path [] "p1" [company]],
       unknown "u2" "Administrator"
        [path [company] "u1",
         notExists [unknown "u3" "Administrator.Revoked" [path [role "administrator" "Administrator"] "u2"]]]]
      (fact "u2") },
  { name := "projected-label-reaches-the-tail"
    description := "The rule projects a label the head binds. It is a given of the tail, next to the split label."
    source := "#297, the blog rule"
    spec := spec [("p1", "Post")]
      [unknown "u1" "Jinaga.User" [path [] "p1" [blog, creator]],
       unknown "u2" "Post" [path [blog] "p1" [blog]]]
      (fact "u1") },
  { name := "several-paths-each-walk-predecessors"
    description := "One Owner joined to both endpoints' workspaces. Each path gets its own head label."
    source := "#231, formulation A"
    spec := spec [("p1", "Link")]
      [unknown "u1" "Owner"
        [path [workspace] "p1" [item, workspace], path [workspace] "p1" [parent, workspace]],
       unknown "u2" "Jinaga.User" [path [] "u1" [user]]]
      (fact "u2") },
  { name := "several-paths-one-reuses-a-head-label"
    description := "Walk one endpoint's workspace first, then join the Owner to the other. Only the second condition needs a split label."
    source := "#231, formulation C"
    spec := spec [("p1", "Link")]
      [unknown "u1" "Workspace" [path [] "p1" [item, workspace]],
       unknown "u2" "Owner" [path [workspace] "u1", path [workspace] "p1" [parent, workspace]],
       unknown "u3" "Jinaga.User" [path [] "u2" [user]]]
      (fact "u3") },
  { name := "several-paths-match-then-successor"
    description := "A workspace joined to both endpoints is deterministic. The split falls after it and the tail is given that workspace."
    source := "#231, formulation B"
    spec := spec [("p1", "Link")]
      [unknown "u1" "Workspace" [path [] "p1" [item, workspace], path [] "p1" [parent, workspace]],
       unknown "u2" "Owner" [path [workspace] "u1"],
       unknown "u3" "Jinaga.User" [path [] "u2" [user]]]
      (fact "u3") },
  { name := "existential-reads-the-given"
    description := "The tail's existential condition walks from the given fact, so the given is also a given of the tail."
    source := "#297, formulation D of #231"
    spec := spec [("p1", "Link")]
      [unknown "u1" "Owner"
        [path [workspace] "p1" [item, workspace],
         exists' [unknown "u2" "Owner" [path [workspace] "p1" [parent, workspace], path [user] "u1" [user]]]],
       unknown "u3" "Jinaga.User" [path [] "u1" [user]]]
      (fact "u3") },
  { name := "given-only-an-existential-uses"
    description := "The pivot's existential condition reads a second given that no head match mentions. The head is given every given, and projects the one the tail needs."
    source := "#297: the head's own projection takes part in deriving its givens"
    spec := spec [("p1", "Post"), ("p2", "Jinaga.User")]
      [unknown "u1" "Blog" [path [] "p1" [blog]],
       unknown "u2" "Post"
        [path [blog] "u1",
         notExists [unknown "u3" "Ban" [path [user] "p2"]]]]
      (fact "u2") },
  { name := "pivot-joins-a-second-given"
    description := "The pivot has two path conditions. One joins the head's label and one joins a second given directly, so the tail is given both."
    source := "#231: a pivot with several path conditions"
    spec := spec [("p1", "Post"), ("p2", "Jinaga.User")]
      [unknown "u1" "Blog" [path [] "p1" [blog]],
       unknown "u2" "Post" [path [blog] "u1", path [author] "p2"]]
      (fact "u2") }
  ]

/-- A specification, and the rules a person reading them expects it to violate.
The generator checks the oracle agrees that it is well-formed exactly when it
violates none. -/
structure WellFormedCase where
  name : String
  description : String
  source : String
  spec : Specification
  /-- The rules the specification violates: `scoped`, `named` or `projected`. -/
  violates : List String

def wellFormedCases : List WellFormedCase :=
  let office := role "office" "Office"
  let revoked := role "revoked" "Revoked"
  let simple := [unknown "u1" "Office" [path [] "p1" [office]]]
  [
  { name := "simple"
    description := "A given, one match joined to it, and a projection of that match."
    source := "the baseline"
    spec := spec [("p1", "Employee")] simple (fact "u1")
    violates := [] },
  { name := "existential-uses-the-enclosing-unknown"
    description := "An existential condition joins the unknown of the match it belongs to. That unknown is in scope inside it, and only there."
    source := "splitSpecificationSpec: should split path when existential condition exists"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "Office" [path [] "p1" [office], notExists [unknown "u2" "Revoked" [path [revoked] "u1"]]]]
      (fact "u1")
    violates := [] },
  { name := "sibling-existentials-reuse-a-name"
    description := "Two existential conditions each declare a match named e. Scope is lexical, so the second does not see the first."
    source := "SpecificationParser.parseMatches discards a nested match's labels when the condition ends"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "Office"
        [path [] "p1" [office],
         notExists [unknown "e" "Revoked" [path [revoked] "u1"]],
         notExists [unknown "e" "Revoked" [path [revoked] "u1"]]]]
      (fact "u1")
    violates := [] },
  { name := "composite-projection"
    description := "A composite projection names a given and a top-level unknown."
    source := "the baseline"
    spec := spec [("p1", "Employee")] simple
      (.composite [{ name := "employee", label := "p1" }, { name := "office", label := "u1" }])
    violates := [] },
  { name := "path-joins-an-undefined-label"
    description := "A path condition joins a label nothing declares."
    source := "SpecificationParser.parsePathCondition: The label ... has not been defined"
    spec := spec [("p1", "Employee")] [unknown "u1" "Office" [path [] "nosuch" [office]]] (fact "u1")
    violates := ["scoped"] },
  { name := "path-joins-its-own-unknown"
    description := "A match joins its own unknown. The split reads it bound in the original and unbound in the head."
    source := "the counterexample to splitPaths_correct without pivot_paths_ne"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "Office" [path [] "p1" [office], path [office] "u1" [office]]] (fact "u1")
    violates := ["scoped"] },
  { name := "path-joins-a-later-match"
    description := "A match joins a label that a later match declares."
    source := "scope is lexical: a match sees only the matches before it"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "Office" [path [] "u2" [office]],
       unknown "u2" "Office" [path [] "p1" [office]]]
      (fact "u1")
    violates := ["scoped"] },
  { name := "existential-joins-an-undefined-label"
    description := "A path condition inside an existential condition joins a label nothing declares."
    source := "SpecificationParser.parsePathCondition, in a nested match"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "Office"
        [path [] "p1" [office], notExists [unknown "e" "Revoked" [path [revoked] "nosuch"]]]]
      (fact "u1")
    violates := ["scoped"] },
  { name := "existential-joins-a-sibling-conditions-match"
    description := "The second existential condition joins the match the first declares. That match is not in scope outside its own condition."
    source := "SpecificationParser.parseMatches discards a nested match's labels"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "Office"
        [path [] "p1" [office],
         notExists [unknown "e1" "Revoked" [path [revoked] "u1"]],
         notExists [unknown "e2" "Revoked" [path [revoked] "e1"]]]]
      (fact "u1")
    violates := ["scoped"] },
  { name := "unknown-shadows-a-given"
    description := "A match declares a label that is already a given."
    source := "SpecificationParser.parseMatch: The name ... has already been used"
    spec := spec [("p1", "Employee")] [unknown "p1" "Office" [path [] "p1" [office]]] (fact "p1")
    violates := ["named"] },
  { name := "unknown-shadows-an-earlier-match"
    description := "Two matches declare the same label."
    source := "SpecificationParser.parseMatch: The name ... has already been used"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "Office" [path [] "p1" [office]],
       unknown "u1" "Office" [path [] "p1" [office]]]
      (fact "u1")
    violates := ["named"] },
  { name := "existential-shadows-an-outer-label"
    description := "A match inside an existential condition declares a label that is already in scope."
    source := "SpecificationParser.parseExistentialCondition passes the outer labels down"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "Office"
        [path [] "p1" [office], notExists [unknown "p1" "Revoked" [path [revoked] "u1"]]]]
      (fact "u1")
    violates := ["named"] },
  { name := "existential-shadows-the-enclosing-unknown"
    description := "A match inside an existential condition declares the enclosing match's unknown."
    source := "SpecificationParser.parseExistentialCondition adds the unknown to the scope"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "Office"
        [path [] "p1" [office], notExists [unknown "u1" "Revoked" [path [revoked] "p1"]]]]
      (fact "u1")
    violates := ["named"] },
  { name := "unknown-uses-a-reserved-label"
    description := "A match declares a label that begins with `__`, which the split reserves for the facts it hands from the head to the tail."
    source := "the reserved-label rule"
    spec := spec [("p1", "Employee")] [unknown "__s0" "Office" [path [] "p1" [office]]] (fact "__s0")
    violates := ["named"] },
  { name := "given-uses-a-reserved-label"
    description := "A given begins with `__`."
    source := "the reserved-label rule"
    spec := spec [("__p", "Employee")] [unknown "u1" "Office" [path [] "__p" [office]]] (fact "u1")
    violates := ["named"] },
  { name := "existential-uses-a-reserved-label"
    description := "A match inside an existential condition declares a label that begins with `__`."
    source := "the reserved-label rule"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "Office"
        [path [] "p1" [office], notExists [unknown "__s1" "Revoked" [path [revoked] "u1"]]]]
      (fact "u1")
    violates := ["named"] },
  { name := "projection-names-an-undefined-label"
    description := "The projection names a label nothing declares. The parser and validateSpecification accept this today."
    source := "docs/contracts.md: the gap"
    spec := spec [("p1", "Employee")] simple (fact "nosuchlabel")
    violates := ["projected"] },
  { name := "composite-projection-names-an-undefined-label"
    description := "One component of a composite projection names a label nothing declares."
    source := "docs/contracts.md: the gap"
    spec := spec [("p1", "Employee")] simple
      (.composite [{ name := "office", label := "u1" }, { name := "other", label := "nosuch" }])
    violates := ["projected"] },
  { name := "projection-names-a-nested-unknown"
    description := "The projection names a match declared inside an existential condition, which is not in scope outside it."
    source := "the theorem's Projected condition"
    spec := spec [("p1", "Employee")]
      [unknown "u1" "Office"
        [path [] "p1" [office], notExists [unknown "e" "Revoked" [path [revoked] "u1"]]]]
      (fact "e")
    violates := ["projected"] }
  ]

end JinagaSpec
