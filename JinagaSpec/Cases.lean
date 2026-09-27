import JinagaSpec.Build

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
    description := "The first match walks successors of the given, so there is no head."
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
  { name := "split-label-avoids-an-unknown"
    description := "An earlier match is already named s1, so the split label is s2."
    source := "the naming rule of #231"
    spec := spec [("p1", "Employee")]
      [unknown "s1" "Office" [path [] "p1" [office]],
       unknown "u1" "President" [path [office] "p1" [office]]]
      (fact "u1") },
  { name := "split-label-avoids-a-nested-unknown"
    description := "An existential condition declares s1 in its own match, so the split label is s2."
    source := "the naming rule of #231"
    spec := spec [("p1", "Link")]
      [unknown "u1" "Owner"
        [path [workspace] "p1" [item, workspace],
         notExists [unknown "s1" "Revoked" [path [role "owner" "Owner"] "u1"]]]]
      (fact "u1") },
  { name := "given-only-an-existential-uses"
    description := "The pivot's existential condition reads a second given that no head match mentions. The head must still name that given, because it projects it."
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

end JinagaSpec
