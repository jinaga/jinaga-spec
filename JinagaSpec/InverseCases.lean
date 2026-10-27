import JinagaSpec.Build
import JinagaSpec.Semantics

/-!
# Named cases for inversion

Each is a specification, a graph, the subscription's givens, and a fresh batch
of facts that changes the result. Most batches are one fact. `lake exe vectors`
writes one inverse vector per case (`vectors/inverse/`), and `check-inverse`
measures each.
-/
namespace JinagaSpec

open Build

structure InverseCase where
  name : String
  description : String
  source : String
  spec : Specification
  givens : List (Name × FactId)
  graph : Graph
  batch : List Fact

private def r (n t : Name) : Role := role n t

def inverseCases : List InverseCase := [
  { name := "not-exists-removes"
    description := "One notExists. A Done arrives for an open task, which leaves the result."
    source := "jinaga/jinaga-spec#8"
    spec := spec [("p1", "Root")]
      [unknown "t" "Task" [path [r "root" "Root"] "p1",
        notExists [unknown "d" "Done" [path [r "task" "Task"] "t"]]]]
      (fact "t")
    givens := [("p1", 0)]
    graph := [⟨0, "Root", []⟩, ⟨1, "Task", [("root", 0)]⟩]
    batch := [⟨2, "Done", [("task", 1)]⟩] },
  { name := "not-exists-adds"
    description := "One notExists. A new task arrives, bound to a top-level unknown, and joins the result."
    source := "jinaga/jinaga-spec#8"
    spec := spec [("p1", "Root")]
      [unknown "t" "Task" [path [r "root" "Root"] "p1",
        notExists [unknown "d" "Done" [path [r "task" "Task"] "t"]]]]
      (fact "t")
    givens := [("p1", 0)]
    graph := [⟨0, "Root", []⟩, ⟨1, "Task", [("root", 0)]⟩]
    batch := [⟨2, "Task", [("root", 0)]⟩] },
  { name := "not-exists-not-exists-delete"
    description := "notExists { notExists }: an account with no unrestored freeze. A Freeze arrives and removes the account."
    source := "jinaga/jinaga-spec#8"
    spec := freezeSpec
    givens := [("p1", 0)]
    graph := [⟨0, "Owner", []⟩, ⟨1, "Account", [("owner", 0)]⟩]
    batch := [⟨2, "Freeze", [("account", 1)]⟩] },
  { name := "not-exists-not-exists-restore"
    description := "notExists { notExists }: an Unfreeze arrives for the only freeze and restores the account."
    source := "jinaga/jinaga-spec#8"
    spec := freezeSpec
    givens := [("p1", 0)]
    graph := [⟨0, "Owner", []⟩, ⟨1, "Account", [("owner", 0)]⟩, ⟨2, "Freeze", [("account", 1)]⟩]
    batch := [⟨3, "Unfreeze", [("freeze", 2)]⟩] },
  { name := "exists-not-exists-removes"
    description := "exists { notExists }: accounts with a current mirror. Retiring the only current mirror removes the account."
    source := "jinaga/jinaga.js#338"
    spec := mirrorSpec
    givens := [("p1", 0)]
    graph := [⟨0, "Root", []⟩, ⟨1, "Account", [("root", 0)]⟩, ⟨2, "Mirror", [("account", 1)]⟩]
    batch := [⟨3, "Retired", [("mirror", 2)]⟩] },
  { name := "correlated-not-exists"
    description := "A notExists correlated over two predecessors: messages in a channel that this user has not read. A Read by this user removes the message."
    source := "jinaga/jinaga-spec#8"
    spec := spec [("p1", "User"), ("p2", "Channel")]
      [unknown "m" "Message" [path [r "channel" "Channel"] "p2",
        notExists [unknown "rd" "Read" [path [r "message" "Message"] "m", path [r "user" "User"] "p1"]]]]
      (fact "m")
    givens := [("p1", 0), ("p2", 1)]
    graph := [⟨0, "User", []⟩, ⟨1, "Channel", []⟩, ⟨2, "Message", [("channel", 1)]⟩]
    batch := [⟨3, "Read", [("message", 2), ("user", 0)]⟩] },
  { name := "current-value"
    description := "A mutable property's current value: names with no successor revision. A new revision replaces the current one: one gained, one lost."
    source := "jinaga/jinaga-spec#8"
    spec := spec [("p1", "Account")]
      [unknown "n" "Name" [path [r "account" "Account"] "p1",
        notExists [unknown "next" "Name" [path [r "prior" "Name"] "n"]]]]
      (fact "n")
    givens := [("p1", 0)]
    graph := [⟨0, "Account", []⟩, ⟨1, "Name", [("account", 0)]⟩]
    batch := [⟨2, "Name", [("account", 0), ("prior", 1)]⟩] },
  { name := "sibling-not-exists"
    description := "Two sibling notExists conditions that one fact falsifies together. Each inverse of jinaga.js keeps the other condition, so neither reports the removal."
    source := "jinaga/jinaga.js#338"
    spec := spec [("p1", "Root")]
      [unknown "u1" "Task" [path [r "root" "Root"] "p1",
        notExists [unknown "e1" "Done" [path [r "task" "Task"] "u1"]],
        notExists [unknown "e2" "Done" [path [r "other" "Task"] "u1"]]]]
      (fact "u1")
    givens := [("p1", 0)]
    graph := [⟨0, "Root", []⟩, ⟨1, "Task", [("root", 0)]⟩]
    batch := [⟨2, "Done", [("task", 1), ("other", 1)]⟩] },
  { name := "reused-label"
    description := "A label reused, after an existential condition, by a later match. jinaga.js's inverse looks the label up across scopes and misses the removal."
    source := "jinaga/jinaga.js#343"
    spec := spec [("r", "Root")]
      [unknown "t" "Task" [path [r "root" "Root"] "r",
        notExists [unknown "x" "Done" [path [r "task" "Task"] "t"]]],
       unknown "x" "Note" [path [r "root" "Root"] "r"]]
      (.composite [{ name := "t", label := "t" }, { name := "x", label := "x" }])
    givens := [("r", 0)]
    graph := [⟨0, "Root", []⟩, ⟨1, "Task", [("root", 0)]⟩, ⟨2, "Note", [("root", 0)]⟩]
    batch := [⟨3, "Done", [("task", 1)]⟩] },
  { name := "depth-three-gain"
    description := "notExists { notExists { exists } }: the new fact makes the innermost exists true, which removes the middle solution, which adds the result."
    source := "jinaga/jinaga.js#338"
    spec := spec [("p1", "Root")]
      [unknown "a" "A" [path [r "root" "Root"] "p1",
        notExists [unknown "b" "B" [path [r "a" "A"] "a",
          notExists [unknown "c" "C" [path [r "b" "B"] "b",
            exists' [unknown "d" "D" [path [r "c" "C"] "c"]]]]]]]]
      (fact "a")
    givens := [("p1", 0)]
    graph := [⟨0, "Root", []⟩, ⟨1, "A", [("root", 0)]⟩, ⟨2, "B", [("a", 1)]⟩, ⟨3, "C", [("b", 2)]⟩]
    batch := [⟨4, "D", [("c", 3)]⟩] },
  { name := "not-exists-two-matches"
    description := "notExists { two matches, the second joined to the first }: tasks with no completed assignment. A Completion of an existing assignment removes the task: the path reaches the task from the second match through the first."
    source := "coverage: an existential condition with several matches"
    spec := assignmentSpec false
    givens := [("p1", 0)]
    graph := [⟨0, "Project", []⟩, ⟨1, "Task", [("project", 0)]⟩, ⟨2, "Assignment", [("task", 1)]⟩]
    batch := [⟨3, "Completion", [("assignment", 2)]⟩] },
  { name := "batch-exists-two-matches"
    description := "exists { two matches, the second joined to the first }: tasks with a completed assignment. The assignment and its completion arrive in one batch, the completion listed first, so each inner match is bound to a new fact."
    source := "coverage: an existential condition with several matches"
    spec := assignmentSpec true
    givens := [("p1", 0)]
    graph := [⟨0, "Project", []⟩, ⟨1, "Task", [("project", 0)]⟩]
    batch := [⟨3, "Completion", [("assignment", 2)]⟩, ⟨2, "Assignment", [("task", 1)]⟩] },
  { name := "batch-exists-together"
    description := "exists { notExists }: accounts with a current mirror. An account and its mirror arrive in one batch, the mirror listed first. Neither fact's inverses find the account on a graph without the other."
    source := "jinaga/jinaga-spec#11"
    spec := mirrorSpec
    givens := [("p1", 0)]
    graph := [⟨0, "Root", []⟩]
    batch := [⟨2, "Mirror", [("account", 1)]⟩, ⟨1, "Account", [("root", 0)]⟩] },
  { name := "batch-current-value"
    description := "A mutable property's current value. Two revisions arrive in one batch, the second replacing the first: the old value is lost, the last is gained, and the one between is gained and lost within the batch."
    source := "jinaga/jinaga-spec#11"
    spec := spec [("p1", "Account")]
      [unknown "n" "Name" [path [r "account" "Account"] "p1",
        notExists [unknown "next" "Name" [path [r "prior" "Name"] "n"]]]]
      (fact "n")
    givens := [("p1", 0)]
    graph := [⟨0, "Account", []⟩, ⟨1, "Name", [("account", 0)]⟩]
    batch := [⟨2, "Name", [("account", 0), ("prior", 1)]⟩, ⟨3, "Name", [("account", 0), ("prior", 2)]⟩] }
]
where
  mirrorSpec := spec [("p1", "Root")]
    [unknown "u1" "Account" [path [r "root" "Root"] "p1",
      exists' [unknown "e1" "Mirror" [path [r "account" "Account"] "u1",
        notExists [unknown "e2" "Retired" [path [r "mirror" "Mirror"] "e1"]]]]]]
    (fact "u1")
  assignmentSpec (e : Bool) := spec [("p1", "Project")]
    [unknown "t" "Task" [path [r "project" "Project"] "p1",
      .existential e [unknown "a" "Assignment" [path [r "task" "Task"] "t"],
        unknown "c" "Completion" [path [r "assignment" "Assignment"] "a"]]]]
    (fact "t")
  freezeSpec := spec [("p1", "Owner")]
    [unknown "a" "Account" [path [r "owner" "Owner"] "p1",
      notExists [unknown "fz" "Freeze" [path [r "account" "Account"] "a",
        notExists [unknown "uf" "Unfreeze" [path [r "freeze" "Freeze"] "fz"]]]]]]
    (fact "a")

def InverseCase.env (c : InverseCase) : Env := fun n => c.givens.lookup n

end JinagaSpec
