import JinagaSpec.Maintain
import JinagaSpec.Split

/-!
# Candidates: which results might a new fact have changed?

When a fact `f` arrives, a result can change in only one way: `f` *touches* it.
Either `f` is bound to one of the result's own unknowns, or one of the result's
existential conditions changed its answer because, inside it, something
changed in the same way, one level down. Following that down always ends at an
unknown bound to `f`. `Proofs/Candidates.lean` proves this.

`touchMatches` lists every such path through a specification, and for each one
builds an *inverse*: an ordinary specification, given the subscription's
givens and `f` (under the reserved label `pinLabel`), whose results include
every result that path can change. The inverse keeps the original's nesting,
so no label is renamed. Along the path:

* **The unknown at the bottom is pinned to `f`**: it gains the condition
  `u = __f`.
* **The existential condition the path passes through becomes `exists`.** The
  path's change inside it is a solution that exists on the new graph, whatever
  the condition originally asked.
* **A level whose solution was lost drops its other existential conditions.**
  Its solution existed on the old graph, so its conditions held there, and may
  not hold on the new one. Its path conditions are kept: a lost solution never
  binds `f`, and a walk that starts anywhere else is the same on both graphs.
  A level that gained its solution keeps everything, because its conditions
  hold on the new graph.

Whether a level gained or lost is known from the top: the result itself either
gained or lost, and each existential condition passes the direction down
unchanged (`exists`) or reversed (`notExists`). So `touchMatches true` lists
the inverses for gained results, and `touchMatches false` those for lost ones.

The inverses do not say "add" or "remove". They find *candidates*, and the
stream decides each one by reading the specification (`Maintain.lean`). So
they need only be complete, not exact.

Written in the portable subset: inductive types, total functions, structural
recursion and lists.
-/
namespace JinagaSpec

/-- The label an inverse gives the new fact. Reserved, so no specification
declares it. -/
def pinLabel : Name := "__f"

/-- `u = __f`: the unknown is the new fact. -/
def pinCondition : Condition :=
  .path { rolesLeft := [], labelRight := pinLabel, rolesRight := [] }

/-- A level that lost its solution keeps only its path conditions. -/
def relax (gained : Bool) (cs : List Condition) : List Condition :=
  if gained then cs else cs.filter (·.isPath)

def relaxMatches (gained : Bool) (ms : List Match) : List Match :=
  if gained then ms else ms.map fun m => .mk m.unknown (relax false m.conditions)

mutual
  /-- Every way `f` can change a solution of `ms`, in the direction `gained`:
  the pinned unknown, and `ms` rewritten for that path. -/
  def touchMatches (gained : Bool) : List Match → List (Label × List Match)
    | [] => []
    | .mk u cs :: rest =>
      (if gained then [(u, .mk u (pinCondition :: cs) :: rest)] else []) ++
      (touchConditions gained cs).map (fun (p, cs') => (p, .mk u cs' :: relaxMatches gained rest)) ++
      (touchMatches gained rest).map (fun (p, rest') => (p, .mk u (relax gained cs) :: rest'))

  /-- Through one of the conditions; the others relax. -/
  def touchConditions (gained : Bool) : List Condition → List (Label × List Condition)
    | [] => []
    | c :: cs =>
      (touchCondition gained c).map (fun (p, c') => (p, c' :: relax gained cs)) ++
      (touchConditions gained cs).map (fun (p, cs') => (p, relax gained [c] ++ cs'))

  /-- Into an existential condition, which becomes `exists`. Inside a
  `notExists`, a gain is a loss and a loss is a gain. -/
  def touchCondition (gained : Bool) : Condition → List (Label × Condition)
    | .path _ => []
    | .existential e ms =>
      (touchMatches (gained == e) ms).map fun (p, ms') => (p, .existential true ms')
end

/-- The inverses of a specification: for each path, a specification given the
subscription's givens and the new fact. -/
def inverses (s : Specification) : List Specification :=
  (touchMatches true s.matchList ++ touchMatches false s.matchList).map fun (p, ms) =>
    { given := s.given ++ [{ name := pinLabel, type := p.type }], matchList := ms,
      projection := s.projection }

/-- The subscription's givens, and the new fact as `pinLabel`. -/
def pinEnv (s : Specification) (env : Env) (f : Fact) : Env :=
  (env.restrictTo (s.given.map (·.name))).bind pinLabel f.id

/-- The results `f` might have changed. If `f` is one of the subscription's own
givens, any result might have, so every result old and new is a candidate. -/
def candidates (s : Specification) (env : Env) (g : Graph) (f : Fact) : List Row :=
  if s.given.any (env ·.name == some f.id) then
    s.evaluate g env ++ s.evaluate (g ++ [f]) env
  else
    (inverses s).flatMap (·.evaluate (g ++ [f]) (pinEnv s env f))

end JinagaSpec
