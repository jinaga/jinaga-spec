import JinagaSpec.WellFormed
import JinagaSpec.Reorder

/-!
# Distribution-based content storage

The replicator's content store, from "Distribution-Based Content Storage:
Functional Requirements" (Nov 20, 2026). A content fact names an object by the
hash of its bytes. The object itself is never part of a fact: the replicator
keeps it beside the fact store, indexed by the content fact's own id, the
*content key* (ST-1), never by the content hash.

Two endpoints change or read that index:

* `Replicator.write` (RW-1 to RW-9): store an object under a content key, once
  the writer is authorized to create the fact and the bytes match its hash.
* `Replicator.read` (RR-1 to RR-7): return the object under a content key, once
  the distribution rules let the reader run the proof's specification with its
  givens, and that query yields the content fact.

What a fact's fields hold, how a writer is authorized and how distribution
rules are evaluated are not modelled here: `Policy` takes each as a parameter,
and the theorems (`Proofs/Content.lean`) hold for every policy. The fact store
already models authorization rules (`Store.lean`); distribution rules have no
model yet. A policy names, for a fact, its content hash (none if its type is not
content-bearing, MD-1); for bytes, their hash; whether an object fits the
declared constraints (MD-2); whether a user may create a fact; and whether the
distribution rules let a user run a specification with given facts (RR-3).

Reactive authorization (RR-6), chunked uploads and the client are out of scope.

Written in the same portable subset as `Split.lean`.
-/
namespace JinagaSpec

/-- An object's bytes. -/
abbrev Bytes := String
/-- A hash of bytes, as stored in a content fact's content hash field. -/
abbrev Hash := String
/-- A user, by the id of their user fact. -/
abbrev User := FactId

/-- What the content store reads from the model and its rules. -/
structure Policy where
  /-- The hash of an object's bytes, by the algorithm Jinaga uses for facts. -/
  hash : Bytes → Hash
  /-- The fact's content hash field, if its type is declared content-bearing. -/
  contentHash : Fact → Option Hash
  /-- The object meets the declared size and media-type constraints. -/
  fits : Fact → Bytes → Bool
  /-- The authorization rules let the user create the fact, on this store. -/
  mayCreate : User → Graph → Fact → Bool
  /-- The distribution rules let the user run the specification with these
  givens, on this store. -/
  distributes : User → Specification → List FactId → Graph → Bool

/-- A reader's proof: a specification and the given facts it is run with. -/
structure Proof where
  spec : Specification
  givens : List FactId

/-- Every given is bound, and the specification and each of its child
specifications are well formed (RR-1). A proof that leaves a given unbound
says nothing about which facts its reader can reach, and `Proof.confirms`
is `Proof.yields` only on well-formed descendants (`confirms_eq_yields`).
`Proof.bound_iff` proves this decides `Proof.Bound`. -/
def Proof.bound (p : Proof) : Bool :=
  p.givens.length == p.spec.given.length && isWellFormedDeep p.spec

/-- Running the proof's specification with its givens on `g` yields the fact
`key`: some result names it, at any depth of child specifications (RR-4, CR-1).
A child specification's results under some solution of its parent are the
results of the descendant whose matches go on from the parent's
(`Specification.descendants`), so a fact a client reached through a nested
query is yielded. -/
def Proof.yields (p : Proof) (g : Graph) (key : FactId) : Bool :=
  p.spec.descendants.any fun d => (d.read g (d.bindGivens p.givens)).any (·.contains (some key))

/-! ## Confirming that a proof yields the content fact

`Proof.yields` reads every result. The replicator need not: it knows which
fact it wants. For each projected label it binds that label to the content
fact and asks whether a solution exists (RR-4). A label that is a given is
bound already, so the given must be the fact. A label that is an unknown is
pinned to the fact with the inverse's reserved `pinLabel` (`Candidates.lean`),
and the pinned matches are reordered to start at the pin (`reorderOrSelf`,
`Reorder.lean`), so the read walks from the content fact to the givens instead
of from the givens to every result. `confirms_eq_yields`
(`Proofs/Content.lean`) proves the check is `Proof.yields` for every bound
proof. -/

/-- `ms`, with the match whose unknown is `l` pinned to the new fact: it gains
the condition `l = __f`, and keeps its own conditions. -/
def pinUnknown (l : Name) (ms : List Match) : List Match :=
  ms.map fun m => if m.unknown.name == l then .mk m.unknown (pinCondition :: m.conditions) else m

/-- `d`, with the unknown `u` pinned to the new fact, given as `pinLabel`, and
projected: its solutions are those of `d` that bind `u` to the new fact. -/
def Specification.pinResult (d : Specification) (u : Label) : Specification :=
  { given := d.given ++ [{ name := pinLabel, type := u.type }], matchList := pinUnknown u.name d.matchList,
    projection := .fact u.name }

/-- Some solution of `d`'s matches from `env` binds the label `l` to `key`.
If `l` is one of the matches' unknowns, pin it to `key` and look for a
solution, reading from the pin. Otherwise the matches do not bind `l`, so it
is as `env` binds it (a given), and any solution will do. -/
def Specification.bindsResult (d : Specification) (g : Graph) (env : Env) (key : FactId) (l : Name) : Bool :=
  match d.matchList.find? (·.unknown.name == l) with
  | some m => !((reorderOrSelf (d.pinResult m.unknown)).evaluate g (env.bind pinLabel key)).isEmpty
  | none => env l == some key && !(evalMatches g env d.matchList).isEmpty

/-- The check the replicator runs for RR-4: some descendant of the proof's
specification, with every given held, has a projected label that some
solution binds to `key`. -/
def Proof.confirms (p : Proof) (g : Graph) (key : FactId) : Bool :=
  p.spec.descendants.any fun d =>
    let env := d.bindGivens p.givens
    d.given.all (g.has env) && d.projection.labels.any (d.bindsResult g env key)

/-- The distribution rules let `u` run the proof, and it yields `key`. -/
def Policy.admits (P : Policy) (g : Graph) (u : User) (key : FactId) (p : Proof) : Bool :=
  P.distributes u p.spec p.givens g && p.yields g key

/-- The replicator's state: the fact store, and the objects by content key. -/
structure Replicator where
  store : Graph
  objects : List (FactId × Bytes)

def Replicator.empty : Replicator := { store := [], objects := [] }

/-- An endpoint's answer. -/
inductive Response where
  /-- 200, with the object. -/
  | ok (o : Bytes)
  /-- 201: stored. -/
  | stored
  /-- 200: the same key was already stored (RW-8). -/
  | alreadyStored
  /-- 400: the proof leaves a given unbound, or is not well formed (RR-1). -/
  | badRequest
  /-- 401: no valid token (RR-2). -/
  | unauthenticated
  /-- 403 (RW-4, RR-5). -/
  | forbidden
  /-- 404 `not_uploaded`: authorized, but no object is stored (RR-7). -/
  | notUploaded
  /-- The content fact is not in the store, and the request did not carry it
  (RW-2). -/
  | factMissing
  /-- 422: not a content-bearing type (RW-3), or the bytes do not match the
  content hash (RW-5). -/
  | unprocessable
  /-- 413: the object breaks the declared constraints (RW-6). -/
  | tooLarge
deriving DecidableEq, Repr

/-- `PUT /content/{key}`: store `o` under `key`. The user is the one behind the
token, if it is valid. The writer must be authorized to create the fact
(RW-4), and the bytes must hash to the fact's content hash (RW-5), before
anything is stored. A repeat upload leaves the stored object in place (RW-8).

The writer is checked as soon as the fact is found, so a writer who may not
create it learns only that it is in the store (which naming its key implies
they know), not whether its type is content-bearing or an object is stored.
Only the fact being missing (RW-2) is answered first: there is no fact to
authorize. -/
def Replicator.write (P : Policy) (r : Replicator) (user : Option User) (key : FactId) (o : Bytes) :
    Replicator × Response :=
  match user with
  | none => (r, .unauthenticated)
  | some u =>
    match r.store.factOf key with
    | none => (r, .factMissing)
    | some f =>
      if !P.mayCreate u r.store f then (r, .forbidden)
      else match P.contentHash f with
      | none => (r, .unprocessable)
      | some h =>
        if P.hash o != h then (r, .unprocessable)
        else if !P.fits f o then (r, .tooLarge)
        else match r.objects.lookup key with
          | some _ => (r, .alreadyStored)
          | none => ({ r with objects := (key, o) :: r.objects }, .stored)

/-- `POST /content/{key}/read`: the object under `key`, if the distribution
rules let the user run the proof and it yields the content fact (RR-3, RR-4),
which `Proof.confirms` checks by binding the fact as a result.
Otherwise 403, whether or not an object is stored (RR-5). The object is looked
up by its content key alone (ST-1). The bytes are not hashed again: `write`
verified them. -/
def Replicator.read (P : Policy) (r : Replicator) (user : Option User) (key : FactId) (p : Proof) :
    Response :=
  match user with
  | none => .unauthenticated
  | some u =>
    if !p.bound then .badRequest
    else if !(P.distributes u p.spec p.givens r.store && p.confirms r.store key) then .forbidden
    else match r.objects.lookup key with
      | none => .notUploaded
      | some o => .ok o

/-- What changes the replicator's state: a fact saved through the normal path,
or an upload. A read changes nothing. A save appends any fact, unchecked: the
fact store's own authorization is not modelled, so the theorems hold against
every store. Facts are content-addressed, so a second fact with an id already
stored would be the same fact; `factOf` finds the first. -/
inductive Event where
  | save (f : Fact)
  | write (user : Option User) (key : FactId) (o : Bytes)

def Replicator.step (P : Policy) (r : Replicator) : Event → Replicator
  | .save f => { r with store := r.store ++ [f] }
  | .write u key o => (r.write P u key o).1

/-- The state after a history of events, from an empty replicator. -/
def Replicator.run (P : Policy) (evs : List Event) : Replicator :=
  evs.foldl (Replicator.step P) .empty

end JinagaSpec
