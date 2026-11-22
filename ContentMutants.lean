import JinagaSpec

/-!
# Mutants of the content store

One read handler and one write handler, parameterized over the rule each
mutant breaks. Shared by `check-content`, which checks that SEC-1 to SEC-5 rule
out each one, and `lake exe vectors`, which checks that the content vectors
catch each one.
-/
open JinagaSpec

/-- What a mutant changes. With no field changed, `readWith` and `writeWith`
are `Replicator.read` and `Replicator.write`, which `check-content` confirms on
every request. The specification's own handlers stay unparameterized. -/
structure Mutant where
  /-- How a read finds the object for a key. -/
  lookup : Policy → Replicator → FactId → Option Bytes := fun _ r k => r.objects.lookup k
  /-- Whether the rules admit a reader. -/
  admits : Policy → Graph → User → FactId → Proof → Bool := Policy.admits
  /-- Answer 404 before checking the proof. -/
  existenceFirst : Bool := false
  /-- Whether the writer may create the fact. -/
  mayCreate : Policy → User → Graph → Fact → Bool := Policy.mayCreate
  /-- Compare the uploaded bytes with the content hash. -/
  checkHash : Bool := true
  /-- Answer a repeat upload (RW-8) before checking the writer. -/
  repeatFirst : Bool := false
  /-- Bytes that do not match take the stored bytes of the same hash instead. -/
  hashShortcut : Bool := false

def readWith (m : Mutant) (P : Policy) (r : Replicator) (user : Option User) (key : FactId) (p : Proof) :
    Response :=
  match user with
  | none => .unauthenticated
  | some u =>
    if !p.bound then .badRequest
    else if m.existenceFirst && (m.lookup P r key).isNone then .notUploaded
    else if !m.admits P r.store u key p then .forbidden
    else match m.lookup P r key with
      | none => .notUploaded
      | some o => .ok o

def writeWith (m : Mutant) (P : Policy) (r : Replicator) (user : Option User) (key : FactId) (o : Bytes) :
    Replicator × Response :=
  match user with
  | none => (r, .unauthenticated)
  | some u =>
    match r.store.factOf key with
    | none => (r, .factMissing)
    | some f =>
      if m.repeatFirst && (r.objects.lookup key).isSome then (r, .alreadyStored)
      else if !m.mayCreate P u r.store f then (r, .forbidden)
      else match P.contentHash f with
      | none => (r, .unprocessable)
      | some h =>
        let known := if m.hashShortcut then (r.objects.find? fun (_, b) => P.hash b == h).map (·.2) else none
        let o := if P.hash o != h then known.getD o else o
        if m.checkHash && P.hash o != h then (r, .unprocessable)
        else if !P.fits f o then (r, .tooLarge)
        else match r.objects.lookup key with
          | some _ => (r, .alreadyStored)
          | none => ({ r with objects := (key, o) :: r.objects }, .stored)

def stepWith (m : Mutant) (P : Policy) (r : Replicator) : Event → Replicator
  | .save f => { r with store := r.store ++ [f] }
  | .write u key o => (writeWith m P r u key o).1

/-- The spoof: any object stored under a key whose fact has the same content
hash. -/
def byContentHash (P : Policy) (r : Replicator) (k : FactId) : Option Bytes :=
  match (r.store.factOf k).bind P.contentHash with
  | none => none
  | some h => (r.objects.find? fun (k', _) => (r.store.factOf k').bind P.contentHash == some h).map (·.2)

def mutants : List (String × Mutant) := [
  ("SEC-1: no yields check", { admits := fun P g u _ p => P.distributes u p.spec p.givens g }),
  ("SEC-1: no distribution check", { admits := fun _ g _ key p => p.yields g key }),
  ("SEC-2: store bytes without hashing them", { checkHash := false }),
  ("SEC-3: authorize the fact's presence, not the writer", { mayCreate := fun _ _ _ _ => true }),
  ("SEC-3: map a key to stored bytes of the same hash", { hashShortcut := true }),
  ("SEC-4: look an object up by its content hash", { lookup := byContentHash }),
  ("SEC-5: answer 404 before checking the proof", { existenceFirst := true }),
  ("SEC-5: answer a repeat upload before checking the writer", { repeatFirst := true })
]

