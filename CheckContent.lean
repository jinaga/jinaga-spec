import CheckGen

/-!
# Randomized check of the content store

`lake exe check-content [seed]` tests SEC-1 to SEC-5 (`Proofs/Content.lean`), as
the theorems state them, on random histories of saves and uploads: a random
well-formed specification, a graph for it, uploads by random users to random
keys interleaved with the saves, then reads by every user of every key with
random proofs. The policy makes collisions common: a content hash is one of
three values, so many content facts share one, and different bytes share a
hash.

The theorems are proved, so the real handlers fail none of them. What the check
measures is that each statement rules out the mutant it is meant to: each
mutant breaks one rule of `read` or `write`, and must be caught on some
histories, by the statement named in its label.
-/
open JinagaSpec

instance : Inhabited Replicator := ⟨.empty⟩

/-! ## The mutant family

One read handler and one write handler, parameterized over the rule each
mutant changes. With no field changed they are `Replicator.read` and
`Replicator.write`, which the check confirms on every request. The
specification's own handlers stay unparameterized. -/

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
      match P.contentHash f with
      | none => (r, .unprocessable)
      | some h =>
        let known := if m.hashShortcut then (r.objects.find? fun (_, b) => P.hash b == h).map (·.2) else none
        let o := if P.hash o != h then known.getD o else o
        if !m.mayCreate P u r.store f then (r, .forbidden)
        else if m.checkHash && P.hash o != h then (r, .unprocessable)
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
  ("SEC-5: answer 404 before checking the proof", { existenceFirst := true })
]

/-! ## The statements, as the theorems state them -/

/-- A policy in which collisions are common. -/
def policy : Policy where
  hash b := toString (b.length % 3)
  contentHash f := if f.id % 4 == 3 then none else some (toString (f.id % 3))
  fits _ b := b.length ≤ 4
  mayCreate u g f := (u * 7 + f.id * 3 + g.length) % 3 != 0
  distributes u _ gs _ := (u + gs.foldl (· + ·) 0) % 3 != 0

/-- Which statements a history and its reads break, by name. -/
def violations (m : Mutant) (P : Policy) (evs : List Event) (reads : List (Option User × FactId × Proof)) :
    List String := Id.run do
  let states := (List.range (evs.length + 1)).map fun i => (evs.take i).foldl (stepWith m P) .empty
  let r := states.getLast!
  let mut out := []
  -- SEC-3: every stored object was uploaded, those bytes, by an authorized writer.
  for (k, o) in r.objects do
    let witnessed := (evs.zip states).any fun (e, s) => match e with
      | .write (some u) k' o' => k' == k && o' == o && match s.store.factOf k with
        | some f => P.mayCreate u s.store f && P.contentHash f == some (P.hash o)
        | none => false
      | _ => false
    unless witnessed do out := "SEC-3" :: out
  for (user, key, p) in reads do
    let resp := readWith m P r user key p
    if let .ok o := resp then
      -- SEC-1
      unless (match user with | some u => P.distributes u p.spec p.givens r.store && p.yields r.store key | none => false) do
        out := "SEC-1" :: out
      -- SEC-2
      unless (match r.store.factOf key with | some f => P.contentHash f == some (P.hash o) | none => false) do
        out := "SEC-2" :: out
    -- SEC-4: the same store, and only the object under this key.
    unless resp == readWith m P { r with objects := r.objects.filter (·.1 == key) } user key p do
      out := "SEC-4" :: out
    -- SEC-5: to a user the rules do not admit, the same answer with no objects.
    let admitted := match user with | some u => P.admits r.store u key p | none => false
    unless admitted || resp == readWith m P { r with objects := [] } user key p do
      out := "SEC-5" :: out
  return out.eraseDups

/-! ## Random histories -/

def genBytes : Gen Bytes := do
  let n ← below 6
  return String.ofList (← repeatGen n (pick ['a', 'b']))

def genUser : Gen (Option User) := do
  if ← chance 1 6 then return none else return some (← below 4)

def genGivens (s : Specification) (g : Graph) : Gen (List FactId) := do
  let mut ids := []
  for l in s.given do
    let candidates := (g.filter (·.type == l.type)).map (·.id)
    ids := ids ++ [← if candidates.isEmpty then pure 0 else pick candidates]
  if ← chance 1 10 then return ids.drop 1 else return ids

/-- An upload to a random key. Half its bytes match the key's content hash in
`policy`, so that most writers who may create the fact get it stored. -/
def genUpload : Gen Event := do
  let key ← below 8
  let matching := String.ofList (← repeatGen (key % 3 + 3 * (← below 2)) (pick ['a', 'b']))
  let bytes ← if ← chance 1 2 then genBytes else pure matching
  return .write (← genUser) key bytes

/-- The graph's facts saved in order, with uploads among them. Some uploads are
for a key that is not saved yet; many repeat a key. -/
def genHistory (g : Graph) : Gen (List Event) := do
  let mut evs := []
  for f in g do
    for _ in [0:(← below 3)] do
      evs := evs ++ [← genUpload]
    evs := evs ++ [.save f]
  for _ in [0:(← below 4)] do
    evs := evs ++ [← genUpload]
  return evs

def main (args : List String) : IO UInt32 := do
  let seed := (args.head?.bind String.toNat?).getD 1
  let mut gen : StdGen × Nat := (mkStdGen seed, 0)
  let histories := 2000
  let mut reads := 0
  let mut served := 0
  let mut stored := 0
  let mut real := 0
  let mut first : Option String := none
  let mut caught : List (Nat × List String) := mutants.map fun _ => (0, [])
  for _ in [0:histories] do
    let ((g, evs, rs), gen') := (do
      let s ← genSpec
      let g ← genGraph s 6
      let evs ← genHistory g
      let mut rs := []
      for key in List.range 8 do
        for user in [none, some 0, some 1, some 2, some 3] do
          rs := (user, key, { spec := s, givens := ← genGivens s g : Proof }) :: rs
      return (g, evs, rs) : Gen (Graph × List Event × List (Option User × FactId × Proof))).run gen
    gen := gen'
    let r := Replicator.run policy evs
    -- The mutant family with no rule changed is the specification's handlers.
    unless r.objects == (evs.foldl (stepWith {} policy) .empty).objects do
      throw <| IO.userError "the mutant family's write differs from Replicator.write"
    for (user, key, p) in rs do
      unless r.read policy user key p == readWith {} policy r user key p do
        throw <| IO.userError "the mutant family's read differs from Replicator.read"
      if let .ok _ := r.read policy user key p then served := served + 1
    reads := reads + rs.length
    stored := stored + r.objects.length
    let v := violations {} policy evs rs
    unless v.isEmpty do
      real := real + 1
      if first.isNone then first := some s!"{v}: {g.length} facts, {evs.length} events"
    caught := (caught.zip mutants).map fun ((n, by_), (_, mu)) =>
      let v := violations mu policy evs rs
      if v.isEmpty then (n, by_) else (n + 1, (by_ ++ v).eraseDups)
  IO.println s!"histories {histories}, objects stored {stored}, reads {reads}, served {served}"
  IO.println s!"real handlers: {real} histories break a statement"
  for ((label, _), (n, by_)) in mutants.zip caught do
    IO.println s!"  mutant \"{label}\": caught on {n} of {histories} histories, by {by_.mergeSort (· ≤ ·)}"
  match first with
  | some f => IO.println s!"\nFIRST FAILURE\n{f}"; return 1
  | none =>
    -- Each mutant must be caught by the statement its label names.
    let named := (caught.zip mutants).all fun ((_, by_), (label, _)) => by_.any (label.startsWith ·)
    return if named then 0 else 1
