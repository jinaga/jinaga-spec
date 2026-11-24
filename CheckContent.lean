import CheckGen
import ContentMutants

/-!
# Randomized check of the content store

`lake exe check-content [seed]` tests SEC-1 to SEC-5, `read_admitted` and
`confirms_eq_yields` (`Proofs/Content.lean`), as
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

/-! ## The statements, as the theorems state them -/

/-- A policy in which collisions are common. -/
def policy : Policy where
  hash b := toString (b.length % 3)
  contentHash f := if f.id % 4 == 3 then none else some (toString (f.id % 3))
  fits _ b := b.length ≤ 4
  mayCreate u g f := (u * 7 + f.id * 3 + g.length) % 3 != 0
  -- One feed, authorized when the proof's own specification yields the user.
  distribution s gs := [[{ spec := s, givens := gs }]]

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
  -- SEC-5, for uploads: to a writer the rules refuse, the same answer with no objects.
  for (e, s) in evs.zip states do
    if let .write (some u) k o := e then
      let refused := match s.store.factOf k with | some f => !P.mayCreate u s.store f | none => true
      if refused && (writeWith m P s (some u) k o).2 != (writeWith m P { s with objects := [] } (some u) k o).2 then
        out := "SEC-5" :: out
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
    -- RR-1: an authenticated read is refused with 400 exactly when the proof is not bound.
    if user.isSome && (resp == .badRequest) != !p.bound then
      out := "RR-1" :: out
    -- confirms_eq_yields: for a bound proof, the handler's check that the proof
    -- yields the key is `Proof.yields`, seen with distribution rules that admit everyone.
    if let some u := user then
      let all := { P with distribution := fun _ _ => [] }
      if p.bound && m.admits all r.store u key p != p.yields r.store key then
        out := "confirms_eq_yields" :: out
    -- read_admitted: an admitted reader with a bound proof is served, or told nothing is stored.
    if admitted && p.bound then
      unless resp == (match r.objects.lookup key with | none => .notUploaded | some o => .ok o) do
        out := "read_admitted" :: out
  return out.eraseDups

/-- A proof yields `key` as `Specification.readsOf` lists nested results:
some result, at any depth of child specifications, names it. `yields_iff`
proves `Proof.yields` is the nested reading; this checks `readsOf`, whose
results are read (`reads_of_mem_readsOf`), agrees. -/
partial def resultNames (key : FactId) : Result → Bool
  | .mk row children => row.contains (some key) || children.any (·.any (resultNames key))

def yieldsByReads (p : Proof) (g : Graph) (key : FactId) : Bool :=
  (p.spec.readsOf g (p.spec.bindGivens p.givens)).any (resultNames key)

/-! ## Random histories -/

def genBytes : Gen Bytes := do
  let n ← below 6
  return String.ofList (← repeatGen n (pick ['a', 'b']))

def genUser : Gen (Option User) := do
  if ← chance 1 6 then return none else return some (← below 4)

def genGivens (s : Specification) (g : Graph) (key : FactId) : Gen (List FactId) := do
  let mut ids := []
  for l in s.given do
    let candidates := (g.filter (·.type == l.type)).map (·.id)
    ids := ids ++ [← if candidates.isEmpty then pure 0 else pick candidates]
  if ← chance 1 10 then return ids.drop 1
  -- Sometimes a given is the key read, whatever its type, so the store may
  -- not hold it as a given.
  if ← chance 1 8 then
    return ids.set (← below ids.length) key
  return ids

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
    evs := evs ++ [.save [f]]
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
  let mut disagree := 0
  let mut first : Option String := none
  let mut caught : List (Nat × List String) := mutants.map fun _ => (0, [])
  -- `confirms_eq_yields`: on bound proofs, the check is `Proof.yields`.
  let mut confirmDisagree := 0
  -- How often `reorderChecked` refuses a pinned specification, so the check
  -- reads it in written order.
  let mut pinned := 0
  let mut fallback := 0
  for _ in [0:histories] do
    let ((g, evs, rs), gen') := (do
      -- One history in three has child specifications.
      let children ← chance 1 3
      let s ← if children then genChildSpec else genSpec
      let g ← if children then genFeedGraph s 6 else genGraph s 6
      let evs ← genHistory g
      let mut rs := []
      for key in List.range 8 do
        for user in [none, some 0, some 1, some 2, some 3] do
          rs := (user, key, { spec := s, givens := ← genGivens s g key : Proof }) :: rs
      -- Some proofs have an ill-formed child specification: one that declares
      -- its parent's unknowns again.
      if !s.matchList.isEmpty then
        let bad := { s with projection := .composite [.specification "again" s.matchList s.projection] }
        rs := (some 0, 0, { spec := bad, givens := ← genGivens bad g 0 : Proof }) :: rs
      return (g, evs, rs) : Gen (Graph × List Event × List (Option User × FactId × Proof))).run gen
    gen := gen'
    let r := Replicator.run policy evs
    if let some (_, _, p) := rs.getLast? then
      for d in p.spec.descendants do
        for l in d.projection.labels do
          if let some m := d.matchList.find? (·.unknown.name == l) then
            pinned := pinned + 1
            if (reorderChecked (d.pinResult m.unknown)).isNone then fallback := fallback + 1
    -- The mutant family with no rule changed is the specification's handlers.
    unless r.objects == (evs.foldl (stepWith {} policy) .empty).objects do
      throw <| IO.userError "the mutant family's write differs from Replicator.write"
    for (user, key, p) in rs do
      unless r.read policy user key p == readWith {} policy r user key p do
        throw <| IO.userError "the mutant family's read differs from Replicator.read"
      if let .ok _ := r.read policy user key p then served := served + 1
      -- `Proof.yields` agrees with the test library's nested reading.
      if p.yields r.store key != yieldsByReads p r.store key then disagree := disagree + 1
      unless confirmsWith {} p r.store key == p.confirms r.store key do
        throw <| IO.userError "the check family differs from Proof.confirms"
      if p.bound then
        if p.confirms r.store key != p.yields r.store key then confirmDisagree := confirmDisagree + 1
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
  IO.println s!"real handlers: {real} histories break a statement; yields disagrees with readsOf on {disagree} reads, confirms with yields on {confirmDisagree} bound reads"
  IO.println s!"pinned specifications {pinned}, read in written order (reorderChecked refuses) {fallback}"
  for ((label, _), (n, by_)) in mutants.zip caught do
    IO.println s!"  mutant \"{label}\": caught on {n} of {histories} histories, by {by_.mergeSort (· ≤ ·)}"
  if disagree > 0 || confirmDisagree > 0 then return 1
  match first with
  | some f => IO.println s!"\nFIRST FAILURE\n{f}"; return 1
  | none =>
    -- Each mutant must be caught by the statement its label names.
    let named := (caught.zip mutants).all fun ((_, by_), (label, _)) => by_.any (label.startsWith ·)
    return if named then 0 else 1
