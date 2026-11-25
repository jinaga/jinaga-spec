import CheckGen
import ContentMutants

/-!
# Randomized check of the content store

`lake exe check-content [seed]` tests SEC-1 to SEC-5, `read_admitted`, `write_tooLarge` and
`confirms_eq_yields` (`Proofs/Content.lean`), and `Replicator.save_fresh`,
`Replicator.run_closed` and `cached_read` (`Proofs/ContentCache.lean`), as the theorems state them, on random histories
of saves, uploads and reads: a random well-formed specification, a graph for
it, and memberships in its givens' facts, some removed and some removals
restored, saved in batches, with uploads by random users to random keys and
reads with a few random proofs among them; then reads by every user of every
key with random proofs. The distribution rule is membership
(`ContentCases.membersOf`). The policy makes collisions common: a content hash
is one of three values, so many content facts share one, and different bytes
share a hash.

The theorems are proved, so the real handlers fail none of them. What the check
measures is that each statement rules out the mutant it is meant to: each
mutant breaks one rule of `read` or `write`, or of the cache's invalidation,
and must be caught on some histories, by the statement named in its label.
-/
open JinagaSpec

instance : Inhabited Replicator := ⟨.empty⟩
instance : Inhabited Role := ⟨{ name := "", predecessorType := "" }⟩
instance : Inhabited Proof := ⟨{ spec := { given := [], matchList := [], projection := .fact "" }, givens := [] }⟩

/-! ## The statements, as the theorems state them -/

/-- A policy in which collisions are common. The distribution rule is
membership: of the first given itself, or of the fact `via` reaches from it. -/
def policyVia (via : Option Role) : Policy where
  hash b := toString (b.length % 3)
  contentHash f := if f.id % 4 == 3 then none else some (toString (f.id % 3))
  fits _ b := b.length ≤ 4
  mayCreate u g f := (u * 7 + f.id * 3 + g.length) % 3 != 0
  -- One feed, which the current members of the first given's group may read.
  distribution s gs := match s.given.head? with
    | some l =>
      let rule := membersOf ("g", l.type) ((via.map (·.predecessorType)).getD l.type) via.toList
      [[{ spec := rule, givens := gs.take 1 }]]
    | none => [[]]

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
  -- write_tooLarge: an authorized upload to a content-bearing fact that breaks
  -- the constraints is refused with 413, whatever its hash.
  for (e, s) in evs.zip states do
    if let .write (some u) k o := e then
      if let some f := s.store.factOf k then
        let (s', resp) := writeWith m P s (some u) k o
        if P.mayCreate u s.store f && (P.contentHash f).isSome && !P.fits f o &&
            (resp != .tooLarge || s'.objects != s.objects) then
          out := "write_tooLarge" :: out
  for ((e, s), s') in (evs.zip states).zip states.tail do
    if let .save B := e then
      -- save_fresh: a save stores the whole batch, and only if it is fresh, or nothing.
      unless s'.store.length == s.store.length || (s'.store.length == s.store.length + B.length && isFresh s.store B) do
        out := "save_fresh" :: out
      -- run_closed: the store holds every predecessor of each fact it holds.
      unless isClosed [] s'.store do out := "run_closed" :: out
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

/-- The users, whose facts every history saves first. -/
def users : List User := [100, 101, 102, 103]

def genUser : Gen (Option User) := do
  if ← chance 1 6 then return none else return some (← pick users)

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
`policyVia`, so that most writers who may create the fact get it stored. -/
def genUpload : Gen Event := do
  let key ← below 8
  let matching := String.ofList (← repeatGen (key % 3 + 3 * (← below 2)) (pick ['a', 'b']))
  let bytes ← if ← chance 1 2 then genBytes else pure matching
  return .write (← genUser) key bytes

/-- Memberships of random users in random facts of type `t`, some removed, and
some of the removals restored. -/
def genMemberships (g : Graph) (t : Name) : Gen (List Fact) := do
  let groups := (g.filter (·.type == t)).map (·.id)
  if groups.isEmpty then return []
  let mut ms := []
  for i in [0:4] do
    ms := ms ++ [{ id := 200 + i, type := "Member", predecessors := [("group", ← pick groups), ("user", ← pick users)] }]
  let mut rs := []
  for m in ms do
    if ← chance 1 2 then rs := rs ++ [{ id := m.id + 100, type := "Removal", predecessors := [("member", m.id)] }]
  let mut ss := []
  for r in rs do
    if ← chance 1 2 then ss := ss ++ [{ id := r.id + 100, type := "Restore", predecessors := [("removal", r.id)] }]
  return ms ++ rs ++ ss

/-- The graph's facts and the memberships, interleaved at random, each in its
own order, and a membership only once its predecessors are placed. Half the
time a membership is placed as soon as it can be, so that the graph's later
facts arrive for readers already admitted. -/
def genOrder (graph extra : List Fact) : Gen (List Fact) := do
  let eager ← chance 1 2
  let mut a := graph
  let mut b := extra
  let mut out : List Fact := []
  for _ in [0:graph.length + extra.length] do
    let ready := match b with
      | f :: _ => f.predecessors.all fun p => users.contains p.2 || out.any (·.id == p.2)
      | [] => false
    match a, b with
    | x :: a', f :: b' =>
      if ready && (eager || (← chance 1 2)) then out := out ++ [f]; b := b'
      else out := out ++ [x]; a := a'
    | x :: a', [] => out := out ++ [x]; a := a'
    | [], f :: b' => out := out ++ [f]; b := b'
    | [], [] => pure ()
  return out

/-- A history: the users' facts, then `facts` saved in batches of one to four,
with uploads and reads with proofs from `pool` among them. One batch in ten
also repeats a fact already saved, so is not fresh, and is not stored; one in
ten is preceded by a later fact saved alone before a predecessor it names, so
not closed, and not stored. Some
uploads are for a key that is not saved yet; many repeat a key. -/
def genHistory (facts : List Fact) (pool : List (Option User × FactId × Proof)) : Gen (List Request) := do
  let mut hs : List Request := [.event (.save (users.map fun u => { id := u, type := "Jinaga.User", predecessors := [] }))]
  let mut rest := facts
  let mut saved : List Fact := []
  while !rest.isEmpty do
    for _ in [0:(← below 3)] do
      hs := hs ++ [.event (← genUpload)]
    let n := (← below 4) + 1
    let mut B := rest.take n
    saved := saved ++ B
    rest := rest.drop n
    if !saved.isEmpty && (← chance 1 10) then B := B ++ [← pick saved]
    -- One batch in ten is preceded by a later fact alone, before a
    -- predecessor it names: not closed, so not stored.
    let early := rest.filter fun f => f.predecessors.any fun p => !users.contains p.2 && !saved.any (·.id == p.2)
    if !early.isEmpty && (← chance 1 10) then hs := hs ++ [.event (.save [← pick early])]
    hs := hs ++ [.event (.save B)]
    for _ in [0:(← below 3) + 1] do
      let (u, k, p) ← pick pool
      hs := hs ++ [.read u k p]
  for _ in [0:(← below 4)] do
    hs := hs ++ [.event (← genUpload)]
  return hs

/-- `cached_read`: every read in the history, answered by the cached
replicator whose saves invalidate as `m` makes them, is answered as
`Replicator.read` answers it on the state the same events produce. -/
def cacheViolations (m : CacheMutant) (P : Policy) (hs : List Request) : List String := Id.run do
  let mut c := Cached.empty
  let mut r := Replicator.empty
  for q in hs do
    match q with
    | .read u k p =>
      let (c', resp) := c.read P u k p
      if resp != r.read P u k p then return ["cached_read"]
      c := c'
    | .event e => c := cachedStepWith m P c q; r := r.step P e
  return []

/-- The cache mutant family with no field changed is `Cached.step`: the same
entries after every request. -/
def cacheFamilyAgrees (P : Policy) (hs : List Request) : Bool := Id.run do
  let mut c := Cached.empty
  let mut c' := Cached.empty
  for q in hs do
    c := c.step P q
    c' := cachedStepWith {} P c' q
    let key (e : Entry) := (e.user, e.key, e.admitted)
    unless c.cache.map key == c'.cache.map key && c.replicator.store.map (·.id) == c'.replicator.store.map (·.id) do return false
  return true

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
  let mut cacheCaught : List Nat := cacheMutants.map fun _ => 0
  let mut requests := 0
  let mut notFresh := 0
  let mut notClosed := 0
  -- `confirms_eq_yields`: on bound proofs, the check is `Proof.yields`.
  let mut confirmDisagree := 0
  -- How often `reorderChecked` refuses a pinned specification, so the check
  -- reads it in written order.
  let mut pinned := 0
  let mut fallback := 0
  for _ in [0:histories] do
    let ((g, hs, rs, policy), gen') := (do
      -- One history in three has child specifications.
      let children ← chance 1 3
      let s ← if children then genChildSpec else genSpec
      let g ← if children then genFeedGraph s 6 else genAcyclicGraph s 6
      -- The rule's group: the first given, or half the time a predecessor of it.
      let givenType := (s.given.head?.map (·.type)).getD ""
      let roles := (g.filter (·.type == givenType)).flatMap fun f => f.predecessors.filterMap fun (r, id) =>
        (g.factOf id).map fun t => ({ name := r, predecessorType := t.type } : Role)
      let via ← if !roles.isEmpty && (← chance 1 2) then some <$> pick roles else pure none
      let groupOf (f : Fact) : List FactId := match via with
        | none => [f.id]
        | some r => f.predecessors.filterMap fun (n, id) => if n == r.name then some id else none
      let extra ← genMemberships g ((via.map (·.predecessorType)).getD givenType)
      let memberUsers := extra.filterMap fun m => if m.type == "Member" then m.predecessors.lookup "user" else none
      let memberGroups := extra.filterMap fun m => if m.type == "Member" then m.predecessors.lookup "group" else none
      -- A few proofs, read again and again through the history: often by a
      -- member, of a group with members, for a key the proof yields.
      let mut pool := []
      for _ in [0:4] do
        let key ← below 8
        let mut givens ← genGivens s g key
        let admitted := (g.filter fun f => f.type == givenType && (groupOf f).any memberGroups.contains).map (·.id)
        if !givens.isEmpty && !admitted.isEmpty && (← chance 2 3) then givens := givens.set 0 (← pick admitted)
        let p : Proof := { spec := s, givens }
        let yielded := (p.spec.descendants.flatMap fun d => (d.read g (d.bindGivens givens)).flatten).filterMap id
        let key ← if !yielded.isEmpty && (← chance 2 3) then pick yielded else pure key
        let user ← if !memberUsers.isEmpty && (← chance 2 3) then some <$> pick memberUsers else genUser
        pool := (user, key, p) :: pool
      let hs ← genHistory (← genOrder g extra) pool
      let mut rs := []
      for key in List.range 8 do
        for user in none :: users.map some do
          rs := (user, key, { spec := s, givens := ← genGivens s g key : Proof }) :: rs
      -- Some proofs have an ill-formed child specification: one that declares
      -- its parent's unknowns again.
      if !s.matchList.isEmpty then
        let bad := { s with projection := .composite [.specification "again" s.matchList s.projection] }
        rs := (some 0, 0, { spec := bad, givens := ← genGivens bad g 0 : Proof }) :: rs
      return (g, hs, rs, policyVia via) : Gen (Graph × List Request × List (Option User × FactId × Proof) × Policy)).run gen
    gen := gen'
    let evs := hs.filterMap Request.event?
    requests := requests + hs.length
    let mut before := Replicator.empty
    for e in evs do
      if let .save B := e then
        if !isFresh before.store B then notFresh := notFresh + 1
        if !isClosed before.store B then notClosed := notClosed + 1
      before := before.step policy e
    unless cacheFamilyAgrees policy hs do
      throw <| IO.userError "the cache mutant family differs from Cached.step"
    unless (cacheViolations {} policy hs).isEmpty do
      real := real + 1
      if first.isNone then first := some s!"cached_read: {hs.length} requests"
    cacheCaught := (cacheCaught.zip cacheMutants).map fun (n, (_, m)) =>
      if (cacheViolations m policy hs).isEmpty then n else n + 1
    let r := Replicator.run policy evs
    if let some (_, _, p) := rs.getLast? then
      for d in p.spec.descendants do
        for l in d.projection.labels do
          if let some m := d.matchList.find? (·.unknown.name == l) then
            pinned := pinned + 1
            if (reorderChecked (d.pinResult m.unknown)).isNone then fallback := fallback + 1
    -- The mutant family with no rule changed is the specification's handlers.
    let r' := evs.foldl (stepWith {} policy) .empty
    unless r.objects == r'.objects && r.store.map (·.id) == r'.store.map (·.id) do
      throw <| IO.userError "the mutant family's write or save differs from Replicator.step"
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
  IO.println s!"histories {histories}, requests {requests}, batches not fresh {notFresh}, not closed {notClosed}, objects stored {stored}, reads {reads}, served {served}"
  IO.println s!"real handlers: {real} histories break a statement; yields disagrees with readsOf on {disagree} reads, confirms with yields on {confirmDisagree} bound reads"
  IO.println s!"pinned specifications {pinned}, read in written order (reorderChecked refuses) {fallback}"
  for ((label, _), (n, by_)) in mutants.zip caught do
    IO.println s!"  mutant \"{label}\": caught on {n} of {histories} histories, by {by_.mergeSort (· ≤ ·)}"
  for ((label, _), n) in cacheMutants.zip cacheCaught do
    IO.println s!"  cache mutant \"{label}\": caught on {n} of {histories} histories, by cached_read"
  if disagree > 0 || confirmDisagree > 0 then return 1
  match first with
  | some f => IO.println s!"\nFIRST FAILURE\n{f}"; return 1
  | none =>
    -- Each mutant must be caught by the statement its label names.
    let named := (caught.zip mutants).all fun ((_, by_), (label, _)) => by_.any (label.startsWith ·)
    return if named && cacheCaught.all (· > 0) then 0 else 1
