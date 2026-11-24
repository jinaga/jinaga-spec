import JinagaSpec

/-!
# Mutants of the content store

One read handler, one write handler and one save step, parameterized over the
rule each mutant breaks. Shared by `check-content`, which checks that SEC-1 to
SEC-5, `read_badRequest`, `confirms_eq_yields`, `read_admitted`,
`Replicator.save_fresh` and `Replicator.run_closed` rule out each one, and `lake exe vectors`, which checks that the content vectors
catch each one.
-/
open JinagaSpec

/-- What a mutant changes. With no field changed, `readWith`, `writeWith` and
`stepWith` are `Replicator.read`, `Replicator.write` and `Replicator.step`, which `check-content` confirms on
every request. The specification's own handlers stay unparameterized. -/
structure Mutant where
  /-- Which proofs a read accepts (RR-1). -/
  bound : Proof → Bool := Proof.bound
  /-- How a read finds the object for a key. -/
  lookup : Policy → Replicator → FactId → Option Bytes := fun _ r k => r.objects.lookup k
  /-- Whether the rules admit a reader: the distribution rules, and the
  replicator's check that the proof yields the key. -/
  admits : Policy → Graph → User → FactId → Proof → Bool :=
    fun P g u key p => P.distributes u p.spec p.givens g && p.confirms g key
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
  /-- A save stores a batch only if it is fresh. -/
  checkFresh : Bool := true
  /-- A save stores a batch only if the store and the batch hold every
  predecessor it names. -/
  checkClosed : Bool := true

def readWith (m : Mutant) (P : Policy) (r : Replicator) (user : Option User) (key : FactId) (p : Proof) :
    Response :=
  match user with
  | none => .unauthenticated
  | some u =>
    if !m.bound p then .badRequest
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
  | .save B =>
    if (!m.checkFresh || isFresh r.store B) && (!m.checkClosed || isClosed r.store B) then
      { r with store := r.store ++ B }
    else r
  | .write u key o => (writeWith m P r u key o).1

/-- The spoof: any object stored under a key whose fact has the same content
hash. -/
def byContentHash (P : Policy) (r : Replicator) (k : FactId) : Option Bytes :=
  match (r.store.factOf k).bind P.contentHash with
  | none => none
  | some h => (r.objects.find? fun (k', _) => (r.store.factOf k').bind P.contentHash == some h).map (·.2)

/-- What a mutant of the replicator's check, `Proof.confirms`, changes. With
no field changed, `confirmsWith` is `Proof.confirms`, which `check-content`
confirms on every read. -/
structure Check where
  /-- The specifications checked: every descendant, or fewer. -/
  descendants : Specification → List Specification := Specification.descendants
  /-- The projected labels bound to the content fact: all, or fewer. -/
  labels : List Name → List Name := id
  /-- The pinned match keeps its own conditions. -/
  keepConditions : Bool := true
  /-- Every given must be held. -/
  held : Bool := true

def Check.pinResult (c : Check) (d : Specification) (u : Label) : Specification :=
  { given := d.given ++ [{ name := pinLabel, type := u.type }], projection := .fact u.name,
    matchList := d.matchList.map fun m => if m.unknown.name == u.name then
      .mk m.unknown (pinCondition :: if c.keepConditions then m.conditions else []) else m }

def Check.bindsResult (c : Check) (d : Specification) (g : Graph) (env : Env) (key : FactId) (l : Name) : Bool :=
  match d.matchList.find? (·.unknown.name == l) with
  | some m => !((reorderOrSelf (c.pinResult d m.unknown)).evaluate g (env.bind pinLabel key)).isEmpty
  | none => env l == some key && !(evalMatches g env d.matchList).isEmpty

def confirmsWith (c : Check) (p : Proof) (g : Graph) (key : FactId) : Bool :=
  (c.descendants p.spec).any fun d =>
    let env := d.bindGivens p.givens
    (!c.held || d.given.all (g.has env)) && (c.labels d.projection.labels).any (c.bindsResult d g env key)

/-- Mutants of the replicator's check that a proof yields the key. -/
def checkMutants : List (String × Check) := [
  ("read_admitted: yields ignores child specifications", { descendants := fun s => [s] }),
  ("read_admitted: bind only the first projected label", { labels := List.take 1 }),
  ("SEC-1: drop the pinned match's own conditions", { keepConditions := false }),
  ("confirms_eq_yields: skip the check that the givens are held", { held := false })
]

def mutants : List (String × Mutant) := [
  ("SEC-1: no yields check", { admits := fun P g u _ p => P.distributes u p.spec p.givens g })] ++
  checkMutants.map (fun (label, c) =>
    (label, { admits := fun P g u key p => P.distributes u p.spec p.givens g && confirmsWith c p g key })) ++ [
  ("RR-1: check only the top-level specification",
    { bound := fun p => p.givens.length == p.spec.given.length && isWellFormed p.spec }),
  ("SEC-1: no distribution check", { admits := fun _ g _ key p => p.yields g key }),
  ("SEC-2: store bytes without hashing them", { checkHash := false }),
  ("SEC-3: authorize the fact's presence, not the writer", { mayCreate := fun _ _ _ _ => true }),
  ("SEC-3: map a key to stored bytes of the same hash", { hashShortcut := true }),
  ("SEC-4: look an object up by its content hash", { lookup := byContentHash }),
  ("SEC-5: answer 404 before checking the proof", { existenceFirst := true }),
  ("SEC-5: answer a repeat upload before checking the writer", { repeatFirst := true }),
  ("save_fresh: store a batch without checking it is fresh", { checkFresh := false }),
  ("run_closed: store a batch that names a predecessor not stored", { checkClosed := false })
]


/-! ## Mutants of the cache

One cached replicator, parameterized over how a save invalidates
(`ContentCache.lean`). With no field changed, `cachedStepWith` is
`Cached.step` and `candidatesWith` is `candidates`, which `check-content`
confirms on every request. Each mutant is a way to invalidate too little. -/

/-- A batch's candidates (`candidates`, `Reorder.lean`), parameterized over the
inverses, whether a given arriving in the batch counts, and the graph each
fact's inverses read. -/
def candidatesWith (inv : Specification → List Specification) (arrival : Bool)
    (graph : Graph → List Fact → Fact → Graph) (s : Specification) (env : Env) (g : Graph) (B : List Fact) :
    List Row :=
  let inverses := (inv s).map reorderOrSelf
  B.flatMap fun f =>
    let new := graph g B f
    if arrival && s.given.any (env ·.name == some f.id) then s.read new env
    else inverses.flatMap (·.evaluate new (pinEnv s env f))

structure CacheMutant where
  inverses : Specification → List Specification := JinagaSpec.inverses
  /-- A given arriving in the batch makes every result a candidate. -/
  arrival : Bool := true
  /-- The graph a fact's inverses read: the store and the whole batch. -/
  graph : Graph → List Fact → Fact → Graph := fun g B _ => g ++ B
  /-- The rule proofs are checked, not only the reader's. -/
  rules : Bool := true
  /-- An entry the rules refused is invalidated too. -/
  refused : Bool := true
  /-- Any fact may invalidate, not only one of the content fact's type. -/
  anyType : Bool := true

def CacheMutant.mayChange (m : CacheMutant) (p : Proof) (g : Graph) (B : List Fact) (k : FactId) : Bool :=
  p.spec.descendants.any fun d =>
    (candidatesWith m.inverses m.arrival m.graph d (d.bindGivens p.givens) g B).any (·.contains (some k))

def CacheMutant.invalidates (m : CacheMutant) (P : Policy) (g : Graph) (B : List Fact) (e : Entry) : Bool :=
  (m.refused || e.admitted) &&
    (m.anyType || B.any fun f => ((g ++ B).factOf e.key).any (·.type == f.type)) &&
    (m.mayChange e.proof g B e.key ||
      m.rules && (P.distribution e.proof.spec e.proof.givens).any (·.any (m.mayChange · g B e.user)))

def cachedStepWith (m : CacheMutant) (P : Policy) (c : Cached) : Request → Cached
  | .event (.save B) =>
    if c.replicator.store.accepts B then
      { replicator := c.replicator.step P (.save B), cache := c.cache.filter (!m.invalidates P c.replicator.store B ·) }
    else c
  | q => c.step P q

def cacheMutants : List (String × CacheMutant) := [
  ("cached_read: invalidate only on a fact of the content fact's type", { anyType := false }),
  ("cached_read: ignore a given arriving in the batch", { arrival := false }),
  ("cached_read: read each fact of a batch alone", { graph := fun g _ f => g ++ [f] }),
  ("cached_read: never invalidate on a revocation", { inverses := inversesFor true }),
  ("cached_read: keep the entries the rules refused", { refused := false }),
  ("cached_read: invalidate on the reader's proof only, never the rules", { rules := false })
]
