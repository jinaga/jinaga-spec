import JinagaSpec.Content
import JinagaSpec.Reorder

/-!
# Caching read decisions (NF-2)

The replicator SHOULD cache proof results per user, specification and givens
(NF-2), and any saved fact that could change a result MUST invalidate the
entry. `Cached` is the replicator of `Content.lean` with a cache of
`Policy.admits` decisions, keyed by user, proof and content key.

A decision is `P.distributes u p.spec p.givens g && p.yields g key`, and both
parts are proofs read on the store: the reader's own, and each rule proof of
`P.distribution p.spec p.givens`, run for the user. So the inverse candidates
of `Reorder.lean`, which find every result a fresh batch adds or removes, also
find every decision it may change: a save of a fresh batch `B` onto `g` drops an
entry when, for the reader's proof and the content key, or for some rule proof
and the user, some descendant has a candidate row naming that fact
(`Proof.mayChange`). The candidates include those of negative existential
conditions, so a revocation invalidates, and of conditions nested under them,
so a restore does too.

A read with no token, or with a proof that is not bound, is answered as
`Replicator.read` answers it, and nothing is cached. Otherwise the decision is
taken from the cache, or computed on the store and cached. Reads change the
state, so a history (`Request`) holds reads as well as events.

`Proofs/ContentCache.lean` proves that the cache never changes an answer
(`cached_read`), so SEC-1 holds at the moment of every read, cached or not
(`cached_read_authorized`): the pointwise form of SEC-7.

Written in the same portable subset as `Split.lean`.
-/
namespace JinagaSpec

/-! ## Comparing proofs -/

/-- The same specification, run with the same givens. -/
def Proof.beq (p q : Proof) : Bool :=
  p.spec.given == q.spec.given && Match.beqList p.spec.matchList q.spec.matchList &&
    Projection.beq p.spec.projection q.spec.projection && p.givens == q.givens

/-! ## Invalidation -/

/-- Saving the fresh batch `B` onto `g` may change whether the proof yields
`k`: for some descendant of its specification, some candidate row (`candidates`,
`Reorder.lean`) names `k`. -/
def Proof.mayChange (p : Proof) (g : Graph) (B : List Fact) (k : FactId) : Bool :=
  p.spec.descendants.any fun d => (candidates d (d.bindGivens p.givens) g B).any (·.contains (some k))

/-- A cached decision: whether the rules admit `user` reading `key` with
`proof`. -/
structure Entry where
  user : User
  proof : Proof
  key : FactId
  admitted : Bool

/-- Saving the fresh batch `B` onto `g` may change the entry's decision: it may
change whether the reader's proof yields the key, or whether one of the
distribution rule proofs yields the user. -/
def Policy.invalidates (P : Policy) (g : Graph) (B : List Fact) (e : Entry) : Bool :=
  e.proof.mayChange g B e.key ||
    (P.distribution e.proof.spec e.proof.givens).any (·.any (·.mayChange g B e.user))

/-! ## The cached replicator -/

structure Cached where
  replicator : Replicator
  cache : List Entry

def Cached.empty : Cached := { replicator := .empty, cache := [] }

/-- The rules' decision for `u` reading `key` with `p`: cached, or computed on
the store as `Replicator.read` computes it (`Proof.confirms`), and cached. -/
def Cached.admits (P : Policy) (c : Cached) (u : User) (key : FactId) (p : Proof) : Cached × Bool :=
  match c.cache.find? fun e => e.user == u && e.key == key && e.proof.beq p with
  | some e => (c, e.admitted)
  | none =>
    let a := P.distributes u p.spec p.givens c.replicator.store && p.confirms c.replicator.store key
    ({ c with cache := { user := u, proof := p, key, admitted := a } :: c.cache }, a)

/-- `Replicator.read`, with the decision taken from the cache. -/
def Cached.read (P : Policy) (c : Cached) (user : Option User) (key : FactId) (p : Proof) :
    Cached × Response :=
  match user with
  | none => (c, .unauthenticated)
  | some u =>
    if !p.bound then (c, .badRequest)
    else
      let (c, a) := c.admits P u key p
      (c, if !a then .forbidden
        else match c.replicator.objects.lookup key with
          | none => .notUploaded
          | some o => .ok o)

/-- An event or a read, in the order the replicator handles them. -/
inductive Request where
  | event (e : Event)
  | read (user : Option User) (key : FactId) (p : Proof)

def Request.event? : Request → Option Event
  | .event e => some e
  | .read .. => none

/-- A save of a batch the store accepts (fresh and closed, `Graph.accepts`)
drops every entry it may invalidate; a save the store refuses changes nothing.
An upload changes no fact, so no decision. -/
def Cached.step (P : Policy) (c : Cached) : Request → Cached
  | .event (.save B) =>
    { replicator := c.replicator.step P (.save B),
      cache := if c.replicator.store.accepts B then c.cache.filter (!P.invalidates c.replicator.store B ·)
        else c.cache }
  | .event e => { c with replicator := c.replicator.step P e }
  | .read u key p => (c.read P u key p).1

/-- The state after a history of requests, from an empty replicator and cache. -/
def Cached.run (P : Policy) (hs : List Request) : Cached :=
  hs.foldl (Cached.step P) .empty

end JinagaSpec
