import JinagaSpec.ContentCache

/-!
# Holding a Reactive read (RR-6, SEC-6)

`Replicator.read` decides at once. RR-6 asks more of a read the rules may yet
admit: hold it for up to a timeout, re-evaluate it as facts are saved, then
answer with the object or 403, or 409 Retry-After if it is still undecided;
never 403 while it is still Reactive. SEC-6: if the granting facts are saved
within the timeout, a read that began while Reactive returns the object.

## What Reactive means (jinaga-spec#65)

Reactive is derived from the distribution rules, as jinaga-server's
`POST /feeds` derives its `decision`: a specification is Reactive for a user
when the rules do not let them run it now (`canDistributeToAll` fails), and
some rule could: `intersectForSubscribe` finds a rule with a user
specification whose share feed has the target's shape and givens. The server
rewrites the specification, through intersection with that rule's user
condition, into one that filters on the authorizing fact, and delivers its
results as soon as that fact arrives. With no such rule the read is Denied:
403 at once. Rules combine with OR, so one rule is enough.

In this model `Policy.distribution` already lists, for a specification and its
givens, the rule proofs that match its shape, clause by clause, and a rule
proof is usable exactly when it is bound (`Proof.bound`: the givens' count,
and every descendant well formed). So "some rule matches the read's shape and
has a user condition" is `Policy.rewrites`: some clause has a bound rule proof.
It reads the proof and the rules only, never the store and never `objects`;
the store enters only through `Policy.distributes`, which is condition (1).

A proof that does not yet yield the content fact is not Reactive: the rules
authorize its specification, so the server can answer, and the answer is 403
(RR-5). Reactive does not promise that a later save admits the read (a reader
may stay Reactive until the timeout), so no theorem says it will.

## The hold

A held read keeps its user, key, proof and deadline. Each save re-evaluates
the held reads whose decision it may change, which `Policy.invalidates`
names, exactly as it drops their cache entries (`ContentCache.lean`): a held
read is a refused decision, so its entry is `(user, proof, key, false)`. A
read no longer Reactive is answered as `Replicator.read` answers it on the new
store. A tick advances the clock and answers 409 every held read whose
deadline has passed: a hold with timeout `t` survives `t` ticks. The decision
is recomputed each time from the store, never taken from the cache.

`Proofs/ContentHold.lean` proves that waking only the reads `invalidates`
names is the same as re-evaluating every held read on every save
(`wake_on_invalidates`), that every answer other than 409 is `read`'s on the
store at that moment, given while the read is not Reactive (`held_answer`),
and SEC-1, SEC-5 and SEC-6 for held reads.

Written in the same portable subset as `Split.lean`.
-/
namespace JinagaSpec

/-- Some distribution rule could admit the proof once its user condition
holds: some clause has a bound rule proof. Reads no store. -/
def Policy.rewrites (P : Policy) (p : Proof) : Bool :=
  (P.distribution p.spec p.givens).any (·.any Proof.bound)

/-- The read is Reactive on `g` (RR-6): authenticated, with a bound proof, not
distributed to the user now, and some rule could admit it. -/
def Policy.reactive (P : Policy) (g : Graph) (user : Option User) (p : Proof) : Bool :=
  match user with
  | some u => p.bound && P.rewrites p && !P.distributes u p.spec p.givens g
  | none => false

/-- A read held until a deadline, in ticks. -/
structure Hold where
  user : Option User
  key : FactId
  proof : Proof
  deadline : Nat

/-- Saving the fresh batch `B` onto `g` may change the held read's decision:
`Policy.invalidates` names its entry, a refused decision. -/
def Hold.wakes (P : Policy) (g : Graph) (B : List Fact) (h : Hold) : Bool :=
  h.user.any fun u => P.invalidates g B { user := u, proof := h.proof, key := h.key, admitted := false }

/-- The cached replicator, a clock, and the reads held. -/
structure Holding where
  cached : Cached := .empty
  clock : Nat := 0
  held : List Hold := []

/-- Move to the cached replicator `c`, and answer, as `Replicator.read` does on
it, each held read that `woken` picks and that is no longer Reactive there. -/
def Holding.settle (P : Policy) (s : Holding) (c : Cached) (woken : Hold → Bool) : Holding × List (Hold × Response) :=
  let (done, held) := s.held.partition fun h => woken h && !P.reactive c.replicator.store h.user h.proof
  ({ s with cached := c, held }, done.map fun h => (h, c.replicator.read P h.user h.key h.proof))

/-- A request, and the held reads it answers. A hold not Reactive is answered
at once; a save wakes the held reads it may change; a tick times out those
past their deadline. Reads and uploads are answered by `Cached`. -/
def Holding.step (P : Policy) (s : Holding) : Request → Holding × List (Hold × Response)
  | .event (.save B) => s.settle P (s.cached.step P (.event (.save B))) (Hold.wakes P s.cached.replicator.store B)
  | .hold user key p t =>
    let h : Hold := { user, key, proof := p, deadline := s.clock + t }
    if P.reactive s.cached.replicator.store user p then ({ s with held := s.held ++ [h] }, [])
    else (s, [(h, s.cached.replicator.read P user key p)])
  | .tick =>
    let (late, held) := s.held.partition (·.deadline < s.clock + 1)
    ({ s with clock := s.clock + 1, held }, late.map (·, .retryAfter))
  | q => ({ s with cached := s.cached.step P q }, [])

/-- The state after a history of requests, from an empty replicator, cache
and clock. -/
def Holding.run (P : Policy) (hs : List Request) : Holding :=
  hs.foldl (fun s q => (s.step P q).1) {}

end JinagaSpec
