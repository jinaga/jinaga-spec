import JinagaSpec.ContentCache
import JinagaSpec.Proofs.Content
import JinagaSpec.Proofs.Stream
import JinagaSpec.Proofs.WellFormedCheck

/-!
# The cache never changes an answer (NF-2, SEC-7)

* `isFresh_iff`: the check `Replicator.step` runs before storing a batch
  decides `Fresh`, the hypothesis of `candidates_complete`.
* `yields_stable`: a fresh batch that `Proof.mayChange` does not flag leaves
  `Proof.yields` as it was. This is `candidates_complete` read for one fact:
  whether a proof yields `k` depends only on which rows naming `k` it reads,
  and every such row that the batch adds or removes is a candidate.
* `admits_stable`: so does the whole decision, for an entry the save does not
  invalidate.
* `cache_valid`: after any history, every cached decision is the one the
  current store gives, for a bound proof.
* `cached_read`: so the cached replicator answers every read exactly as the
  uncached one does, on the state the same events produce.
* `cached_read_authorized` (SEC-7, pointwise): every read answered with an
  object, from the cache or not, satisfies SEC-1 at that moment.

SEC-7 as written ("once the proof stops yielding the fact, or the user loses
distribution rights, no later read returns the object") is false of Jinaga:
a revocation is a negative existential condition, and a later fact can undo it
(a restore), so a proof can stop and then start yielding again. What holds, and
what the cache must not break, is SEC-1 at the moment of each read.

No theorem here has a hypothesis on the history: `Replicator.step` stores only
a fresh batch.
-/
namespace JinagaSpec

theorem isFresh_iff (g : Graph) (B : List Fact) : isFresh g B = true ↔ Fresh g B := by
  simp only [isFresh, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨fun h => ⟨fun x hx b hb => (h b hb x hx).1, fun x hx p hp b hb => (h b hb x hx).2 p hp⟩,
    fun h b hb x hx => ⟨h.idNew x hx b hb, fun p hp => h.unreferenced x hx p hp b hb⟩⟩

mutual
  theorem Projection.eq_of_beq : ∀ {a b : Projection}, Projection.beq a b = true → a = b
    | .fact _, .fact _, h => by simp [Projection.beq] at h; rw [h]
    | .composite _, .composite _, h => by rw [Component.eq_of_beqList h]
    | .fact _, .composite _, h | .composite _, .fact _, h => by simp [Projection.beq] at h

  theorem Component.eq_of_beqList : ∀ {a b : List Component}, Component.beqList a b = true → a = b
    | [], [], _ => rfl
    | _ :: _, _ :: _, h => by
      simp only [Component.beqList, Bool.and_eq_true] at h
      rw [Component.eq_of_beq h.1, Component.eq_of_beqList h.2]
    | [], _ :: _, h | _ :: _, [], h => by simp [Component.beqList] at h

  theorem Component.eq_of_beq : ∀ {a b : Component}, Component.beq a b = true → a = b
    | .fact _ _, .fact _ _, h => by
      simp only [Component.beq, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, h.2]
    | .specification _ _ _, .specification _ _ _, h => by
      simp only [Component.beq, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1, Match.eq_of_beqList h.1.2, Projection.eq_of_beq h.2]
    | .fact _ _, .specification _ _ _, h | .specification _ _ _, .fact _ _, h => by simp [Component.beq] at h
end

theorem Proof.eq_of_beq {p q : Proof} (h : p.beq q = true) : p = q := by
  obtain ⟨⟨g, ms, pr⟩, gs⟩ := p
  obtain ⟨⟨g', ms', pr'⟩, gs'⟩ := q
  simp only [Proof.beq, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1.1.1, Match.eq_of_beqList h.1.1.2, Projection.eq_of_beq h.1.2, h.2]

theorem any_congr_mem {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.any_cons, h a (.head _), ih fun b hb => h b (.tail _ hb)]

theorem all_congr_mem {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) : l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.all_cons, h a (.head _), ih fun b hb => h b (.tail _ hb)]

/-- **A fresh batch that `mayChange` does not flag leaves `yields` as it was.** -/
theorem yields_stable {p : Proof} {g : Graph} {B : List Fact} {k : FactId} (hb : p.bound = true)
    (hf : Fresh g B) (h : p.mayChange g B k = false) : p.yields (g ++ B) k = p.yields g k := by
  have hwf := (isWellFormedDeep_iff p.spec).1 (by simp_all [Proof.bound])
  simp only [Proof.mayChange, List.any_eq_false, Bool.not_eq_true] at h
  refine any_congr_mem fun d hd => ?_
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  have hc := candidates_complete d (hwf d hd) hf (d.bindGivens p.givens)
  have hk : ∀ r, r.contains (some k) = true → (r ∈ d.read g _ ↔ r ∈ d.read (g ++ B) _) := fun r hr =>
    (hc r).resolve_right fun hm => Bool.eq_false_iff.1 (h d hd r hm) hr
  exact ⟨fun ⟨r, hr, hk'⟩ => ⟨r, (hk r hk').2 hr, hk'⟩, fun ⟨r, hr, hk'⟩ => ⟨r, (hk r hk').1 hr, hk'⟩⟩

/-- **A decision the save does not invalidate stands.** -/
theorem admits_stable {P : Policy} {g : Graph} {B : List Fact} {e : Entry} (hb : e.proof.bound = true)
    (hf : Fresh g B) (h : P.invalidates g B e = false) :
    P.admits (g ++ B) e.user e.key e.proof = P.admits g e.user e.key e.proof := by
  simp only [Policy.invalidates, Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true] at h
  simp only [Policy.admits, Policy.distributes, yields_stable hb hf h.1]
  congr 1
  refine all_congr_mem fun clause hc => any_congr_mem fun q hq => ?_
  cases hq' : q.bound
  · rfl
  · simp [yields_stable hq' hf (h.2 clause hc q hq)]

/-- Every cached decision is the one the store gives now, for a bound proof. -/
def Cached.Valid (P : Policy) (c : Cached) : Prop :=
  ∀ e ∈ c.cache, e.proof.bound = true ∧ e.admitted = P.admits c.replicator.store e.user e.key e.proof

/-- On a valid cache, a read answers as `Replicator.read` does, keeps the
cache valid, and changes neither store nor objects. -/
theorem Cached.read_valid {P : Policy} {c : Cached} (hv : c.Valid P) (user : Option User) (key : FactId)
    (p : Proof) :
    (c.read P user key p).2 = c.replicator.read P user key p ∧ (c.read P user key p).1.Valid P ∧
      (c.read P user key p).1.replicator = c.replicator := by
  cases user with
  | none => exact ⟨rfl, hv, rfl⟩
  | some u =>
    cases hb : p.bound
    · simp [read, Replicator.read, hb, hv]
    rw [Replicator.read_bound hb]
    cases he : c.cache.find? fun e => e.user == u && e.key == key && e.proof.beq p <;>
      simp only [Cached.read, Cached.admits, hb, he, Bool.not_true, Bool.false_eq_true, ite_false]
    case some e =>
      have hm := List.find?_some he
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨⟨rfl, rfl⟩, hp⟩ := hm
      rw [← Proof.eq_of_beq hp, ← (hv e (List.mem_of_find?_eq_some he)).2]
      exact ⟨rfl, hv, trivial⟩
    case none =>
      rw [confirms_eq_yields (p.bound_iff.1 hb).2]
      refine ⟨rfl, fun e he => ?_, trivial⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨hb, rfl⟩
      · exact hv e he

/-- Every request keeps the cache valid, and moves the replicator as its event
does. -/
theorem Cached.step_valid {P : Policy} {c : Cached} (hv : c.Valid P) (q : Request) :
    (c.step P q).Valid P ∧ (c.step P q).replicator = match q.event? with
      | some e => c.replicator.step P e
      | none => c.replicator := by
  match q with
  | .read u key p => exact (read_valid hv u key p).2
  | .event (.write u key o) =>
    refine ⟨fun e he => ?_, rfl⟩
    simpa [Cached.step, Replicator.step, Replicator.write_store] using hv e he
  | .event (.save B) =>
    refine ⟨fun e he => ?_, rfl⟩
    rw [Cached.step] at he ⊢
    by_cases hB : isFresh c.replicator.store B
    · simp only [hB, ite_true, List.mem_filter, Bool.not_eq_true'] at he
      simpa [Replicator.step, hB, admits_stable (hv e he.1).1 ((isFresh_iff _ _).1 hB) he.2] using hv e he.1
    · simp only [hB, Bool.false_eq_true, ite_false] at he
      simpa [Replicator.step, hB] using hv e he

theorem Cached.run_valid (P : Policy) (hs : List Request) :
    (Cached.run P hs).Valid P ∧ (Cached.run P hs).replicator = Replicator.run P (hs.filterMap Request.event?) := by
  unfold Cached.run Replicator.run
  suffices ∀ (c : Cached), c.Valid P → (hs.foldl (Cached.step P) c).Valid P ∧
      (hs.foldl (Cached.step P) c).replicator = (hs.filterMap Request.event?).foldl (Replicator.step P) c.replicator from
    this .empty fun _ h => nomatch h
  induction hs with
  | nil => exact fun c hv => ⟨hv, rfl⟩
  | cons q hs ih =>
    intro c hv
    obtain ⟨hv', hr⟩ := step_valid hv q
    refine (ih _ hv').imp_right fun h => h.trans ?_
    cases q <;> simp_all [Request.event?, List.filterMap_cons]

/-- **The cache is valid.** After any history of saves, uploads and reads,
every cached decision is the one the current store gives, for a bound proof. -/
theorem cache_valid (P : Policy) (hs : List Request) : (Cached.run P hs).Valid P :=
  (Cached.run_valid P hs).1

/-- **The cache never changes an answer (NF-2).** After any history, a read
from the cached replicator answers exactly as `Replicator.read` does on the
state the same saves and uploads produce. -/
theorem cached_read (P : Policy) (hs : List Request) (user : Option User) (key : FactId) (p : Proof) :
    ((Cached.run P hs).read P user key p).2 = (Replicator.run P (hs.filterMap Request.event?)).read P user key p := by
  rw [(Cached.read_valid (cache_valid P hs) user key p).1, (Cached.run_valid P hs).2]

/-- **SEC-7, pointwise.** A read answered with an object, whether its decision
came from the cache or not, is by an authenticated user whom the distribution
rules let run the proof on the store at that moment, and whose proof yields
the content fact there. -/
theorem cached_read_authorized {P : Policy} {hs : List Request}
    (h : ((Cached.run P hs).read P user key p).2 = .ok o) :
    ∃ u, user = some u ∧ P.distributes u p.spec p.givens (Cached.run P hs).replicator.store = true ∧
      p.yields (Cached.run P hs).replicator.store key = true := by
  rw [(Cached.read_valid (cache_valid P hs) user key p).1] at h
  exact read_authorized h

end JinagaSpec
