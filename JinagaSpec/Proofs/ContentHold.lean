import JinagaSpec.ContentHold
import JinagaSpec.Proofs.ContentCache

/-!
# Held reads (RR-6, SEC-6)

* `held_answer`: every answer to a held read is 409, or `Replicator.read`'s
  answer on the store at that moment, given while the read is not Reactive.
  So `held_authorized` (SEC-1 at answer time) and `held_not_forbidden` (never
  403 while Reactive).
* `held_reactive`: after any history, every held read is Reactive on the
  current store, so a 409 too is given only while it is Reactive.
* `held_live` (SEC-6): a save that admits a held read answers it with the
  object, or 404 `not_uploaded`.
* `held_timeout`: a tick answers 409 every held read past its deadline.
* `wake_on_invalidates`: waking only the held reads `Policy.invalidates` names
  is re-evaluating every held read on every save.
* `held_noninterference` (SEC-5): two states that differ only in `objects`
  give every reader not admitted the same answers, and step to states that
  differ only in `objects`; so, step by step, the sequence of such a reader's
  answers and the moment of each.

No theorem has a hypothesis on the history.
-/
namespace JinagaSpec

theorem Cached.read_replicator (P : Policy) (c : Cached) (user : Option User) (key : FactId) (p : Proof) :
    (c.read P user key p).1.replicator = c.replicator := by
  cases user with
  | none => rfl
  | some u =>
    have : (c.admits P u key p).1.replicator = c.replicator := by unfold Cached.admits; split <;> rfl
    simp only [Cached.read]; split
    · rfl
    · generalize c.admits P u key p = x at this ⊢; exact this

theorem List.partition_congr {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.partition f = l.partition g := by
  rw [List.partition_eq_filter_filter, List.partition_eq_filter_filter, List.filter_congr h,
    List.filter_congr (p := not ∘ f) (q := not ∘ g) fun a ha => by simp [h a ha]]

theorem Cached.read_objects (P : Policy) (c : Cached) (objects : List (FactId × Bytes)) (user : Option User)
    (key : FactId) (p : Proof) :
    ({ c with replicator := { c.replicator with objects } }.read P user key p).1 =
      { (c.read P user key p).1 with replicator := { c.replicator with objects } } := by
  cases user with
  | none => rfl
  | some u =>
    cases hb : p.bound
    · simp [Cached.read, hb]
    · cases hf : c.cache.find? fun e => e.user == u && e.key == key && e.proof.beq p <;>
        simp [Cached.read, Cached.admits, hb, hf]

/-- The held read stays Reactive across a save that does not wake it. -/
theorem Hold.reactive_stable {P : Policy} {c : Cached} {h : Hold}
    (hr : P.reactive c.replicator.store h.user h.proof = true) (hw : h.wakes P c.replicator.store B = false) :
    P.reactive (c.step P (.event (.save B))).replicator.store h.user h.proof = true := by
  rcases (c.replicator.save_fresh P B) with he | ⟨he, hf⟩ <;> simp only [Cached.step, he, hr]
  obtain ⟨user, key, p, _⟩ := h
  cases user with
  | none => simp [Policy.reactive] at hr
  | some u =>
    simp only [Hold.wakes, Option.any_some, Policy.invalidates, Bool.or_eq_false_iff] at hw
    simpa only [Policy.reactive, distributes_stable hf hw.2] using hr

/-- Every held read is Reactive on the current store. -/
def Holding.Valid (P : Policy) (s : Holding) : Prop :=
  ∀ h ∈ s.held, P.reactive s.cached.replicator.store h.user h.proof = true

theorem Holding.step_cached (P : Policy) (s : Holding) (q : Request) : (s.step P q).1.cached = s.cached.step P q := by
  unfold step; repeat' split
  all_goals simp_all [settle, Cached.step]

theorem Holding.step_valid {P : Policy} {s : Holding} (hv : s.Valid P) (q : Request) : (s.step P q).1.Valid P := by
  intro h hh
  rw [step_cached]
  match q with
  | .event (.save B) =>
    obtain ⟨hh, hk⟩ := List.mem_filter.1 (by simpa only [step, settle, List.partition_eq_filter_filter] using hh)
    cases hw : h.wakes P s.cached.replicator.store B
    · exact Hold.reactive_stable (hv h hh) hw
    · simpa [hw] using hk
  | .event (.write u k o) => simpa [Cached.step, Replicator.step, Replicator.write_store] using hv h (by simpa [step] using hh)
  | .read u k p => simpa [Cached.step, Cached.read_replicator] using hv h (by simpa [step] using hh)
  | .hold u k p t =>
    simp only [step] at hh
    split at hh
    · rcases List.mem_append.1 hh with hh | hh
      · exact hv h hh
      · rw [List.mem_singleton.1 hh]; assumption
    · exact hv h hh
  | .tick => exact hv h (List.mem_filter.1 (by simpa only [step, List.partition_eq_filter_filter] using hh)).1

theorem Holding.run_valid (P : Policy) (hs : List Request) :
    (Holding.run P hs).Valid P ∧ (Holding.run P hs).cached = Cached.run P hs := by
  unfold Holding.run Cached.run
  suffices ∀ s : Holding, s.Valid P → (hs.foldl (fun s q => (s.step P q).1) s).Valid P ∧
      (hs.foldl (fun s q => (s.step P q).1) s).cached = hs.foldl (Cached.step P) s.cached from this {} nofun
  induction hs with
  | nil => exact fun _ hv => ⟨hv, rfl⟩
  | cons q hs ih => exact fun s hv => by simpa [Holding.step_cached] using ih _ (Holding.step_valid hv q)

/-- **A held read is Reactive.** After any history, every read still held is
Reactive on the current store, whose cached replicator is `Cached.run`'s. -/
theorem held_reactive (P : Policy) (hs : List Request) :
    ∀ h ∈ (Holding.run P hs).held, P.reactive (Cached.run P hs).replicator.store h.user h.proof = true := by
  rw [← (Holding.run_valid P hs).2]; exact (Holding.run_valid P hs).1

/-- **Every answer is 409, or `read`'s, given while not Reactive.** Any other
answer to a held read is the one `Replicator.read` gives on the store at that
moment, and the read is not Reactive there. -/
theorem held_answer {P : Policy} {s : Holding} {q : Request} (ha : (h, a) ∈ (s.step P q).2) :
    a = .retryAfter ∨ (P.reactive (s.step P q).1.cached.replicator.store h.user h.proof = false ∧
      a = (s.step P q).1.cached.replicator.read P h.user h.key h.proof) := by
  rw [Holding.step_cached]
  match q with
  | .event (.save B) =>
    simp only [Holding.step, Holding.settle, List.partition_eq_filter_filter, List.mem_map, List.mem_filter,
      Bool.and_eq_true, Bool.not_eq_true', Prod.mk.injEq] at ha ⊢
    obtain ⟨h', ⟨_, _, hr⟩, rfl, rfl⟩ := ha
    exact .inr ⟨hr, rfl⟩
  | .event (.write ..) | .read .. => simp [Holding.step] at ha
  | .hold u k p t =>
    simp only [Holding.step] at ha ⊢
    split at ha
    · cases ha
    · next hr =>
      simp only [List.mem_singleton, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      exact .inr ⟨Bool.eq_false_of_ne_true hr, rfl⟩
  | .tick =>
    simp only [Holding.step, List.partition_eq_filter_filter, List.mem_map, Prod.mk.injEq] at ha
    obtain ⟨_, _, _, rfl⟩ := ha
    exact .inl rfl

/-- **SEC-1, at answer time.** A held read answered with an object is by a
user whom the distribution rules let run the proof on the store when it is
answered, and whose proof yields the content fact there. -/
theorem held_authorized {P : Policy} {s : Holding} {q : Request} (ha : (h, .ok o) ∈ (s.step P q).2) :
    ∃ u, h.user = some u ∧ P.distributes u h.proof.spec h.proof.givens (s.step P q).1.cached.replicator.store = true ∧
      h.proof.yields (s.step P q).1.cached.replicator.store h.key = true := by
  rcases held_answer ha with h' | ⟨_, h'⟩
  · cases h'
  · exact read_authorized h'.symm

/-- **Never 403 while Reactive.** A held read answered 403 is not Reactive on
the store when it is answered. -/
theorem held_not_forbidden {P : Policy} {s : Holding} {q : Request} (ha : (h, .forbidden) ∈ (s.step P q).2) :
    P.reactive (s.step P q).1.cached.replicator.store h.user h.proof = false := by
  rcases held_answer ha with h' | ⟨h', _⟩
  · cases h'
  · exact h'

/-- **SEC-6.** After any history, a save that makes a held read admitted
answers it with the object stored under its key then, or 404 `not_uploaded`
if there is none: never 403, never 409. -/
theorem held_live {P : Policy} {hs : List Request} (hh : h ∈ (Holding.run P hs).held) (hu : h.user = some u)
    (ha : P.admits ((Holding.run P hs).step P (.event (.save B))).1.cached.replicator.store u h.key h.proof = true) :
    (h, match ((Holding.run P hs).step P (.event (.save B))).1.cached.replicator.objects.lookup h.key with
      | none => .notUploaded
      | some o => .ok o) ∈ ((Holding.run P hs).step P (.event (.save B))).2 := by
  rw [Holding.step_cached] at ha ⊢
  have hr := (Holding.run_valid P hs).1 h hh
  have hb : h.proof.bound = true := by simp_all [Policy.reactive]
  have hd : P.distributes u h.proof.spec h.proof.givens _ = true := (Bool.and_eq_true _ _ ▸ ha).1
  simp only [Holding.step, Holding.settle, List.partition_eq_filter_filter, List.mem_map, List.mem_filter,
    Prod.mk.injEq] at ha ⊢
  refine ⟨h, ⟨hh, ?_⟩, rfl, by rw [hu, read_admitted hb ha]; rfl⟩
  have hn : P.reactive (Cached.step P (Holding.run P hs).cached (.event (.save B))).replicator.store h.user
      h.proof = false := by simp [Policy.reactive, hu, hd]
  cases hw : h.wakes P (Holding.run P hs).cached.replicator.store B
  · rw [Hold.reactive_stable hr hw] at hn; cases hn
  · simp [hn]

/-- **A held read times out.** A tick answers 409 every held read whose
deadline it passes. -/
theorem held_timeout {P : Policy} {s : Holding} (hh : h ∈ s.held) (hd : h.deadline < s.clock + 1) :
    (h, .retryAfter) ∈ (s.step P .tick).2 := by
  simp only [Holding.step, List.partition_eq_filter_filter, List.mem_map]
  exact ⟨h, List.mem_filter.2 ⟨hh, decide_eq_true hd⟩, rfl⟩

/-- **Waking on invalidation is re-evaluating on every save.** After any
history, a save that wakes only the held reads `Policy.invalidates` names
moves to the same state, with the same answers, as one that re-evaluates
every held read. -/
theorem wake_on_invalidates (P : Policy) (hs : List Request) (B : List Fact) :
    (Holding.run P hs).step P (.event (.save B)) =
      (Holding.run P hs).settle P ((Holding.run P hs).cached.step P (.event (.save B))) fun _ => true := by
  simp only [Holding.step, Holding.settle]
  have : ∀ h ∈ (Holding.run P hs).held,
      (h.wakes P (Holding.run P hs).cached.replicator.store B &&
        !P.reactive ((Holding.run P hs).cached.step P (.event (.save B))).replicator.store h.user h.proof) =
      (true && !P.reactive ((Holding.run P hs).cached.step P (.event (.save B))).replicator.store h.user h.proof) := by
    intro h hh
    cases hw : h.wakes P _ B
    · simp [Hold.reactive_stable ((Holding.run_valid P hs).1 h hh) hw]
    · rfl
  rw [List.partition_congr this]

/-- The state, with `objects` in place of the stored objects. -/
def Holding.withObjects (s : Holding) (objects : List (FactId × Bytes)) : Holding :=
  { s with cached := { s.cached with replicator := { s.cached.replicator with objects } } }

/-- The rules admit the held read on `g`. -/
def Policy.admitsHold (P : Policy) (g : Graph) (h : Hold) : Bool :=
  h.user.any fun u => P.admits g u h.key h.proof

/-- **SEC-5, for held reads.** With other objects stored, a request answers
every held read the rules do not admit on the store then exactly as before,
and moves to the same state but for the objects. -/
theorem held_noninterference (P : Policy) (s : Holding) (objects : List (FactId × Bytes)) (q : Request) :
    ((s.withObjects objects).step P q).2.filter (!P.admitsHold (s.step P q).1.cached.replicator.store ·.1) =
      (s.step P q).2.filter (!P.admitsHold (s.step P q).1.cached.replicator.store ·.1) ∧
    ∃ objects', ((s.withObjects objects).step P q).1 = (s.step P q).1.withObjects objects' := by
  -- A read answered on `r` is answered so on `r` with other objects, if the rules do not admit it.
  have hr : ∀ (r : Replicator) (h : Hold), P.admitsHold r.store h = false →
      { r with objects := objects }.read P h.user h.key h.proof = r.read P h.user h.key h.proof := by
    intro r h ha
    refine (read_noninterference (fun u hu => ?_) objects).symm
    simpa [Policy.admitsHold, hu] using ha
  have hm : ∀ (r : Replicator) (l : List Hold) (g : Graph), g = r.store →
      (l.map fun h => (h, { r with objects := objects }.read P h.user h.key h.proof)).filter (!P.admitsHold g ·.1) =
        (l.map fun h => (h, r.read P h.user h.key h.proof)).filter (!P.admitsHold g ·.1) := by
    intro r l g hg
    simp only [List.filter_map]
    exact List.map_congr_left fun h hh => by
      rw [hr r h (by simpa [hg] using (List.mem_filter.1 hh).2)]
  match q with
  | .tick => exact ⟨rfl, objects, rfl⟩
  | .hold u k p t =>
    by_cases hc : P.reactive s.cached.replicator.store u p = true
    · simp only [Holding.step, Holding.withObjects, hc, ite_true]; exact ⟨trivial, objects, rfl⟩
    · simp only [Holding.step, Holding.withObjects, hc, Bool.false_eq_true, ite_false]
      exact ⟨hm s.cached.replicator [_] _ rfl, objects, rfl⟩
  | .event (.save B) =>
    have : ({ s.cached.replicator with objects }.step P (.save B)) = { s.cached.replicator.step P (.save B) with objects } := by
      by_cases ha : s.cached.replicator.store.accepts B <;> simp [Replicator.step, ha]
    simp only [Holding.step, Holding.settle, Holding.withObjects, Cached.step, this]
    exact ⟨hm _ _ _ rfl, objects, rfl⟩
  | .event (.write u k o) =>
    refine ⟨rfl, ({ s.cached.replicator with objects }.write P u k o).1.objects, ?_⟩
    simp only [Holding.step, Holding.withObjects, Cached.step, Replicator.step]
    have h := Replicator.write_store P { s.cached.replicator with objects } u k o
    rw [Replicator.write_store]
    generalize (Replicator.write P { s.cached.replicator with objects } u k o).1 = x at h ⊢
    cases x; simp_all
  | .read u k p =>
    refine ⟨rfl, objects, ?_⟩
    simp only [Holding.step, Holding.withObjects, Cached.step]
    rw [Cached.read_objects, Cached.read_replicator]

end JinagaSpec
