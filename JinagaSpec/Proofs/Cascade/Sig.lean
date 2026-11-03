import JinagaSpec.Cascade.Sig
import JinagaSpec.Proofs.Cascade.Pipeline
import JinagaSpec.Proofs.Cascade.Input

/-!
# Cascade: steps emit only what their descriptors declare

Each step keeps its signature (`…_keeps`), keeping composes (`andThen_keeps`),
and a caller's operations declare nothing beyond adding and removing rows. So a
pipeline emits, for what a caller does, only changes and moves its descriptor
declares (`ops_declared`), and an output session that subscribes to the
descriptor hears every one (`ops_heard`).
-/
namespace JinagaSpec.Cascade

noncomputable section

theorem declared_added (σ : Sig) (l : Level) (k : Key) (p : Option Key) (ps : Props) :
    (Event.added l k p ps).Declared σ := trivial

theorem declared_removed (σ : Sig) (l : Level) (k : Key) : (Event.removed l k).Declared σ :=
  trivial

/-- A signature that declares at least what another does. -/
theorem declared_mono {σ σ' : Sig} (hm : ∀ l p, σ.mutable l p = true → σ'.mutable l p = true)
    (hv : ∀ l, σ.movable l = true → σ'.movable l = true) {e : Event} (h : e.Declared σ) :
    e.Declared σ' := by
  cases e with
  | modified l k p _ _ => exact hm l p h
  | placed l k _ _ => exact hv l h
  | _ => trivial

/-! ## Composition -/

theorem run_keeps {S : Step} {σ σ' : Sig} (hS : Keeps S σ σ') :
    ∀ (es : List Event) (U : Tree), (∀ e ∈ es, e.Declared σ) → ∀ e' ∈ run S U es, e'.Declared σ' := by
  intro es
  induction es with
  | nil => intro _ _ e' he'; simp [run] at he'
  | cons e es ih =>
    intro U hd e' he'
    simp only [run] at he'
    split at he'
    · rename_i U' hU
      rcases List.mem_append.mp he' with h | h
      · exact hS U e (by simp [hU]) (hd e (List.mem_cons_self ..)) e' h
      · exact ih U' (fun x hx => hd x (List.mem_cons_of_mem _ hx)) e' h
    · simp at he'

/-- **`andThen_keeps`.** Steps that keep their signatures keep them in sequence. -/
theorem andThen_keeps {S₁ S₂ : Step} {σ σ₁ σ₂ : Sig} (F : Tree → Tree) (h₁ : Keeps S₁ σ σ₁)
    (h₂ : Keeps S₂ σ₁ σ₂) : Keeps (S₁.andThen S₂ F) σ σ₂ :=
  fun T e ha hd => run_keeps h₂ _ (F T) (h₁ T e ha hd)

/-! ## Each step -/

theorem dropProperty_keeps (s : Level) (q : String) (σ : Sig) :
    Keeps (dropProperty s q) σ (dropProperty.sig s q σ) := by
  intro T e _ hd e' he'
  cases e with
  | added => simp [dropProperty] at he'; subst he'; trivial
  | removed => simp [dropProperty] at he'; subst he'; trivial
  | modified l k p old new =>
    simp only [dropProperty] at he'
    split at he'
    · simp at he'
    · rename_i h
      simp at he'; subst he'
      simp only [Event.Declared, dropProperty.sig, Bool.and_eq_true, Bool.not_eq_true',
        Bool.and_eq_false_iff, beq_eq_false_iff_ne]
      refine ⟨hd, ?_⟩
      by_cases hl : l = s
      · exact Or.inr fun hp => h ⟨hl, hp⟩
      · exact Or.inl hl
  | placed => simp [dropProperty] at he'; subst he'; exact hd

theorem defineProperty_keeps (s : Level) (q : String) (f : Props → Option Val) (deps : List String)
    (σ : Sig) : Keeps (defineProperty s q f deps) σ (defineProperty.sig s q deps σ) := by
  intro T e _ hd e' he'
  have mono : ∀ {x : Event}, x.Declared σ → x.Declared (defineProperty.sig s q deps σ) :=
    fun h => declared_mono (σ := σ) (σ' := defineProperty.sig s q deps σ)
      (fun l p h' => by simp [defineProperty.sig, h']) (fun _ h' => h') h
  cases e with
  | added => simp [defineProperty] at he'; subst he'; trivial
  | removed => simp [defineProperty] at he'; subst he'; trivial
  | placed => simp [defineProperty] at he'; subst he'; exact hd
  | modified l k p old new =>
    simp only [defineProperty] at he'
    split at he'
    · rename_i hl
      split at he'
      · simp at he'
      · split at he'
        · rcases List.mem_cons.mp he' with rfl | he'
          · exact mono hd
          · split at he'
            · rename_i hdep
              simp at he'; subst he'
              have : deps ≠ [] := List.ne_nil_of_mem hdep.1
              simp [Event.Declared, defineProperty.sig, hl, this]
            · simp at he'
        · simp at he'
    · simp at he'; subst he'; exact mono hd

theorem aggregate_keeps (c : Level) (q : String) (contributes : Props → Bool)
    (g : List Props → Option Val) (σ : Sig) : Keeps (aggregateStep c q contributes g) σ (aggregate.sig c q σ) := by
  intro T e _ hd e' he'
  have mono : ∀ {x : Event}, x.Declared σ → x.Declared (aggregate.sig c q σ) :=
    fun h => declared_mono (σ := σ) (σ' := aggregate.sig c q σ)
      (fun l p h' => by simp [aggregate.sig, h']) (fun _ h' => h') h
  -- Every change the step makes is to the aggregate of a parent.
  have touch : ∀ (U : Tree) (k : Key) (x : Event),
      x ∈ (if aggregate c contributes g T k = aggregate c contributes g U k then []
        else [Event.modified c.dropLast k q (aggregate c contributes g T k)
          (aggregate c contributes g U k)]) → x.Declared (aggregate.sig c q σ) := by
    intro U k x hx
    split at hx
    · simp at hx
    · simp at hx; subst hx; simp [Event.Declared, aggregate.sig]
  simp only [aggregateStep] at he'
  split at he'
  · simp at he'
  · rename_i T' _
    cases e with
    | added l k p ps =>
      simp only at he'
      split at he'
      · simp at he'; subst he'; trivial
      · rcases List.mem_cons.mp he' with rfl | he'
        · trivial
        · split at he'
          · obtain ⟨k', -, hx⟩ := List.mem_flatMap.mp he'
            exact touch T' k' e' hx
          · simp at he'
    | removed l k =>
      simp only at he'
      rcases List.mem_cons.mp he' with rfl | he'
      · trivial
      · split at he'
        · obtain ⟨k', -, hx⟩ := List.mem_flatMap.mp he'
          exact touch T' k' e' hx
        · simp at he'
    | modified l k p old new =>
      simp only at he'
      split at he'
      · simp at he'
      · rcases List.mem_cons.mp he' with rfl | he'
        · exact mono hd
        · split at he'
          · obtain ⟨k', -, hx⟩ := List.mem_flatMap.mp he'
            exact touch T' k' e' hx
          · simp at he'
    | placed l k a b =>
      simp only at he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact mono hd
      · split at he'
        · rcases List.mem_append.mp he' with hx | hx
          · exact touch T' a e' hx
          · exact touch T' b e' hx
        · simp at he'

theorem groupBy_keeps (G : List String) (C : String) (σ : Sig) :
    Keeps (groupBy G C) σ (groupBy.sig G C σ) := by
  intro T e ha hd e' he'
  cases e with
  | added l k p ps =>
    cases l with
    | nil =>
      simp only [groupBy] at he'
      rcases List.mem_append.mp he' with h | h
      · split at h
        · simp at h
        · simp at h; subst h; trivial
      · simp at h; subst h; trivial
    | cons c l => simp [groupBy] at he'; subst he'; trivial
  | removed l k =>
    cases l with
    | nil =>
      simp only [groupBy] at he'
      split at he'
      · rcases List.mem_cons.mp he' with rfl | he'
        · trivial
        · split at he'
          · simp at he'
          · simp at he'; subst he'; trivial
      · simp at he'
    | cons c l => simp [groupBy] at he'; subst he'; trivial
  | modified l k p old new =>
    cases l with
    | nil =>
      simp only [groupBy] at he'
      split at he'
      · split at he'
        · rename_i hp
          rcases List.mem_append.mp he' with h | h
          · rcases List.mem_append.mp h with h | h
            · split at h
              · simp at h
              · simp at h; subst h; trivial
            · simp at h; subst h
              simp only [Event.Declared, groupBy.sig, beq_self_eq_true, Bool.true_and,
                List.any_eq_true]
              exact ⟨p, hp, hd⟩
          · split at h
            · simp at h
            · simp at h; subst h; trivial
        · rename_i hp
          simp at he'; subst he'
          simp [Event.Declared, groupBy.sig, hp]
          exact hd
      · simp at he'
    | cons c l =>
      simp [groupBy] at he'; subst he'
      simp [Event.Declared, groupBy.sig]
      exact hd
  | placed l k a b =>
    cases l with
    | nil =>
      -- A root node has no parent to move from.
      simp [Tree.apply] at ha
      split at ha
      · rename_i n _
        simp [Tree.parentOk] at ha
      · simp at ha
    | cons c l =>
      simp [groupBy] at he'; subst he'
      simp [Event.Declared, groupBy.sig]; exact hd

theorem admit_added {T : Tree} {x : Id} {e : Event} (h : e ∈ admit T x) :
    ∃ l k p ps, e = .added l k p ps := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp h
  exact ⟨_, _, _, _, rfl⟩

theorem evict_removed {T : Tree} {x : Id} {e : Event} (h : e ∈ evict T x) :
    ∃ l k, e = .removed l k := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp h
  exact ⟨_, _, rfl⟩

theorem filter_keeps (P : Props → Bool) (deps : List String) (σ : Sig) :
    Keeps (filterStep P deps) σ (filterStep.sig σ) := by
  intro T e _ hd e' he'
  have adm : ∀ U x, e' ∈ admit U x → e'.Declared σ := by
    intro U x h; obtain ⟨_, _, _, _, rfl⟩ := admit_added h; trivial
  have evi : ∀ U x, e' ∈ evict U x → e'.Declared σ := by
    intro U x h; obtain ⟨_, _, rfl⟩ := evict_removed h; trivial
  simp only [filterStep, filterStep.sig] at he' ⊢
  split at he'
  · simp at he'
  · rename_i T' _
    cases e with
    | added l k _ _ =>
      simp only at he'; split at he' <;> simp at he'; subst he'; trivial
    | removed l k =>
      simp only at he'; split at he' <;> simp at he'; subst he'; trivial
    | modified l k p _ _ =>
      simp only at he'
      split at he'
      · split at he'
        · simp at he'; subst he'; exact hd
        · exact adm _ _ he'
        · exact evi _ _ he'
        · simp at he'
      · split at he' <;> simp at he'; subst he'; exact hd
    | placed l k _ _ =>
      simp only at he'
      split at he'
      · simp at he'; subst he'; exact hd
      · exact adm _ _ he'
      · exact evi _ _ he'
      · simp at he'

/-! ## What a caller does -/

/-- The input emits only adds and removes, which any signature declares. -/
theorem input_declared (σ : Sig) (T : Tree) (op : Op) : ∀ e ∈ input.handle T op, e.Declared σ := by
  intro e he
  cases op with
  | add l r rest ps =>
    simp only [input.handle] at he
    split at he
    · simp at he; subst he; trivial
    · simp at he
  | remove l r rest =>
    simp only [input.handle] at he
    split at he
    · obtain ⟨_, _, rfl⟩ := evict_removed he; trivial
    · simp at he

/-- **`ops_declared`.** A pipeline that keeps the input's signature as `σ`
emits, for what a caller does, only changes and moves `σ` declares. -/
theorem ops_declared {S : Step} {σ : Sig} (hS : Keeps S Sig.input σ) :
    ∀ (ops : List Op) (T : Tree), ∀ e ∈ runOps S T ops, e.Declared σ := by
  intro ops
  induction ops with
  | nil => intro _ e he; simp [runOps] at he
  | cons op ops ih =>
    intro T e he
    simp only [runOps] at he
    rcases List.mem_append.mp he with h | h
    · exact run_keeps hS _ T (input_declared _ T op) e h
    · exact ih _ e h

/-- **`ops_heard`.** A consumer that subscribes to the descriptor of a pipeline
that keeps its signature hears every event the pipeline emits. -/
theorem ops_heard {S : Step} {σ : Sig} (hS : Keeps S Sig.input σ) (ops : List Op) (T : Tree) :
    (runOps S T ops).filter σ.hears = runOps S T ops := by
  rw [List.filter_eq_self]
  intro e he
  have := ops_declared hS ops T e he
  cases e with
  | modified => exact this
  | _ => rfl

/-! ## The tiers pipeline -/

def tiersSig : Sig :=
  aggregate.sig ["groups"] "tierTotal" <|
  groupBy.sig ["tier"] "groups" <|
  defineProperty.sig [] "tier" ["total"] <|
  aggregate.sig ["items"] "total" <|
  groupBy.sig ["item"] "items" Sig.input

/-- **`tiers_keeps`.** The tiers pipeline emits only what its signature declares. -/
theorem tiers_keeps : Keeps tiers Sig.input tiersSig :=
  andThen_keeps _ (andThen_keeps _ (andThen_keeps _ (andThen_keeps _
    (groupBy_keeps _ _ _) (aggregate_keeps _ _ _ _ _)) (defineProperty_keeps _ _ _ _ _))
    (groupBy_keeps _ _ _)) (aggregate_keeps _ _ _ _ _)

/-- An item moves between tiers, because its tier is derived from its total. Its
total and the tier's total can change; its rows never move. -/
theorem tiersSig_facts :
    tiersSig.movable ["groups"] = true ∧ tiersSig.movable ["groups", "items"] = false ∧
      tiersSig.mutable ["groups"] "total" = true ∧ tiersSig.mutable [] "tierTotal" = true ∧
      tiersSig.mutable ["groups", "items"] "v" = false := by
  decide

end

end JinagaSpec.Cascade
