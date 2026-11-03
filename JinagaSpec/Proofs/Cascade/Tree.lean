import JinagaSpec.Cascade.Step

/-!
# Cascade: facts about trees and events

A tree's list order means nothing: everything `apply` checks and does is
determined by `get`, provided ids are distinct. So `apply` keeps a tree well
formed (`apply_wf`) and takes equivalent trees to equivalent trees
(`applyAll_equiv`).
-/
namespace JinagaSpec.Cascade

noncomputable section

/-! ## `get` under each list operation -/

@[simp] theorem get_nil (id : Id) : Tree.get [] id = none := rfl

theorem get_cons (id id' : Id) (n : Node) (T : Tree) :
    Tree.get ((id', n) :: T) id = if id' = id then some n else T.get id := by
  by_cases h : id' = id <;> simp [Tree.get, h]

theorem get_append (A B : Tree) (id : Id) : Tree.get (A ++ B) id = (A.get id).or (B.get id) := by
  simp only [Tree.get, List.find?_append]
  cases A.find? (·.1 == id) <;> simp

theorem get_filter (T : Tree) (x id : Id) :
    Tree.get (T.filter (·.1 != x)) id = if id = x then none else T.get id := by
  induction T with
  | nil => simp
  | cons e T ih =>
    obtain ⟨id', n⟩ := e
    by_cases hx : id' = x
    · subst hx
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ih, get_cons]
      by_cases h : id = id' <;> simp [h, Ne.symm]
    · simp only [List.filter_cons, bne_iff_ne, ne_eq, hx, not_false_eq_true,
        ↓reduceIte, get_cons, ih]
      by_cases h : id = x
      · subst h; simp [hx]
      · simp [h]

theorem get_update (T : Tree) (x id : Id) (f : Node → Node) :
    (T.update x f).get id = if id = x then (T.get id).map f else T.get id := by
  induction T with
  | nil => simp [Tree.update]
  | cons e T ih =>
    obtain ⟨id', n⟩ := e
    simp only [Tree.update, List.map_cons, beq_iff_eq] at ih ⊢
    by_cases hx : id' = x
    · subst hx
      simp only [↓reduceIte, get_cons]
      by_cases h : id' = id
      · subst h; simp
      · simp [h, Ne.symm h, ih]
    · simp only [hx, ↓reduceIte, get_cons]
      by_cases h : id' = id
      · subst h; simp [hx]
      · simp [h, ih]

/-! ## With distinct ids, `get` sees every entry -/

theorem get_of_mem {T : Tree} (hnd : (T.map (·.1)).Nodup) {id : Id} {n : Node}
    (h : (id, n) ∈ T) : T.get id = some n := by
  induction T with
  | nil => simp at h
  | cons e T ih =>
    obtain ⟨id', n'⟩ := e
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rw [get_cons]
    rcases List.mem_cons.mp h with h | h
    · cases h; simp
    · have hne : id' ≠ id := fun he => hnd.1 ⟨(id, n), h, he.symm⟩
      simp [hne, ih hnd.2 h]

theorem mem_of_get {T : Tree} {id : Id} {n : Node} (h : T.get id = some n) : (id, n) ∈ T := by
  induction T with
  | nil => simp at h
  | cons e T ih =>
    obtain ⟨id', n'⟩ := e
    rw [get_cons] at h
    by_cases he : id' = id
    · simp only [he, ↓reduceIte, Option.some.injEq] at h; subst he h; simp
    · simp only [he, ↓reduceIte] at h; exact List.mem_cons_of_mem _ (ih h)

theorem hasChild_iff {T : Tree} (hnd : (T.map (·.1)).Nodup) (l : Level) (k : Key) :
    T.hasChild l k = true ↔
      ∃ l' k' n, T.get (l', k') = some n ∧ l' ≠ [] ∧ l'.dropLast = l ∧ n.parent = some k := by
  simp only [Tree.hasChild, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, beq_iff_eq, Prod.exists]
  constructor
  · rintro ⟨l', k', n, hm, ⟨h1, h2⟩, h3⟩
    exact ⟨l', k', n, get_of_mem hnd hm, h1, h2, h3⟩
  · rintro ⟨l', k', n, hg, h1, h2, h3⟩
    exact ⟨l', k', n, mem_of_get hg, ⟨h1, h2⟩, h3⟩

/-! ## `apply` keeps a tree well formed -/

theorem keys_filter (T : Tree) (x : Id) :
    (T.filter (·.1 != x)).map (·.1) = (T.map (·.1)).filter (· != x) := by
  induction T with
  | nil => rfl
  | cons e T ih => by_cases h : e.1 = x <;> simp [h, ih]

theorem keys_update (T : Tree) (x : Id) (f : Node → Node) :
    (T.update x f).map (·.1) = T.map (·.1) := by
  induction T with
  | nil => rfl
  | cons e T ih =>
    simp only [Tree.update, List.map_cons, beq_iff_eq] at ih ⊢
    by_cases h : e.1 = x <;> simp [h, ih]

theorem parentOk_of_get {T U : Tree} (h : ∀ id, (T.get id).isSome → (U.get id).isSome)
    {l : Level} {p : Option Key} (hp : T.parentOk l p = true) : U.parentOk l p = true := by
  cases p with
  | none => exact hp
  | some q =>
    simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true'] at hp ⊢
    exact ⟨hp.1, h _ hp.2⟩

/-! ## What `apply` does, case by case -/

theorem apply_added {T T' : Tree} {l : Level} {k : Key} {p : Option Key} {ps : Props} :
    T.apply (.added l k p ps) = some T' ↔
      T.get (l, k) = none ∧ T.parentOk l p = true ∧ T' = ((l, k), ⟨p, ps⟩) :: T := by
  simp only [Tree.apply]
  by_cases h1 : T.get (l, k) = none <;> by_cases h2 : T.parentOk l p = true <;>
    simp [h1, h2, @eq_comm _ T']

theorem apply_removed {T T' : Tree} {l : Level} {k : Key} :
    T.apply (.removed l k) = some T' ↔
      (T.get (l, k)).isSome ∧ T.hasChild l k = false ∧ T' = T.filter (·.1 != (l, k)) := by
  simp only [Tree.apply]
  by_cases h1 : (T.get (l, k)).isSome <;> by_cases h2 : T.hasChild l k = true <;>
    simp [h1, h2, @eq_comm _ T']

theorem apply_modified {T T' : Tree} {l : Level} {k : Key} {p : String} {old new : Option Val} :
    T.apply (.modified l k p old new) = some T' ↔
      ∃ n, T.get (l, k) = some n ∧ n.props p = old ∧ old ≠ new ∧
        T' = T.update (l, k) fun n => { n with props := n.props.set p new } := by
  simp only [Tree.apply]
  cases hn : T.get (l, k) with
  | none => simp
  | some n =>
    by_cases h1 : n.props p = old <;> by_cases h2 : old = new <;> simp [h1, h2, @eq_comm _ T']

theorem apply_placed {T T' : Tree} {l : Level} {k : Key} {a b : Key} :
    T.apply (.placed l k a b) = some T' ↔
      ∃ n, T.get (l, k) = some n ∧ n.parent = some a ∧ a ≠ b ∧ T.parentOk l (some b) = true ∧
        T' = T.update (l, k) fun n => { n with parent := some b } := by
  simp only [Tree.apply]
  cases hn : T.get (l, k) with
  | none => simp
  | some n =>
    by_cases h1 : n.parent = some a <;> by_cases h2 : a = b <;>
      by_cases h3 : T.parentOk l (some b) = true <;> simp [h1, h2, h3, @eq_comm _ T']

theorem isSome_get_update (T : Tree) (x id : Id) (f : Node → Node) :
    ((T.update x f).get id).isSome = (T.get id).isSome := by
  rw [get_update]; split <;> simp_all

theorem parentOk_congr {T U : Tree} (h : T.Equiv U) (l : Level) (p : Option Key) :
    T.parentOk l p = U.parentOk l p := by
  cases p <;> simp [Tree.parentOk, h _]

theorem parentOk_update (T : Tree) (x : Id) (f : Node → Node) (l : Level) (p : Option Key) :
    (T.update x f).parentOk l p = T.parentOk l p := by
  cases p <;> simp [Tree.parentOk, isSome_get_update]

/-! ## `apply` keeps a tree well formed -/

theorem apply_wf {T T' : Tree} {e : Event} (hwf : T.WF) (h : T.apply e = some T') : T'.WF := by
  cases e with
  | added l k p ps =>
    obtain ⟨hn, hp, rfl⟩ := apply_added.mp h
    have mono : ∀ id, (T.get id).isSome → (Tree.get (((l, k), ⟨p, ps⟩) :: T) id).isSome := by
      intro id hs; rw [get_cons]; split <;> simp_all
    refine ⟨?_, fun id n hg => ?_⟩
    · refine List.nodup_cons.mpr ⟨fun hm => ?_, hwf.nodup⟩
      obtain ⟨⟨id', n⟩, hmem, he⟩ := List.mem_map.mp hm
      simp only at he; subst he
      simp [get_of_mem hwf.nodup hmem] at hn
    · rw [get_cons] at hg
      split at hg
      · rename_i he; cases hg; subst he; exact parentOk_of_get mono hp
      · exact parentOk_of_get mono (hwf.parents id n hg)
  | removed l k =>
    obtain ⟨hs, hc, rfl⟩ := apply_removed.mp h
    refine ⟨?_, fun id n hg => ?_⟩
    · rw [keys_filter]; exact hwf.nodup.filter _
    · rw [get_filter] at hg
      split at hg
      · simp at hg
      · rename_i hne
        have hok := hwf.parents id n hg
        cases hpar : n.parent with
        | none => rw [hpar] at hok; exact hok
        | some q =>
          rw [hpar] at hok
          simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true',
            List.isEmpty_eq_false_iff] at hok ⊢
          refine ⟨hok.1, ?_⟩
          rw [get_filter]
          split
          · rename_i heq
            have : T.hasChild l k = true := (hasChild_iff hwf.nodup l k).mpr
              ⟨id.1, id.2, n, hg, hok.1, (Prod.mk.inj heq).1, by rw [hpar, (Prod.mk.inj heq).2]⟩
            simp [this] at hc
          · exact hok.2
  | modified l k p old new =>
    obtain ⟨n0, hn0, -, -, rfl⟩ := apply_modified.mp h
    refine ⟨by rw [keys_update]; exact hwf.nodup, fun id n hg => ?_⟩
    rw [parentOk_update]
    rw [get_update] at hg
    split at hg
    · rename_i he; subst he
      rw [hn0] at hg; cases hg; exact hwf.parents _ n0 hn0
    · exact hwf.parents id n hg
  | placed l k a b =>
    obtain ⟨n0, hn0, -, -, hb, rfl⟩ := apply_placed.mp h
    refine ⟨by rw [keys_update]; exact hwf.nodup, fun id n hg => ?_⟩
    rw [parentOk_update]
    rw [get_update] at hg
    split at hg
    · rename_i he; subst he
      rw [hn0] at hg; cases hg; exact hb
    · exact hwf.parents id n hg

theorem applyAll_wf {T T' : Tree} {es : List Event} (hwf : T.WF) (h : T.applyAll es = some T') :
    T'.WF := by
  induction es generalizing T with
  | nil => cases h; exact hwf
  | cons e es ih =>
    simp only [Tree.applyAll, Option.bind_eq_some_iff] at h
    obtain ⟨T1, h1, h2⟩ := h
    exact ih (apply_wf hwf h1) h2

theorem applyAll_append (T : Tree) (a b : List Event) :
    T.applyAll (a ++ b) = (T.applyAll a).bind (·.applyAll b) := by
  induction a generalizing T with
  | nil => rfl
  | cons e a ih =>
    simp only [List.cons_append, Tree.applyAll, Option.bind_assoc]
    cases T.apply e <;> simp [ih]

/-! ## `apply` takes equivalent trees to equivalent trees -/

theorem Tree.Equiv.refl (T : Tree) : T.Equiv T := fun _ => rfl
theorem Tree.Equiv.symm {T U : Tree} (h : T.Equiv U) : U.Equiv T := fun id => (h id).symm
theorem Tree.Equiv.trans {T U V : Tree} (h₁ : T.Equiv U) (h₂ : U.Equiv V) : T.Equiv V :=
  fun id => (h₁ id).trans (h₂ id)

theorem hasChild_congr {T U : Tree} (hT : T.WF) (hU : U.WF) (h : T.Equiv U) (l : Level) (k : Key) :
    T.hasChild l k = U.hasChild l k := by
  rw [Bool.eq_iff_iff, hasChild_iff hT.nodup, hasChild_iff hU.nodup]
  simp only [h _]

theorem apply_equiv {T U T' : Tree} {e : Event} (hT : T.WF) (hU : U.WF) (h : T.Equiv U)
    (ha : T.apply e = some T') : ∃ U', U.apply e = some U' ∧ T'.Equiv U' := by
  cases e with
  | added l k p ps =>
    obtain ⟨hn, hp, rfl⟩ := apply_added.mp ha
    refine ⟨_, apply_added.mpr ⟨(h _).symm.trans hn, (parentOk_congr h l p).symm.trans hp, rfl⟩,
      fun id => ?_⟩
    simp only [get_cons, h id]
  | removed l k =>
    obtain ⟨hs, hc, rfl⟩ := apply_removed.mp ha
    refine ⟨_, apply_removed.mpr ⟨h _ ▸ hs, (hasChild_congr hT hU h l k).symm.trans hc, rfl⟩,
      fun id => ?_⟩
    simp only [get_filter, h id]
  | modified l k p old new =>
    obtain ⟨n, hn, h1, h2, rfl⟩ := apply_modified.mp ha
    refine ⟨_, apply_modified.mpr ⟨n, (h _).symm.trans hn, h1, h2, rfl⟩, fun id => ?_⟩
    simp only [get_update, h id]
  | placed l k a b =>
    obtain ⟨n, hn, h1, h2, h3, rfl⟩ := apply_placed.mp ha
    refine ⟨_, apply_placed.mpr ⟨n, (h _).symm.trans hn, h1, h2,
      (parentOk_congr h l _).symm.trans h3, rfl⟩, fun id => ?_⟩
    simp only [get_update, h id]

theorem applyAll_equiv {T U T' : Tree} {es : List Event} (hT : T.WF) (hU : U.WF) (h : T.Equiv U)
    (ha : T.applyAll es = some T') : ∃ U', U.applyAll es = some U' ∧ T'.Equiv U' := by
  induction es generalizing T U with
  | nil => cases ha; exact ⟨U, rfl, h⟩
  | cons e es ih =>
    simp only [Tree.applyAll, Option.bind_eq_some_iff] at ha ⊢
    obtain ⟨T1, h1, h2⟩ := ha
    obtain ⟨U1, hu1, he1⟩ := apply_equiv hT hU h h1
    obtain ⟨U', hu', he'⟩ := ih (apply_wf hT h1) (apply_wf hU hu1) he1 h2
    exact ⟨U', ⟨U1, hu1, hu'⟩, he'⟩

end

end JinagaSpec.Cascade
