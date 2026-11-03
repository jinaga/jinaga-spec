import JinagaSpec.Proofs.Cascade.MapProps

/-!
# Cascade: `groupBy` at the root

The output has a group at the root for each distinct grouping value, each root
row below its group at level `[C]`, and the rest of the tree one level deeper
(`get_groupBy`). A row's group is its placement: when a grouping value changes,
the step moves the row with one `placed` event, and its subtree goes with it.

`groupBy_correct` is what issue jinaga/jinaga-cascade-core#29 broke: the step
used to move a row by removing it and adding it again with the values it had
when it first arrived.
-/
namespace JinagaSpec.Cascade

variable {G : List String} {C : String}

/-! ## `dedup` -/

theorem mem_dedup {α : Type} [DecidableEq α] {a : α} : ∀ {l : List α}, a ∈ dedup l ↔ a ∈ l
  | [] => by simp [dedup]
  | b :: l => by
    unfold dedup
    split
    · rename_i h; rw [mem_dedup]; constructor
      · exact List.mem_cons_of_mem _
      · intro h'; rcases List.mem_cons.mp h' with rfl | h' <;> assumption
    · simp [mem_dedup]

theorem nodup_dedup {α : Type} [DecidableEq α] : ∀ (l : List α), (dedup l).Nodup
  | [] => List.nodup_nil
  | b :: l => by
    unfold dedup
    split
    · exact nodup_dedup l
    · rename_i h; exact List.nodup_cons.mpr ⟨fun h' => h (mem_dedup.mp h'), nodup_dedup l⟩

/-! ## `get` of the output -/

theorem get_append (A B : Tree) (id : Id) : Tree.get (A ++ B) id = (A.get id).or (B.get id) := by
  simp only [Tree.get, List.find?_append]
  cases A.find? (·.1 == id) <;> simp

theorem get_groups (L : List Key) (node : Key → Node) (id : Id) :
    Tree.get (L.map fun g => (([], g), node g)) id =
      if id.1 = [] ∧ id.2 ∈ L then some (node id.2) else none := by
  induction L with
  | nil => simp
  | cons g L ih =>
    rw [List.map_cons, get_cons, ih]
    obtain ⟨l, k⟩ := id
    by_cases h : ([], g) = (l, k)
    · cases h; simp
    · simp only [h, ↓reduceIte, List.mem_cons]
      have : ¬(l = [] ∧ k = g) := fun ⟨h1, h2⟩ => h (by rw [h1, h2])
      by_cases hl : l = [] <;> simp_all

theorem get_items (T : Tree) (l : Level) (k : Key) :
    Tree.get (T.map fun e => ((C :: e.1.1, e.1.2), relevel G e.1.1 e.2)) (l, k) =
      match l with
      | x :: l => if x = C then (T.get (l, k)).map (relevel G l) else none
      | [] => none := by
  induction T with
  | nil => cases l <;> simp
  | cons e T ih =>
    obtain ⟨⟨l', k'⟩, n⟩ := e
    rw [List.map_cons, get_cons, ih]
    cases l with
    | nil => simp
    | cons x l =>
      simp only [Prod.mk.injEq, List.cons.injEq, get_cons]
      by_cases hx : x = C
      · subst hx
        by_cases h : l' = l ∧ k' = k
        · obtain ⟨rfl, rfl⟩ := h; simp
        · have : ¬((l', k') = (l, k)) := fun he => h (Prod.mk.inj he)
          simp [h, this]
      · simp [Ne.symm hx, hx]

/-- Whether some root row belongs to group `g`, read through `get`. -/
def Member (G : List String) (T : Tree) (g : Key) : Prop :=
  ∃ k n, T.get ([], k) = some n ∧ groupKey G n.props = g

theorem hasMember_iff {T : Tree} (hnd : (T.map (·.1)).Nodup) (g : Key) :
    hasMember G T g = true ↔ Member G T g := by
  simp only [hasMember, List.any_eq_true, Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq, Member]
  constructor
  · rintro ⟨⟨⟨l, k⟩, n⟩, hm, hl, hg⟩
    simp only at hl; subst hl
    exact ⟨k, n, get_of_mem hnd hm, hg⟩
  · rintro ⟨k, n, hn, hg⟩
    exact ⟨(([], k), n), mem_of_get hn, rfl, hg⟩

theorem mem_rootGroups {T : Tree} (g : Key) :
    g ∈ dedup ((T.filter (·.1.1.isEmpty)).map fun e => groupKey G e.2.props) ↔
      hasMember G T g = true := by
  simp only [mem_dedup, List.mem_map, List.mem_filter, hasMember, List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨e, ⟨hm, hl⟩, hg⟩; exact ⟨e, hm, hl, hg⟩
  · rintro ⟨e, hm, hl, hg⟩; exact ⟨e, ⟨hm, hl⟩, hg⟩

/-- **`get_groupBy`.** What the output holds at the root: the groups. -/
theorem get_groupBy_root (T : Tree) (k : Key) :
    (groupBy.F G C T).get ([], k) =
      if hasMember G T k then some ⟨none, groupProps G k⟩ else none := by
  unfold groupBy.F
  rw [get_append, get_groups, get_items]
  simp only [true_and, Option.or_none, mem_rootGroups]

/-- Below the root: the input, one level deeper. -/
theorem get_groupBy_cons (T : Tree) (x : String) (l : Level) (k : Key) :
    (groupBy.F G C T).get (x :: l, k) =
      if x = C then (T.get (l, k)).map (relevel G l) else none := by
  unfold groupBy.F
  rw [get_append, get_groups, get_items]
  simp

/-! ## The output is well formed -/

theorem relevel_parent_ok {T : Tree} (hwf : T.WF) {l : Level} {k : Key} {n : Node}
    (hn : T.get (l, k) = some n) :
    (groupBy.F G C T).parentOk (C :: l) (relevel G l n).parent = true := by
  have hp := hwf.parents _ _ hn
  unfold relevel
  split
  · rename_i hl; subst hl
    simp only [Tree.parentOk, List.isEmpty_cons, Bool.not_false, Bool.true_and,
      List.dropLast_singleton, get_groupBy_root]
    simp [(hasMember_iff hwf.nodup _).mpr ⟨k, n, hn, rfl⟩]
  · rename_i hl
    cases hq : n.parent with
    | none => rw [hq] at hp; simp [Tree.parentOk, hl] at hp
    | some q =>
      rw [hq] at hp
      simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff]
        at hp ⊢
      refine ⟨by simp, ?_⟩
      rw [List.dropLast_cons_of_ne_nil hl, get_groupBy_cons]
      simp only [↓reduceIte, Option.isSome_map]
      exact hp.2

theorem groupBy_wf {T : Tree} (hwf : T.WF) : (groupBy.F G C T).WF := by
  refine ⟨?_, ?_⟩
  · unfold groupBy.F
    rw [List.map_append, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.map_map]
      exact (nodup_dedup _).map _ fun a b hab h => hab (by simpa using h)
    · have : (T.map fun e => ((C :: e.1.1, e.1.2), relevel G e.1.1 e.2)).map (·.1) =
          (T.map (·.1)).map fun id => (C :: id.1, id.2) := by simp [List.map_map, Function.comp]
      rw [this]
      exact hwf.nodup.map _ fun a b hab h => hab (by
        simp only [Prod.mk.injEq, List.cons.injEq, true_and] at h; exact Prod.ext h.1 h.2)
    · intro a ha b hb hab
      simp only [List.map_map, List.mem_map, Function.comp] at ha hb
      obtain ⟨_, _, rfl⟩ := ha
      obtain ⟨_, _, rfl⟩ := hb
      simp at hab
  · rintro ⟨l, k⟩ n hn
    cases l with
    | nil =>
      rw [get_groupBy_root] at hn
      by_cases hm : hasMember G T k = true
      · simp only [hm, ↓reduceIte, Option.some.injEq] at hn; subst hn; rfl
      · simp [hm] at hn
    | cons x l =>
      rw [get_groupBy_cons] at hn
      by_cases hx : x = C
      · subst hx
        simp only [↓reduceIte, Option.map_eq_some_iff] at hn
        obtain ⟨m, hm, rfl⟩ := hn
        exact relevel_parent_ok hwf hm
      · simp [hx] at hn

theorem hasMember_congr {T U : Tree} (hT : T.WF) (hU : U.WF) (h : T.Equiv U) (g : Key) :
    hasMember G T g = hasMember G U g := by
  rw [Bool.eq_iff_iff, hasMember_iff hT.nodup, hasMember_iff hU.nodup]
  simp only [Member, h _]

theorem groupBy_denotation (G : List String) (C : String) : Denotation (groupBy.F G C) := by
  refine ⟨fun _ hT => groupBy_wf hT, fun T U hT hU h id => ?_⟩
  obtain ⟨l, k⟩ := id
  cases l with
  | nil => rw [get_groupBy_root, get_groupBy_root, hasMember_congr hT hU h]
  | cons x l => rw [get_groupBy_cons, get_groupBy_cons, h]

/-! ## Membership after an event -/

theorem hasMember_cons (e : Id × Node) (T : Tree) (g : Key) :
    hasMember G (e :: T) g = ((e.1.1.isEmpty && groupKey G e.2.props == g) || hasMember G T g) := by
  simp [hasMember]

theorem any_filter_irrel {α : Type} (f p : α → Bool) (L : List α)
    (h : ∀ e ∈ L, p e = false → f e = false) : (L.filter p).any f = L.any f := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    have ih' := ih fun e' he' => h e' (List.mem_cons_of_mem _ he')
    by_cases hp : p e = true
    · simp [List.filter_cons, hp, ih']
    · simp [List.filter_cons, hp, ih', h e List.mem_cons_self (by simpa using hp)]

theorem any_map_irrel {α : Type} (f : α → Bool) (g : α → α) (L : List α)
    (h : ∀ e ∈ L, f (g e) = f e) : (L.map g).any f = L.any f := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [List.map_cons, List.any_cons, h e List.mem_cons_self,
      ih fun e' he' => h e' (List.mem_cons_of_mem _ he')]

/-- Removing a node that is not a member of `g` leaves `g`'s membership alone. -/
theorem hasMember_filter {T : Tree} (hnd : (T.map (·.1)).Nodup) (y : Id) (g : Key)
    (h : ∀ n, T.get y = some n → ¬(y.1 = [] ∧ groupKey G n.props = g)) :
    hasMember G (T.filter (·.1 != y)) g = hasMember G T g := by
  apply any_filter_irrel
  rintro ⟨id, n⟩ hm hy
  simp only [bne_eq_false_iff_eq] at hy; subst hy
  have := h n (get_of_mem hnd hm)
  simpa [List.isEmpty_iff] using this

/-- Changing a node whose membership of `g` is the same before and after leaves
`g`'s membership alone. -/
theorem hasMember_update {T : Tree} (hnd : (T.map (·.1)).Nodup) (y : Id) (f : Node → Node)
    (g : Key) (h : ∀ n, T.get y = some n →
      ((y.1 = [] ∧ groupKey G (f n).props = g) ↔ (y.1 = [] ∧ groupKey G n.props = g))) :
    hasMember G (T.update y f) g = hasMember G T g := by
  apply any_map_irrel
  rintro ⟨id, n⟩ hm
  by_cases hy : id = y
  · subst hy
    have := h n (get_of_mem hnd hm)
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [Bool.eq_iff_iff]; simpa [List.isEmpty_iff] using this
  · simp [hy]

/-! ## Children in the output -/

/-- Below the root, a node of the output has a child exactly when the input
node it came from has one. -/
theorem hasChild_groupBy_cons {T : Tree} (hwf : T.WF) (l : Level) (k : Key) :
    (groupBy.F G C T).hasChild (C :: l) k = T.hasChild l k := by
  rw [Bool.eq_iff_iff, hasChild_iff (groupBy_wf hwf).nodup, hasChild_iff hwf.nodup]
  constructor
  · rintro ⟨l', k', m, hm, h1, h2, h3⟩
    cases l' with
    | nil => exact absurd rfl h1
    | cons x l'' =>
      rw [get_groupBy_cons] at hm
      by_cases hx : x = C
      · subst hx
        simp only [↓reduceIte, Option.map_eq_some_iff] at hm
        obtain ⟨m', hm', rfl⟩ := hm
        have hl'' : l'' ≠ [] := fun h => by subst h; simp at h2
        rw [List.dropLast_cons_of_ne_nil hl'', List.cons.injEq] at h2
        exact ⟨l'', k', m', hm', hl'', h2.2, by simpa [relevel, hl''] using h3⟩
      · simp [hx] at hm
  · rintro ⟨l', k', m, hm, h1, h2, h3⟩
    refine ⟨C :: l', k', m, ?_, by simp, by rw [List.dropLast_cons_of_ne_nil h1, h2], h3⟩
    rw [get_groupBy_cons]; simp [hm, relevel, h1]

/-! ## Events below the root move one level down -/

theorem relevel_cons (x : String) (l : Level) (n : Node) : relevel G (x :: l) n = n := by
  simp [relevel]

theorem parentOk_groupBy_cons {T : Tree} (x : String) (l : Level) (p : Option Key)
    (hp : T.parentOk (x :: l) p = true) : (groupBy.F G C T).parentOk (C :: x :: l) p = true := by
  cases p with
  | none => simp [Tree.parentOk] at hp
  | some q =>
    simp only [Tree.parentOk, List.isEmpty_cons, Bool.not_false, Bool.true_and] at hp ⊢
    rw [List.dropLast_cons_of_ne_nil (by simp), get_groupBy_cons]
    simpa using hp

/-- The root of the output, after an event that leaves the input's root rows alone. -/
theorem groupBy_root_same {T T' U : Tree} (hU : ∀ g, U.get ([], g) = (groupBy.F G C T).get ([], g))
    (hm : ∀ g, hasMember G T' g = hasMember G T g) (g : Key) :
    U.get ([], g) = (groupBy.F G C T').get ([], g) := by
  rw [hU, get_groupBy_root, get_groupBy_root, hm]

theorem groupBy_added_cons {T T' : Tree} {x : String} {l : Level} {k : Key} {p : Option Key}
    {ps : Props} (he : T.apply (.added (x :: l) k p ps) = some T') :
    ∃ U, (groupBy.F G C T).apply (.added (C :: x :: l) k p ps) = some U ∧
      U.Equiv (groupBy.F G C T') := by
  obtain ⟨hn, hp, rfl⟩ := apply_added.mp he
  refine ⟨_, apply_added.mpr ⟨by simp [get_groupBy_cons, hn], parentOk_groupBy_cons x l p hp, rfl⟩,
    ?_⟩
  rintro ⟨l0, k0⟩
  cases l0 with
  | nil =>
    refine groupBy_root_same (T := T) (fun g => ?_) (fun g => by simp [hasMember_cons]) k0
    rw [get_cons]; simp
  | cons y l0 =>
    rw [get_cons, get_groupBy_cons, get_groupBy_cons, get_cons]
    by_cases hy : y = C
    · subst y
      by_cases h : (x :: l, k) = (l0, k0)
      · cases h; simp [relevel_cons]
      · have : ¬((C :: x :: l, k) = (C :: l0, k0)) := fun he => h (by cases he; rfl)
        simp [h, this]
    · have : ¬((C :: x :: l, k) = (y :: l0, k0)) := fun he => hy (by cases he; rfl)
      simp [hy, this]

theorem groupBy_removed_cons {T T' : Tree} (hwf : T.WF) {x : String} {l : Level} {k : Key}
    (he : T.apply (.removed (x :: l) k) = some T') :
    ∃ U, (groupBy.F G C T).apply (.removed (C :: x :: l) k) = some U ∧
      U.Equiv (groupBy.F G C T') := by
  obtain ⟨hs, hc, rfl⟩ := apply_removed.mp he
  refine ⟨_, apply_removed.mpr ⟨by simpa [get_groupBy_cons] using hs,
    by rw [hasChild_groupBy_cons hwf]; exact hc, rfl⟩, ?_⟩
  rintro ⟨l0, k0⟩
  cases l0 with
  | nil =>
    refine groupBy_root_same (T := T) (fun g => ?_) (fun g => ?_) k0
    · rw [get_filter]; simp
    · exact hasMember_filter hwf.nodup _ g (by simp)
  | cons y l0 =>
    rw [get_filter, get_groupBy_cons, get_groupBy_cons, get_filter]
    by_cases hy : y = C
    · subst y
      by_cases h : (l0, k0) = (x :: l, k)
      · cases h; simp
      · have : ¬((C :: l0, k0) = (C :: x :: l, k)) := fun he => h (by cases he; rfl)
        simp [h, this]
    · simp [hy]

theorem groupBy_modified_cons {T T' : Tree} {x : String} {l : Level} {k : Key} {p : String}
    {old new : Option Val} (hwf : T.WF) (he : T.apply (.modified (x :: l) k p old new) = some T') :
    ∃ U, (groupBy.F G C T).apply (.modified (C :: x :: l) k p old new) = some U ∧
      U.Equiv (groupBy.F G C T') := by
  obtain ⟨n, hn, h1, h2, rfl⟩ := apply_modified.mp he
  refine ⟨_, apply_modified.mpr ⟨n, by simp [get_groupBy_cons, hn, relevel_cons], h1, h2, rfl⟩, ?_⟩
  rintro ⟨l0, k0⟩
  cases l0 with
  | nil =>
    refine groupBy_root_same (T := T) (fun g => ?_) (fun g => ?_) k0
    · rw [get_update]; simp
    · exact hasMember_update hwf.nodup _ _ g (by simp)
  | cons y l0 =>
    rw [get_update, get_groupBy_cons, get_groupBy_cons, get_update]
    by_cases hy : y = C
    · subst y
      by_cases h : (l0, k0) = (x :: l, k)
      · cases h; simp [hn, relevel_cons]
      · have : ¬((C :: l0, k0) = (C :: x :: l, k)) := fun he => h (by cases he; rfl)
        simp [h, this]
    · simp [hy]

theorem groupBy_placed_cons {T T' : Tree} {x : String} {l : Level} {k a b : Key}
    (hwf : T.WF) (he : T.apply (.placed (x :: l) k a b) = some T') :
    ∃ U, (groupBy.F G C T).apply (.placed (C :: x :: l) k a b) = some U ∧
      U.Equiv (groupBy.F G C T') := by
  obtain ⟨n, hn, h1, h2, h3, rfl⟩ := apply_placed.mp he
  refine ⟨_, apply_placed.mpr ⟨n, by simp [get_groupBy_cons, hn, relevel_cons], h1, h2,
    parentOk_groupBy_cons x l _ h3, rfl⟩, ?_⟩
  rintro ⟨l0, k0⟩
  cases l0 with
  | nil =>
    refine groupBy_root_same (T := T) (fun g => ?_) (fun g => ?_) k0
    · rw [get_update]; simp
    · exact hasMember_update hwf.nodup _ _ g (by simp)
  | cons y l0 =>
    rw [get_update, get_groupBy_cons, get_groupBy_cons, get_update]
    by_cases hy : y = C
    · subst y
      by_cases h : (l0, k0) = (x :: l, k)
      · cases h; simp [hn, relevel_cons]
      · have : ¬((C :: l0, k0) = (C :: x :: l, k)) := fun he => h (by cases he; rfl)
        simp [h, this]
    · simp [hy]

/-! ## Root rows -/

theorem groupKey_set_not_mem {p : String} (hp : p ∉ G) (ps : Props) (v : Option Val) :
    groupKey G (ps.set p v) = groupKey G ps := by
  simp only [groupKey, Key.group.injEq]
  refine List.map_inj_left.mpr fun x hx => ?_
  have : x ≠ p := fun h => hp (h ▸ hx)
  simp [Props.set, this]

theorem groupKey_set_ne {p : String} (hp : p ∈ G) {ps : Props} {v : Option Val} (hv : ps p ≠ v) :
    groupKey G (ps.set p v) ≠ groupKey G ps := by
  intro h
  simp only [groupKey, Key.group.injEq] at h
  have := List.map_inj_left.mp h p hp
  simp [Props.set] at this
  exact hv this.symm

theorem omitProps_set_mem {p : String} (hp : p ∈ G) (ps : Props) (v : Option Val) :
    omitProps G (ps.set p v) = omitProps G ps := by
  funext r; by_cases hr : r ∈ G <;> simp [omitProps, Props.set, hr]
  intro h; subst h; exact absurd hp hr

theorem omitProps_set_not_mem {p : String} (hp : p ∉ G) (ps : Props) (v : Option Val) :
    omitProps G (ps.set p v) = (omitProps G ps).set p v := by
  funext r; by_cases hr : r ∈ G <;> by_cases h : r = p <;> simp_all [omitProps, Props.set]

theorem relevel_root (n : Node) : relevel G [] n = ⟨some (groupKey G n.props), omitProps G n.props⟩ :=
  rfl

/-- A root row's parent is none. -/
theorem root_parent {T : Tree} (hwf : T.WF) {k : Key} {n : Node} (hn : T.get ([], k) = some n) :
    n.parent = none := by
  have := hwf.parents _ _ hn
  cases h : n.parent with
  | none => rfl
  | some q => rw [h] at this; simp [Tree.parentOk] at this

theorem groupBy_added_root {T T' : Tree} {k : Key} {p : Option Key} {ps : Props}
    (he : T.apply (.added [] k p ps) = some T') :
    ∃ U, (groupBy.F G C T).applyAll ((groupBy G C).handle T (.added [] k p ps)) = some U ∧
      U.Equiv (groupBy.F G C T') := by
  obtain ⟨hn, hp, rfl⟩ := apply_added.mp he
  have hp0 : p = none := by cases p <;> simp_all [Tree.parentOk]
  subst hp0
  simp only [groupBy]
  generalize hg : groupKey G ps = g
  have hitem : ((groupBy.F G C T).get ([C], k)) = none := by simp [get_groupBy_cons, hn]
  have hmem : ∀ g0, hasMember G (((([], k), ⟨none, ps⟩) :: T)) g0 = (g == g0 || hasMember G T g0) := by
    intro g0; rw [hasMember_cons]; simp [hg]
  have hitems : ∀ y l0 k0, (groupBy.F G C ((([], k), ⟨none, ps⟩) :: T)).get (y :: l0, k0) =
      if ([C], k) = (y :: l0, k0) then some ⟨some g, omitProps G ps⟩
      else (groupBy.F G C T).get (y :: l0, k0) := by
    intro y l0 k0
    rw [get_groupBy_cons, get_groupBy_cons, get_cons]
    by_cases hy : y = C
    · subst y
      by_cases h : ([], k) = (l0, k0)
      · cases h; simp [relevel_root, hg]
      · have : ¬(([C], k) = (C :: l0, k0)) := fun he => h (by cases he; rfl)
        simp [h, this]
    · have : ¬(([C], k) = (y :: l0, k0)) := fun he => hy (by cases he; rfl)
      simp [hy, this]
  by_cases hm : hasMember G T g = true
  · simp only [hm, ↓reduceIte, List.nil_append, applyAll_single]
    refine ⟨_, apply_added.mpr ⟨hitem, by simp [Tree.parentOk, get_groupBy_root, hm], rfl⟩, ?_⟩
    rintro ⟨l0, k0⟩
    cases l0 with
    | nil =>
      rw [get_cons, get_groupBy_root, get_groupBy_root, hmem]
      by_cases h : g = k0
      · subst h; simp [hm]
      · simp [h]
    | cons y l0 => rw [get_cons, hitems]
  · simp only [hm, Bool.false_eq_true, ↓reduceIte, List.singleton_append, Tree.applyAll]
    have h1 : (groupBy.F G C T).apply (.added [] g none (groupProps G g)) =
        some ((([], g), ⟨none, groupProps G g⟩) :: groupBy.F G C T) :=
      apply_added.mpr ⟨by simp [get_groupBy_root, hm], rfl, rfl⟩
    rw [h1, Option.bind_some, bind_some_eq]
    refine ⟨_, apply_added.mpr ⟨by rw [get_cons]; simpa using hitem,
      by simp [Tree.parentOk, get_cons], rfl⟩, ?_⟩
    rintro ⟨l0, k0⟩
    cases l0 with
    | nil =>
      rw [get_cons, get_cons, get_groupBy_root, get_groupBy_root, hmem]
      by_cases h : g = k0
      · subst h; simp
      · simp [h]
    | cons y l0 => rw [get_cons, get_cons, hitems]; simp

theorem groupBy_removed_root {T T' : Tree} (hwf : T.WF) {k : Key}
    (he : T.apply (.removed [] k) = some T') :
    ∃ U, (groupBy.F G C T).applyAll ((groupBy G C).handle T (.removed [] k)) = some U ∧
      U.Equiv (groupBy.F G C T') := by
  obtain ⟨hs, hc, rfl⟩ := apply_removed.mp he
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
  simp only [groupBy, hn]
  generalize hg : groupKey G n.props = g
  have hrest : Tree.WF (T.filter (·.1 != ([], k))) := apply_wf hwf he
  have hT : hasMember G T g = true := (hasMember_iff hwf.nodup g).mpr ⟨k, n, hn, hg⟩
  have hother : ∀ g0, g0 ≠ g → hasMember G (T.filter (·.1 != ([], k))) g0 = hasMember G T g0 :=
    fun g0 hg0 => hasMember_filter hwf.nodup _ g0 fun m hm => by
      rw [hn] at hm; cases hm; exact fun h => hg0 (h.2.symm.trans hg)
  have h1 : (groupBy.F G C T).apply (.removed [C] k) =
      some ((groupBy.F G C T).filter (·.1 != ([C], k))) :=
    apply_removed.mpr ⟨by simp [get_groupBy_cons, hn], by rw [hasChild_groupBy_cons hwf]; exact hc, rfl⟩
  have hitems : ∀ y l0 k0, Tree.get ((groupBy.F G C T).filter (·.1 != ([C], k))) (y :: l0, k0) =
      (groupBy.F G C (T.filter (·.1 != ([], k)))).get (y :: l0, k0) := by
    intro y l0 k0
    rw [get_filter, get_groupBy_cons, get_groupBy_cons, get_filter]
    by_cases hy : y = C
    · subst y
      by_cases h : (l0, k0) = ([], k)
      · cases h; simp
      · have : ¬((C :: l0, k0) = ([C], k)) := fun he => h (by cases he; rfl)
        simp [h, this]
    · have : ¬((y :: l0, k0) = ([C], k)) := fun he => hy (by cases he; rfl)
      simp [hy, this]
  by_cases hm : hasMember G (T.filter (·.1 != ([], k))) g = true
  · simp only [hm, ↓reduceIte, applyAll_single, h1, Option.some.injEq, exists_eq_left']
    rintro ⟨l0, k0⟩
    cases l0 with
    | nil =>
      rw [get_filter, get_groupBy_root, get_groupBy_root]
      simp only [show ¬(([] : Level), k0) = ([C], k) by simp, ↓reduceIte]
      by_cases h : k0 = g
      · subst h; simp [hm, hT]
      · rw [hother k0 h]
    | cons y l0 => exact hitems y l0 k0
  · simp only [hm, Bool.false_eq_true, ↓reduceIte, Tree.applyAll, h1, Option.bind_some, bind_some_eq]
    have hA := apply_wf (groupBy_wf (G := G) (C := C) hwf) h1
    have hnochild : Tree.hasChild ((groupBy.F G C T).filter (·.1 != ([C], k))) [] g = false := by
      rw [Bool.eq_false_iff]; intro hch
      obtain ⟨l', k', m, hm', hl', hd, hp⟩ := (hasChild_iff hA.nodup _ _).mp hch
      obtain ⟨y, hy⟩ : ∃ y, l' = [y] := by
        cases l' with
        | nil => exact absurd rfl hl'
        | cons y l'' => cases l'' with
          | nil => exact ⟨y, rfl⟩
          | cons z l''' => simp at hd
      subst hy
      rw [hitems, get_groupBy_cons] at hm'
      by_cases hyc : y = C
      · subst y
        simp only [↓reduceIte, Option.map_eq_some_iff] at hm'
        obtain ⟨m', hm'', rfl⟩ := hm'
        simp only [relevel_root, Option.some.injEq] at hp
        exact hm ((hasMember_iff hrest.nodup g).mpr ⟨k', m', hm'', hp⟩)
      · simp [hyc] at hm'
    refine ⟨_, apply_removed.mpr ⟨by
      rw [get_filter]; simp [get_groupBy_root, hT], hnochild, rfl⟩, ?_⟩
    rintro ⟨l0, k0⟩
    cases l0 with
    | nil =>
      rw [get_filter, get_filter, get_groupBy_root, get_groupBy_root]
      simp only [show ¬(([] : Level), k0) = ([C], k) by simp, ↓reduceIte]
      by_cases h : k0 = g
      · subst h; simp [hm]
      · simp [h, hother k0 h]
    | cons y l0 =>
      rw [get_filter, hitems]
      simp

/-- **The case of issue #29.** A grouping value of a root row changes. The row
moves to its new group with one `placed` event, keeping its values and its
subtree. -/
theorem groupBy_modified_grouping {T T' : Tree} (hwf : T.WF) {k : Key} {p : String}
    {old new : Option Val} (hpG : p ∈ G) (he : T.apply (.modified [] k p old new) = some T') :
    ∃ U, (groupBy.F G C T).applyAll ((groupBy G C).handle T (.modified [] k p old new)) = some U ∧
      U.Equiv (groupBy.F G C T') := by
  obtain ⟨n, hn, h1, h2, rfl⟩ := apply_modified.mp he
  have hT' := apply_wf hwf he
  have hFT := groupBy_wf (G := G) (C := C) hwf
  have hrestnd : ((T.filter (·.1 != ([], k))).map (·.1)).Nodup := by
    rw [keys_filter]; exact hwf.nodup.filter _
  simp only [groupBy, hn, hpG, ↓reduceIte]
  generalize hg : groupKey G n.props = g
  generalize hg' : groupKey G (n.props.set p new) = g'
  have hne : g ≠ g' := fun h => groupKey_set_ne hpG (h1 ▸ h2) (hg'.trans (h.symm.trans hg.symm))
  -- Membership before and after.
  have hTg : hasMember G T g = true := (hasMember_iff hwf.nodup g).mpr ⟨k, n, hn, hg⟩
  have hrest : ∀ g0, g0 ≠ g →
      hasMember G (T.filter (·.1 != ([], k))) g0 = hasMember G T g0 := fun g0 h0 =>
    hasMember_filter hwf.nodup _ g0 fun m hm => by
      rw [hn] at hm; cases hm; exact fun h => h0 (h.2.symm.trans hg)
  have hT'g' : hasMember G (T.update ([], k) fun n => { n with props := n.props.set p new }) g' = true :=
    (hasMember_iff hT'.nodup g').mpr
      ⟨k, { n with props := n.props.set p new }, by rw [get_update]; simp [hn], hg'⟩
  have hT'g : hasMember G (T.update ([], k) fun n => { n with props := n.props.set p new }) g =
      hasMember G (T.filter (·.1 != ([], k))) g := by
    rw [Bool.eq_iff_iff, hasMember_iff hT'.nodup, hasMember_iff hrestnd]
    constructor
    · rintro ⟨k0, m, hm, hmg⟩
      rw [get_update] at hm
      by_cases h : (([] : Level), k0) = ([], k)
      · cases h; simp only [↓reduceIte, hn, Option.map_some, Option.some.injEq] at hm
        subst hm; exact absurd (hg'.symm.trans hmg).symm hne
      · exact ⟨k0, m, by rw [get_filter]; simpa [h] using hm, hmg⟩
    · rintro ⟨k0, m, hm, hmg⟩
      rw [get_filter] at hm
      by_cases h : (([] : Level), k0) = ([], k)
      · simp [h] at hm
      · exact ⟨k0, m, by rw [get_update]; simpa [h] using hm, hmg⟩
  have hT'other : ∀ g0, g0 ≠ g → g0 ≠ g' →
      hasMember G (T.update ([], k) fun n => { n with props := n.props.set p new }) g0 =
        hasMember G T g0 := fun g0 h0 h0' =>
    hasMember_update hwf.nodup _ _ g0 fun m hm => by
      rw [hn] at hm; cases hm
      simp only [true_and]
      exact ⟨fun h => absurd (hg'.symm.trans h) (Ne.symm h0'), fun h => absurd (hg.symm.trans h) (Ne.symm h0)⟩
  -- After the new group, if any.
  let A : Tree := if hasMember G (T.filter (·.1 != ([], k))) g' then groupBy.F G C T
    else (([], g'), ⟨none, groupProps G g'⟩) :: groupBy.F G C T
  have hA : (groupBy.F G C T).applyAll
      (if hasMember G (T.filter (·.1 != ([], k))) g' then []
        else [.added [] g' none (groupProps G g')]) = some A := by
    by_cases hm : hasMember G (T.filter (·.1 != ([], k))) g' = true
    · simp [A, hm, Tree.applyAll]
    · simp only [A, hm, Bool.false_eq_true, ↓reduceIte, applyAll_single]
      rw [hrest g' (Ne.symm hne)] at hm
      exact apply_added.mpr ⟨by simp [get_groupBy_root, hm], rfl, rfl⟩
  have hAroot : ∀ g0, A.get ([], g0) =
      if g0 = g' then some ⟨none, groupProps G g'⟩ else (groupBy.F G C T).get ([], g0) := by
    intro g0
    by_cases hm : hasMember G (T.filter (·.1 != ([], k))) g' = true
    · simp only [A, hm, ↓reduceIte]
      by_cases h : g0 = g'
      · subst h; rw [hrest g0 (Ne.symm hne)] at hm; simp [get_groupBy_root, hm]
      · simp [h]
    · simp only [A, hm, Bool.false_eq_true, ↓reduceIte, get_cons]
      by_cases h : g0 = g'
      · subst h; simp
      · have : g' ≠ g0 := fun e => h e.symm
        simp [h, this]
  have hAcons : ∀ y l0 k0, A.get (y :: l0, k0) = (groupBy.F G C T).get (y :: l0, k0) := by
    intro y l0 k0
    by_cases hm : hasMember G (T.filter (·.1 != ([], k))) g' = true
    · simp [A, hm]
    · simp [A, hm, get_cons]
  have hAwf : A.WF := applyAll_wf hFT hA
  -- The move.
  have hitem : A.get ([C], k) = some ⟨some g, omitProps G n.props⟩ := by
    rw [hAcons, get_groupBy_cons]; simp [hn, relevel_root, hg]
  have hplace : A.apply (.placed [C] k g g') =
      some (A.update ([C], k) fun m => { m with parent := some g' }) :=
    apply_placed.mpr ⟨_, hitem, rfl, hne, by simp [Tree.parentOk, hAroot], rfl⟩
  let A2 := A.update ([C], k) fun m => { m with parent := some g' }
  have hA2wf : A2.WF := apply_wf hAwf hplace
  have hA2root : ∀ g0, A2.get ([], g0) = A.get ([], g0) := fun g0 => by
    simp only [A2, get_update]; simp
  have hA2cons : ∀ y l0 k0, A2.get (y :: l0, k0) = if (y :: l0, k0) = ([C], k)
      then some ⟨some g', omitProps G n.props⟩ else (groupBy.F G C T).get (y :: l0, k0) := by
    intro y l0 k0
    simp only [A2, get_update]
    split
    · rename_i h; cases h; rw [hitem]; rfl
    · exact hAcons y l0 k0
  -- The items match the output for the changed input.
  have hitems : ∀ y l0 k0, A2.get (y :: l0, k0) =
      (groupBy.F G C (T.update ([], k) fun n => { n with props := n.props.set p new })).get
        (y :: l0, k0) := by
    intro y l0 k0
    rw [hA2cons, get_groupBy_cons, get_groupBy_cons, get_update]
    by_cases hy : y = C
    · subst y
      by_cases h : (l0, k0) = ([], k)
      · cases h; simp [hn, relevel_root, hg', omitProps_set_mem hpG]
      · have : ¬((C :: l0, k0) = ([C], k)) := fun he => h (by cases he; rfl)
        simp [h, this]
    · have : ¬((y :: l0, k0) = ([C], k)) := fun he => hy (by cases he; rfl)
      simp [hy, this]
  by_cases hmg : hasMember G (T.filter (·.1 != ([], k))) g = true
  · simp only [hmg, ↓reduceIte, List.append_nil, applyAll_append, hA, Option.bind_some,
      applyAll_single, hplace, Option.some.injEq, exists_eq_left']
    rintro ⟨l0, k0⟩
    cases l0 with
    | nil =>
      rw [hA2root, hAroot, get_groupBy_root, get_groupBy_root]
      by_cases h' : k0 = g'
      · subst h'; simp [hT'g']
      · by_cases h : k0 = g
        · subst h; simp [h', hTg, hT'g, hmg]
        · simp [h', hT'other k0 h h']
    | cons y l0 => exact hitems y l0 k0
  · have hnochild : A2.hasChild [] g = false := by
      rw [Bool.eq_false_iff]; intro hch
      obtain ⟨l', k', m, hm', hl', hd, hp⟩ := (hasChild_iff hA2wf.nodup _ _).mp hch
      obtain ⟨y, hy⟩ : ∃ y, l' = [y] := by
        cases l' with
        | nil => exact absurd rfl hl'
        | cons y l'' => cases l'' with
          | nil => exact ⟨y, rfl⟩
          | cons z l''' => simp at hd
      subst hy
      rw [hA2cons] at hm'
      split at hm'
      · cases hm'; simp at hp; exact hne hp.symm
      · rename_i hk
        rw [get_groupBy_cons] at hm'
        by_cases hyc : y = C
        · subst y
          simp only [↓reduceIte, Option.map_eq_some_iff] at hm'
          obtain ⟨m', hm'', rfl⟩ := hm'
          simp only [relevel_root, Option.some.injEq] at hp
          have hk' : (([] : Level), k') ≠ ([], k) := fun h => hk (by cases h; rfl)
          exact hmg ((hasMember_iff hrestnd g).mpr ⟨k', m', by rw [get_filter]; simpa [hk'] using hm'', hp⟩)
        · simp [hyc] at hm'
    have hremove : A2.apply (.removed [] g) = some (A2.filter (·.1 != ([], g))) :=
      apply_removed.mpr ⟨by rw [hA2root, hAroot]; simp [hne, get_groupBy_root, hTg],
        hnochild, rfl⟩
    simp only [hmg, Bool.false_eq_true, ↓reduceIte, applyAll_append, hA, Option.bind_some,
      applyAll_single, hplace]
    change ∃ U, A2.apply (.removed [] g) = some U ∧ _
    rw [hremove]
    refine ⟨_, rfl, ?_⟩
    rintro ⟨l0, k0⟩
    cases l0 with
    | nil =>
      rw [get_filter, hA2root, hAroot, get_groupBy_root, get_groupBy_root]
      by_cases h' : k0 = g'
      · subst h'; simp [Ne.symm hne, hT'g']
      · by_cases h : k0 = g
        · subst h; simp [hT'g, hmg]
        · simp [h', h, hT'other k0 h h']
    | cons y l0 => rw [get_filter]; simpa using hitems y l0 k0

/-- Any other property of a root row changes on the row below its group. -/
theorem groupBy_modified_other {T T' : Tree} (hwf : T.WF) {k : Key} {p : String}
    {old new : Option Val} (hpG : p ∉ G) (he : T.apply (.modified [] k p old new) = some T') :
    ∃ U, (groupBy.F G C T).applyAll ((groupBy G C).handle T (.modified [] k p old new)) = some U ∧
      U.Equiv (groupBy.F G C T') := by
  obtain ⟨n, hn, h1, h2, rfl⟩ := apply_modified.mp he
  simp only [groupBy, hn, hpG, ↓reduceIte, applyAll_single]
  refine ⟨_, apply_modified.mpr ⟨⟨some (groupKey G n.props), omitProps G n.props⟩,
    by simp [get_groupBy_cons, hn, relevel_root], by simp [omitProps, hpG, h1], h2, rfl⟩, ?_⟩
  rintro ⟨l0, k0⟩
  cases l0 with
  | nil =>
    rw [get_update, get_groupBy_root, get_groupBy_root,
      hasMember_update hwf.nodup _ _ k0 fun m hm => by
        rw [hn] at hm; cases hm; simp [groupKey_set_not_mem hpG]]
    simp
  | cons y l0 =>
    rw [get_update, get_groupBy_cons, get_groupBy_cons, get_update]
    by_cases hy : y = C
    · subst y
      by_cases h : (l0, k0) = ([], k)
      · cases h
        simp [hn, relevel_root, groupKey_set_not_mem hpG, omitProps_set_not_mem hpG]
      · have : ¬((C :: l0, k0) = ([C], k)) := fun he => h (by cases he; rfl)
        simp [h, this]
    · have : ¬((y :: l0, k0) = ([C], k)) := fun he => hy (by cases he; rfl)
      simp [hy, this]

/-- **`groupBy_correct`.** -/
theorem groupBy_correct (G : List String) (C : String) :
    Correct (groupBy G C) (groupBy.F G C) := by
  intro T e T' hwf he
  cases e with
  | added l k p ps =>
    cases l with
    | nil => exact groupBy_added_root he
    | cons x l => simpa [groupBy, applyAll_single] using groupBy_added_cons he
  | removed l k =>
    cases l with
    | nil => exact groupBy_removed_root hwf he
    | cons x l => simpa [groupBy, applyAll_single] using groupBy_removed_cons hwf he
  | modified l k p old new =>
    cases l with
    | nil =>
      by_cases hpG : p ∈ G
      · exact groupBy_modified_grouping hwf hpG he
      · exact groupBy_modified_other hwf hpG he
    | cons x l => simpa [groupBy, applyAll_single] using groupBy_modified_cons hwf he
  | placed l k a b =>
    cases l with
    | nil =>
      obtain ⟨n, hn, h1, -⟩ := apply_placed.mp he
      exact absurd (root_parent hwf hn) (by simp [h1])
    | cons x l => simpa [groupBy, applyAll_single] using groupBy_placed_cons hwf he

end JinagaSpec.Cascade
