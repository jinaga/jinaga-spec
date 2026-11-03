import JinagaSpec.Cascade.Flatten
import JinagaSpec.Proofs.Cascade.GroupBy

/-!
# Cascade: `flatten` at the root

The output's nodes are read through `get` (`get_flatten`): each output level
comes from one input level (`flatten.source`), and a flattened row from a child
and its parent. `flatten_correct` follows event by event.
-/
namespace JinagaSpec.Cascade

variable {P C O : String} {I : List String}

/-! ## Levels -/

theorem level_source (hPO : P ≠ O) (l l' : Level) :
    flatten.level P C O l = some l' ↔ flatten.source P C O l' = some l := by
  constructor
  · intro h
    cases l with
    | nil => simp [flatten.level] at h; subst h; rfl
    | cons x rest =>
      unfold flatten.level at h
      by_cases hxO : x = O
      · simp [hxO] at h
      · by_cases hxP : x = P
        · subst hxP
          simp only [hxO, ↓reduceIte] at h
          cases rest with
          | nil => simp at h
          | cons y rest' =>
            by_cases hy : y = C
            · subst hy; simp at h; subst h; simp [flatten.source]
            · simp [hy] at h
        · simp only [hxO, hxP, ↓reduceIte, Option.some.injEq] at h
          subst h; simp [flatten.source, hxO, hxP]
  · intro h
    cases l' with
    | nil => simp [flatten.source] at h; subst h; rfl
    | cons x rest =>
      unfold flatten.source at h
      by_cases hxO : x = O
      · subst hxO; simp at h; subst h; simp [flatten.level, hPO]
      · by_cases hxP : x = P
        · subst hxP; simp [hPO] at h
        · simp only [hxO, hxP, ↓reduceIte, Option.some.injEq] at h
          subst h; simp [flatten.level, hxO, hxP]

/-! ## `get` through a renaming `filterMap` -/

/-- A `filterMap` that keeps or drops each entry, and renames a kept one's id by
`rename`, whose preimage is `back`. Its `get` reads the input at the preimage. -/
theorem get_filterMap_rename (f : Id × Node → Option (Id × Node)) (back : Id → Option Id)
    (hf : ∀ e e', f e = some e' → back e'.1 = some e.1)
    (hback : ∀ e id', back id' = some e.1 → (f e).isSome → (f e).map (·.1) = some id') :
    ∀ (L : Tree), (L.map (·.1)).Nodup → ∀ id', Tree.get (L.filterMap f) id' =
      (back id').bind fun id => (Tree.get L id).bind fun n => (f (id, n)).map (·.2) := by
  intro L
  induction L with
  | nil => intro _ id'; cases back id' <;> simp
  | cons x L ih =>
    obtain ⟨xid, xn⟩ := x
    intro hnd id'
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hfresh : Tree.get L xid = none := by
      cases h : Tree.get L xid with
      | none => rfl
      | some n => exact absurd (List.mem_map.mpr ⟨(xid, n), mem_of_get h, rfl⟩) hnd.1
    rw [List.filterMap_cons]
    cases hx : f (xid, xn) with
    | none =>
      simp only
      rw [ih hnd.2 id']
      cases hb : back id' with
      | none => rfl
      | some id =>
        simp only [Option.bind_some]
        rw [get_cons]
        by_cases he : xid = id
        · subst he; simp [hfresh, hx]
        · simp [he]
    | some e' =>
      simp only
      rw [get_cons, ih hnd.2 id']
      have hb' := hf (xid, xn) e' hx
      by_cases he : e'.1 = id'
      · subst he
        simp only [↓reduceIte, hb', Option.bind_some]
        rw [get_cons]
        simp [hx]
      · simp only [he, ↓reduceIte]
        cases hb : back id' with
        | none => rfl
        | some id =>
          simp only [Option.bind_some]
          rw [get_cons]
          by_cases hxi : xid = id
          · exfalso
            subst hxi
            have := hback (xid, xn) id' hb (by simp [hx])
            simp [hx] at this
            exact he this
          · simp [hxi]

/-! ## `get` of the output -/

/-- What a node at input level `l` becomes. -/
def flatten.node (P C : String) (I : List String) (T : Tree) (l : Level) (n : Node) : Option Node :=
  if l = [P, C] then (flatten.parentOf P T n).map fun pn => ⟨pn.parent, flattenProps I pn.props n.props⟩
  else some n

theorem get_flatten (hPO : P ≠ O) {T : Tree} (hnd : (T.map (·.1)).Nodup) (l' : Level) (k : Key) :
    (flatten.F P C O I T).get (l', k) =
      (flatten.source P C O l').bind fun l => (T.get (l, k)).bind (flatten.node P C I T l) := by
  unfold flatten.F
  rw [get_filterMap_rename _ (fun id => (flatten.source P C O id.1).map (·, id.2)) ?_ ?_ T hnd (l', k)]
  · cases hs : flatten.source P C O l' with
    | none => rfl
    | some l =>
      simp only [Option.map_some, Option.bind_some]
      cases T.get (l, k) with
      | none => rfl
      | some n =>
        simp only [Option.bind_some, flatten.node]
        have hl := (level_source hPO l l').mpr hs
        simp only [hl, Option.bind_some]
        split <;> simp [Option.map_map, Function.comp_def]
  · rintro ⟨⟨l, k⟩, n⟩ ⟨⟨l', k'⟩, n'⟩ h
    simp only at h ⊢
    cases hl : flatten.level P C O l with
    | none => simp [hl] at h
    | some l'' =>
      simp only [hl, Option.bind_some] at h
      have hs := (level_source hPO l l'').mp hl
      split at h
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨_, -, h⟩ := h
        simp only [Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, -⟩ := h
        simp [hs]
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, -⟩ := h
        simp [hs]
  · rintro ⟨⟨l, k⟩, n⟩ ⟨l', k'⟩ hb hsome
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hb
    obtain ⟨l0, hs, rfl, rfl⟩ := hb
    have hl := (level_source hPO _ l').mpr hs
    simp only [hl, Option.bind_some]
    split
    · simp only [Option.isSome_iff_exists] at hsome ⊢
      simp_all
      obtain ⟨_, _, _, pn, hpn, -⟩ := hsome
      exact ⟨pn, hpn⟩
    · simp_all

/-- The root, and every array other than `P` and `O`, are unchanged. -/
theorem get_flatten_root (hPO : P ≠ O) {T : Tree} (hnd : (T.map (·.1)).Nodup) (k : Key) :
    (flatten.F P C O I T).get ([], k) = T.get ([], k) := by
  rw [get_flatten hPO hnd]
  simp only [flatten.source, Option.bind_some]
  cases T.get ([], k) with
  | none => rfl
  | some n => simp [flatten.node]

theorem get_flatten_other (hPO : P ≠ O) {T : Tree} (hnd : (T.map (·.1)).Nodup) {x : String}
    (hxO : x ≠ O) (hxP : x ≠ P) (rest : Level) (k : Key) :
    (flatten.F P C O I T).get (x :: rest, k) = T.get (x :: rest, k) := by
  rw [get_flatten hPO hnd]
  simp only [flatten.source, hxO, hxP, ↓reduceIte, Option.bind_some]
  cases T.get (x :: rest, k) with
  | none => rfl
  | some n =>
    have : x :: rest ≠ [P, C] := fun h => hxP (List.cons.inj h).1
    simp [flatten.node, this]

/-- A parent's level is gone. -/
theorem get_flatten_parent (hPO : P ≠ O) {T : Tree} (hnd : (T.map (·.1)).Nodup) (rest : Level)
    (k : Key) : (flatten.F P C O I T).get (P :: rest, k) = none := by
  rw [get_flatten hPO hnd]
  simp [flatten.source, hPO]

/-- A flattened row: a child, under its parent's parent, with its parent's values. -/
theorem get_flatten_row (hPO : P ≠ O) {T : Tree} (hnd : (T.map (·.1)).Nodup) (k : Key) :
    (flatten.F P C O I T).get ([O], k) =
      (T.get ([P, C], k)).bind fun n =>
        (flatten.parentOf P T n).map fun pn => ⟨pn.parent, flattenProps I pn.props n.props⟩ := by
  rw [get_flatten hPO hnd]
  simp only [flatten.source, ↓reduceIte, Option.bind_some]
  cases T.get ([P, C], k) with
  | none => rfl
  | some n => simp [flatten.node]

/-- What was below a child stays below its row. -/
theorem get_flatten_below (hPO : P ≠ O) {T : Tree} (hnd : (T.map (·.1)).Nodup) {rest : Level}
    (hr : rest ≠ []) (k : Key) :
    (flatten.F P C O I T).get (O :: rest, k) = T.get (P :: C :: rest, k) := by
  rw [get_flatten hPO hnd]
  simp only [flatten.source, ↓reduceIte, Option.bind_some]
  cases T.get (P :: C :: rest, k) with
  | none => rfl
  | some n =>
    have : P :: C :: rest ≠ [P, C] := fun h => hr (by simpa using h)
    simp [flatten.node, this]

/-! ## The output is well formed -/

theorem nodup_filterMap_rename (f : Id × Node → Option (Id × Node)) (back : Id → Option Id)
    (hf : ∀ e e', f e = some e' → back e'.1 = some e.1) {L : Tree} (hnd : (L.map (·.1)).Nodup) :
    ((L.filterMap f).map (·.1)).Nodup := by
  unfold List.Nodup at hnd ⊢
  rw [List.pairwise_map] at hnd ⊢
  refine hnd.filterMap f fun a a' hne b hb b' hb' heq => hne ?_
  have h1 := hf a b hb
  have h2 := hf a' b' hb'
  rw [heq, h2] at h1
  exact (Option.some.inj h1).symm

theorem flatten_nodup (hPO : P ≠ O) {T : Tree} (hnd : (T.map (·.1)).Nodup) :
    ((flatten.F P C O I T).map (·.1)).Nodup := by
  unfold flatten.F
  refine nodup_filterMap_rename _ (fun id => (flatten.source P C O id.1).map (·, id.2)) ?_ hnd
  rintro ⟨⟨l, k⟩, n⟩ ⟨⟨l', k'⟩, n'⟩ h
  simp only at h ⊢
  cases hl : flatten.level P C O l with
  | none => simp [hl] at h
  | some l'' =>
    simp only [hl, Option.bind_some] at h
    have hs := (level_source hPO l l'').mp hl
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, -, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      simp [hs]
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      simp [hs]

/-- A node's parent, if it has one, is at the level above. -/
theorem parent_above {T : Tree} (hwf : T.WF) {l : Level} {k : Key} {n : Node}
    (hn : T.get (l, k) = some n) (hl : l ≠ []) : ∃ q, n.parent = some q ∧ (T.get (l.dropLast, q)).isSome := by
  have hp := hwf.parents _ _ hn
  cases hq : n.parent with
  | none => rw [hq] at hp; simp [Tree.parentOk, hl] at hp
  | some q =>
    rw [hq] at hp
    simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    exact ⟨q, rfl, hp.2⟩

theorem flatten_wf (hPO : P ≠ O) {T : Tree} (hwf : T.WF) : (flatten.F P C O I T).WF := by
  have hnd := hwf.nodup
  refine ⟨flatten_nodup hPO hnd, ?_⟩
  rintro ⟨l, k⟩ n hn
  simp only
  cases l with
  | nil =>
    rw [get_flatten_root hPO hnd] at hn
    have := hwf.parents _ _ hn
    cases hq : n.parent with
    | none => rfl
    | some q => rw [hq] at this; simp [Tree.parentOk] at this
  | cons x rest =>
    by_cases hxO : x = O
    · subst hxO
      cases rest with
      | nil =>
        -- A flattened row is under its parent's parent.
        rw [get_flatten_row hPO hnd] at hn
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hn
        obtain ⟨m, hm, pn, hpn, rfl⟩ := hn
        unfold flatten.parentOf at hpn
        simp only [Option.bind_eq_some_iff] at hpn
        obtain ⟨pk, -, hpk⟩ := hpn
        obtain ⟨g, hg, hgs⟩ := parent_above hwf hpk (by simp)
        simp only [hg, Tree.parentOk, List.isEmpty_cons, Bool.not_false, Bool.true_and,
          List.dropLast_singleton, get_flatten_root hPO hnd]
        simpa using hgs
      | cons y rest' =>
        -- Below a flattened row, under the same parent.
        rw [get_flatten_below hPO hnd (by simp)] at hn
        obtain ⟨q, hq, hqs⟩ := parent_above hwf hn (by simp)
        simp only [hq, Tree.parentOk, List.isEmpty_cons, Bool.not_false, Bool.true_and]
        rw [List.dropLast_cons_of_ne_nil (by simp)]
        rw [List.dropLast_cons_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil (by simp)] at hqs
        cases hr : (y :: rest').dropLast with
        | nil =>
          rw [hr] at hqs
          obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hqs
          obtain ⟨pk, hpk, hpks⟩ := parent_above hwf hm (by simp)
          obtain ⟨pn, hpn⟩ := Option.isSome_iff_exists.mp hpks
          have hpn' : T.get ([P], pk) = some pn := by simpa using hpn
          rw [get_flatten_row hPO hnd, hm]
          simp [flatten.parentOf, hpk, hpn']
        | cons z rest'' =>
          rw [hr] at hqs
          rw [get_flatten_below hPO hnd (by simp)]
          exact hqs
    · by_cases hxP : x = P
      · subst hxP; rw [get_flatten_parent hPO hnd] at hn; cases hn
      · rw [get_flatten_other hPO hnd hxO hxP] at hn
        obtain ⟨q, hq, hqs⟩ := parent_above hwf hn (by simp)
        simp only [hq, Tree.parentOk, List.isEmpty_cons, Bool.not_false, Bool.true_and]
        cases rest with
        | nil => simpa [get_flatten_root hPO hnd] using hqs
        | cons y rest' =>
          rw [List.dropLast_cons_of_ne_nil (by simp)] at hqs ⊢
          rw [get_flatten_other hPO hnd hxO hxP]
          exact hqs

theorem flatten_denotation (hPO : P ≠ O) : Denotation (flatten.F P C O I) := by
  refine ⟨fun _ hT => flatten_wf hPO hT, fun T U hT hU h id => ?_⟩
  obtain ⟨l, k⟩ := id
  have hnode : flatten.node P C I T = flatten.node P C I U := by
    funext l n; simp [flatten.node, flatten.parentOf, h _]
  rw [get_flatten hPO hT.nodup, get_flatten hPO hU.nodup, hnode]
  simp only [h _]

/-! ## Frames -/

theorem level_nil {l : Level} (hPO : P ≠ O) (h : flatten.level P C O l = some []) : l = [] := by
  have := (level_source hPO l []).mp h
  simp [flatten.source] at this
  exact this

theorem level_ne_nil {l l' : Level} (hl : l ≠ []) (h : flatten.level P C O l = some l') : l' ≠ [] := by
  cases l with
  | nil => exact absurd rfl hl
  | cons x rest =>
    by_cases hxO : x = O
    · simp [flatten.level, hxO] at h
    · by_cases hxP : x = P
      · subst hxP
        cases rest with
        | nil => simp [flatten.level, hxO] at h
        | cons y r =>
          by_cases hy : y = C
          · subst hy; simp [flatten.level, hxO] at h; subst h; simp
          · simp [flatten.level, hxO, hy] at h
      · simp [flatten.level, hxO, hxP] at h; subst h; simp

/-- The level above a kept level is kept, at the level above its image. -/
theorem level_dropLast {l l' : Level} (hl : l ≠ []) (hPC : l ≠ [P, C])
    (h : flatten.level P C O l = some l') : flatten.level P C O l.dropLast = some l'.dropLast := by
  cases l with
  | nil => exact absurd rfl hl
  | cons x rest =>
    unfold flatten.level at h
    by_cases hxO : x = O
    · simp [hxO] at h
    · by_cases hxP : x = P
      · subst hxP
        simp only [hxO, ↓reduceIte] at h
        cases rest with
        | nil => simp at h
        | cons y rest' =>
          by_cases hy : y = C
          · subst hy
            simp only [↓reduceIte, Option.some.injEq] at h
            subst h
            have hr : rest' ≠ [] := fun h => hPC (by rw [h])
            rw [List.dropLast_cons_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil hr,
              List.dropLast_cons_of_ne_nil hr]
            simp [flatten.level, hxO]
          · simp [hy] at h
      · simp only [hxO, hxP, ↓reduceIte, Option.some.injEq] at h
        subst h
        cases rest with
        | nil => rfl
        | cons y rest' =>
          rw [List.dropLast_cons_of_ne_nil (by simp)]
          simp [flatten.level, hxO, hxP]

/-- In a well-formed tree, every node has its image. -/
theorem node_isSome {T : Tree} (hwf : T.WF) {l : Level} {k : Key} {n : Node}
    (hn : T.get (l, k) = some n) : (flatten.node P C I T l n).isSome := by
  unfold flatten.node
  split
  · rename_i hl; subst hl
    obtain ⟨pk, hpk, hpks⟩ := parent_above hwf hn (by simp)
    obtain ⟨pn, hpn⟩ := Option.isSome_iff_exists.mp hpks
    have : T.get ([P], pk) = some pn := by simpa using hpn
    simp [flatten.parentOf, hpk, this]
  · rfl

/-- Changing the input at one id outside the parents' level changes the output
only at that id's image. -/
theorem flatten_frame (hPO : P ≠ O) {T T' : Tree} (hnd : (T.map (·.1)).Nodup)
    (hnd' : (T'.map (·.1)).Nodup) {l : Level} {k : Key} (hlP : l ≠ [P])
    (hsame : ∀ id, id ≠ (l, k) → T'.get id = T.get id) (l0 : Level) (k0 : Key)
    (hne : ¬(flatten.source P C O l0 = some l ∧ k0 = k)) :
    (flatten.F P C O I T').get (l0, k0) = (flatten.F P C O I T).get (l0, k0) := by
  have hnode : flatten.node P C I T' = flatten.node P C I T := by
    funext l1 n
    simp only [flatten.node, flatten.parentOf]
    split
    · congr 1
      rcases n.parent with _ | pk
      · rfl
      · exact hsame _ fun h => hlP (Prod.mk.inj h).1.symm
    · rfl
  rw [get_flatten hPO hnd', get_flatten hPO hnd, hnode]
  cases hs : flatten.source P C O l0 with
  | none => rfl
  | some s =>
    simp only [Option.bind_some]
    rw [hsame]
    intro h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact hne ⟨hs, rfl⟩

theorem source_ne_of_ne (hPO : P ≠ O) {l l' : Level} {k : Key} (hl : flatten.level P C O l = some l')
    {l0 : Level} {k0 : Key} (h : (l0, k0) ≠ (l', k)) :
    ¬(flatten.source P C O l0 = some l ∧ k0 = k) := by
  rintro ⟨hs, rfl⟩
  have := (level_source hPO l l0).mpr hs
  rw [hl] at this
  exact h (by rw [Option.some.inj this])

theorem source_none (hPO : P ≠ O) {l : Level} (hl : flatten.level P C O l = none) (l0 : Level) (k0 k : Key) :
    ¬(flatten.source P C O l0 = some l ∧ k0 = k) := by
  rintro ⟨hs, -⟩
  have := (level_source hPO l l0).mpr hs
  rw [hl] at this
  cases this

/-- A kept node other than a child is itself in the output. -/
theorem get_flatten_kept (hPO : P ≠ O) {T : Tree} (hnd : (T.map (·.1)).Nodup) {l l' : Level}
    (hPC : l ≠ [P, C]) (hl : flatten.level P C O l = some l') (k : Key) :
    (flatten.F P C O I T).get (l', k) = T.get (l, k) := by
  rw [get_flatten hPO hnd, (level_source hPO l l').mp hl]
  simp only [Option.bind_some]
  cases T.get (l, k) with
  | none => rfl
  | some n => simp [flatten.node, hPC]

/-- Where a kept node may go, its image may go. -/
theorem parentOk_flatten (hPO : P ≠ O) {T : Tree} (hwf : T.WF) {l l' : Level} (hPC : l ≠ [P, C])
    (hl : flatten.level P C O l = some l') {p : Option Key} (hp : T.parentOk l p = true) :
    (flatten.F P C O I T).parentOk l' p = true := by
  cases p with
  | none =>
    simp only [Tree.parentOk, List.isEmpty_iff] at hp ⊢
    subst hp
    simpa [flatten.level] using hl.symm
  | some q =>
    simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp ⊢
    obtain ⟨hl0, hq⟩ := hp
    refine ⟨level_ne_nil hl0 hl, ?_⟩
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hq
    rw [get_flatten hPO hwf.nodup, (level_source hPO _ _).mp (level_dropLast hl0 hPC hl)]
    simp only [Option.bind_some, hm]
    exact node_isSome hwf hm

/-- A child of a node's image is the image of one of its children, or, at the
root, a flattened row whose parent is the node's child. -/
theorem hasChild_of_flatten (hPO : P ≠ O) {T : Tree} (hwf : T.WF) {l l' : Level} {k : Key}
    (hl : flatten.level P C O l = some l') (h : (flatten.F P C O I T).hasChild l' k = true) :
    T.hasChild l k = true := by
  rw [hasChild_iff (flatten_nodup hPO hwf.nodup)] at h
  rw [hasChild_iff hwf.nodup]
  obtain ⟨l3, k3, n3, hg, hl3, hdrop, hpar⟩ := h
  rw [get_flatten hPO hwf.nodup] at hg
  cases hs : flatten.source P C O l3 with
  | none => simp [hs] at hg
  | some s =>
    simp only [hs, Option.bind_some, Option.bind_eq_some_iff] at hg
    obtain ⟨m, hm, hnode⟩ := hg
    have hls := (level_source hPO s l3).mpr hs
    unfold flatten.node at hnode
    split at hnode
    · -- A flattened row at the root: its parent's parent is `k`.
      rename_i hsPC; subst hsPC
      simp [flatten.level, hPO] at hls
      subst hls
      simp at hdrop
      subst hdrop
      have hl0 := level_nil hPO hl
      subst hl0
      simp only [Option.map_eq_some_iff] at hnode
      obtain ⟨pn, hpn, rfl⟩ := hnode
      simp only [flatten.parentOf, Option.bind_eq_some_iff] at hpn
      obtain ⟨pk, -, hpk⟩ := hpn
      exact ⟨[P], pk, pn, hpk, by simp, by simp, hpar⟩
    · rename_i hsPC
      simp only [Option.some.injEq] at hnode
      subst hnode
      have hs0 : s ≠ [] := fun h => hl3 (by subst h; simpa [flatten.level] using hls.symm)
      have hd : flatten.level P C O s.dropLast = some l' := by
        rw [level_dropLast hs0 hsPC hls, hdrop]
      have h1 := (level_source hPO _ _).mp hd
      rw [(level_source hPO _ _).mp hl] at h1
      exact ⟨s, k3, m, hm, hs0, (Option.some.inj h1).symm, hpar⟩

/-! ## Events the output relocates or drops -/

/-- The node an event names. -/
def Event.id : Event → Id
  | .added l k _ _ => (l, k)
  | .removed l k => (l, k)
  | .modified l k _ _ _ => (l, k)
  | .placed l k _ _ => (l, k)

/-- An event changes the tree only at the node it names. -/
theorem apply_same {T T' : Tree} {e : Event} (h : T.apply e = some T') :
    ∀ id, id ≠ e.id → T'.get id = T.get id := by
  intro id hid
  cases e with
  | added l k p ps =>
    obtain ⟨-, -, rfl⟩ := apply_added.mp h
    rw [get_cons]; simp [Event.id] at hid; simp [Ne.symm hid]
  | removed l k =>
    obtain ⟨-, -, rfl⟩ := apply_removed.mp h
    rw [get_filter]; simp [Event.id] at hid; simp [hid]
  | modified l k p old new =>
    obtain ⟨-, -, -, -, rfl⟩ := apply_modified.mp h
    rw [get_update]; simp [Event.id] at hid; simp [hid]
  | placed l k a b =>
    obtain ⟨-, -, -, -, -, rfl⟩ := apply_placed.mp h
    rw [get_update]; simp [Event.id] at hid; simp [hid]

/-- An event at a level the output does not keep leaves the output as it was. -/
theorem flatten_dropped (hPO : P ≠ O) {T T' : Tree} (hwf : T.WF) {e : Event}
    (he : T.apply e = some T') (hl : flatten.level P C O e.id.1 = none) (hlP : e.id.1 ≠ [P]) :
    (flatten.F P C O I T).Equiv (flatten.F P C O I T') := by
  have hwf' := apply_wf hwf he
  rintro ⟨l0, k0⟩
  exact (flatten_frame hPO hwf.nodup hwf'.nodup hlP (apply_same he) l0 k0
    (source_none hPO hl l0 k0 e.id.2)).symm

section relocated
variable {T T' : Tree} {l l' : Level} {k : Key}

theorem flatten_relocated_added (hPO : P ≠ O) (hwf : T.WF) (hl : flatten.level P C O l = some l')
    (hlP : l ≠ [P]) (hPC : l ≠ [P, C]) {p : Option Key} {ps : Props}
    (he : T.apply (.added l k p ps) = some T') :
    ∃ U, (flatten.F P C O I T).apply (.added l' k p ps) = some U ∧ U.Equiv (flatten.F P C O I T') := by
  have hwf' := apply_wf hwf he
  obtain ⟨hn, hp, rfl⟩ := apply_added.mp he
  refine ⟨_, apply_added.mpr ⟨by rw [get_flatten_kept hPO hwf.nodup hPC hl]; exact hn,
    parentOk_flatten hPO hwf hPC hl hp, rfl⟩, ?_⟩
  rintro ⟨l0, k0⟩
  rw [get_cons]
  by_cases h : (l', k) = (l0, k0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rw [get_flatten_kept hPO hwf'.nodup hPC hl, get_cons]; simp
  · simp only [h, ↓reduceIte]
    exact (flatten_frame hPO hwf.nodup hwf'.nodup hlP (apply_same he) l0 k0
      (source_ne_of_ne hPO hl (Ne.symm h))).symm

theorem flatten_relocated_removed (hPO : P ≠ O) (hwf : T.WF) (hl : flatten.level P C O l = some l')
    (hlP : l ≠ [P]) (hPC : l ≠ [P, C]) (he : T.apply (.removed l k) = some T') :
    ∃ U, (flatten.F P C O I T).apply (.removed l' k) = some U ∧ U.Equiv (flatten.F P C O I T') := by
  have hwf' := apply_wf hwf he
  obtain ⟨hs, hc, rfl⟩ := apply_removed.mp he
  have hc' : (flatten.F P C O I T).hasChild l' k = false := by
    cases h : (flatten.F P C O I T).hasChild l' k
    · rfl
    · rw [hasChild_of_flatten hPO hwf hl h] at hc; cases hc
  refine ⟨_, apply_removed.mpr ⟨by rw [get_flatten_kept hPO hwf.nodup hPC hl]; exact hs, hc', rfl⟩, ?_⟩
  rintro ⟨l0, k0⟩
  rw [get_filter]
  by_cases h : (l0, k0) = (l', k)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rw [get_flatten_kept hPO hwf'.nodup hPC hl, get_filter]; simp
  · simp only [h, ↓reduceIte]
    exact (flatten_frame hPO hwf.nodup hwf'.nodup hlP (apply_same he) l0 k0
      (source_ne_of_ne hPO hl h)).symm

theorem flatten_relocated_modified (hPO : P ≠ O) (hwf : T.WF) (hl : flatten.level P C O l = some l')
    (hlP : l ≠ [P]) (hPC : l ≠ [P, C]) {x : String} {old new : Option Val}
    (he : T.apply (.modified l k x old new) = some T') :
    ∃ U, (flatten.F P C O I T).apply (.modified l' k x old new) = some U ∧
      U.Equiv (flatten.F P C O I T') := by
  have hwf' := apply_wf hwf he
  obtain ⟨n, hn, h1, h2, rfl⟩ := apply_modified.mp he
  refine ⟨_, apply_modified.mpr ⟨n, by rw [get_flatten_kept hPO hwf.nodup hPC hl]; exact hn,
    h1, h2, rfl⟩, ?_⟩
  rintro ⟨l0, k0⟩
  rw [get_update]
  by_cases h : (l0, k0) = (l', k)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rw [get_flatten_kept hPO hwf'.nodup hPC hl, get_update, get_flatten_kept hPO hwf.nodup hPC hl]; simp
  · simp only [h, ↓reduceIte]
    exact (flatten_frame hPO hwf.nodup hwf'.nodup hlP (apply_same he) l0 k0
      (source_ne_of_ne hPO hl h)).symm

theorem flatten_relocated_placed (hPO : P ≠ O) (hwf : T.WF) (hl : flatten.level P C O l = some l')
    (hlP : l ≠ [P]) (hPC : l ≠ [P, C]) {a b : Key} (he : T.apply (.placed l k a b) = some T') :
    ∃ U, (flatten.F P C O I T).apply (.placed l' k a b) = some U ∧ U.Equiv (flatten.F P C O I T') := by
  have hwf' := apply_wf hwf he
  obtain ⟨n, hn, h1, h2, h3, rfl⟩ := apply_placed.mp he
  refine ⟨_, apply_placed.mpr ⟨n, by rw [get_flatten_kept hPO hwf.nodup hPC hl]; exact hn,
    h1, h2, parentOk_flatten hPO hwf hPC hl h3, rfl⟩, ?_⟩
  rintro ⟨l0, k0⟩
  rw [get_update]
  by_cases h : (l0, k0) = (l', k)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rw [get_flatten_kept hPO hwf'.nodup hPC hl, get_update, get_flatten_kept hPO hwf.nodup hPC hl]; simp
  · simp only [h, ↓reduceIte]
    exact (flatten_frame hPO hwf.nodup hwf'.nodup hlP (apply_same he) l0 k0
      (source_ne_of_ne hPO hl h)).symm

end relocated

/-! ## A parent's children -/

theorem mem_children {T : Tree} (hnd : (T.map (·.1)).Nodup) {k c : Key} :
    c ∈ flatten.children P C T k ↔ ∃ n, T.get ([P, C], c) = some n ∧ n.parent = some k := by
  simp only [flatten.children, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨l, c'⟩, n⟩, ⟨hm, hl, hp⟩, rfl⟩
    simp only at hl hp ⊢
    subst hl
    exact ⟨n, get_of_mem hnd hm, hp⟩
  · rintro ⟨n, hn, hp⟩
    exact ⟨(([P, C], c), n), ⟨mem_of_get hn, rfl, hp⟩, rfl⟩

theorem nodup_children {T : Tree} (hnd : (T.map (·.1)).Nodup) (k : Key) :
    (flatten.children P C T k).Nodup := by
  unfold flatten.children List.Nodup
  rw [List.pairwise_map]
  have hf : ((T.filter fun e => e.1.1 = [P, C] ∧ e.2.parent = some k).map (·.1)).Nodup :=
    hnd.sublist (List.filter_sublist.map _)
  unfold List.Nodup at hf
  rw [List.pairwise_map] at hf
  refine hf.imp_of_mem fun {a b} ha hb hne hk => hne (Prod.ext ?_ hk)
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  rw [ha.2.1, hb.2.1]

/-! ## Inherited values -/

theorem flattenProps_set_mem {x : String} (hx : x ∈ I) (pp cp : Props) (v : Option Val) :
    flattenProps I (pp.set x v) cp = (flattenProps I pp cp).set x v := by
  funext y; by_cases hy : y = x
  · subst hy; simp [flattenProps, Props.set, hx]
  · simp [flattenProps, Props.set, hy]

theorem flattenProps_set_not_mem_parent {x : String} (hx : x ∉ I) (pp cp : Props) (v : Option Val) :
    flattenProps I (pp.set x v) cp = flattenProps I pp cp := by
  funext y; by_cases hy : y = x
  · subst hy; simp [flattenProps, hx]
  · simp [flattenProps, Props.set, hy]

theorem flattenProps_set_mem_child {x : String} (hx : x ∈ I) (pp cp : Props) (v : Option Val) :
    flattenProps I pp (cp.set x v) = flattenProps I pp cp := by
  funext y; by_cases hy : y = x
  · subst hy; simp [flattenProps, hx]
  · simp [flattenProps, Props.set, hy]

theorem flattenProps_set_not_mem_child {x : String} (hx : x ∉ I) (pp cp : Props) (v : Option Val) :
    flattenProps I pp (cp.set x v) = (flattenProps I pp cp).set x v := by
  funext y; by_cases hy : y = x
  · subst hy; simp [flattenProps, Props.set, hx]
  · simp [flattenProps, Props.set, hy]

/-! ## Applying one event per row -/

/-- A change to the same property of each row in `cs`, from the value each has. -/
theorem applyAll_modified_rows {x : String} {old new : Option Val} (hne : old ≠ new) :
    ∀ (cs : List Key) (U : Tree), cs.Nodup →
      (∀ c ∈ cs, ∃ m, U.get ([O], c) = some m ∧ m.props x = old) →
      ∃ U', U.applyAll (cs.map fun c => .modified [O] c x old new) = some U' ∧
        ∀ id, U'.get id = if id.1 = [O] ∧ id.2 ∈ cs
          then (U.get id).map (fun m => { m with props := m.props.set x new }) else U.get id := by
  intro cs
  induction cs with
  | nil => intro U _ _; exact ⟨U, rfl, fun id => by simp⟩
  | cons c cs ih =>
    intro U hnd hrows
    simp only [List.nodup_cons] at hnd
    obtain ⟨m, hm, hmx⟩ := hrows c (List.mem_cons_self ..)
    let U1 := U.update ([O], c) fun m => { m with props := m.props.set x new }
    have h1 : U.apply (.modified [O] c x old new) = some U1 :=
      apply_modified.mpr ⟨m, hm, hmx, hne, rfl⟩
    obtain ⟨U', hU', hget⟩ := ih U1 hnd.2 fun c' hc' => by
      have hne' : ([O], c') ≠ ([O], c) := fun h => hnd.1 (by cases h; exact hc')
      rw [get_update, ite_eq_right hne']
      exact hrows c' (List.mem_cons_of_mem _ hc')
    refine ⟨U', by simp [Tree.applyAll, h1, hU'], fun id => ?_⟩
    rw [hget, get_update]
    obtain ⟨l0, k0⟩ := id
    simp only [List.mem_cons, Prod.mk.injEq]
    by_cases hl0 : l0 = [O]
    · subst hl0
      by_cases hk : k0 = c
      · subst hk; simp [hnd.1]
      · simp [hk]
    · simp [hl0]

/-- A move of each row in `cs` from parent `a` to parent `b`. -/
theorem applyAll_placed_rows {a b : Key} (hne : a ≠ b) :
    ∀ (cs : List Key) (U : Tree), cs.Nodup → U.parentOk [O] (some b) = true →
      (∀ c ∈ cs, ∃ m, U.get ([O], c) = some m ∧ m.parent = some a) →
      ∃ U', U.applyAll (cs.map fun c => .placed [O] c a b) = some U' ∧
        ∀ id, U'.get id = if id.1 = [O] ∧ id.2 ∈ cs
          then (U.get id).map (fun m => { m with parent := some b }) else U.get id := by
  intro cs
  induction cs with
  | nil => intro U _ _ _; exact ⟨U, rfl, fun id => by simp⟩
  | cons c cs ih =>
    intro U hnd hb hrows
    simp only [List.nodup_cons] at hnd
    obtain ⟨m, hm, hma⟩ := hrows c (List.mem_cons_self ..)
    let U1 := U.update ([O], c) fun m => { m with parent := some b }
    have h1 : U.apply (.placed [O] c a b) = some U1 :=
      apply_placed.mpr ⟨m, hm, hma, hne, hb, rfl⟩
    obtain ⟨U', hU', hget⟩ := ih U1 hnd.2 (by rw [parentOk_update]; exact hb) fun c' hc' => by
      have hne' : ([O], c') ≠ ([O], c) := fun h => hnd.1 (by cases h; exact hc')
      rw [get_update, ite_eq_right hne']
      exact hrows c' (List.mem_cons_of_mem _ hc')
    refine ⟨U', by simp [Tree.applyAll, h1, hU'], fun id => ?_⟩
    rw [hget, get_update]
    obtain ⟨l0, k0⟩ := id
    simp only [List.mem_cons, Prod.mk.injEq]
    by_cases hl0 : l0 = [O]
    · subst hl0
      by_cases hk : k0 = c
      · subst hk; simp [hnd.1]
      · simp [hk]
    · simp [hl0]

/-- The changes to a moved child's row: each inherited name that differs takes
the new parent's value. -/
theorem applyAll_inherited {k : Key} {pa pb : Props} :
    ∀ (L : List String) (V : Tree) (m : Node), L.Nodup → V.get ([O], k) = some m →
      (∀ x ∈ L, m.props x = pa x) →
      ∃ V', V.applyAll (L.filterMap fun x =>
          if pa x = pb x then none else some (.modified [O] k x (pa x) (pb x))) = some V' ∧
        ∀ id, V'.get id = if id = ([O], k)
          then some { m with props := fun x => if x ∈ L then pb x else m.props x } else V.get id := by
  intro L
  induction L with
  | nil => intro V m _ hm _; exact ⟨V, rfl, fun id => by split <;> simp_all⟩
  | cons x L ih =>
    intro V m hnd hm hx
    simp only [List.nodup_cons] at hnd
    by_cases hxe : pa x = pb x
    · obtain ⟨V', hV', hget⟩ := ih V m hnd.2 hm fun y hy => hx y (List.mem_cons_of_mem _ hy)
      refine ⟨V', by simpa [List.filterMap_cons, hxe] using hV', fun id => ?_⟩
      rw [hget]
      split
      · congr 2; funext y
        by_cases hy : y = x
        · subst hy; simp [hnd.1, hx y (List.mem_cons_self ..), hxe]
        · simp [hy]
      · rfl
    · let m1 : Node := { m with props := m.props.set x (pb x) }
      have h1 : V.apply (.modified [O] k x (pa x) (pb x)) =
          some (V.update ([O], k) fun m => { m with props := m.props.set x (pb x) }) :=
        apply_modified.mpr ⟨m, hm, hx x (List.mem_cons_self ..), hxe, rfl⟩
      have hm1 : (V.update ([O], k) fun m => { m with props := m.props.set x (pb x) }).get ([O], k) =
          some m1 := by rw [get_update]; simp [hm, m1]
      obtain ⟨V', hV', hget⟩ := ih _ m1 hnd.2 hm1 fun y hy => by
        have : y ≠ x := fun h => hnd.1 (h ▸ hy)
        simp [m1, Props.set, this, hx y (List.mem_cons_of_mem _ hy)]
      refine ⟨V', by simp [List.filterMap_cons, hxe, Tree.applyAll, h1, hV'], fun id => ?_⟩
      rw [hget, get_update]
      by_cases hid : id = ([O], k)
      · subst hid
        simp only [↓reduceIte, Option.some.injEq]
        congr 1; funext y
        by_cases hy : y = x
        · subst hy; simp [m1, Props.set, hnd.1]
        · simp [m1, Props.set, hy]
      · simp [hid]

/-! ## A parent's events -/

/-- No output level comes from the parents' level. -/
theorem source_ne_parent {l0 s0 : Level} (hs : flatten.source P C O l0 = some s0) : s0 ≠ [P] := by
  cases l0 with
  | nil => simp [flatten.source] at hs; subst hs; simp
  | cons x r =>
    by_cases hxO : x = O
    · simp [flatten.source, hxO] at hs; subst hs; simp
    · by_cases hxP : x = P
      · subst hxP; simp [flatten.source, hxO] at hs
      · simp [flatten.source, hxO, hxP] at hs; subst hs; simp [hxP]

/-- Changing a parent changes the output only at its children's rows. -/
theorem flatten_parent_frame (hPO : P ≠ O) {T T' : Tree} (hnd : (T.map (·.1)).Nodup)
    (hnd' : (T'.map (·.1)).Nodup) {k : Key} (hsame : ∀ id, id ≠ ([P], k) → T'.get id = T.get id)
    (l0 : Level) (k0 : Key) (hrow : l0 = [O] → ∀ n, T.get ([P, C], k0) = some n → n.parent ≠ some k) :
    (flatten.F P C O I T').get (l0, k0) = (flatten.F P C O I T).get (l0, k0) := by
  rw [get_flatten hPO hnd', get_flatten hPO hnd]
  cases hs : flatten.source P C O l0 with
  | none => rfl
  | some s0 =>
    simp only [Option.bind_some]
    have hsP : s0 ≠ [P] := source_ne_parent hs
    rw [hsame _ fun h => hsP (Prod.mk.inj h).1]
    cases hg : T.get (s0, k0) with
    | none => rfl
    | some n =>
      simp only [Option.bind_some, flatten.node, flatten.parentOf]
      split
      · rename_i hPC; subst hPC
        have hl0 : l0 = [O] := by
          have := (level_source hPO _ _).mpr hs
          simpa [flatten.level, hPO] using this.symm
        congr 1
        rcases hp : n.parent with _ | pk
        · rfl
        · simp only [Option.bind_some]
          exact hsame _ fun h => hrow hl0 n hg (by rw [hp, (Prod.mk.inj h).2])
      · rfl

theorem flatten_parent_added (hPO : P ≠ O) {T T' : Tree} (hwf : T.WF) {k : Key} {p : Option Key}
    {ps : Props} (he : T.apply (.added [P] k p ps) = some T') :
    (flatten.F P C O I T).Equiv (flatten.F P C O I T') := by
  have hwf' := apply_wf hwf he
  obtain ⟨hn, -, rfl⟩ := apply_added.mp he
  rintro ⟨l0, k0⟩
  refine (flatten_parent_frame hPO hwf.nodup hwf'.nodup (apply_same he) l0 k0 fun _ n hg hp => ?_).symm
  -- A new parent has no children: a child's parent exists.
  obtain ⟨q, hq, hqs⟩ := parent_above hwf hg (by simp)
  rw [hp] at hq
  obtain rfl := Option.some.inj hq
  simp [hn] at hqs

theorem flatten_parent_removed (hPO : P ≠ O) {T T' : Tree} (hwf : T.WF) {k : Key}
    (he : T.apply (.removed [P] k) = some T') :
    (flatten.F P C O I T).Equiv (flatten.F P C O I T') := by
  have hwf' := apply_wf hwf he
  obtain ⟨-, hc, rfl⟩ := apply_removed.mp he
  rintro ⟨l0, k0⟩
  refine (flatten_parent_frame hPO hwf.nodup hwf'.nodup (apply_same he) l0 k0 fun _ n hg hp => ?_).symm
  -- A parent that leaves has no children.
  have : T.hasChild [P] k = true :=
    (hasChild_iff hwf.nodup [P] k).mpr ⟨[P, C], k0, n, hg, by simp, by simp, hp⟩
  rw [hc] at this; cases this

/-- The output row of a child of parent `k`, whose node is `pn`. -/
theorem get_row_of_child (hPO : P ≠ O) {T : Tree} (hnd : (T.map (·.1)).Nodup) {k c : Key}
    {n pn : Node} (hn : T.get ([P, C], c) = some n) (hp : n.parent = some k)
    (hpn : T.get ([P], k) = some pn) :
    (flatten.F P C O I T).get ([O], c) = some ⟨pn.parent, flattenProps I pn.props n.props⟩ := by
  rw [get_flatten_row hPO hnd, hn]
  simp [flatten.parentOf, hp, hpn]

theorem flatten_parent_modified (hPO : P ≠ O) {T T' : Tree} (hwf : T.WF) {k : Key} {x : String}
    {old new : Option Val} (he : T.apply (.modified [P] k x old new) = some T') :
    ∃ U, (flatten.F P C O I T).applyAll
        (if x ∈ I then (flatten.children P C T k).map fun c => .modified [O] c x old new else []) = some U ∧
      U.Equiv (flatten.F P C O I T') := by
  have hwf' := apply_wf hwf he
  obtain ⟨pn, hpn, h1, h2, rfl⟩ := apply_modified.mp he
  have hpn' : (T.update ([P], k) fun n => { n with props := n.props.set x new }).get ([P], k) =
      some { pn with props := pn.props.set x new } := by rw [get_update]; simp [hpn]
  -- Rows of other parents' children do not change.
  have hother : ∀ l0 k0, ¬(l0 = [O] ∧ k0 ∈ flatten.children P C T k) →
      (flatten.F P C O I (T.update ([P], k) fun n => { n with props := n.props.set x new })).get (l0, k0) =
        (flatten.F P C O I T).get (l0, k0) := by
    intro l0 k0 hnot
    exact flatten_parent_frame hPO hwf.nodup hwf'.nodup (apply_same he) l0 k0 fun hl n hg hp =>
      hnot ⟨hl, (mem_children hwf.nodup).mpr ⟨n, hg, hp⟩⟩
  by_cases hx : x ∈ I
  · simp only [hx, ↓reduceIte]
    obtain ⟨U', hU', hget⟩ := applyAll_modified_rows (O := O) (x := x) h2 (flatten.children P C T k)
      (flatten.F P C O I T) (nodup_children hwf.nodup k) fun c hc => by
        obtain ⟨n, hn, hp⟩ := (mem_children hwf.nodup).mp hc
        exact ⟨_, get_row_of_child hPO hwf.nodup hn hp hpn, by simp [flattenProps, hx, h1]⟩
    refine ⟨U', hU', ?_⟩
    rintro ⟨l0, k0⟩
    rw [hget]
    by_cases hin : l0 = [O] ∧ k0 ∈ flatten.children P C T k
    · obtain ⟨rfl, hc⟩ := hin
      obtain ⟨n, hn, hp⟩ := (mem_children hwf.nodup).mp hc
      have hn' : (T.update ([P], k) fun n => { n with props := n.props.set x new }).get ([P, C], k0) =
          some n := by rw [get_update]; simp [hn]
      simp only [hc, and_self, ↓reduceIte]
      rw [get_row_of_child hPO hwf.nodup hn hp hpn, get_row_of_child hPO hwf'.nodup hn' hp hpn']
      simp [flattenProps_set_mem hx]
    · simp only [hin, ↓reduceIte]
      exact (hother l0 k0 hin).symm
  · simp only [hx, ↓reduceIte]
    refine ⟨_, rfl, ?_⟩
    rintro ⟨l0, k0⟩
    by_cases hin : l0 = [O] ∧ k0 ∈ flatten.children P C T k
    · obtain ⟨rfl, hc⟩ := hin
      obtain ⟨n, hn, hp⟩ := (mem_children hwf.nodup).mp hc
      have hn' : (T.update ([P], k) fun n => { n with props := n.props.set x new }).get ([P, C], k0) =
          some n := by rw [get_update]; simp [hn]
      rw [get_row_of_child hPO hwf.nodup hn hp hpn, get_row_of_child hPO hwf'.nodup hn' hp hpn']
      simp [flattenProps_set_not_mem_parent hx]
    · exact (hother l0 k0 hin).symm

theorem flatten_parent_placed (hPO : P ≠ O) {T T' : Tree} (hwf : T.WF) {k a b : Key}
    (he : T.apply (.placed [P] k a b) = some T') :
    ∃ U, (flatten.F P C O I T).applyAll ((flatten.children P C T k).map fun c => .placed [O] c a b) = some U ∧
      U.Equiv (flatten.F P C O I T') := by
  have hwf' := apply_wf hwf he
  obtain ⟨pn, hpn, h1, h2, h3, rfl⟩ := apply_placed.mp he
  have hpn' : (T.update ([P], k) fun n => { n with parent := some b }).get ([P], k) =
      some { pn with parent := some b } := by rw [get_update]; simp [hpn]
  have hb : (flatten.F P C O I T).parentOk [O] (some b) = true := by
    simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h3 ⊢
    refine ⟨by simp, ?_⟩
    simpa [get_flatten_root hPO hwf.nodup] using h3.2
  obtain ⟨U', hU', hget⟩ := applyAll_placed_rows (O := O) h2 (flatten.children P C T k)
    (flatten.F P C O I T) (nodup_children hwf.nodup k) hb fun c hc => by
      obtain ⟨n, hn, hp⟩ := (mem_children hwf.nodup).mp hc
      exact ⟨_, get_row_of_child hPO hwf.nodup hn hp hpn, h1⟩
  refine ⟨U', hU', ?_⟩
  rintro ⟨l0, k0⟩
  rw [hget]
  by_cases hin : l0 = [O] ∧ k0 ∈ flatten.children P C T k
  · obtain ⟨rfl, hc⟩ := hin
    obtain ⟨n, hn, hp⟩ := (mem_children hwf.nodup).mp hc
    have hn' : (T.update ([P], k) fun n => { n with parent := some b }).get ([P, C], k0) = some n := by
      rw [get_update]; simp [hn]
    simp only [hc, and_self, ↓reduceIte]
    rw [get_row_of_child hPO hwf.nodup hn hp hpn, get_row_of_child hPO hwf'.nodup hn' hp hpn']
    simp
  · simp only [hin, ↓reduceIte]
    exact (flatten_parent_frame hPO hwf.nodup hwf'.nodup (apply_same he) l0 k0 fun hl n hg hp =>
      hin ⟨hl, (mem_children hwf.nodup).mpr ⟨n, hg, hp⟩⟩).symm

end JinagaSpec.Cascade
