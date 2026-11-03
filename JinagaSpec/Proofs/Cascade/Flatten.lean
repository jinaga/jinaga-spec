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

end JinagaSpec.Cascade
