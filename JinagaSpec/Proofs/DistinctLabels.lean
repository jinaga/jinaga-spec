import JinagaSpec.DistinctLabels
import JinagaSpec.Proofs.Children
import JinagaSpec.Proofs.Derivation
import JinagaSpec.Proofs.Hoist
import JinagaSpec.Candidates
import JinagaSpec.GivenConditions

/-!
# Renaming reused labels keeps results
-/
namespace JinagaSpec

/-! ## New names -/

theorem isReserved_iff (n : Name) : isReserved n = true ↔ ['_', '_'] <+: n.toList := by
  simp [isReserved, String.startsWith_string_iff]

/-- A name followed by a number is reserved only if the name is. -/
theorem isReserved_append_toString {n : Name} (h : isReserved n = false) (k : Nat) :
    isReserved (n ++ toString k) = false := by
  rw [Bool.eq_false_iff, ne_eq, isReserved_iff] at h ⊢
  have hd : '_' ∉ (toString k).toList := by
    simpa [Nat.toString_eq_repr, Nat.repr] using Nat.underscore_not_in_toDigits
  rw [String.toList_append]
  generalize n.toList = l at h; generalize (toString k).toList = d at hd
  rintro ⟨t, ht⟩
  match l, d with
  | _ :: _ :: _, _ => simp at ht h; exact h ht.1 ht.2.1
  | [_], _ :: _ => simp at ht hd; exact hd.1 ht.2.1
  | [], _ :: _ => simp at ht hd; exact hd.1 ht.1
  | _, [] => simp at ht; exact h ⟨t, ht⟩

theorem isReserved_freshBase (n : Name) : isReserved (freshBase n) = false := by
  unfold freshBase
  split
  · simp only
    split
    · simp [Bool.eq_false_iff, isReserved_iff]
    · rename_i h
      rw [Bool.eq_false_iff, ne_eq, isReserved_iff]
      rintro ⟨t, ht⟩
      have := List.head_dropWhile_not (· == '_') (l := n.toList)
      simp only [String.toList_ofList] at ht
      rw [← ht] at this
      simp at this
  · exact Bool.eq_false_iff.mpr ‹¬_›

/-- The candidates are distinct, so one of them is not taken. -/
theorem freshName_fresh (taken : List Name) (name : Name) : freshName taken name ∉ taken := by
  have hnd : (freshCandidates taken name).Nodup := by
    refine List.pairwise_map.2 (List.nodup_range.imp fun hne h => hne ?_)
    have := (String.append_right_inj _).mp h
    simp only [Nat.toString_eq_repr] at this
    exact Nat.add_right_cancel (Nat.repr_injective this)
  unfold freshName
  cases hf : (freshCandidates taken name).find? (!taken.contains ·) with
  | some c => simpa using List.find?_some hf
  | none =>
    have hall : ∀ c ∈ freshCandidates taken name, c ∈ taken := by
      intro c hc; simpa using List.find?_eq_none.mp hf c hc
    have := hnd.length_le_of_subset hall
    simp [freshCandidates] at this; omega

theorem isReserved_freshName (taken : List Name) (name : Name) :
    isReserved (freshName taken name) = false := by
  unfold freshName
  cases hf : (freshCandidates taken name).find? (!taken.contains ·) with
  | some c =>
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
    exact isReserved_append_toString (isReserved_freshBase name) _
  | none => exact isReserved_freshBase name

/-- `declared` is within `taken`: what lets a new name, which is not taken,
not be declared. -/
def RenameState.Inv (st : RenameState) : Prop := ∀ x ∈ st.declared, x ∈ st.taken

theorem RenameState.declare_fresh {st : RenameState} (h : st.Inv) (n : Name) :
    (st.declare n).2 ∉ st.declared := by
  unfold RenameState.declare
  split
  · exact fun hm => freshName_fresh _ _ (h _ hm)
  · exact fun hm => ‹¬_› (List.contains_iff_mem.mpr hm)

theorem RenameState.declare_ordinary (st : RenameState) {n : Name} (h : isReserved n = false) :
    isReserved (st.declare n).2 = false := by
  unfold RenameState.declare; split
  · exact isReserved_freshName _ _
  · exact h

/-! ## The state -/

theorem declaredConditions_cons (c : Condition) (cs : List Condition) :
    declaredConditions (c :: cs) = declaredConditions [c] ++ declaredConditions cs := by
  cases c <;> simp [declaredConditions]

theorem declaredConditions_append (a b : List Condition) :
    declaredConditions (a ++ b) = declaredConditions a ++ declaredConditions b := by
  induction a with
  | nil => simp [declaredConditions]
  | cons c a ih => rw [List.cons_append, declaredConditions_cons, ih, declaredConditions_cons c a,
      List.append_assoc]

mutual
  /-- A walk over matches declares, in `declared` and in `taken`, exactly the
  names its matches now declare, latest first. -/
  theorem renameMatches_state : ∀ (ρ : Name → Name) (st : RenameState) (ms : List Match),
      (renameMatches ρ st ms).1.declared = (declaredMatches (renameMatches ρ st ms).2.1).reverse ++ st.declared ∧
      (renameMatches ρ st ms).1.taken = (declaredMatches (renameMatches ρ st ms).2.1).reverse ++ st.taken
    | _, _, [] => by simp [renameMatches, declaredMatches]
    | ρ, st, .mk u cs :: rest => by
      have h1 := renameConditions_state (renameTo ρ u.name (st.declare u.name).2) ρ (st.declare u.name).1 cs
      have h2 := renameMatches_state (renameTo ρ u.name (st.declare u.name).2)
        (renameConditions (renameTo ρ u.name (st.declare u.name).2) ρ (st.declare u.name).1 cs).1 rest
      simp only [renameMatches, declaredMatches, List.reverse_cons, List.reverse_append,
        List.append_assoc, h1, h2] at *
      simp [RenameState.declare]

  theorem renameConditions_state : ∀ (inner outer : Name → Name) (st : RenameState) (cs : List Condition),
      (renameConditions inner outer st cs).1.declared =
        (declaredConditions (renameConditions inner outer st cs).2).reverse ++ st.declared ∧
      (renameConditions inner outer st cs).1.taken =
        (declaredConditions (renameConditions inner outer st cs).2).reverse ++ st.taken
    | _, _, _, [] => by simp [renameConditions, declaredConditions]
    | inner, outer, st, c :: cs => by
      have h1 := renameCondition_state inner outer st c
      have h2 := renameConditions_state inner outer (renameCondition inner outer st c).1 cs
      simp only [renameConditions] at *
      rw [declaredConditions_cons]
      simp [h1, h2]

  theorem renameCondition_state : ∀ (inner outer : Name → Name) (st : RenameState) (c : Condition),
      (renameCondition inner outer st c).1.declared =
        (declaredConditions [(renameCondition inner outer st c).2]).reverse ++ st.declared ∧
      (renameCondition inner outer st c).1.taken =
        (declaredConditions [(renameCondition inner outer st c).2]).reverse ++ st.taken
    | _, _, _, .path _ => by simp [renameCondition, declaredConditions]
    | inner, _, st, .existential _ ms => by
      have h := renameMatches_state inner st ms
      simp only [renameCondition, declaredConditions, List.append_nil]
      exact h
end

theorem RenameState.Inv.extend {st st' : RenameState} (h : st.Inv) (L : List Name)
    (hd : st'.declared = L ++ st.declared) (ht : st'.taken = L ++ st.taken) : st'.Inv := by
  intro x hx; rw [hd] at hx; rw [ht]
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ hx
  · exact List.mem_append_right _ (h x hx)

theorem renameMatches_inv {ρ : Name → Name} {st : RenameState} (h : st.Inv) (ms : List Match) :
    (renameMatches ρ st ms).1.Inv :=
  h.extend _ (renameMatches_state ρ st ms).1 (renameMatches_state ρ st ms).2

theorem renameConditions_inv {inner outer : Name → Name} {st : RenameState} (h : st.Inv) (cs : List Condition) :
    (renameConditions inner outer st cs).1.Inv :=
  h.extend _ (renameConditions_state inner outer st cs).1 (renameConditions_state inner outer st cs).2

theorem RenameState.declare_declared (st : RenameState) (n : Name) :
    (st.declare n).1.declared = (st.declare n).2 :: st.declared := rfl

theorem RenameState.declare_inv {st : RenameState} (h : st.Inv) (n : Name) : (st.declare n).1.Inv :=
  h.extend [(st.declare n).2] rfl rfl

/-! ## Each descendant declares each name once -/

mutual
  /-- The matches now declare each name once, and none declared before. -/
  theorem renameMatches_distinct : ∀ (ρ : Name → Name) (st : RenameState), st.Inv → ∀ (ms : List Match),
      (declaredMatches (renameMatches ρ st ms).2.1).Nodup ∧
        ∀ x ∈ declaredMatches (renameMatches ρ st ms).2.1, x ∉ st.declared
    | _, _, _, [] => by simp [renameMatches, declaredMatches]
    | ρ, st, h, .mk u cs :: rest => by
      have hn := st.declare_fresh h u.name
      have h1 := st.declare_inv h u.name
      have ⟨n1, d1⟩ := renameConditions_distinct (renameTo ρ u.name (st.declare u.name).2) ρ _ h1 cs
      have ⟨n2, d2⟩ := renameMatches_distinct (renameTo ρ u.name (st.declare u.name).2) _
        (renameConditions_inv (inner := renameTo ρ u.name (st.declare u.name).2) (outer := ρ) h1 cs) rest
      rw [(renameConditions_state _ _ _ cs).1, st.declare_declared] at d2
      rw [st.declare_declared] at d1
      simp only [renameMatches, declaredMatches]
      generalize (st.declare u.name).1 = st1 at *
      generalize (st.declare u.name).2 = n at *
      simp only [List.nodup_cons, List.nodup_append, List.mem_cons, List.mem_append, List.mem_reverse] at *
      grind

  theorem renameConditions_distinct : ∀ (inner outer : Name → Name) (st : RenameState), st.Inv →
      ∀ (cs : List Condition),
      (declaredConditions (renameConditions inner outer st cs).2).Nodup ∧
        ∀ x ∈ declaredConditions (renameConditions inner outer st cs).2, x ∉ st.declared
    | _, _, _, _, [] => by simp [renameConditions, declaredConditions]
    | inner, outer, st, h, c :: cs => by
      have ⟨n1, d1⟩ := renameCondition_distinct inner outer st h c
      have ⟨n2, d2⟩ := renameConditions_distinct inner outer _ (h.extend _
        (renameCondition_state inner outer st c).1 (renameCondition_state inner outer st c).2) cs
      rw [(renameCondition_state _ _ _ c).1] at d2
      simp only [renameConditions] at *
      rw [declaredConditions_cons]
      simp only [List.nodup_append, List.mem_append, List.mem_reverse] at *
      grind

  theorem renameCondition_distinct : ∀ (inner outer : Name → Name) (st : RenameState), st.Inv →
      ∀ (c : Condition),
      (declaredConditions [(renameCondition inner outer st c).2]).Nodup ∧
        ∀ x ∈ declaredConditions [(renameCondition inner outer st c).2], x ∉ st.declared
    | _, _, _, _, .path _ => by simp [renameCondition, declaredConditions]
    | inner, _, st, h, .existential _ ms => by
      simpa [renameCondition, declaredConditions] using renameMatches_distinct inner st h ms
end

/-! ## Scope -/

/-- Every label in scope `S` now has a name the descendant has declared. -/
def Hygienic (S : List Name) (ρ : Name → Name) (D : List Name) : Prop := ∀ x ∈ S, ρ x ∈ D

theorem Hygienic.mono {S : List Name} {ρ : Name → Name} {D D' : List Name} (h : Hygienic S ρ D)
    (hD : ∀ x ∈ D, x ∈ D') : Hygienic S ρ D' := fun x hx => hD _ (h x hx)

/-- Declaring a match's unknown, which is not in scope: its new name is not the
new name of anything in scope, and the scope inside it is the scope outside it
and that name. -/
theorem declare_scope {st : RenameState} (hi : st.Inv) {S : List Name} {ρ : Name → Name}
    (hh : Hygienic S ρ st.declared) {u : Name} (hu : u ∉ S) :
    (st.declare u).2 ∉ S.map ρ ∧
      (u :: S).map (renameTo ρ u (st.declare u).2) = (st.declare u).2 :: S.map ρ ∧
      (∀ x ∈ S, renameTo ρ u (st.declare u).2 x = ρ x) ∧
      Hygienic (u :: S) (renameTo ρ u (st.declare u).2) (st.declare u).1.declared := by
  have hS : ∀ x ∈ S, renameTo ρ u (st.declare u).2 x = ρ x := fun x hx => by
    simp [renameTo, show x ≠ u from fun h => hu (h ▸ hx)]
  refine ⟨fun hm => ?_, ?_, hS, ?_⟩
  · obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
    exact st.declare_fresh hi u (he ▸ hh x hx)
  · simp [renameTo, List.map_congr_left hS]
  · intro x hx
    rw [st.declare_declared]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp [renameTo]
    · rw [hS x hx]; exact List.mem_cons_of_mem _ (hh x hx)

/-- Growth of what is declared, read off `renameConditions_state`. -/
theorem renameConditions_declared_mono (inner outer : Name → Name) (st : RenameState) (cs : List Condition) :
    ∀ x ∈ st.declared, x ∈ (renameConditions inner outer st cs).1.declared := fun x hx => by
  rw [(renameConditions_state inner outer st cs).1]; exact List.mem_append_right _ hx

theorem renameMatches_declared_mono (ρ : Name → Name) (st : RenameState) (ms : List Match) :
    ∀ x ∈ st.declared, x ∈ (renameMatches ρ st ms).1.declared := fun x hx => by
  rw [(renameMatches_state ρ st ms).1]; exact List.mem_append_right _ hx

/-! ## Well-formedness -/

mutual
  /-- The renamed matches are scoped and well named in the renamed scope. -/
  theorem renameMatches_wellFormed : ∀ (ρ : Name → Name) (st : RenameState) (S : List Name) (ms : List Match),
      st.Inv → Hygienic S ρ st.declared → ScopedMatches S ms → WellNamedMatches S ms →
      ScopedMatches (S.map ρ) (renameMatches ρ st ms).2.1 ∧ WellNamedMatches (S.map ρ) (renameMatches ρ st ms).2.1
    | _, _, _, [], _, _, _, _ => by simp [renameMatches, ScopedMatches, WellNamedMatches]
    | ρ, st, S, .mk u cs :: rest, hi, hh, ⟨hsc, hsr⟩, ⟨hu, hres, hwc, hwr⟩ => by
      obtain ⟨hn, hmap, -, hh1⟩ := declare_scope hi hh hu
      have hi1 := st.declare_inv hi u.name
      have ⟨sc, wc⟩ := renameConditions_wellFormed (renameTo ρ u.name (st.declare u.name).2) ρ _ _ _ cs
        hi1 hh1 hsc hwc
      have ⟨sr, wr⟩ := renameMatches_wellFormed (renameTo ρ u.name (st.declare u.name).2) _ _ rest
        (renameConditions_inv (inner := renameTo ρ u.name (st.declare u.name).2) (outer := ρ) hi1 cs)
        (hh1.mono (renameConditions_declared_mono _ ρ _ cs)) hsr hwr
      rw [hmap] at sc wc sr wr
      exact ⟨⟨sc, sr⟩, hn, st.declare_ordinary hres, wc, wr⟩

  theorem renameConditions_wellFormed : ∀ (inner outer : Name → Name) (st : RenameState) (I O : List Name)
      (cs : List Condition), st.Inv → Hygienic I inner st.declared → ScopedConditions I O cs →
      WellNamedConditions I cs →
      ScopedConditions (I.map inner) (O.map outer) (renameConditions inner outer st cs).2 ∧
        WellNamedConditions (I.map inner) (renameConditions inner outer st cs).2
    | _, _, _, _, _, [], _, _, _, _ => by simp [renameConditions, ScopedConditions, WellNamedConditions]
    | inner, outer, st, I, O, c :: cs, hi, hh, ⟨h1, h2⟩, ⟨w1, w2⟩ => by
      have ⟨a1, b1⟩ := renameCondition_wellFormed inner outer st I O c hi hh h1 w1
      have hst := renameCondition_state inner outer st c
      have ⟨a2, b2⟩ := renameConditions_wellFormed inner outer _ I O cs (hi.extend _ hst.1 hst.2)
        (hh.mono fun x hx => by rw [hst.1]; exact List.mem_append_right _ hx) h2 w2
      exact ⟨⟨a1, a2⟩, b1, b2⟩

  theorem renameCondition_wellFormed : ∀ (inner outer : Name → Name) (st : RenameState) (I O : List Name)
      (c : Condition), st.Inv → Hygienic I inner st.declared → ScopedCondition I O c →
      WellNamedCondition I c →
      ScopedCondition (I.map inner) (O.map outer) (renameCondition inner outer st c).2 ∧
        WellNamedCondition (I.map inner) (renameCondition inner outer st c).2
    | _, _, _, _, _, .path _, _, _, h, _ => ⟨List.mem_map_of_mem h, trivial⟩
    | inner, _, st, I, _, .existential _ ms, hi, hh, h, w => renameMatches_wellFormed inner st I ms hi hh h w
end

/-- The scope after the matches, renamed, is the scope after the renamed
matches. -/
theorem renameMatches_scopeAfter : ∀ (ρ : Name → Name) (st : RenameState) (S : List Name) (ms : List Match),
    WellNamedMatches S ms →
    (scopeAfter S ms).map (renameMatches ρ st ms).2.2 = scopeAfter (S.map ρ) (renameMatches ρ st ms).2.1
  | _, _, _, [], _ => by simp [renameMatches, scopeAfter]
  | ρ, st, S, .mk u cs :: rest, ⟨hu, _, _, hwr⟩ => by
    have hS : ∀ x ∈ S, renameTo ρ u.name (st.declare u.name).2 x = ρ x := fun x hx => by
      simp [renameTo, show x ≠ u.name from fun h => hu (h ▸ hx)]
    have := renameMatches_scopeAfter (renameTo ρ u.name (st.declare u.name).2)
      (renameConditions (renameTo ρ u.name (st.declare u.name).2) ρ (st.declare u.name).1 cs).1 _ rest hwr
    simp only [renameMatches, scopeAfter, Match.unknown_mk] at this ⊢
    rw [this]; simp [renameTo, List.map_congr_left hS]

/-- After the matches, everything in scope still has a declared name. -/
theorem renameMatches_hygienic : ∀ (ρ : Name → Name) (st : RenameState) (S : List Name) (ms : List Match),
    Hygienic S ρ st.declared →
    Hygienic (scopeAfter S ms) (renameMatches ρ st ms).2.2 (renameMatches ρ st ms).1.declared
  | _, _, _, [], h => h
  | ρ, st, S, .mk u cs :: rest, h => by
    have h1 : Hygienic (u.name :: S) (renameTo ρ u.name (st.declare u.name).2) (st.declare u.name).1.declared := by
      intro x hx
      rw [st.declare_declared]
      by_cases hxu : x = u.name
      · simp [renameTo, hxu]
      · simp only [renameTo, hxu, ite_false]
        exact List.mem_cons_of_mem _ (h x ((List.mem_cons.mp hx).resolve_left hxu))
    exact renameMatches_hygienic _ _ _ rest (h1.mono (renameConditions_declared_mono _ ρ _ cs))

/-! ## Meaning -/

/-- Two lists related element by element. -/
inductive Pointwise {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Pointwise R [] []
  | cons {a b l l'} : R a b → Pointwise R l l' → Pointwise R (a :: l) (b :: l')

theorem Pointwise.length_eq {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : Pointwise R l l') : l.length = l'.length := by
  induction h <;> simp [*]

theorem Pointwise.append {α β : Type} {R : α → β → Prop} {l1 l2 : List α} {l1' l2' : List β}
    (h1 : Pointwise R l1 l1') (h2 : Pointwise R l2 l2') : Pointwise R (l1 ++ l2) (l1' ++ l2') := by
  induction h1 with
  | nil => exact h2
  | cons h _ ih => exact .cons h ih

theorem Pointwise.flatMap {α β γ : Type} {R : α → β → Prop} {l : List γ} {F : γ → List α} {G : γ → List β}
    (h : ∀ x ∈ l, Pointwise R (F x) (G x)) : Pointwise R (l.flatMap F) (l.flatMap G) := by
  induction l with
  | nil => exact .nil
  | cons x l ih =>
    simp only [List.flatMap_cons]
    exact (h x (List.mem_cons_self ..)).append (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem Pointwise.mono {α β : Type} {R R' : α → β → Prop} {l : List α} {l' : List β}
    (h : Pointwise R l l') (hR : ∀ a b, R a b → R' a b) : Pointwise R' l l' := by
  induction h with
  | nil => exact .nil
  | cons hab _ ih => exact .cons (hR _ _ hab) ih

theorem Pointwise.exists_of_mem_right {α β : Type} {R : α → β → Prop} {l : List α} {l' : List β}
    (h : Pointwise R l l') {b : β} (hb : b ∈ l') : ∃ a, R a b := by
  induction h with
  | nil => simp at hb
  | cons hab _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, hab⟩
    · exact ih hb

theorem Pointwise.map_eq {α β γ : Type} {R : α → β → Prop} {l : List α} {l' : List β} {f : α → γ} {g : β → γ}
    (h : Pointwise R l l') (hfg : ∀ a b, R a b → f a = g b) : l.map f = l'.map g := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hfg _ _ hab, ih]

/-- Each label in scope `S` is bound in `e1` to what its new name is bound to in
`e2`. -/
def Corresponds (S : List Name) (ρ : Name → Name) (e1 e2 : Env) : Prop := ∀ x ∈ S, e1 x = e2 (ρ x)

/-- Binding a match's unknown, and its new name, to the same fact. -/
theorem Corresponds.bind {S : List Name} {ρ : Name → Name} {e1 e2 : Env} (h : Corresponds S ρ e1 e2)
    {u n : Name} (hu : u ∉ S) (hn : n ∉ S.map ρ) (f : FactId) :
    Corresponds (u :: S) (renameTo ρ u n) (e1.bind u f) (e2.bind n f) ∧
      Corresponds S ρ (e1.bind u f) (e2.bind n f) := by
  have hS : ∀ x ∈ S, (e1.bind u f) x = (e2.bind n f) (ρ x) := fun x hx => by
    have hxu : x ≠ u := fun h => hu (h ▸ hx)
    have hxn : ρ x ≠ n := fun h => hn (h ▸ List.mem_map_of_mem hx)
    simp [Env.bind, hxu, hxn, h x hx]
  refine ⟨fun x hx => ?_, hS⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · simp [Env.bind, renameTo]
  · rw [hS x hx]; simp [renameTo, show x ≠ u from fun h => hu (h ▸ hx)]

mutual
  /-- The renamed matches have the solutions of the matches, each binding every
  label in scope after them as its new name is bound. -/
  theorem renameMatches_eval (g : Graph) : ∀ (ρ : Name → Name) (st : RenameState) (S : List Name)
      (ms : List Match) (e1 e2 : Env), st.Inv → Hygienic S ρ st.declared → ScopedMatches S ms →
      WellNamedMatches S ms → Corresponds S ρ e1 e2 →
      Pointwise (Corresponds (scopeAfter S ms) (renameMatches ρ st ms).2.2)
        (evalMatches g e1 ms) (evalMatches g e2 (renameMatches ρ st ms).2.1)
    | _, _, _, [], _, _, _, _, _, _, h => .cons h .nil
    | ρ, st, S, .mk u cs :: rest, e1, e2, hi, hh, ⟨hsc, hsr⟩, ⟨hu, _, hwc, hwr⟩, hc => by
      obtain ⟨hn, -, -, hh1⟩ := declare_scope hi hh hu
      have hi1 := st.declare_inv hi u.name
      simp only [renameMatches, evalMatches, scopeAfter, Match.unknown_mk]
      refine Pointwise.flatMap fun f _ => ?_
      have ⟨hc1, hc2⟩ := hc.bind hu hn f.id
      rw [renameConditions_eval g _ ρ _ _ _ cs _ _ u.name (st.declare u.name).2 hi1 hh1 hsc hwc hc1 hc2
        (by simp [Env.bind])]
      split
      · exact renameMatches_eval g _ _ _ rest _ _
          (renameConditions_inv (inner := renameTo ρ u.name (st.declare u.name).2) (outer := ρ) hi1 cs)
          (hh1.mono (renameConditions_declared_mono _ ρ _ cs)) hsr hwr hc1
      · exact .nil

  theorem renameConditions_eval (g : Graph) : ∀ (inner outer : Name → Name) (st : RenameState)
      (I O : List Name) (cs : List Condition) (e1 e2 : Env) (u n : Name), st.Inv →
      Hygienic I inner st.declared → ScopedConditions I O cs → WellNamedConditions I cs →
      Corresponds I inner e1 e2 → Corresponds O outer e1 e2 → e1 u = e2 n →
      allHold g e2 n (renameConditions inner outer st cs).2 = allHold g e1 u cs
    | _, _, _, _, _, [], _, _, _, _, _, _, _, _, _, _, _ => rfl
    | inner, outer, st, I, O, c :: cs, e1, e2, u, n, hi, hh, ⟨h1, h2⟩, ⟨w1, w2⟩, hci, hco, hu => by
      have hst := renameCondition_state inner outer st c
      simp only [renameConditions, allHold]
      rw [renameCondition_eval g inner outer st I O c e1 e2 u n hi hh h1 w1 hci hco hu,
        renameConditions_eval g inner outer _ I O cs e1 e2 u n (hi.extend _ hst.1 hst.2)
          (hh.mono fun x hx => by rw [hst.1]; exact List.mem_append_right _ hx) h2 w2 hci hco hu]

  theorem renameCondition_eval (g : Graph) : ∀ (inner outer : Name → Name) (st : RenameState)
      (I O : List Name) (c : Condition) (e1 e2 : Env) (u n : Name), st.Inv →
      Hygienic I inner st.declared → ScopedCondition I O c → WellNamedCondition I c →
      Corresponds I inner e1 e2 → Corresponds O outer e1 e2 → e1 u = e2 n →
      holds g e2 n (renameCondition inner outer st c).2 = holds g e1 u c
    | _, _, _, _, _, .path pc, _, _, _, _, _, _, h, _, _, hco, hu => by
      simp [renameCondition, holds, PathCondition.holds, hu, ← hco _ h]
    | inner, _, st, I, _, .existential _ ms, e1, e2, _, _, hi, hh, h, w, hci, _, _ => by
      simp only [renameCondition, holds]
      have he : ∀ l : List Env, l.isEmpty = (l.length == 0) := fun l => by cases l <;> rfl
      rw [he, he, (renameMatches_eval g inner st I ms e1 e2 hi hh h w hci).length_eq]
end

/-! ## Projections -/

/-- A child specification renamed from `D` and `T`, as `renameComponent` renames
it. -/
def renameChild (ρ : Name → Name) (D T : List Name) (c : List Match × Projection) : List Match × Projection :=
  ((renameMatches ρ { taken := T, declared := D } c.1).2.1,
    (renameProjection (renameMatches ρ { taken := T, declared := D } c.1).2.2
      (renameMatches ρ { taken := T, declared := D } c.1).1.declared
      (renameMatches ρ { taken := T, declared := D } c.1).1.taken c.2).2)

mutual
  /-- Renaming a projection only adds to `taken`. -/
  theorem renameProjection_taken : ∀ (ρ : Name → Name) (D T : List Name) (p : Projection),
      ∀ x ∈ T, x ∈ (renameProjection ρ D T p).1
    | _, _, _, .fact _ => fun _ h => h
    | ρ, D, T, .composite cs => renameComponents_taken ρ D T cs

  theorem renameComponents_taken : ∀ (ρ : Name → Name) (D T : List Name) (cs : List Component),
      ∀ x ∈ T, x ∈ (renameComponents ρ D T cs).1
    | _, _, _, [] => fun _ h => h
    | ρ, D, T, c :: cs => fun x h =>
      renameComponents_taken ρ D _ cs x (renameComponent_taken ρ D T c x h)

  theorem renameComponent_taken : ∀ (ρ : Name → Name) (D T : List Name) (c : Component),
      ∀ x ∈ T, x ∈ (renameComponent ρ D T c).1
    | _, _, _, .fact .. => fun _ h => h
    | ρ, D, T, .specification _ ms p => fun x h => by
      simp only [renameComponent]
      refine renameProjection_taken _ _ _ p x ?_
      rw [(renameMatches_state ρ _ ms).2]; exact List.mem_append_right _ h
end

theorem renameProjection_labels (ρ : Name → Name) (D T : List Name) :
    ∀ p : Projection, (renameProjection ρ D T p).2.labels = p.labels.map ρ
  | .fact _ => rfl
  | .composite cs => by
    simp only [renameProjection, Projection.labels]
    induction cs generalizing T with
    | nil => rfl
    | cons c cs ih =>
      simp only [renameComponents, List.flatMap_cons, List.map_append, ih]
      cases c <;> simp [renameComponent, Component.labels]

/-- The renamed projection's child specifications are its child specifications,
each renamed from what its parent declared and from at least what was taken. -/
theorem renameProjection_children (ρ : Name → Name) (D T : List Name) :
    ∀ p : Projection, Pointwise (fun c c' => c ∈ p.children ∧ ∃ T', (∀ x ∈ T, x ∈ T') ∧ c' = renameChild ρ D T' c)
      p.children (renameProjection ρ D T p).2.children
  | .fact _ => .nil
  | .composite cs => by
    simp only [renameProjection]
    induction cs generalizing T with
    | nil => exact .nil
    | cons c cs ih =>
      have ih' := ih (renameComponent ρ D T c).1
      cases c with
      | fact =>
        simpa [renameComponents, renameComponent, Projection.children] using
          ih'.mono fun a b ⟨ha, T', hT, he⟩ =>
            ⟨by simp_all [Projection.children], T', fun x hx => hT x hx, he⟩
      | specification n ms q =>
        simp only [renameComponents, renameComponent, Projection.children, List.filterMap_cons] at ih' ⊢
        refine .cons ⟨List.mem_cons_self .., T, fun _ h => h, rfl⟩ (ih'.mono fun a b ⟨ha, T', hT, he⟩ =>
          ⟨List.mem_cons_of_mem _ ha, T', fun x hx => hT x (renameProjection_taken _ _ _ q x ?_), he⟩)
        rw [(renameMatches_state ρ _ ms).2]; exact List.mem_append_right _ hx

/-- Every path from `p` is scoped and well named from `S`, and projects only
labels in scope at its end: what `WellFormed` asks of each descendant, from the
matches before `p`. -/
def PathsWellFormed (S : List Name) (p : Projection) : Prop :=
  ∀ x ∈ p.paths, ScopedMatches S x.1 ∧ WellNamedMatches S x.1 ∧ ∀ l ∈ x.2.labels, l ∈ scopeAfter S x.1

theorem scopeAfter_append (S : List Name) (a b : List Match) :
    scopeAfter S (a ++ b) = scopeAfter (scopeAfter S a) b := by
  induction a generalizing S with
  | nil => rfl
  | cons m a ih => exact ih _

theorem PathsWellFormed.labels {S : List Name} {p : Projection} (h : PathsWellFormed S p) :
    ∀ l ∈ p.labels, l ∈ S :=
  (h _ (mem_paths.mpr (Or.inl rfl))).2.2

theorem PathsWellFormed.child {S : List Name} {p : Projection} (h : PathsWellFormed S p)
    {c : List Match × Projection} (hc : c ∈ p.children) :
    ScopedMatches S c.1 ∧ WellNamedMatches S c.1 ∧ PathsWellFormed (scopeAfter S c.1) c.2 := by
  have hp : ∀ y ∈ c.2.paths, (c.1 ++ y.1, y.2) ∈ p.paths := fun y hy =>
    mem_paths.mpr (Or.inr ⟨c, hc, y, hy, rfl⟩)
  have h0 := h _ (hp _ (mem_paths.mpr (Or.inl rfl)))
  simp only [List.append_nil] at h0
  refine ⟨h0.1, h0.2.1, fun y hy => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h _ (hp y hy)
  rw [scopedMatches_append] at h1; rw [wellNamedMatches_append] at h2; rw [scopeAfter_append] at h3
  exact ⟨h1.2, h2.2, h3⟩

theorem resultsAt_eq (g : Graph) (p : Projection) (σ : Env) :
    p.resultsAt g σ = .mk (p.labels.map σ) (p.children.map fun c => (evalMatches g σ c.1).map (c.2.resultsAt g)) := by
  rw [Projection.resultsAt]; congr 1
  exact List.map_attach_eq_pmap .. ▸ by simp

/-- **Renaming keeps results, at every depth.** -/
theorem renameProjection_resultsAt (g : Graph) : ∀ (p : Projection) (ρ : Name → Name) (D T S : List Name)
    (σ1 σ2 : Env), (∀ x ∈ D, x ∈ T) → Hygienic S ρ D → PathsWellFormed S p → Corresponds S ρ σ1 σ2 →
    p.resultsAt g σ1 = (renameProjection ρ D T p).2.resultsAt g σ2
  | p, ρ, D, T, S, σ1, σ2, hi, hh, hw, hc => by
    rw [resultsAt_eq, resultsAt_eq, renameProjection_labels, List.map_map]
    congr 1
    · exact List.map_congr_left fun l hl => hc l (hw.labels l hl)
    · refine (renameProjection_children ρ D T p).map_eq fun c c' ⟨hcp, T', hT, he⟩ => ?_
      subst he
      have hi' : RenameState.Inv { taken := T', declared := D } := fun x hx => hT x (hi x hx)
      obtain ⟨hs, hwn, hw'⟩ := hw.child hcp
      refine (renameMatches_eval g ρ _ S c.1 σ1 σ2 hi' hh hs hwn hc).map_eq fun τ1 τ2 hτ =>
        renameProjection_resultsAt g c.2 _ _ _ _ τ1 τ2 (renameMatches_inv hi' c.1)
          (renameMatches_hygienic ρ _ S c.1 hh) hw' hτ
termination_by p => sizeOf p
decreasing_by exact Projection.sizeOf_children hcp

/-- Every path of the renamed projection is well formed from the renamed
scope. -/
theorem renameProjection_wellFormed : ∀ (p : Projection) (ρ : Name → Name) (D T S : List Name),
    (∀ x ∈ D, x ∈ T) → Hygienic S ρ D → PathsWellFormed S p →
    PathsWellFormed (S.map ρ) (renameProjection ρ D T p).2
  | p, ρ, D, T, S, hi, hh, hw => fun x hx => by
    rcases mem_paths.mp hx with rfl | ⟨c', hc', y, hy, rfl⟩
    · refine ⟨trivial, trivial, fun l hl => ?_⟩
      rw [renameProjection_labels] at hl
      obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl
      exact List.mem_map_of_mem (hw.labels l0 hl0)
    · obtain ⟨c, hc, T', hT, rfl⟩ := (renameProjection_children ρ D T p).exists_of_mem_right hc'
      have hi' : RenameState.Inv { taken := T', declared := D } := fun x hx => hT x (hi x hx)
      obtain ⟨hs, hwn, hw'⟩ := hw.child hc
      obtain ⟨hs', hwn'⟩ := renameMatches_wellFormed ρ _ S c.1 hi' hh hs hwn
      have hy' := renameProjection_wellFormed c.2 _ _ _ _ (renameMatches_inv hi' c.1)
        (renameMatches_hygienic ρ _ S c.1 hh) hw' y hy
      rw [renameMatches_scopeAfter ρ _ S c.1 hwn] at hy'
      refine ⟨scopedMatches_append.mpr ⟨hs', hy'.1⟩, wellNamedMatches_append.mpr ⟨hwn', hy'.2.1⟩, ?_⟩
      simpa [renameChild, scopeAfter_append] using hy'.2.2
termination_by p => sizeOf p
decreasing_by exact Projection.sizeOf_children hc

/-- Every path of the renamed projection declares each name once, none of them
one declared before it. -/
theorem renameProjection_distinct : ∀ (p : Projection) (ρ : Name → Name) (D T L : List Name),
    (∀ x ∈ D, x ∈ T) → L.Nodup → (∀ x ∈ L, x ∈ D) →
    ∀ x ∈ (renameProjection ρ D T p).2.paths, (L ++ declaredMatches x.1).Nodup
  | p, ρ, D, T, L, hi, hL, hLD => fun x hx => by
    rcases mem_paths.mp hx with rfl | ⟨c', hc', y, hy, rfl⟩
    · simpa [declaredMatches] using hL
    · obtain ⟨c, hc, T', hT, rfl⟩ := (renameProjection_children ρ D T p).exists_of_mem_right hc'
      have hi' : RenameState.Inv { taken := T', declared := D } := fun x hx => hT x (hi x hx)
      obtain ⟨hn, hd⟩ := renameMatches_distinct ρ _ hi' c.1
      have hst := (renameMatches_state ρ { taken := T', declared := D } c.1).1
      have := renameProjection_distinct c.2 _ _ _ (L ++ declaredMatches (renameMatches ρ _ c.1).2.1)
        (renameMatches_inv hi' c.1)
        (List.nodup_append.mpr ⟨hL, hn, fun a ha b hb hab => hd b hb (hab ▸ hLD a ha)⟩)
        (fun z hz => by
          rw [hst]
          rcases List.mem_append.mp hz with hz | hz
          · exact List.mem_append_right _ (hLD z hz)
          · exact List.mem_append_left _ (List.mem_reverse.mpr hz)) y hy
      simpa [renameChild, declared_append] using this
termination_by p => sizeOf p
decreasing_by exact Projection.sizeOf_children hc

/-! ## The specification -/

/-- What `withDistinctLabels` computes, by name. -/
theorem withDistinctLabels_eq (s : Specification) :
    withDistinctLabels s =
      let r := renameMatches id { taken := s.labelsOf, declared := s.given.map (·.name) } s.matchList
      { given := s.given, matchList := r.2.1, projection := (renameProjection r.2.2 r.1.declared r.1.taken s.projection).2 } :=
  rfl

/-- `WellFormed` of every descendant, from the matches and from the paths of
the projection. -/
theorem descendants_wellFormed_iff (s : Specification) :
    (∀ d ∈ s.descendants, WellFormed d) ↔
      (∀ g ∈ s.given, isReserved g.name = false) ∧ ScopedMatches (s.given.map (·.name)) s.matchList ∧
        WellNamedMatches (s.given.map (·.name)) s.matchList ∧
        PathsWellFormed (scopeAfter (s.given.map (·.name)) s.matchList) s.projection := by
  have hwf : ∀ x : List Match × Projection,
      WellFormed { given := s.given, matchList := s.matchList ++ x.1, projection := x.2 } ↔
        (∀ g ∈ s.given, isReserved g.name = false) ∧ ScopedMatches (s.given.map (·.name)) s.matchList ∧
          WellNamedMatches (s.given.map (·.name)) s.matchList ∧
          ScopedMatches (scopeAfter (s.given.map (·.name)) s.matchList) x.1 ∧
          WellNamedMatches (scopeAfter (s.given.map (·.name)) s.matchList) x.1 ∧
          ∀ l ∈ x.2.labels, l ∈ scopeAfter (scopeAfter (s.given.map (·.name)) s.matchList) x.1 := fun x => by
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      rw [scopedMatches_append] at h2; rw [wellNamedMatches_append] at h3
      exact ⟨h1, h2.1, h3.1, h2.2, h3.2, fun l hl => by
        rw [← scopeAfter_append, mem_scopeAfter]; exact (h4 l hl).symm⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      exact ⟨h1, scopedMatches_append.mpr ⟨h2, h4⟩, wellNamedMatches_append.mpr ⟨h3, h5⟩, fun l hl => by
        have := h6 l hl; rw [← scopeAfter_append, mem_scopeAfter] at this; exact this.symm⟩
  simp only [Specification.descendants, List.forall_mem_map, hwf, PathsWellFormed]
  have h0 : ([], s.projection) ∈ s.projection.paths := mem_paths.mpr (Or.inl rfl)
  exact ⟨fun h => ⟨(h _ h0).1, (h _ h0).2.1, (h _ h0).2.2.1, fun x hx => (h x hx).2.2.2⟩,
    fun ⟨h1, h2, h3, h4⟩ x hx => ⟨h1, h2, h3, h4 x hx⟩⟩

/-- The renamed scope from the givens is the givens. -/
private theorem hygienic_givens (s : Specification) :
    Hygienic (s.given.map (·.name)) id (s.given.map (·.name)) := fun _ h => h

private theorem inv_labelsOf (s : Specification) :
    RenameState.Inv { taken := s.labelsOf, declared := s.given.map (·.name) } :=
  fun _ h => List.mem_append_left _ h

/-- **Renaming keeps a specification well formed.** -/
theorem withDistinctLabels_wellFormed {s : Specification} (h : WellFormed s) :
    WellFormed (withDistinctLabels s) := by
  rw [withDistinctLabels_eq]
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ⟨s2, s3⟩ := renameMatches_wellFormed id _ _ s.matchList (inv_labelsOf s) (hygienic_givens s) h2 h3
  have hsa := renameMatches_scopeAfter id { taken := s.labelsOf, declared := s.given.map (·.name) } _ _ h3
  rw [List.map_id] at s2 s3 hsa
  refine ⟨h1, s2, s3, fun l hl => ?_⟩
  rw [renameProjection_labels] at hl
  obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl
  have : l0 ∈ scopeAfter (s.given.map (·.name)) s.matchList := mem_scopeAfter.mpr (h4 l0 hl0).symm
  have := hsa ▸ List.mem_map_of_mem (f := (renameMatches id _ s.matchList).2.2) this
  exact (mem_scopeAfter.mp this).symm

/-- **Renaming keeps every descendant well formed.** -/
theorem withDistinctLabels_descendants_wellFormed {s : Specification} (h : ∀ d ∈ s.descendants, WellFormed d) :
    ∀ d ∈ (withDistinctLabels s).descendants, WellFormed d := by
  rw [descendants_wellFormed_iff] at h ⊢
  rw [withDistinctLabels_eq]
  obtain ⟨h1, h2, h3, h4⟩ := h
  have ⟨s2, s3⟩ := renameMatches_wellFormed id _ _ s.matchList (inv_labelsOf s) (hygienic_givens s) h2 h3
  have hsa := renameMatches_scopeAfter id { taken := s.labelsOf, declared := s.given.map (·.name) } _ _ h3
  rw [List.map_id] at s2 s3 hsa
  refine ⟨h1, s2, s3, hsa ▸ renameProjection_wellFormed _ _ _ _ _ (renameMatches_inv (inv_labelsOf s) _)
    (renameMatches_hygienic _ _ _ _ (hygienic_givens s)) h4⟩

/-- **Renaming establishes `DistinctLabels`** of every descendant, whatever the
specification. -/
theorem withDistinctLabels_distinct (s : Specification) :
    ∀ d ∈ (withDistinctLabels s).descendants, DistinctLabels d := by
  rw [withDistinctLabels_eq]
  simp only [Specification.descendants, List.forall_mem_map, DistinctLabels, declared_append]
  have hi := inv_labelsOf s
  obtain ⟨hn, -⟩ := renameMatches_distinct id _ hi s.matchList
  have hst := (renameMatches_state id { taken := s.labelsOf, declared := s.given.map (·.name) } s.matchList).1
  exact renameProjection_distinct _ _ _ _ _ (renameMatches_inv hi _) hn fun z hz => by
    rw [hst]; exact List.mem_append_left _ (List.mem_reverse.mpr hz)

/-- **Renaming keeps results** of the projection's rows. -/
theorem withDistinctLabels_evaluate {s : Specification} (h : WellFormed s) (g : Graph) (env : Env) :
    (withDistinctLabels s).evaluate g env = s.evaluate g env := by
  rw [withDistinctLabels_eq]
  obtain ⟨-, h2, h3, h4⟩ := h
  simp only [Specification.evaluate, renameProjection_labels, List.map_map]
  exact ((renameMatches_eval g id _ _ s.matchList env env (inv_labelsOf s) (hygienic_givens s) h2 h3
    fun _ _ => rfl).map_eq fun e1 e2 hc => List.map_congr_left fun l hl =>
      hc l (mem_scopeAfter.mpr (h4 l hl).symm)).symm

/-- **Renaming keeps what a replica reads**, child specifications' results
included, at every depth. -/
theorem withDistinctLabels_readsOf {s : Specification} (h : ∀ d ∈ s.descendants, WellFormed d)
    (g : Graph) (env : Env) : (withDistinctLabels s).readsOf g env = s.readsOf g env := by
  rw [descendants_wellFormed_iff] at h
  obtain ⟨-, h2, h3, h4⟩ := h
  rw [withDistinctLabels_eq]
  simp only [Specification.readsOf, Projection.resultsOf]
  split
  · exact ((renameMatches_eval g id _ _ s.matchList env env (inv_labelsOf s) (hygienic_givens s) h2 h3
      fun _ _ => rfl).map_eq fun e1 e2 hc =>
        renameProjection_resultsAt g _ _ _ _ _ e1 e2 (renameMatches_inv (inv_labelsOf s) _)
          (renameMatches_hygienic _ _ _ _ (hygienic_givens s)) h4 hc).symm
  · rfl

theorem withDistinctLabels_reads {s : Specification} (h : ∀ d ∈ s.descendants, WellFormed d)
    (g : Graph) (env : Env) (r : Result) : (withDistinctLabels s).Reads g env r ↔ s.Reads g env r := by
  rw [reads_iff_readsOf, reads_iff_readsOf, withDistinctLabels_readsOf h]

/-! ## Rooted matches -/

theorem rootedMatches_append {a b : List Match} : RootedMatches (a ++ b) ↔ RootedMatches a ∧ RootedMatches b := by
  induction a with
  | nil => simp [RootedMatches]
  | cons m a ih => obtain ⟨u, cs⟩ := m; simp only [List.cons_append, RootedMatches, ih, and_assoc]

mutual
  theorem renameMatches_rooted : ∀ (ρ : Name → Name) (st : RenameState) (ms : List Match),
      RootedMatches ms → RootedMatches (renameMatches ρ st ms).2.1
    | _, _, [], _ => by simp [renameMatches, RootedMatches]
    | ρ, st, .mk u cs :: rest, h => by
      simp only [RootedMatches] at h
      obtain ⟨hc, hcs, hr⟩ := h
      have ⟨h1, h2⟩ := renameConditions_rooted (renameTo ρ u.name (st.declare u.name).2) ρ
        (st.declare u.name).1 cs hcs
      simp only [renameMatches, RootedMatches]
      exact ⟨h2 hc, h1, renameMatches_rooted _ _ rest hr⟩

  theorem renameConditions_rooted : ∀ (inner outer : Name → Name) (st : RenameState) (cs : List Condition),
      RootedConditions cs → RootedConditions (renameConditions inner outer st cs).2 ∧
        ((∃ c ∈ cs, c.isPath = true) → ∃ c ∈ (renameConditions inner outer st cs).2, c.isPath = true)
    | _, _, _, [], _ => by simp [renameConditions, RootedConditions]
    | inner, outer, st, .path pc :: cs, h => by
      simp only [RootedConditions] at h
      have ⟨h1, _⟩ := renameConditions_rooted inner outer st cs h
      simp only [renameConditions, renameCondition, RootedConditions]
      exact ⟨h1, fun _ => ⟨_, List.mem_cons_self .., rfl⟩⟩
    | inner, outer, st, .existential e ms :: cs, h => by
      simp only [RootedConditions] at h
      have ⟨h1, h2⟩ := renameConditions_rooted inner outer (renameMatches inner st ms).1 cs h.2
      simp only [renameConditions, renameCondition, RootedConditions]
      refine ⟨⟨renameMatches_rooted inner st ms h.1, h1⟩, fun ⟨c, hc, hp⟩ => ?_⟩
      rcases List.mem_cons.mp hc with rfl | hc
      · simp [Condition.isPath] at hp
      · obtain ⟨c', hc', hp'⟩ := h2 ⟨c, hc, hp⟩
        exact ⟨c', List.mem_cons_of_mem _ hc', hp'⟩
end

theorem renameProjection_rooted : ∀ (p : Projection) (ρ : Name → Name) (D T : List Name),
    (∀ x ∈ p.paths, RootedMatches x.1) → ∀ x ∈ (renameProjection ρ D T p).2.paths, RootedMatches x.1
  | p, ρ, D, T, h => fun x hx => by
    rcases mem_paths.mp hx with rfl | ⟨c', hc', y, hy, rfl⟩
    · simp [RootedMatches]
    · obtain ⟨c, hc, T', -, rfl⟩ := (renameProjection_children ρ D T p).exists_of_mem_right hc'
      have hp : ∀ y ∈ c.2.paths, RootedMatches c.1 ∧ RootedMatches y.1 := fun y hy =>
        rootedMatches_append.mp (h _ (mem_paths.mpr (Or.inr ⟨c, hc, y, hy, rfl⟩)))
      exact rootedMatches_append.mpr ⟨renameMatches_rooted _ _ _ (hp _ (mem_paths.mpr (Or.inl rfl))).1,
        renameProjection_rooted c.2 _ _ _ (fun y hy => (hp y hy).2) y hy⟩
termination_by p => sizeOf p
decreasing_by exact Projection.sizeOf_children hc

/-- **Renaming keeps every match rooted.** -/
theorem withDistinctLabels_rooted {s : Specification} (h : ∀ d ∈ s.descendants, RootedMatches d.matchList) :
    ∀ d ∈ (withDistinctLabels s).descendants, RootedMatches d.matchList := by
  simp only [Specification.descendants, List.forall_mem_map, rootedMatches_append] at h ⊢
  rw [withDistinctLabels_eq]
  have h0 := h _ (mem_paths.mpr (Or.inl rfl))
  exact fun x hx => ⟨renameMatches_rooted _ _ _ h0.1,
    renameProjection_rooted _ _ _ _ (fun y hy => (h y hy).2) x hx⟩

/-! ## Nothing to rename -/

theorem renameTo_self (u : Name) : renameTo id u u = id := by
  funext n; by_cases h : n = u <;> simp [renameTo, h]

mutual
  /-- Matches that declare each name once, none already declared, are not
  renamed. -/
  theorem renameMatches_self : ∀ (st : RenameState) (ms : List Match), (declaredMatches ms).Nodup →
      (∀ x ∈ declaredMatches ms, x ∉ st.declared) →
      (renameMatches id st ms).2.1 = ms ∧ (renameMatches id st ms).2.2 = id
    | _, [], _, _ => ⟨rfl, rfl⟩
    | st, .mk u cs :: rest, hn, hd => by
      simp only [declaredMatches, List.nodup_cons, List.nodup_append, List.mem_cons, List.mem_append] at hn hd
      have hu : (st.declare u.name).2 = u.name := by
        simp [RenameState.declare, hd u.name (Or.inl rfl)]
      have hcs := renameConditions_self (st.declare u.name).1 cs hn.2.1 fun x hx hm => by
        rw [st.declare_declared, hu] at hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hn.1 (Or.inl hx)
        · exact hd x (Or.inr (Or.inl hx)) hm
      have hst := (renameConditions_state id id (st.declare u.name).1 cs).1
      rw [hcs, st.declare_declared, hu] at hst
      have hr := renameMatches_self (renameConditions id id (st.declare u.name).1 cs).1 rest hn.2.2.1
        fun x hx hm => by
          rw [hst] at hm
          rcases List.mem_append.mp hm with hm | hm
          · exact hn.2.2.2 x (List.mem_reverse.mp hm) x hx rfl
          · rcases List.mem_cons.mp hm with rfl | hm
            · exact hn.1 (Or.inr hx)
            · exact hd x (Or.inr (Or.inr hx)) hm
      simp only [renameMatches, hu, renameTo_self] at hcs hr ⊢
      rw [hcs, hr.1, hr.2]; exact ⟨rfl, rfl⟩

  theorem renameConditions_self : ∀ (st : RenameState) (cs : List Condition), (declaredConditions cs).Nodup →
      (∀ x ∈ declaredConditions cs, x ∉ st.declared) → (renameConditions id id st cs).2 = cs
    | _, [], _, _ => rfl
    | st, .path pc :: cs, hn, hd => by
      simp only [renameConditions, renameCondition, declaredConditions] at hn hd ⊢
      rw [renameConditions_self st cs hn hd]; rfl
    | st, .existential e ms :: cs, hn, hd => by
      simp only [declaredConditions, List.nodup_append, List.mem_append] at hn hd
      have hm := renameMatches_self st ms hn.1 fun x hx => hd x (Or.inl hx)
      have hst := (renameMatches_state id st ms).1
      rw [hm.1] at hst
      simp only [renameConditions, renameCondition]
      rw [hm.1, renameConditions_self _ cs hn.2.1 fun x hx hm' => by
        rw [hst] at hm'
        rcases List.mem_append.mp hm' with hm' | hm'
        · exact hn.2.2 x (List.mem_reverse.mp hm') x hx rfl
        · exact hd x (Or.inr hx) hm']
end

/-- Every path from `p` declares each name once, none of them in `D`. -/
def FreshPaths (D : List Name) (p : Projection) : Prop :=
  ∀ x ∈ p.paths, (declaredMatches x.1).Nodup ∧ ∀ y ∈ declaredMatches x.1, y ∉ D

theorem children_cons (c : Component) (cs : List Component) :
    (Projection.composite (c :: cs)).children =
      (Projection.composite [c]).children ++ (Projection.composite cs).children := by
  cases c <;> simp [Projection.children]

mutual
  /-- A projection none of whose paths needs a new name is not renamed. -/
  theorem renameProjection_self : ∀ (p : Projection) (D T : List Name), FreshPaths D p →
      (renameProjection id D T p).2 = p
    | .fact _, _, _, _ => rfl
    | .composite cs, D, T, h => by
      simp only [renameProjection]
      rw [renameComponents_self cs D T fun c hc y hy =>
        h _ (mem_paths.mpr (Or.inr ⟨c, hc, y, hy, rfl⟩))]

  theorem renameComponents_self : ∀ (cs : List Component) (D T : List Name),
      (∀ c ∈ (Projection.composite cs).children, ∀ y ∈ c.2.paths,
        (declaredMatches (c.1 ++ y.1)).Nodup ∧ ∀ z ∈ declaredMatches (c.1 ++ y.1), z ∉ D) →
      (renameComponents id D T cs).2 = cs
    | [], _, _, _ => rfl
    | c :: cs, D, T, h => by
      rw [children_cons] at h
      simp only [renameComponents]
      rw [renameComponent_self c D T fun c' hc' => h c' (List.mem_append_left _ hc'),
        renameComponents_self cs D _ fun c' hc' => h c' (List.mem_append_right _ hc')]

  theorem renameComponent_self : ∀ (c : Component) (D T : List Name),
      (∀ c' ∈ (Projection.composite [c]).children, ∀ y ∈ c'.2.paths,
        (declaredMatches (c'.1 ++ y.1)).Nodup ∧ ∀ z ∈ declaredMatches (c'.1 ++ y.1), z ∉ D) →
      (renameComponent id D T c).2 = c
    | .fact .., _, _, _ => rfl
    | .specification n ms q, D, T, h => by
      have h' : ∀ y ∈ q.paths, (declaredMatches (ms ++ y.1)).Nodup ∧
          ∀ z ∈ declaredMatches (ms ++ y.1), z ∉ D := h (ms, q) (by simp [Projection.children])
      have h0 := h' _ (mem_paths.mpr (Or.inl rfl))
      simp only [List.append_nil] at h0
      have hm := renameMatches_self { taken := T, declared := D } ms h0.1 h0.2
      have hst := (renameMatches_state id { taken := T, declared := D } ms).1
      rw [hm.1] at hst
      simp only [renameComponent]
      rw [hm.1, hm.2, renameProjection_self q _ _ fun y hy => by
        have := h' y hy
        rw [declared_append, List.nodup_append] at this
        refine ⟨this.1.2.1, fun z hz hm' => ?_⟩
        rw [hst] at hm'
        rcases List.mem_append.mp hm' with hm' | hm'
        · exact this.1.2.2 z (List.mem_reverse.mp hm') z hz rfl
        · exact this.2 z (List.mem_append_right _ hz) hm']
end

/-- **A specification that repeats no label is unchanged**: one each of whose
descendants declares each label once, and none of them a given's name. -/
theorem withDistinctLabels_eq_self {s : Specification} (hd : ∀ d ∈ s.descendants, DistinctLabels d)
    (hg : ∀ d ∈ s.descendants, ∀ x ∈ declaredMatches d.matchList, x ∉ s.given.map (·.name)) :
    withDistinctLabels s = s := by
  simp only [Specification.descendants, List.forall_mem_map, DistinctLabels, declared_append] at hd hg
  have h0 := hd _ (mem_paths.mpr (Or.inl rfl))
  have hg0 := hg _ (mem_paths.mpr (Or.inl rfl))
  simp only [declaredMatches, List.append_nil] at h0 hg0
  have hm := renameMatches_self { taken := s.labelsOf, declared := s.given.map (·.name) } s.matchList h0
    fun x hx => hg0 x hx
  have hst := (renameMatches_state id { taken := s.labelsOf, declared := s.given.map (·.name) } s.matchList).1
  rw [hm.1] at hst
  rw [withDistinctLabels_eq]
  simp only [hm.1, hm.2]
  rw [renameProjection_self _ _ _ fun x hx => ?_]
  have := hd x hx
  rw [List.nodup_append] at this
  refine ⟨this.2.1, fun z hz hm' => ?_⟩
  rw [hst] at hm'
  rcases List.mem_append.mp hm' with hm' | hm'
  · exact this.2.2 z (List.mem_reverse.mp hm') z hz rfl
  · exact hg x hx z (List.mem_append_right _ hz) hm'

mutual
  /-- A well-named match declares nothing already in scope, and nothing
  reserved, at any depth. -/
  theorem wellNamedMatches_declared : ∀ (S : List Name) (ms : List Match), WellNamedMatches S ms →
      ∀ x ∈ declaredMatches ms, x ∉ S ∧ isReserved x = false
    | _, [], _ => by simp [declaredMatches]
    | S, .mk u cs :: rest, ⟨hu, hres, hc, hr⟩ => fun x hx => by
      simp only [declaredMatches, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact ⟨hu, hres⟩
      · have := wellNamedConditions_declared _ cs hc x hx
        exact ⟨fun h => this.1 (List.mem_cons_of_mem _ h), this.2⟩
      · have := wellNamedMatches_declared _ rest hr x hx
        exact ⟨fun h => this.1 (List.mem_cons_of_mem _ h), this.2⟩

  theorem wellNamedConditions_declared : ∀ (S : List Name) (cs : List Condition), WellNamedConditions S cs →
      ∀ x ∈ declaredConditions cs, x ∉ S ∧ isReserved x = false
    | _, [], _ => by simp [declaredConditions]
    | S, .path _ :: cs, ⟨_, h⟩ => by simpa [declaredConditions] using wellNamedConditions_declared S cs h
    | S, .existential _ ms :: cs, ⟨hm, h⟩ => fun x hx => by
      simp only [declaredConditions, List.mem_append] at hx
      rcases hx with hx | hx
      · exact wellNamedMatches_declared S ms hm x hx
      · exact wellNamedConditions_declared S cs h x hx
end

/-- `withDistinctLabels_eq_self` for a well-formed specification: no
descendant of one declares a given's name. -/
theorem withDistinctLabels_eq_self_of_wellFormed {s : Specification} (hwf : ∀ d ∈ s.descendants, WellFormed d)
    (hd : ∀ d ∈ s.descendants, DistinctLabels d) : withDistinctLabels s = s :=
  withDistinctLabels_eq_self hd fun d hdd => by
    have hw := (hwf d hdd).wellNamed
    have : d.given = s.given := by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hdd; rfl
    rw [← this]; exact fun x hx => (wellNamedMatches_declared _ _ hw x hx).1

/-! ## Feeds accept every well-formed specification

The feed theorems, for the feeds of the renamed specification, under their
hypotheses less `DistinctLabels`, which the renaming establishes. What a
replica reads of the renamed specification is what it reads of the
specification (`withDistinctLabels_reads`), so `feeds_cover` and
`feed_converges` speak of the specification itself. -/

section Feeds
variable {g : Graph} {B : List Fact}

theorem buildFeeds_nodup_renamed {s : Specification} (hwf : ∀ d ∈ s.descendants, WellFormed d) :
    ∀ f ∈ buildFeeds (withDistinctLabels s), (names f.matchList).Nodup :=
  buildFeeds_nodup (withDistinctLabels_descendants_wellFormed hwf) (withDistinctLabels_distinct s)

theorem feeds_defer_renamed {s : Specification} (hwf : ∀ d ∈ s.descendants, WellFormed d) (G : Graph) (env : Env) :
    ∀ f ∈ buildFeeds (withDistinctLabels s), ∃ d ∈ (withDistinctLabels s).descendants,
      (∀ x ∈ names f.matchList, x ∈ declaredMatches d.matchList) ∧
      ∀ a m b, d.matchList = a ++ m :: b → (∃ y ∈ names (flatten b), y ∈ names f.matchList) →
        ∀ τ ∈ evalMatches G env f.matchList, ∀ ns ∈ negativesOf [m], Passes G τ ns :=
  feeds_defer (withDistinctLabels_descendants_wellFormed hwf) (withDistinctLabels_distinct s) G env

theorem feeds_cover_renamed {s : Specification} (hwf : ∀ d ∈ s.descendants, WellFormed d)
    (hr : ∀ d ∈ s.descendants, RootedMatches d.matchList) (hf : Fresh g B) {env : Env} (henv : Settled B env)
    (hgiv : ∀ l ∈ s.given, g.has env l = true)
    (hdel : ∀ id ∈ delivered (withDistinctLabels s) (g ++ B) env, Outside B id) :
    ∀ r, s.Reads g env r ↔ s.Reads (g ++ B) env r := fun r => by
  rw [← withDistinctLabels_reads hwf, ← withDistinctLabels_reads hwf]
  exact feeds_cover (withDistinctLabels_descendants_wellFormed hwf) (withDistinctLabels_distinct s)
    (withDistinctLabels_rooted hr) hf henv hgiv hdel r

end Feeds

/-! ## Transformations keep labels distinct

Renaming once, on entry, suffices for every stage after it, provided each stage
keeps `DistinctLabels` of every descendant. -/

/-! ### The inverse -/

open List in
theorem relax_declared (gained : Bool) (cs : List Condition) :
    declaredConditions (relax gained cs) <+ declaredConditions cs := by
  unfold relax; split
  · exact List.Sublist.refl _
  · have : declaredConditions (cs.filter (·.isPath)) = [] := by
      induction cs with
      | nil => simp [declaredConditions]
      | cons c cs ih => cases c <;> simp_all [declaredConditions, Condition.isPath]
    rw [this]; exact List.nil_sublist _

open List in
theorem relaxMatches_declared (gained : Bool) (ms : List Match) :
    declaredMatches (relaxMatches gained ms) <+ declaredMatches ms := by
  unfold relaxMatches; split
  · exact List.Sublist.refl _
  · induction ms with
    | nil => exact List.Sublist.refl _
    | cons m ms ih =>
      obtain ⟨u, cs⟩ := m
      simpa [declaredMatches] using (relax_declared false cs).append ih

open List in
mutual
  /-- An inverse declares what the specification declares, less what a relaxed
  level drops. -/
  theorem touchMatches_declared : ∀ (gained : Bool) (ms : List Match),
      ∀ x ∈ touchMatches gained ms, declaredMatches x.2 <+ declaredMatches ms
    | _, [] => by simp [touchMatches]
    | gained, .mk u cs :: rest => fun x hx => by
      simp only [touchMatches, List.mem_append, List.mem_map] at hx
      rcases hx with (hx | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩
      · split at hx
        · simp only [List.mem_singleton] at hx; subst hx
          simp [declaredMatches, pinCondition, declaredConditions]
        · simp at hx
      · simpa [declaredMatches] using
          ((touchConditions_declared gained cs y hy).append (relaxMatches_declared gained rest)).cons_cons u.name
      · simpa [declaredMatches] using
          ((relax_declared gained cs).append (touchMatches_declared gained rest y hy)).cons_cons u.name

  theorem touchConditions_declared : ∀ (gained : Bool) (cs : List Condition),
      ∀ x ∈ touchConditions gained cs, declaredConditions x.2 <+ declaredConditions cs
    | _, [] => by simp [touchConditions]
    | gained, c :: cs => fun x hx => by
      simp only [touchConditions, List.mem_append, List.mem_map] at hx
      rw [declaredConditions_cons]
      rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · rw [declaredConditions_cons]
        exact (touchCondition_declared gained c y hy).append (relax_declared gained cs)
      · rw [declaredConditions_append]
        exact (relax_declared gained [c]).append (touchConditions_declared gained cs y hy)

  theorem touchCondition_declared : ∀ (gained : Bool) (c : Condition),
      ∀ x ∈ touchCondition gained c, declaredConditions [x.2] <+ declaredConditions [c]
    | _, .path _ => by simp [touchCondition]
    | gained, .existential e ms => fun x hx => by
      simp only [touchCondition, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa [declaredConditions] using touchMatches_declared _ ms y hy
end

/-- **The inverses keep labels distinct.** -/
theorem inverses_distinct {s : Specification} (hd : ∀ d ∈ s.descendants, DistinctLabels d) :
    ∀ i ∈ inverses s, ∀ d ∈ i.descendants, DistinctLabels d := by
  intro i hi
  simp only [inverses, inversesFor, List.mem_append, List.mem_map] at hi
  simp only [Specification.descendants, List.forall_mem_map, DistinctLabels, declared_append] at hd ⊢
  rcases hi with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩ <;>
    exact fun x hx => ((touchMatches_declared _ _ y hy).append (List.Sublist.refl _)).nodup (hd x hx)

/-! ### The split -/

mutual
  /-- Hoisting keeps what the matches declare. -/
  theorem hoistMatches_declared (scope : List Name) : ∀ (i : Nat) (pos : Bool) (ms : List Match),
      declaredMatches (hoistMatches scope i pos ms).2.2 = declaredMatches ms
    | _, _, [] => rfl
    | i, pos, .mk u cs :: rest => by
      have h1 := hoistConditions_declared scope i pos cs
      have h2 := hoistMatches_declared scope (hoistConditions scope i pos cs).1 pos rest
      rcases hgenC : hoistConditions scope i pos cs with ⟨i1, headCs, cs'⟩
      rcases hgenM : hoistMatches scope i1 pos rest with ⟨i2, headRest, rest'⟩
      rw [hgenC] at h1 h2; rw [hgenM] at h2
      simp only [hoistMatches, hgenC, hgenM, declaredMatches] at h1 h2 ⊢
      rw [h1, h2]

  theorem hoistConditions_declared (scope : List Name) : ∀ (i : Nat) (pos : Bool) (cs : List Condition),
      declaredConditions (hoistConditions scope i pos cs).2.2 = declaredConditions cs
    | _, _, [] => rfl
    | i, pos, c :: cs => by
      have h1 := hoistCondition_declared scope i pos c
      have h2 := hoistConditions_declared scope (hoistCondition scope i pos c).1 pos cs
      rcases hgenC : hoistCondition scope i pos c with ⟨i1, headC, c'⟩
      rcases hgenCs : hoistConditions scope i1 pos cs with ⟨i2, headCs, cs'⟩
      rw [hgenC] at h1 h2; rw [hgenCs] at h2
      simp only [hoistConditions, hgenC, hgenCs] at h1 h2 ⊢
      rw [declaredConditions_cons, h1, h2, ← declaredConditions_cons]

  theorem hoistCondition_declared (scope : List Name) : ∀ (i : Nat) (pos : Bool) (c : Condition),
      declaredConditions [(hoistCondition scope i pos c).2.2] = declaredConditions [c]
    | i, pos, .path pc => by
      unfold hoistCondition
      split <;> simp [declaredConditions]
    | i, pos, .existential e ms => by
      have h := hoistMatches_declared scope i (pos && e) ms
      rcases hgenM : hoistMatches scope i (pos && e) ms with ⟨i1, headMs, ms'⟩
      rw [hgenM] at h
      simp only [hoistCondition, hgenM, declaredConditions] at h ⊢
      rw [h]
end

mutual
  /-- The head matches a hoist produces declare distinct split labels, numbered
  from `i` up to the next free index. -/
  theorem hoistMatches_head (scope : List Name) : ∀ (i : Nat) (pos : Bool) (ms : List Match),
      (declaredMatches (hoistMatches scope i pos ms).2.1).Nodup ∧
        ∀ x ∈ declaredMatches (hoistMatches scope i pos ms).2.1,
          ∃ j, i ≤ j ∧ j < (hoistMatches scope i pos ms).1 ∧ x = splitLabel j
    | _, _, [] => by simp [hoistMatches, declaredMatches]
    | i, pos, .mk u cs :: rest => by
      have h1 := hoistConditions_head scope i pos cs
      have hm1 := hoistConditions_mono scope i pos cs
      have h2 := hoistMatches_head scope (hoistConditions scope i pos cs).1 pos rest
      have hm2 := hoistMatches_mono scope (hoistConditions scope i pos cs).1 pos rest
      rcases hgenC : hoistConditions scope i pos cs with ⟨i1, headCs, cs'⟩
      rcases hgenM : hoistMatches scope i1 pos rest with ⟨i2, headRest, rest'⟩
      rw [hgenC] at h1 h2 hm1 hm2; rw [hgenM] at h2 hm2
      simp only [hoistMatches, hgenC, hgenM, declared_append] at h1 h2 hm1 hm2 ⊢
      refine ⟨List.nodup_append.mpr ⟨h1.1, h2.1, fun a ha b hb hab => ?_⟩, fun x hx => ?_⟩
      · obtain ⟨j, -, hj, rfl⟩ := h1.2 a ha
        obtain ⟨k, hk, -, he⟩ := h2.2 b hb
        have := splitLabel_injective (hab.trans he); omega
      · rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨j, hj1, hj2, rfl⟩ := h1.2 x hx; exact ⟨j, hj1, by omega, rfl⟩
        · obtain ⟨j, hj1, hj2, rfl⟩ := h2.2 x hx; exact ⟨j, by omega, hj2, rfl⟩

  theorem hoistConditions_head (scope : List Name) : ∀ (i : Nat) (pos : Bool) (cs : List Condition),
      (declaredMatches (hoistConditions scope i pos cs).2.1).Nodup ∧
        ∀ x ∈ declaredMatches (hoistConditions scope i pos cs).2.1,
          ∃ j, i ≤ j ∧ j < (hoistConditions scope i pos cs).1 ∧ x = splitLabel j
    | _, _, [] => by simp [hoistConditions, declaredMatches]
    | i, pos, c :: cs => by
      have h1 := hoistCondition_head scope i pos c
      have hm1 := hoistCondition_mono scope i pos c
      have h2 := hoistConditions_head scope (hoistCondition scope i pos c).1 pos cs
      have hm2 := hoistConditions_mono scope (hoistCondition scope i pos c).1 pos cs
      rcases hgenC : hoistCondition scope i pos c with ⟨i1, headC, c'⟩
      rcases hgenCs : hoistConditions scope i1 pos cs with ⟨i2, headCs, cs'⟩
      rw [hgenC] at h1 h2 hm1 hm2; rw [hgenCs] at h2 hm2
      simp only [hoistConditions, hgenC, hgenCs, declared_append] at h1 h2 hm1 hm2 ⊢
      refine ⟨List.nodup_append.mpr ⟨h1.1, h2.1, fun a ha b hb hab => ?_⟩, fun x hx => ?_⟩
      · obtain ⟨j, -, hj, rfl⟩ := h1.2 a ha
        obtain ⟨k, hk, -, he⟩ := h2.2 b hb
        have := splitLabel_injective (hab.trans he); omega
      · rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨j, hj1, hj2, rfl⟩ := h1.2 x hx; exact ⟨j, hj1, by omega, rfl⟩
        · obtain ⟨j, hj1, hj2, rfl⟩ := h2.2 x hx; exact ⟨j, by omega, hj2, rfl⟩

  theorem hoistCondition_head (scope : List Name) : ∀ (i : Nat) (pos : Bool) (c : Condition),
      (declaredMatches (hoistCondition scope i pos c).2.1).Nodup ∧
        ∀ x ∈ declaredMatches (hoistCondition scope i pos c).2.1,
          ∃ j, i ≤ j ∧ j < (hoistCondition scope i pos c).1 ∧ x = splitLabel j
    | i, pos, .path pc => by
      unfold hoistCondition
      split <;> simp [declaredMatches, declaredConditions]
      exact ⟨i, Nat.le_refl _, Nat.lt_succ_self _, rfl⟩
    | i, pos, .existential e ms => by
      have h := hoistMatches_head scope i (pos && e) ms
      rcases hgenM : hoistMatches scope i (pos && e) ms with ⟨i1, headMs, ms'⟩
      rw [hgenM] at h
      simpa only [hoistCondition, hgenM] using h
end

theorem paths_of_children_nil {p : Projection} (h : p.children = []) : p.paths = [([], p)] := by
  rw [Projection.paths]; simp [h]

/-- **The split keeps labels distinct**: its head's and its tail's. -/
theorem split_distinct {s : Specification} (hwf : WellFormed s) (hd : ∀ d ∈ s.descendants, DistinctLabels d) :
    (∀ d ∈ (splitBeforeFirstSuccessor s).head.descendants, DistinctLabels d) ∧
      ∀ t, (splitBeforeFirstSuccessor s).tail = some t → ∀ d ∈ t.descendants, DistinctLabels d := by
  have hd0 : (declaredMatches s.matchList).Nodup := by
    simpa [DistinctLabels] using hd _ (List.mem_map_of_mem (mem_paths.mpr (Or.inl rfl)))
  simp only [Specification.descendants, List.forall_mem_map, DistinctLabels, declared_append] at hd
  unfold splitBeforeFirstSuccessor
  generalize hspan : s.matchList.span matchIsDeterministic = sp
  obtain ⟨before, rest⟩ := sp
  cases rest with
  | nil =>
    simp only [Specification.descendants, List.forall_mem_map, DistinctLabels, declared_append]
    exact ⟨hd, fun _ h => nomatch h⟩
  | cons pivot after =>
    have hs : s.matchList = before ++ pivot :: after := by
      have h := span_loop_append matchIsDeterministic s.matchList []
      unfold List.span at hspan
      rw [hspan] at h
      simpa using h.symm
    have hw := hwf.wellNamed
    rw [hs, wellNamedMatches_append] at hw
    rw [hs, declared_append] at hd0 hd
    unfold hoistAt
    have hh := hoistMatches_head (scopeAt s before) 0 true (pivot :: after)
    have ht := hoistMatches_declared (scopeAt s before) 0 true (pivot :: after)
    rcases hgenM : hoistMatches (scopeAt s before) 0 true (pivot :: after) with ⟨n, hm, tailMatches⟩
    rw [hgenM] at hh ht
    simp only [hgenM] at hh ht ⊢
    refine ⟨?_, fun t ht' => ?_⟩
    · rw [Specification.descendants, paths_of_children_nil (by simp [Projection.children])]
      simp only [List.map_cons, List.map_nil, List.mem_singleton, forall_eq, DistinctLabels, List.append_nil,
        declared_append]
      refine List.nodup_append.mpr ⟨(List.nodup_append.mp hd0).1, hh.1, fun a ha b hb hab => ?_⟩
      obtain ⟨j, -, -, rfl⟩ := hh.2 b hb
      have := (wellNamedMatches_declared _ _ hw.1 a ha).2
      rw [hab, isReserved_splitLabel] at this; exact absurd this (by simp)
    · simp only [Option.some.injEq] at ht'; subst ht'
      simp only [Specification.descendants, List.forall_mem_map, DistinctLabels, declared_append, ht]
      exact fun x hx => (List.sublist_append_right _ _).nodup (by simpa [List.append_assoc] using hd x hx)

/-! ### Conditions on a given

Reducing moves the givens' conditions onto a new first match, so their matches
join the first level of every descendant. `DistinctLabels` of the
specification without them does not say that they declare names the matches do
not: a condition on a given and a match may share a name, which is no reuse in
scope for `WellFormed` (the condition is in scope of neither), and the
reduction then declares it twice in one descendant
(`vectors/distinct-labels/given-condition-shares-a-name.json`). So the
distinctness reduction keeps is one that counts the conditions; and a
specification with conditions on its givens is renamed after it is reduced. -/

/-- No descendant declares a name twice, counting the givens' conditions as
part of every descendant. -/
def ConditionedSpecification.DistinctLabels (c : ConditionedSpecification) : Prop :=
  ∀ d ∈ c.spec.descendants, (declaredConditions c.conditions ++ declaredMatches d.matchList).Nodup

/-- **Reducing conditions on a given keeps labels distinct**, counting the
conditions, when its new label is one no descendant declares. -/
theorem reduceGivenConditions_distinct {c : ConditionedSpecification} {x : Name} (hd : c.DistinctLabels)
    (hx : ∀ d ∈ c.spec.descendants, x ∉ declaredConditions c.conditions ++ declaredMatches d.matchList) :
    ∀ d ∈ (reduceGivenConditions x c).descendants, DistinctLabels d := by
  unfold reduceGivenConditions
  simp only [ConditionedSpecification.DistinctLabels, Specification.descendants, List.forall_mem_map,
    ConditionedSpecification.spec] at hd hx
  split
  · simp only [Specification.descendants, List.forall_mem_map, DistinctLabels, List.cons_append,
      declaredMatches, declaredConditions, declared_append]
    intro y hy
    rw [← declared_append, List.nodup_cons]
    exact ⟨hx y hy, by simpa [declared_append, List.append_assoc] using hd y hy⟩
  · simp only [Specification.descendants, List.forall_mem_map, DistinctLabels]
    exact fun y hy => (List.sublist_append_right _ _).nodup (hd y hy)

end JinagaSpec
