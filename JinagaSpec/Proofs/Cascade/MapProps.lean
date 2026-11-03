import JinagaSpec.Proofs.Cascade.Step
import JinagaSpec.Cascade.Steps

/-!
# Cascade: steps that change the props of one level

`dropProperty` and `defineProperty` keep every node and its parent, and change
only the props of nodes at one level. Their output tree is `T.mapProps s φ`.
Events that leave those props alone pass through unchanged (`mapProps_forward`);
each step handles the rest.
-/
namespace JinagaSpec.Cascade

variable {s : Level} {φ : Key → Props → Props}

def mapNode (s : Level) (φ : Key → Props → Props) (id : Id) (n : Node) : Node :=
  if id.1 = s then { n with props := φ id.2 n.props } else n

theorem get_mapProps (T : Tree) (id : Id) :
    (T.mapProps s φ).get id = (T.get id).map (mapNode s φ id) := by
  induction T with
  | nil => rfl
  | cons e T ih =>
    obtain ⟨id', n⟩ := e
    have : Tree.mapProps ((id', n) :: T) s φ = (id', mapNode s φ id' n) :: Tree.mapProps T s φ := by
      simp only [Tree.mapProps, List.map_cons, mapNode]; split <;> rfl
    rw [this, get_cons, get_cons, ih]
    by_cases h : id' = id
    · subst h; simp
    · simp [h]

@[simp] theorem mapNode_parent (id : Id) (n : Node) : (mapNode s φ id n).parent = n.parent := by
  unfold mapNode; split <;> rfl

theorem isSome_get_mapProps (T : Tree) (id : Id) :
    ((T.mapProps s φ).get id).isSome = (T.get id).isSome := by
  simp [get_mapProps]

theorem parentOk_mapProps (T : Tree) (l : Level) (p : Option Key) :
    (T.mapProps s φ).parentOk l p = T.parentOk l p := by
  cases p <;> simp [Tree.parentOk, isSome_get_mapProps]

theorem keys_mapProps (T : Tree) : (T.mapProps s φ).map (·.1) = T.map (·.1) := by
  induction T with
  | nil => rfl
  | cons e T ih =>
    simp only [Tree.mapProps, List.map_cons] at ih ⊢
    split <;> simp [ih]

theorem hasChild_mapProps {T : Tree} (hwf : T.WF) (l : Level) (k : Key) :
    (T.mapProps s φ).hasChild l k = T.hasChild l k := by
  rw [Bool.eq_iff_iff, hasChild_iff (keys_mapProps T ▸ hwf.nodup), hasChild_iff hwf.nodup]
  simp only [get_mapProps, Option.map_eq_some_iff]
  constructor
  · rintro ⟨l', k', _, ⟨n, hn, rfl⟩, h1, h2, h3⟩
    exact ⟨l', k', n, hn, h1, h2, by simpa using h3⟩
  · rintro ⟨l', k', n, hn, h1, h2, h3⟩
    exact ⟨l', k', _, ⟨n, hn, rfl⟩, h1, h2, by simpa using h3⟩

theorem mapProps_wf {T : Tree} (hwf : T.WF) : (T.mapProps s φ).WF := by
  refine ⟨keys_mapProps T ▸ hwf.nodup, fun id n hg => ?_⟩
  rw [get_mapProps, Option.map_eq_some_iff] at hg
  obtain ⟨n0, hn0, rfl⟩ := hg
  rw [parentOk_mapProps, mapNode_parent]
  exact hwf.parents id n0 hn0

theorem mapProps_denotation : Denotation fun T => T.mapProps s φ :=
  ⟨fun _ hT => mapProps_wf hT, fun T U _ _ h id => by simp only [get_mapProps, h id]⟩

/-- The level whose props an event sets, if it sets any. -/
def Event.propsLevel : Event → Option Level
  | .added l .. => some l
  | .modified l .. => some l
  | _ => none

/-- An event that leaves the props at level `s` alone passes through. -/
theorem mapProps_forward {T T' : Tree} {e : Event} (hwf : T.WF) (he : T.apply e = some T')
    (hs : e.propsLevel ≠ some s) :
    ∃ U, (T.mapProps s φ).apply e = some U ∧ U.Equiv (T'.mapProps s φ) := by
  cases e with
  | added l k p ps =>
    obtain ⟨hn, hp, rfl⟩ := apply_added.mp he
    replace hs : l ≠ s := fun h => hs (by simp [Event.propsLevel, h])
    refine ⟨_, apply_added.mpr ⟨by simp [get_mapProps, hn], by rw [parentOk_mapProps]; exact hp, rfl⟩,
      fun id => ?_⟩
    simp only [get_cons, get_mapProps]
    split
    · rename_i h; subst h; simp [mapNode, hs]
    · rfl
  | removed l k =>
    obtain ⟨hsome, hc, rfl⟩ := apply_removed.mp he
    refine ⟨_, apply_removed.mpr ⟨by simpa [isSome_get_mapProps] using hsome,
      by rw [hasChild_mapProps hwf]; exact hc, rfl⟩, fun id => ?_⟩
    simp only [get_filter, get_mapProps]
    split <;> rfl
  | modified l k p old new =>
    obtain ⟨n, hn, h1, h2, rfl⟩ := apply_modified.mp he
    replace hs : l ≠ s := fun h => hs (by simp [Event.propsLevel, h])
    refine ⟨_, apply_modified.mpr ⟨mapNode s φ (l, k) n, by simp [get_mapProps, hn],
      by simp [mapNode, hs, h1], h2, rfl⟩, fun id => ?_⟩
    have hid : mapNode s φ (l, k) = fun n => n := funext fun n => by simp [mapNode, hs]
    simp only [get_update, get_mapProps]
    split
    · rename_i h; subst h; simp only [hid]; cases T.get (l, k) <;> rfl
    · rfl
  | placed l k a b =>
    obtain ⟨n, hn, h1, h2, h3, rfl⟩ := apply_placed.mp he
    refine ⟨_, apply_placed.mpr ⟨mapNode s φ (l, k) n, by simp [get_mapProps, hn],
      by simp [h1], h2, by rw [parentOk_mapProps]; exact h3, rfl⟩, fun id => ?_⟩
    simp only [get_update, get_mapProps]
    split
    · rename_i h; subst h; cases hn' : T.get (l, k) <;> simp [mapNode]; split <;> rfl
    · rfl

@[simp] theorem bind_some_eq (o : Option Tree) : (o.bind fun x => some x) = o := by
  cases o <;> rfl

theorem applyAll_single (T : Tree) (e : Event) : T.applyAll [e] = T.apply e := by
  simp only [Tree.applyAll]; cases T.apply e <;> rfl

/-- A node added at `s` arrives with its props mapped. -/
theorem mapProps_added {T T' : Tree} {k : Key} {p : Option Key} {ps : Props}
    (he : T.apply (.added s k p ps) = some T') :
    ∃ U, (T.mapProps s φ).apply (.added s k p (φ k ps)) = some U ∧
      U.Equiv (T'.mapProps s φ) := by
  obtain ⟨hn, hp, rfl⟩ := apply_added.mp he
  refine ⟨_, apply_added.mpr ⟨by simp [get_mapProps, hn], by rw [parentOk_mapProps]; exact hp, rfl⟩,
    fun id => ?_⟩
  simp only [get_cons, get_mapProps]
  split
  · rename_i h; subst h; simp [mapNode]
  · rfl

/-- A change to a node at `s` whose mapped props change in the same way. -/
theorem mapProps_modified {T T' : Tree} {k : Key} {p : String} {old new : Option Val}
    (he : T.apply (.modified s k p old new) = some T')
    (hget : ∀ ps, φ k ps p = ps p) (hset : ∀ ps, φ k (ps.set p new) = (φ k ps).set p new) :
    ∃ U, (T.mapProps s φ).apply (.modified s k p old new) = some U ∧
      U.Equiv (T'.mapProps s φ) := by
  obtain ⟨n, hn, h1, h2, rfl⟩ := apply_modified.mp he
  refine ⟨_, apply_modified.mpr ⟨mapNode s φ (s, k) n, by simp [get_mapProps, hn],
    by simp [mapNode, hget, h1], h2, rfl⟩, fun id => ?_⟩
  simp only [get_update, get_mapProps]
  split
  · rename_i h; subst h; simp [hn, mapNode, hset]
  · rfl

/-- A change that the mapped props do not see. -/
theorem mapProps_hidden {T T' : Tree} {k : Key} {p : String} {old new : Option Val}
    (he : T.apply (.modified s k p old new) = some T')
    (hhide : ∀ ps, φ k (ps.set p new) = φ k ps) :
    (T.mapProps s φ).Equiv (T'.mapProps s φ) := by
  obtain ⟨n, hn, -, -, rfl⟩ := apply_modified.mp he
  intro id
  simp only [get_update, get_mapProps]
  split
  · rename_i h; subst h; simp [hn, mapNode, hhide]
  · rfl

/-! ## `dropProperty` -/

theorem Props.drop_set_self (ps : Props) (q : String) (v : Option Val) :
    (ps.set q v).drop q = ps.drop q := by
  funext r; by_cases h : r = q <;> simp [Props.drop, Props.set, h]

theorem Props.drop_set (ps : Props) {q p : String} (h : p ≠ q) (v : Option Val) :
    (ps.set p v).drop q = (ps.drop q).set p v := by
  funext r; simp only [Props.drop, Props.set]
  by_cases hr : r = p <;> simp_all

theorem dropProperty_denotation (s : Level) (q : String) : Denotation (dropProperty.F s q) :=
  mapProps_denotation

/-- **`dropProperty_correct`.** -/
theorem dropProperty_correct (s : Level) (q : String) :
    Correct (dropProperty s q) (dropProperty.F s q) := by
  intro T e T' hwf he
  cases e with
  | added l k p ps =>
    simp only [dropProperty, applyAll_single, dropProperty.F]
    by_cases hl : l = s
    · subst hl; simpa using mapProps_added he
    · simpa [hl] using mapProps_forward hwf he (by simp [Event.propsLevel, hl])
  | removed l k =>
    simpa [dropProperty, applyAll_single, dropProperty.F] using
      mapProps_forward hwf he (by simp [Event.propsLevel])
  | placed l k a b =>
    simpa [dropProperty, applyAll_single, dropProperty.F] using
      mapProps_forward hwf he (by simp [Event.propsLevel])
  | modified l k p old new =>
    simp only [dropProperty, dropProperty.F]
    by_cases hl : l = s
    · subst hl
      by_cases hp : p = q
      · subst hp
        exact ⟨_, by simp [Tree.applyAll], mapProps_hidden he fun ps => Props.drop_set_self ps p new⟩
      · simp only [hp, and_false, ↓reduceIte, applyAll_single]
        exact mapProps_modified he (fun ps => by simp [Props.drop, hp])
          (fun ps => Props.drop_set ps hp new)
    · simpa [hl, applyAll_single] using mapProps_forward hwf he (by simp [Event.propsLevel, hl])

/-! ## `defineProperty` -/

theorem Props.set_set_self (ps : Props) (q : String) (v w : Option Val) :
    (ps.set q v).set q w = ps.set q w := by
  funext r; by_cases h : r = q <;> simp [Props.set, h]

theorem Props.set_comm (ps : Props) {p q : String} (h : p ≠ q) (v w : Option Val) :
    (ps.set p v).set q w = (ps.set q w).set p v := by
  funext r; by_cases hp : r = p <;> by_cases hq : r = q <;> simp_all [Props.set]

theorem defineProperty_denotation (s : Level) (q : String) (f : Props → Option Val) :
    Denotation (defineProperty.F s q f) :=
  mapProps_denotation

/-- **`defineProperty_correct`.** The step is correct when `f` reads only the
properties in `deps`, and `q` is not one of them. -/
theorem defineProperty_correct (s : Level) (q : String) (f : Props → Option Val)
    (deps : List String) (hq : q ∉ deps)
    (hdeps : ∀ ps p v, p ∉ deps → f (ps.set p v) = f ps) :
    Correct (defineProperty s q f deps) (defineProperty.F s q f) := by
  intro T e T' hwf he
  cases e with
  | added l k p ps =>
    simp only [defineProperty, applyAll_single, defineProperty.F]
    by_cases hl : l = s
    · subst hl; simpa using mapProps_added he
    · simpa [hl] using mapProps_forward hwf he (by simp [Event.propsLevel, hl])
  | removed l k =>
    simpa [defineProperty, applyAll_single, defineProperty.F] using
      mapProps_forward hwf he (by simp [Event.propsLevel])
  | placed l k a b =>
    simpa [defineProperty, applyAll_single, defineProperty.F] using
      mapProps_forward hwf he (by simp [Event.propsLevel])
  | modified l k p old new =>
    simp only [defineProperty, defineProperty.F]
    by_cases hl : l = s
    · subst hl
      by_cases hp : p = q
      · subst hp
        refine ⟨_, by simp [Tree.applyAll], mapProps_hidden he fun ps => ?_⟩
        rw [Props.set_set_self, hdeps ps p new hq]
      · obtain ⟨n, hn, h1, h2, rfl⟩ := apply_modified.mp he
        simp only [hp, ↓reduceIte, hn]
        -- First, the change itself.
        have hfirst : (T.mapProps l fun _ ps => ps.set q (f ps)).apply (.modified l k p old new) =
            some ((T.mapProps l fun _ ps => ps.set q (f ps)).update (l, k)
              fun n => { n with props := n.props.set p new }) :=
          apply_modified.mpr ⟨mapNode l (fun _ ps => ps.set q (f ps)) (l, k) n,
            by simp [get_mapProps, hn], by simp [mapNode, Props.set, hp, h1], h2, rfl⟩
        by_cases hchange : p ∈ deps ∧ f n.props ≠ f (n.props.set p new)
        · simp only [hchange, ne_eq, not_false_eq_true, and_self, ↓reduceIte, Tree.applyAll,
            hfirst, Option.bind_some, bind_some_eq]
          refine ⟨_, apply_modified.mpr ⟨{ (mapNode l (fun _ ps => ps.set q (f ps)) (l, k) n) with
            props := (mapNode l (fun _ ps => ps.set q (f ps)) (l, k) n).props.set p new },
            ?_, ?_, hchange.2, rfl⟩, fun id => ?_⟩
          · simp [get_update, get_mapProps, hn]
          · simp [mapNode, Props.set, Ne.symm hp]
          · simp only [get_update, get_mapProps]
            split
            · rename_i h; subst h
              simp [hn, mapNode, Props.set_set_self, Props.set_comm _ hp]
            · rfl
        · have hsame : f (n.props.set p new) = f n.props := by
            by_cases hd : p ∈ deps
            · exact (Classical.not_not.mp fun h => hchange ⟨hd, Ne.symm h⟩)
            · exact hdeps _ p new hd
          simp only [hchange, ↓reduceIte, applyAll_single, hfirst, Option.some.injEq,
            exists_eq_left']
          intro id
          simp only [get_update, get_mapProps]
          split
          · rename_i h; subst h
            simp [hn, mapNode, hsame, Props.set_comm _ hp]
          · rfl
    · simpa [hl, applyAll_single] using mapProps_forward hwf he (by simp [Event.propsLevel, hl])

end JinagaSpec.Cascade
