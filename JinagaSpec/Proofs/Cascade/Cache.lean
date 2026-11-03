import JinagaSpec.Cascade.Cache
import JinagaSpec.Proofs.Cascade.Step
import JinagaSpec.Proofs.Cascade.MapProps
import JinagaSpec.Proofs.Cascade.Aggregate
import JinagaSpec.Proofs.Cascade.GroupBy

/-!
# Cascade: the caches agree with the trees

A cached step that implements a tree step emits the same events for any input
the protocol accepts (`implements_run`), so it is correct for the same
denotation (`implements_correct`). The caches of `groupBy`, the aggregates and
`defineProperty` implement their steps (`…_implements`), so the steps as
TypeScript writes them are correct (`…_cached_correct`).
-/
namespace JinagaSpec.Cascade

/-! ## Implementing a step -/

/-- **`implements_run`.** Over events the input accepts, a cached step emits
what the step it implements emits. -/
theorem implements_run {C : Type} {K : Cached C} {S : Step} {R : C → Tree → Prop}
    (hK : Implements K S R) :
    ∀ (es : List Event) (c : C) (T T' : Tree), R c T → T.WF → T.applyAll es = some T' →
      K.run c es = run S T es := by
  intro es
  induction es with
  | nil => intro _ _ _ _ _ _; rfl
  | cons e es ih =>
    intro c T T' hR hwf h
    simp only [Tree.applyAll] at h
    cases ha : T.apply e with
    | none => simp [ha] at h
    | some T₁ =>
      rw [ha] at h
      obtain ⟨hout, hR'⟩ := hK.step c T e T₁ hR hwf ha
      simp only [Cached.run, run, ha, hout]
      rw [ih _ T₁ T' hR' (apply_wf hwf ha) h]

/-- **`implements_correct`.** A cached step that implements a correct step,
started from its empty cache, holds the step's denotation of what it received. -/
theorem implements_correct {C : Type} {K : Cached C} {S : Step} {R : C → Tree → Prop}
    {F : Tree → Tree} (hK : Implements K S R) (hS : Correct S F) (hF : Denotation F)
    {es : List Event} {T' : Tree} (h : Tree.applyAll [] es = some T') :
    ∃ U, (F []).applyAll (K.run K.init es) = some U ∧ U.Equiv (F T') := by
  have hwf : Tree.WF [] := ⟨List.nodup_nil, fun _ _ h => by simp at h⟩
  rw [implements_run hK es K.init [] T' hK.init hwf h]
  exact run_correct hS hF es [] T' hwf h

/-! ## Counting entries as the tree changes -/

theorem filter_ne_of_not_mem {T : Tree} {id : Id} (h : id ∉ T.map (·.1)) :
    T.filter (·.1 != id) = T := by
  rw [List.filter_eq_self]
  intro e he
  have : e.1 ≠ id := fun hx => h (List.mem_map.mpr ⟨e, he, hx⟩)
  simpa using this

theorem update_of_not_mem {T : Tree} {id : Id} (f : Node → Node) (h : id ∉ T.map (·.1)) :
    T.update id f = T := by
  unfold Tree.update
  conv => rhs; rw [← List.map_id T]
  apply List.map_congr_left
  intro e he
  have : e.1 ≠ id := fun hx => h (List.mem_map.mpr ⟨e, he, hx⟩)
  simp [this]

theorem countP_filter_ne {T : Tree} (hnd : (T.map (·.1)).Nodup) {id : Id} {n : Node}
    (h : T.get id = some n) (P : Id × Node → Bool) :
    (T.filter (·.1 != id)).countP P + (if P (id, n) then 1 else 0) = T.countP P := by
  induction T with
  | nil => simp at h
  | cons x T ih =>
    obtain ⟨id', n'⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [get_cons] at h
    by_cases hx : id' = id
    · subst hx
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        filter_ne_of_not_mem hnd.1, List.countP_cons]
    · simp only [hx, ↓reduceIte] at h
      have hne : (id' != id) = true := by simpa using hx
      simp only [List.filter_cons, hne, ↓reduceIte, List.countP_cons]
      have := ih hnd.2 h
      omega

theorem countP_update {T : Tree} (hnd : (T.map (·.1)).Nodup) {id : Id} {n : Node}
    (h : T.get id = some n) (f : Node → Node) (P : Id × Node → Bool) :
    (T.update id f).countP P + (if P (id, n) then 1 else 0) =
      T.countP P + (if P (id, f n) then 1 else 0) := by
  induction T with
  | nil => simp at h
  | cons x T ih =>
    obtain ⟨id', n'⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [get_cons] at h
    by_cases hx : id' = id
    · subst hx
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      have : Tree.update T id' f = T := update_of_not_mem f hnd.1
      simp only [Tree.update, List.map_cons, beq_self_eq_true, ↓reduceIte] at this ⊢
      rw [this, List.countP_cons, List.countP_cons]
      omega
    · simp only [hx, ↓reduceIte] at h
      have := ih hnd.2 h
      simp only [Tree.update, List.map_cons, beq_iff_eq, hx, ↓reduceIte, List.countP_cons] at this ⊢
      omega

/-! ## `groupBy` -/

theorem groupKey_pick (G : List String) (ps : Props) : groupKey G (pick G ps) = groupKey G ps := by
  simp only [groupKey, Key.group.injEq]
  exact List.map_congr_left fun q hq => by simp [pick, hq]

theorem pick_set_mem {G : List String} {p : String} (hp : p ∈ G) (ps : Props) (v : Option Val) :
    pick G (ps.set p v) = (pick G ps).set p v := by
  funext q
  by_cases hq : q = p
  · subst hq; simp [pick, Props.set, hp]
  · simp [pick, Props.set, hq]

theorem pick_set_not_mem {G : List String} {p : String} (hp : p ∉ G) (ps : Props) (v : Option Val) :
    pick G (ps.set p v) = pick G ps := by
  funext q
  by_cases hq : q ∈ G
  · have : q ≠ p := fun h => hp (h ▸ hq)
    simp [pick, Props.set, hq, this]
  · simp [pick, hq]

theorem hasMember_iff_countP (G : List String) (T : Tree) (g : Key) :
    hasMember G T g = true ↔ 0 < T.countP (isMember G g) := by
  rw [List.countP_pos_iff]
  simp [hasMember, isMember]

theorem isMember_root (G : List String) (g k : Key) (n : Node) :
    isMember G g (([], k), n) = (groupKey G n.props == g) := by
  simp [isMember]

theorem isMember_nonroot (G : List String) (g : Key) {l : Level} (hl : l ≠ []) (k : Key) (n : Node) :
    isMember G g ((l, k), n) = false := by
  cases l with
  | nil => exact absurd rfl hl
  | cons => simp [isMember]

theorem ite_beq (a x : Key) : (if (a == x) = true then 1 else 0) = (if x = a then 1 else 0) := by
  by_cases h : x = a
  · subst h; simp
  · have : (a == x) = false := by simpa using Ne.symm h
    simp [this, h]

/-- **`groupBy_implements`.** `groupBy`'s cache, the grouping values of each
row and the size of each group, implements `groupBy` at the root. -/
theorem groupBy_implements (G : List String) (C : String) :
    Implements (groupBy.cached G C) (groupBy G C) (GroupCache.Describes G) := by
  refine ⟨⟨fun _ => rfl, fun _ => rfl⟩, ?_⟩
  intro c T e T' hR hwf ha
  obtain ⟨hrows, hsizes⟩ := hR
  have hmem : ∀ g, (0 < c.sizes g) ↔ hasMember G T g = true := fun g => by
    rw [hasMember_iff_countP, hsizes g]
  cases e with
  | added l k p ps =>
    obtain ⟨hn, -, rfl⟩ := apply_added.mp ha
    cases l with
    | nil =>
      refine ⟨?_, ?_, ?_⟩
      · simp only [groupBy.cached, groupBy, groupKey_pick]
        by_cases h : hasMember G T (groupKey G ps) = true
        · simp [h, (hmem _).mpr h]
        · simp [h, show ¬ 0 < c.sizes (groupKey G ps) from fun h' => h ((hmem _).mp h')]
      · intro k'
        simp only [groupBy.cached, Map.set, get_cons, Prod.mk.injEq, true_and]
        by_cases hk : k' = k
        · subst hk; simp
        · simp [hk, Ne.symm hk, hrows k']
      · intro g
        simp only [groupBy.cached, Map.set, List.countP_cons, isMember_root, groupKey_pick]
        by_cases hg : g = groupKey G ps
        · subst hg; simp [hsizes]
        · simp [hg, Ne.symm hg, hsizes g]
    | cons d l =>
      refine ⟨rfl, ?_, ?_⟩
      · intro k'
        simp only [groupBy.cached, get_cons, Prod.mk.injEq, reduceCtorEq, false_and, ↓reduceIte]
        exact hrows k'
      · intro g
        simp only [groupBy.cached, List.countP_cons, isMember_nonroot G g (List.cons_ne_nil d l)]
        simp [hsizes g]
  | removed l k =>
    obtain ⟨hs, -, rfl⟩ := apply_removed.mp ha
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
    have hcount := fun P => countP_filter_ne hwf.nodup hn P
    cases l with
    | nil =>
      have hrk : c.rows k = some (pick G n.props) := by rw [hrows k, hn]; rfl
      have hsz : c.sizes (groupKey G n.props) - 1 =
          (T.filter (·.1 != ([], k))).countP (isMember G (groupKey G n.props)) := by
        have := hcount (isMember G (groupKey G n.props))
        rw [isMember_root] at this
        simp only [beq_self_eq_true, ↓reduceIte] at this
        rw [hsizes]; omega
      refine ⟨?_, ?_, ?_⟩
      · simp only [groupBy.cached, groupBy, hrk, hn, groupKey_pick, hsz, ← hasMember_iff_countP]
      · intro k'
        simp only [groupBy.cached, hrk, Map.set, get_filter]
        by_cases hk : k' = k
        · subst hk; simp
        · simp [hk, hrows k']
      · intro g
        simp only [groupBy.cached, hrk, Map.set, groupKey_pick]
        by_cases hg : g = groupKey G n.props
        · subst hg; simpa using hsz
        · have := hcount (isMember G g)
          rw [isMember_root] at this
          have hne : (groupKey G n.props == g) = false := by simpa using Ne.symm hg
          simp only [hne, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at this
          simp [hg, hsizes g, this]
    | cons d l =>
      refine ⟨rfl, ?_, ?_⟩
      · intro k'
        simp only [groupBy.cached, get_filter]
        simp [hrows k']
      · intro g
        have := hcount (isMember G g)
        rw [isMember_nonroot G g (List.cons_ne_nil d l)] at this
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at this
        simp only [groupBy.cached]
        rw [hsizes g, this]
  | modified l k p old new =>
    obtain ⟨n, hn, -, -, rfl⟩ := apply_modified.mp ha
    have hcount := fun P => countP_update hwf.nodup hn
      (fun n => { n with props := n.props.set p new }) P
    cases l with
    | nil =>
      have hrk : c.rows k = some (pick G n.props) := by rw [hrows k, hn]; rfl
      by_cases hp : p ∈ G
      · -- A grouping value changed: the row moves to another group.
        have hg' : groupKey G ((pick G n.props).set p new) = groupKey G (n.props.set p new) := by
          rw [← pick_set_mem hp, groupKey_pick]
        have hrest : ∀ x, c.sizes x - (if x = groupKey G n.props then 1 else 0) =
            (T.filter (·.1 != ([], k))).countP (isMember G x) := by
          intro x
          have := countP_filter_ne hwf.nodup hn (isMember G x)
          rw [isMember_root] at this
          rw [hsizes x]
          by_cases hx : x = groupKey G n.props
          · subst hx; simp only [beq_self_eq_true, ↓reduceIte] at this ⊢; omega
          · have hne : (groupKey G n.props == x) = false := by simpa using Ne.symm hx
            simp only [hne, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at this
            simp [hx, this]
        have hrestg := hrest (groupKey G n.props)
        simp only [↓reduceIte] at hrestg
        refine ⟨?_, ?_, ?_⟩
        · simp only [groupBy.cached, groupBy, hrk, hn, hp, ↓reduceIte, groupKey_pick, hg', hrestg,
            hrest, ← hasMember_iff_countP]
        · intro k'
          simp only [groupBy.cached, hrk, hp, ↓reduceIte, Map.set, get_update]
          by_cases hk : k' = k
          · subst hk; simp [hn, pick_set_mem hp]
          · simp [hk, hrows k']
        · intro x
          simp only [groupBy.cached, hrk, hp, ↓reduceIte, groupKey_pick, hg']
          rw [hrest x]
          have h1 := hcount (isMember G x)
          have hf := countP_filter_ne hwf.nodup hn (isMember G x)
          rw [isMember_root, isMember_root, ite_beq, ite_beq] at h1
          rw [isMember_root, ite_beq] at hf
          simp only at h1
          by_cases hx : x = groupKey G n.props <;> by_cases hx' : x = groupKey G (n.props.set p new) <;>
            simp only [hx, hx', ↓reduceIte] at h1 hf ⊢ <;> omega
      · -- Any other change passes through one level down.
        refine ⟨?_, ?_, ?_⟩
        · simp [groupBy.cached, groupBy, hrk, hn, hp]
        · intro k'
          simp only [groupBy.cached, hrk, hp, ↓reduceIte, get_update]
          by_cases hk : k' = k
          · subst hk; simp [hrows, hn, pick_set_not_mem hp]
          · simp [hk, hrows k']
        · intro x
          simp only [groupBy.cached, hrk, hp, ↓reduceIte]
          have h1 := hcount (isMember G x)
          rw [isMember_root, isMember_root] at h1
          have hsame : groupKey G (n.props.set p new) = groupKey G n.props := by
            rw [← groupKey_pick, pick_set_not_mem hp, groupKey_pick]
          simp only [hsame] at h1
          rw [hsizes x]; omega
    | cons d l =>
      refine ⟨rfl, ?_, ?_⟩
      · intro k'
        simp only [groupBy.cached, get_update]
        simp [hrows k']
      · intro x
        have := hcount (isMember G x)
        rw [isMember_nonroot G x (List.cons_ne_nil d l),
          isMember_nonroot G x (List.cons_ne_nil d l)] at this
        simp only [groupBy.cached]
        rw [hsizes x]; omega
  | placed l k a b =>
    obtain ⟨n, hn, -, -, -, rfl⟩ := apply_placed.mp ha
    have hcount := fun P => countP_update hwf.nodup hn (fun n => { n with parent := some b }) P
    refine ⟨rfl, ?_, ?_⟩
    · intro k'
      simp only [groupBy.cached]
      rw [hrows k', get_update]
      split <;> simp [Option.map_map, Function.comp_def]
    · intro x
      have := hcount (isMember G x)
      have hsame : isMember G x ((l, k), { n with parent := some b }) = isMember G x ((l, k), n) := by
        simp [isMember]
      rw [hsame] at this
      simp only [groupBy.cached]
      rw [hsizes x]; omega

/-! ## Totals as the tree changes -/

theorem sum_filter_ne {T : Tree} (hnd : (T.map (·.1)).Nodup) {id : Id} {n : Node}
    (h : T.get id = some n) (P : Id × Node → Bool) (W : Id × Node → Int) :
    (((T.filter (·.1 != id)).filter P).map W).sum + (if P (id, n) then W (id, n) else 0) =
      ((T.filter P).map W).sum := by
  induction T with
  | nil => simp at h
  | cons x T ih =>
    obtain ⟨id', n'⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [get_cons] at h
    by_cases hx : id' = id
    · subst hx
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      rw [List.filter_cons_of_neg (by simp), filter_ne_of_not_mem hnd.1]
      by_cases hP : P (id', n') = true
      · rw [List.filter_cons_of_pos hP]; simp only [hP, ↓reduceIte, List.map_cons, List.sum_cons]; omega
      · rw [List.filter_cons_of_neg hP]; simp [hP]
    · simp only [hx, ↓reduceIte] at h
      have := ih hnd.2 h
      rw [List.filter_cons_of_pos (by simpa using hx)]
      by_cases hP : P (id', n') = true
      · rw [List.filter_cons_of_pos hP, List.filter_cons_of_pos hP]
        simp only [List.map_cons, List.sum_cons]; omega
      · rw [List.filter_cons_of_neg hP, List.filter_cons_of_neg hP]; exact this

theorem sum_update {T : Tree} (hnd : (T.map (·.1)).Nodup) {id : Id} {n : Node}
    (h : T.get id = some n) (f : Node → Node) (P : Id × Node → Bool) (W : Id × Node → Int) :
    (((T.update id f).filter P).map W).sum + (if P (id, n) then W (id, n) else 0) =
      ((T.filter P).map W).sum + (if P (id, f n) then W (id, f n) else 0) := by
  induction T with
  | nil => simp at h
  | cons x T ih =>
    obtain ⟨id', n'⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [get_cons] at h
    have hcons : Tree.update ((id', n') :: T) id f =
        (if id' = id then (id', f n') else (id', n')) :: Tree.update T id f := by
      simp [Tree.update]
    rw [hcons]
    by_cases hx : id' = id
    · subst hx
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      rw [update_of_not_mem f hnd.1]
      simp only [↓reduceIte]
      by_cases hP : P (id', n') = true <;> by_cases hP' : P (id', f n') = true <;>
        simp only [List.filter_cons, hP, hP', ↓reduceIte, List.map_cons, List.sum_cons,
          Bool.false_eq_true] <;> omega
    · simp only [hx, ↓reduceIte] at h ⊢
      have := ih hnd.2 h
      by_cases hP : P (id', n') = true
      · simp only [List.filter_cons, hP, ↓reduceIte, List.map_cons, List.sum_cons]; omega
      · simp only [List.filter_cons, hP, Bool.false_eq_true, ↓reduceIte]; exact this

/-! ## `sum` and `count` -/

/-- Whether entry `e` contributes to parent `r`'s aggregate. -/
def contributesTo (c : Level) (contributes : Props → Bool) (r : Key) (e : Id × Node) : Bool :=
  decide (e.1.1 = c ∧ e.2.parent = some r ∧ contributes e.2.props)

theorem contributors_eq (c : Level) (contributes : Props → Bool) (T : Tree) (r : Key) :
    contributors c contributes T r = T.filter (contributesTo c contributes r) := rfl

theorem withdraw_count (contributes : Props → Bool) (w : Props → Int) (a : AggCache) (r r' : Key)
    (ps : Props) :
    (a.withdraw contributes w r ps).count r' =
      a.count r' - (if r = r' ∧ contributes ps then 1 else 0) := by
  unfold AggCache.withdraw
  by_cases hc : contributes ps = true
  · by_cases h : r = r'
    · subst h; simp [hc, Map.set]
    · simp [hc, Map.set, h, Ne.symm h]
  · simp [hc]

theorem withdraw_total (contributes : Props → Bool) (w : Props → Int) (a : AggCache) (r r' : Key)
    (ps : Props) :
    (a.withdraw contributes w r ps).total r' =
      a.total r' - (if r = r' ∧ contributes ps then w ps else 0) := by
  unfold AggCache.withdraw
  by_cases hc : contributes ps = true
  · by_cases h : r = r'
    · subst h; simp [hc, Map.set]
    · simp [hc, Map.set, h, Ne.symm h]
  · simp [hc]

theorem deposit_count (contributes : Props → Bool) (w : Props → Int) (a : AggCache) (r r' : Key)
    (ps : Props) :
    (a.deposit contributes w r ps).count r' =
      a.count r' + (if r = r' ∧ contributes ps then 1 else 0) := by
  unfold AggCache.deposit
  by_cases hc : contributes ps = true
  · by_cases h : r = r'
    · subst h; simp [hc, Map.set]
    · simp [hc, Map.set, h, Ne.symm h]
  · simp [hc]

theorem deposit_total (contributes : Props → Bool) (w : Props → Int) (a : AggCache) (r r' : Key)
    (ps : Props) :
    (a.deposit contributes w r ps).total r' =
      a.total r' + (if r = r' ∧ contributes ps then w ps else 0) := by
  unfold AggCache.deposit
  by_cases hc : contributes ps = true
  · by_cases h : r = r'
    · subst h; simp [hc, Map.set]
    · simp [hc, Map.set, h, Ne.symm h]
  · simp [hc]

theorem withdraw_items (contributes : Props → Bool) (w : Props → Int) (a : AggCache) (r : Key)
    (ps : Props) : (a.withdraw contributes w r ps).items = a.items := by
  unfold AggCache.withdraw; split <;> rfl

theorem deposit_items (contributes : Props → Bool) (w : Props → Int) (a : AggCache) (r : Key)
    (ps : Props) : (a.deposit contributes w r ps).items = a.items := by
  unfold AggCache.deposit; split <;> rfl

/-- The cached aggregate is the tree's. -/
theorem value_eq {c : Level} {contributes : Props → Bool} {w : Props → Int} {a : AggCache} {T : Tree}
    (h : a.Describes c contributes w T) (r : Key) : a.value r = aggregate c contributes w T r := by
  unfold AggCache.value aggregate
  rw [h.count r, h.total r]
  split <;> simp_all

theorem contributesTo_at (c : Level) (contributes : Props → Bool) (r : Key) (k : Key) (n : Node) :
    contributesTo c contributes r ((c, k), n) = decide (n.parent = some r ∧ contributes n.props = true) := by
  simp [contributesTo]

theorem contributesTo_other {c l : Level} (contributes : Props → Bool) (r : Key) (k : Key) (n : Node)
    (h : l ≠ c ∨ n.parent = none) : contributesTo c contributes r ((l, k), n) = false := by
  rcases h with h | h <;> simp [contributesTo, h]

section
variable {c : Level} {contributes : Props → Bool} {w : Props → Int} {a : AggCache} {T : Tree}

theorem count_eq (h : a.Describes c contributes w T) (r : Key) :
    a.count r = T.countP (contributesTo c contributes r) := by
  rw [h.count r, contributors_eq, List.countP_eq_length_filter]

theorem total_eq (h : a.Describes c contributes w T) (r : Key) :
    a.total r = ((T.filter (contributesTo c contributes r)).map (fun e : Id × Node => w e.2.props)).sum := by
  rw [h.total r, contributors_eq]

theorem describes_of {a : AggCache} {U : Tree}
    (hi : ∀ k, a.items k = (U.get (c, k)).bind fun n => n.parent.map fun r => (r, n.props))
    (hc : ∀ r, a.count r = U.countP (contributesTo c contributes r))
    (ht : ∀ r, a.total r = ((U.filter (contributesTo c contributes r)).map (fun e : Id × Node => w e.2.props)).sum) :
    a.Describes c contributes w U :=
  ⟨hi, fun r => by rw [hc r, contributors_eq, List.countP_eq_length_filter],
    fun r => by rw [ht r, contributors_eq]⟩

/-- A node that is not a contributing child arrives: nothing changes. -/
theorem describes_cons_other (h : a.Describes c contributes w T) {l : Level} {k : Key} {n : Node}
    (hn : T.get (l, k) = none) (hl : l ≠ c ∨ n.parent = none) :
    a.Describes c contributes w (((l, k), n) :: T) := by
  refine describes_of (fun k' => ?_) (fun r => ?_) (fun r => ?_)
  · rw [h.items k', get_cons]
    split
    · rename_i heq
      obtain ⟨hlc, hk⟩ := Prod.mk.inj heq
      subst hlc hk
      rcases hl with hl | hl
      · exact absurd rfl hl
      · simp [hn, hl]
    · rfl
  · rw [count_eq h, List.countP_cons, contributesTo_other _ _ _ _ hl]; simp
  · rw [total_eq h, List.filter_cons, contributesTo_other _ _ _ _ hl]; simp

/-- A child arrives under parent `r`, and contributes to it. -/
theorem describes_cons_child (h : a.Describes c contributes w T) {k r : Key} {ps : Props}
    (hn : T.get (c, k) = none) :
    ({ a.deposit contributes w r ps with items := Map.set a.items k (some (r, ps)) } : AggCache).Describes
      c contributes w (((c, k), ⟨some r, ps⟩) :: T) := by
  refine describes_of (fun k' => ?_) (fun r' => ?_) (fun r' => ?_)
  · simp only [Map.set, get_cons, Prod.mk.injEq, true_and]
    by_cases hk : k' = k
    · subst hk; simp
    · simp [hk, Ne.symm hk, h.items k']
  · simp only [deposit_count, count_eq h, List.countP_cons, contributesTo_at]
    by_cases hr : r = r' <;> by_cases hc : contributes ps = true <;> simp [hr, hc] <;> omega
  · simp only [deposit_total, total_eq h, List.filter_cons, contributesTo_at]
    by_cases hr : r = r' <;> by_cases hc : contributes ps = true <;> simp [hr, hc] <;> omega

/-- A node that is not a contributing child leaves: nothing changes. -/
theorem describes_filter_other (h : a.Describes c contributes w T) (hnd : (T.map (·.1)).Nodup)
    {l : Level} {k : Key} {n : Node} (hn : T.get (l, k) = some n) (hl : l ≠ c ∨ n.parent = none) :
    a.Describes c contributes w (T.filter (·.1 != (l, k))) := by
  refine describes_of (fun k' => ?_) (fun r => ?_) (fun r => ?_)
  · rw [h.items k', get_filter]
    split
    · rename_i heq
      obtain ⟨hlc, hk⟩ := Prod.mk.inj heq
      subst hlc hk
      rcases hl with hl | hl
      · exact absurd rfl hl
      · simp [hn, hl]
    · rfl
  · have := countP_filter_ne hnd hn (contributesTo c contributes r)
    rw [contributesTo_other _ _ _ _ hl] at this
    rw [count_eq h]; simpa using this.symm
  · have := sum_filter_ne hnd hn (contributesTo c contributes r) (fun e : Id × Node => w e.2.props)
    rw [contributesTo_other _ _ _ _ hl] at this
    rw [total_eq h]; simpa using this.symm

/-- Child `k` under parent `r` leaves, and its contribution with it. -/
theorem describes_filter_child (h : a.Describes c contributes w T) (hnd : (T.map (·.1)).Nodup)
    {k r : Key} {n : Node} (hn : T.get (c, k) = some n) (hp : n.parent = some r) :
    ({ a.withdraw contributes w r n.props with items := Map.set a.items k none } : AggCache).Describes
      c contributes w (T.filter (·.1 != (c, k))) := by
  refine describes_of (fun k' => ?_) (fun r' => ?_) (fun r' => ?_)
  · simp only [Map.set, get_filter, Prod.mk.injEq, true_and]
    by_cases hk : k' = k
    · subst hk; simp
    · simp [hk, h.items k']
  · have := countP_filter_ne hnd hn (contributesTo c contributes r')
    rw [contributesTo_at, hp] at this
    simp only [withdraw_count, count_eq h]
    by_cases hr : r = r' <;> by_cases hc : contributes n.props = true <;> simp [hr, hc] at this ⊢ <;> omega
  · have := sum_filter_ne hnd hn (contributesTo c contributes r') (fun e : Id × Node => w e.2.props)
    rw [contributesTo_at, hp] at this
    simp only [withdraw_total, total_eq h]
    by_cases hr : r = r' <;> by_cases hc : contributes n.props = true <;> simp [hr, hc] at this ⊢ <;> omega

/-- A node that is not a contributing child changes: nothing changes. -/
theorem describes_update_other (h : a.Describes c contributes w T) (hnd : (T.map (·.1)).Nodup)
    {l : Level} {k : Key} {n : Node} (hn : T.get (l, k) = some n) (f : Node → Node)
    (hl : l ≠ c ∨ (n.parent = none ∧ (f n).parent = none)) :
    a.Describes c contributes w (T.update (l, k) f) := by
  have h1 : l ≠ c ∨ n.parent = none := hl.imp id (·.1)
  have h2 : l ≠ c ∨ (f n).parent = none := hl.imp id (·.2)
  refine describes_of (fun k' => ?_) (fun r => ?_) (fun r => ?_)
  · rw [h.items k', get_update]
    split
    · rename_i heq
      obtain ⟨hlc, hk⟩ := Prod.mk.inj heq
      subst hlc hk
      rcases hl with hl | hl
      · exact absurd rfl hl
      · simp [hn, hl.1, hl.2]
    · rfl
  · have := countP_update hnd hn f (contributesTo c contributes r)
    rw [contributesTo_other _ _ _ _ h1, contributesTo_other _ _ _ _ h2] at this
    rw [count_eq h]; simpa using this.symm
  · have := sum_update hnd hn f (contributesTo c contributes r) (fun e : Id × Node => w e.2.props)
    rw [contributesTo_other _ _ _ _ h1, contributesTo_other _ _ _ _ h2] at this
    rw [total_eq h]; simpa using this.symm

/-- Child `k` changes or moves, from parent `r` to `(f n)`'s parent `r'`: its old
contribution is withdrawn and its new one deposited. -/
theorem describes_update_child (h : a.Describes c contributes w T) (hnd : (T.map (·.1)).Nodup)
    {k r r' : Key} {n : Node} (hn : T.get (c, k) = some n) (hp : n.parent = some r) (f : Node → Node)
    (hp' : (f n).parent = some r') :
    ({ (a.withdraw contributes w r n.props).deposit contributes w r' (f n).props with
        items := Map.set a.items k (some (r', (f n).props)) } : AggCache).Describes
      c contributes w (T.update (c, k) f) := by
  refine describes_of (fun k' => ?_) (fun x => ?_) (fun x => ?_)
  · simp only [Map.set, get_update, Prod.mk.injEq, true_and]
    by_cases hk : k' = k
    · subst hk; simp [hn, hp']
    · simp [hk, h.items k']
  · have := countP_update hnd hn f (contributesTo c contributes x)
    have hpos := countP_filter_ne hnd hn (contributesTo c contributes x)
    rw [contributesTo_at, contributesTo_at, hp, hp'] at this
    rw [contributesTo_at, hp] at hpos
    simp only [deposit_count, withdraw_count, count_eq h]
    by_cases hr : r = x <;> by_cases hr' : r' = x <;> by_cases hc : contributes n.props = true <;>
      by_cases hc' : contributes (f n).props = true <;> simp [hr, hr', hc, hc'] at this hpos ⊢ <;> omega
  · have := sum_update hnd hn f (contributesTo c contributes x) (fun e : Id × Node => w e.2.props)
    rw [contributesTo_at, contributesTo_at, hp, hp'] at this
    simp only [deposit_total, withdraw_total, total_eq h]
    by_cases hr : r = x <;> by_cases hr' : r' = x <;> by_cases hc : contributes n.props = true <;>
      by_cases hc' : contributes (f n).props = true <;> simp [hr, hr', hc, hc'] at this ⊢ <;> omega

end

theorem dropLast_eq_self {c : Level} (h : c.dropLast = c) : c = [] := by
  have := congrArg List.length h
  simp at this
  exact List.length_eq_zero_iff.mp (by omega)

/-- A root node has no parent. -/
theorem parent_root {T : Tree} (hwf : T.WF) {k : Key} {n : Node} (h : T.get ([], k) = some n) :
    n.parent = none := by
  have := hwf.parents _ _ h
  cases hp : n.parent with
  | none => rfl
  | some r => rw [hp] at this; simp [Tree.parentOk] at this

/-- **`aggregate_implements`.** The aggregate's cache, each child's parent and
values and each parent's count and total, implements the aggregate. -/
theorem aggregate_implements (c : Level) (q : String) (contributes : Props → Bool) (w : Props → Int) :
    Implements (aggregate.cached c q contributes w) (aggregateStep c q contributes w)
      (AggCache.Describes c contributes w) := by
  refine ⟨⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩, ?_⟩
  intro a T e T' hR hwf ha
  have hnd := hwf.nodup
  cases e with
  | added l k p ps =>
    obtain ⟨hn, hp, rfl⟩ := apply_added.mp ha
    by_cases h1 : l = c.dropLast
    · -- A parent arrives, with its aggregate.
      have hother : l ≠ c ∨ (⟨p, ps⟩ : Node).parent = none := by
        by_cases hlc : l = c
        · subst hlc
          have := dropLast_eq_self h1.symm
          subst this
          right; cases p with
          | none => rfl
          | some => simp [Tree.parentOk] at hp
        · exact Or.inl hlc
      subst h1
      have hR' := describes_cons_other hR hn hother
      refine ⟨?_, by simpa [aggregate.cached] using hR'⟩
      simp only [aggregate.cached, aggregateStep, ha, ↓reduceIte, value_eq hR']
    · by_cases h2 : l = c
      · -- A child arrives under its parent.
        subst h2
        obtain ⟨r, rfl⟩ : ∃ r, p = some r := by
          cases p with
          | some r => exact ⟨r, rfl⟩
          | none =>
            have : l = [] := by simpa [Tree.parentOk] using hp
            subst this; exact absurd rfl h1
        have hR' := describes_cons_child (r := r) (ps := ps) hR hn
        refine ⟨?_, by simpa [aggregate.cached, h1] using hR'⟩
        simp only [aggregate.cached, aggregateStep, ha, h1, ↓reduceIte, Option.toList_some,
          List.flatMap_singleton, ← value_eq hR, ← value_eq hR']
      · have hR' := describes_cons_other (n := ⟨p, ps⟩) hR hn (Or.inl h2)
        refine ⟨?_, by simpa [aggregate.cached, h1, h2] using hR'⟩
        simp [aggregate.cached, aggregateStep, ha, h1, h2]
  | removed l k =>
    obtain ⟨hs, -, rfl⟩ := apply_removed.mp ha
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
    by_cases h2 : l = c
    · subst h2
      cases hpar : n.parent with
      | none =>
        have hik : a.items k = none := by rw [hR.items k, hn]; simp [hpar]
        have hR' := describes_filter_other hR hnd hn (Or.inr hpar)
        refine ⟨?_, by simpa [aggregate.cached, hik] using hR'⟩
        simp [aggregate.cached, aggregateStep, ha, hik, hn, hpar]
      | some r =>
        have hik : a.items k = some (r, n.props) := by rw [hR.items k, hn]; simp [hpar]
        have hR' := describes_filter_child hR hnd hn hpar
        refine ⟨?_, by simpa [aggregate.cached, hik] using hR'⟩
        simp only [aggregate.cached, aggregateStep, ha, hik, hn, hpar, ↓reduceIte, Option.bind_some,
          Option.toList_some, List.flatMap_singleton, ← value_eq hR, ← value_eq hR']
    · have hR' := describes_filter_other hR hnd hn (Or.inl h2)
      refine ⟨?_, by simpa [aggregate.cached, h2] using hR'⟩
      simp [aggregate.cached, aggregateStep, ha, h2]
  | modified l k p old new =>
    obtain ⟨n, hn, -, -, rfl⟩ := apply_modified.mp ha
    by_cases h1 : l = c.dropLast ∧ p = q
    · -- A change to the aggregate itself, from upstream, is hidden.
      have hother : l ≠ c ∨ (n.parent = none ∧ n.parent = none) := by
        by_cases hlc : l = c
        · subst hlc
          have := dropLast_eq_self h1.1.symm
          subst this
          have := parent_root hwf hn
          exact Or.inr ⟨this, this⟩
        · exact Or.inl hlc
      have hR' := describes_update_other hR hnd hn (fun n : Node => { n with props := n.props.set p new }) hother
      obtain ⟨rfl, rfl⟩ := h1
      refine ⟨?_, by simpa [aggregate.cached] using hR'⟩
      simp [aggregate.cached, aggregateStep, ha]
    · by_cases h2 : l = c
      · subst h2
        cases hpar : n.parent with
        | none =>
          have hik : a.items k = none := by rw [hR.items k, hn]; simp [hpar]
          have hR' := describes_update_other hR hnd hn (fun n : Node => { n with props := n.props.set p new }) (Or.inr ⟨hpar, hpar⟩)
          refine ⟨?_, by simpa [aggregate.cached, h1, hik] using hR'⟩
          simp [aggregate.cached, aggregateStep, ha, h1, hik, hn, hpar]
        | some r =>
          have hik : a.items k = some (r, n.props) := by rw [hR.items k, hn]; simp [hpar]
          have hR' := describes_update_child hR hnd hn hpar (fun n : Node => { n with props := n.props.set p new }) hpar
          refine ⟨?_, by simpa [aggregate.cached, h1, hik] using hR'⟩
          simp only [aggregate.cached, aggregateStep, ha, h1, hik, hn, hpar, ↓reduceIte,
            Option.bind_some, Option.toList_some, List.flatMap_singleton, ← value_eq hR, ← value_eq hR']
      · have hR' := describes_update_other hR hnd hn (fun n : Node => { n with props := n.props.set p new }) (Or.inl h2)
        refine ⟨?_, by simpa [aggregate.cached, h1, h2] using hR'⟩
        simp [aggregate.cached, aggregateStep, ha, h1, h2]
  | placed l k x y =>
    obtain ⟨n, hn, hpa, -, -, rfl⟩ := apply_placed.mp ha
    by_cases h2 : l = c
    · subst h2
      have hik : a.items k = some (x, n.props) := by rw [hR.items k, hn]; simp [hpa]
      have hR' := describes_update_child hR hnd hn hpa (fun n : Node => { n with parent := some y }) rfl
      refine ⟨?_, by simpa [aggregate.cached, hik] using hR'⟩
      simp only [aggregate.cached, aggregateStep, ha, hik, ↓reduceIte, ← value_eq hR, ← value_eq hR']
    · have hR' := describes_update_other hR hnd hn (fun n : Node => { n with parent := some y }) (Or.inl h2)
      refine ⟨?_, by simpa [aggregate.cached, h2] using hR'⟩
      simp [aggregate.cached, aggregateStep, ha, h2]

/-! ## `defineProperty` -/

theorem set_comm {a b : String} (h : a ≠ b) (ps : Props) (u v : Option Val) :
    (ps.set a u).set b v = (ps.set b v).set a u := by
  funext x
  by_cases hb : x = b
  · subst hb; simp [Props.set, Ne.symm h]
  · by_cases ha : x = a
    · subst ha; simp [Props.set, h]
    · simp [Props.set, ha, hb]

/-- A function that reads only `deps` ignores changes to other properties. -/
theorem setAll_unlisted {f : Props → Option Val} {deps : List String}
    (hdeps : ∀ ps p v, p ∉ deps → f (ps.set p v) = f ps) (ps : Props) :
    ∀ changes : List (String × Option Val), (∀ x ∈ changes, x.1 ∉ deps) → f (ps.setAll changes) = f ps := by
  intro changes
  induction changes with
  | nil => intro _; rfl
  | cons x changes ih =>
    intro h
    simp only [Props.setAll, List.foldr_cons] at ih ⊢
    rw [hdeps _ _ _ (h x (List.mem_cons_self ..))]
    exact ih fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem setAll_set (ps : Props) (p : String) (v : Option Val) :
    ∀ changes : List (String × Option Val), (∀ x ∈ changes, x.1 ≠ p) →
      (ps.setAll changes).set p v = (ps.set p v).setAll changes := by
  intro changes
  induction changes with
  | nil => intro _; rfl
  | cons x changes ih =>
    intro h
    simp only [Props.setAll, List.foldr_cons] at ih ⊢
    rw [set_comm (h x (List.mem_cons_self ..)), ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **`defineProperty_implements`.** `defineProperty`'s cache, the values it
knows of each node and its computed value, implements `defineProperty`, under
the contract its correctness has: `f` reads only `deps`, and `q` is not one of
them. The cache tracks only changes to `deps`; the contract is what makes that
enough. -/
theorem defineProperty_implements (s : Level) (q : String) (f : Props → Option Val)
    (deps : List String) (hq : q ∉ deps) (hdeps : ∀ ps p v, p ∉ deps → f (ps.set p v) = f ps) :
    Implements (defineProperty.cached s q f deps) (defineProperty s q f deps)
      (DefineCache.Describes s f deps) := by
  refine ⟨⟨fun _ _ => rfl, fun _ _ h => by simp at h⟩, ?_⟩
  intro d T e T' hR hwf ha
  obtain ⟨habs, hpres⟩ := hR
  cases e with
  | added l k p ps =>
    obtain ⟨hn, -, rfl⟩ := apply_added.mp ha
    by_cases hl : l = s
    · subst hl
      refine ⟨by simp [defineProperty.cached, defineProperty], ?_, ?_⟩
      · intro k' h
        simp only [defineProperty.cached, ↓reduceIte, Map.set]
        rw [get_cons] at h
        by_cases hk : k' = k
        · subst hk; simp at h
        · simp only [Prod.mk.injEq, true_and, Ne.symm hk, ↓reduceIte] at h
          simp [hk, habs k' h]
      · intro k' n h
        simp only [defineProperty.cached, ↓reduceIte, Map.set]
        rw [get_cons] at h
        by_cases hk : k' = k
        · subst hk; simp at h; subst h
          exact ⟨ps, [], by simp, by simp, rfl⟩
        · simp only [Prod.mk.injEq, true_and, Ne.symm hk, ↓reduceIte] at h
          simpa [hk] using hpres k' n h
    · have hne : ∀ k', (l, k) ≠ (s, k') := fun k' h => hl (Prod.mk.inj h).1
      refine ⟨by simp [defineProperty.cached, defineProperty, hl], ?_, ?_⟩
      · intro k' h; rw [get_cons, ite_eq_right (hne k')] at h
        simpa [defineProperty.cached, hl] using habs k' h
      · intro k' n h; rw [get_cons, ite_eq_right (hne k')] at h
        simpa [defineProperty.cached, hl] using hpres k' n h
  | removed l k =>
    obtain ⟨-, -, rfl⟩ := apply_removed.mp ha
    by_cases hl : l = s
    · subst hl
      refine ⟨by simp [defineProperty.cached, defineProperty], ?_, ?_⟩
      · intro k' h
        simp only [defineProperty.cached, ↓reduceIte, Map.set]
        by_cases hk : k' = k
        · simp [hk]
        · rw [get_filter, ite_eq_right (by simpa using hk)] at h
          simp [hk, habs k' h]
      · intro k' n h
        simp only [defineProperty.cached, ↓reduceIte, Map.set]
        by_cases hk : k' = k
        · subst hk; rw [get_filter] at h; simp at h
        · rw [get_filter, ite_eq_right (by simpa using hk)] at h
          simpa [hk] using hpres k' n h
    · have hne : ∀ k', (s, k') ≠ (l, k) := fun k' h => hl (Prod.mk.inj h).1.symm
      refine ⟨by simp [defineProperty.cached, defineProperty, hl], ?_, ?_⟩
      · intro k' h; rw [get_filter, ite_eq_right (hne k')] at h
        simpa [defineProperty.cached, hl] using habs k' h
      · intro k' n h; rw [get_filter, ite_eq_right (hne k')] at h
        simpa [defineProperty.cached, hl] using hpres k' n h
  | modified l k p old new =>
    obtain ⟨n, hn, -, -, rfl⟩ := apply_modified.mp ha
    by_cases hl : l = s
    · subst hl
      obtain ⟨known, changes, hi, hch, hprops⟩ := hpres k n hn
      -- What the tree holds after an unlisted change: one more unlisted change.
      have unlisted : p ∉ deps → DefineCache.Describes l f deps d
          (T.update (l, k) fun n => { n with props := n.props.set p new }) := by
        intro hp
        refine ⟨fun k' h => ?_, fun k' n' h => ?_⟩
        · rw [get_update] at h
          split at h
          · rename_i heq; obtain ⟨-, rfl⟩ := Prod.mk.inj heq; simp [hn] at h
          · exact habs k' h
        · rw [get_update] at h
          split at h
          · rename_i heq
            obtain ⟨-, rfl⟩ := Prod.mk.inj heq
            simp [hn] at h; subst h
            refine ⟨known, (p, new) :: changes, ?_, ?_, ?_⟩
            · rw [hi, hdeps _ _ _ hp]
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hp
              · exact hch x hx
            · simp [Props.setAll, hprops]
          · exact hpres k' n' h
      by_cases hpq : p = q
      · subst hpq
        refine ⟨by simp [defineProperty.cached, defineProperty], ?_⟩
        simpa [defineProperty.cached] using unlisted hq
      · by_cases hp : p ∈ deps
        · -- A listed change: recompute from the known values.
          have hafter : f (n.props.set p new) = f (known.set p new) := by
            rw [hprops, setAll_set _ _ _ _ (fun x hx h => hch x hx (h ▸ hp)),
              setAll_unlisted hdeps _ _ hch]
          refine ⟨?_, ?_, ?_⟩
          · simp [defineProperty.cached, defineProperty, hpq, hi, hp, hn, hafter]
          · intro k' h
            simp only [defineProperty.cached, hpq, hi, hp, ↓reduceIte, Map.set]
            rw [get_update] at h
            split at h
            · rename_i heq; obtain ⟨-, rfl⟩ := Prod.mk.inj heq; simp [hn] at h
            · rename_i hne
              have hk : k' ≠ k := fun h => hne (by rw [h])
              simp [hk, habs k' h]
          · intro k' n' h
            simp only [defineProperty.cached, hpq, hi, hp, ↓reduceIte, Map.set]
            rw [get_update] at h
            split at h
            · rename_i heq
              obtain ⟨-, rfl⟩ := Prod.mk.inj heq
              simp [hn] at h; subst h
              refine ⟨known.set p new, changes, by simp [hafter], hch, ?_⟩
              simp only
              rw [hprops, setAll_set _ _ _ _ (fun x hx h => hch x hx (h ▸ hp))]
            · rename_i hne
              have hk : k' ≠ k := fun h => hne (by rw [h])
              simpa [hk] using hpres k' n' h
        · refine ⟨by simp [defineProperty.cached, defineProperty, hpq, hi, hp, hn], ?_⟩
          simpa [defineProperty.cached, hpq, hi, hp] using unlisted hp
    · have hne : ∀ k', (s, k') ≠ (l, k) := fun k' h => hl (Prod.mk.inj h).1.symm
      refine ⟨by simp [defineProperty.cached, defineProperty, hl], ?_, ?_⟩
      · intro k' h; rw [get_update, ite_eq_right (hne k')] at h
        simpa [defineProperty.cached, hl] using habs k' h
      · intro k' n' h; rw [get_update, ite_eq_right (hne k')] at h
        simpa [defineProperty.cached, hl] using hpres k' n' h
  | placed l k a b =>
    obtain ⟨n, hn, -, -, -, rfl⟩ := apply_placed.mp ha
    refine ⟨rfl, fun k' h => ?_, fun k' n' h => ?_⟩
    · rw [get_update] at h
      split at h
      · rename_i heq; rw [← heq] at hn; simp [hn] at h
      · exact habs k' h
    · rw [get_update] at h
      split at h
      · rename_i heq
        rw [← heq] at hn
        simp [hn] at h; subst h
        exact hpres k' n hn
      · exact hpres k' n' h

/-! ## The cached steps are correct -/

/-- **`groupBy_cached_correct`.** -/
theorem groupBy_cached_correct (G : List String) (C : String) {es : List Event} {T' : Tree}
    (h : Tree.applyAll [] es = some T') :
    ∃ U, (groupBy.F G C []).applyAll ((groupBy.cached G C).run (groupBy.cached G C).init es) = some U ∧
      U.Equiv (groupBy.F G C T') :=
  implements_correct (groupBy_implements G C) (groupBy_correct G C) (groupBy_denotation G C) h

/-- **`aggregate_cached_correct`.** -/
theorem aggregate_cached_correct (c : Level) (hc : c ≠ []) (q : String) (contributes : Props → Bool)
    (w : Props → Int) {es : List Event} {T' : Tree} (h : Tree.applyAll [] es = some T') :
    ∃ U, (aggregate.F c q contributes w []).applyAll
        ((aggregate.cached c q contributes w).run (aggregate.cached c q contributes w).init es) = some U ∧
      U.Equiv (aggregate.F c q contributes w T') :=
  implements_correct (aggregate_implements c q contributes w) (aggregate_correct c hc q contributes w)
    (aggregate_denotation c q contributes w) h

/-- **`defineProperty_cached_correct`.** -/
theorem defineProperty_cached_correct (s : Level) (q : String) (f : Props → Option Val)
    (deps : List String) (hq : q ∉ deps) (hdeps : ∀ ps p v, p ∉ deps → f (ps.set p v) = f ps)
    {es : List Event} {T' : Tree} (h : Tree.applyAll [] es = some T') :
    ∃ U, (defineProperty.F s q f []).applyAll
        ((defineProperty.cached s q f deps).run (defineProperty.cached s q f deps).init es) = some U ∧
      U.Equiv (defineProperty.F s q f T') :=
  implements_correct (defineProperty_implements s q f deps hq hdeps)
    (defineProperty_correct s q f deps hq hdeps) (defineProperty_denotation s q f) h

end JinagaSpec.Cascade
