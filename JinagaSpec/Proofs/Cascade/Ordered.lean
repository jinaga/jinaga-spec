import JinagaSpec.Cascade.Ordered
import JinagaSpec.Proofs.Cascade.Aggregate
import JinagaSpec.Proofs.Cascade.Sig

/-!
# Cascade: steps over ordered siblings

`overlay_correct`: forwarding each event, then emitting a change for each node
whose computed value changed, keeps the output equal to `overlay.F`, whatever
the values are. `overlay_denotation`: the output ignores the order of the
tree's list when the values do.

`cumulativeSum` and `replaceToDelta` are instances. Their values ignore list
order (`cumulativeSum_denotation`, and `replaceToDelta_denotation` under a
strict total order), and they are what the TypeScript computes from its sorted
list (`prefix_of_sorted`, `latest_of_sorted`).
-/
namespace JinagaSpec.Cascade

variable {c : Level} {Q : List String} {val : Tree → Key → String → Option Val}

/-! ## `overlay` -/

theorem overlay_set_mem {x : String} (hx : x ∈ Q) (v : String → Option Val) (ps : Props)
    (w : Option Val) : overlay Q v (ps.set x w) = overlay Q v ps := by
  funext y
  by_cases hy : y ∈ Q
  · simp [overlay, hy]
  · have : y ≠ x := fun h => hy (h ▸ hx)
    simp [overlay, hy, Props.set, this]

theorem overlay_set_not_mem {x : String} (hx : x ∉ Q) (v : String → Option Val) (ps : Props)
    (w : Option Val) : overlay Q v (ps.set x w) = (overlay Q v ps).set x w := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [overlay, Props.set, hx]
  · simp [overlay, Props.set, hy]

theorem overlay_overlay (v w : String → Option Val) (ps : Props) :
    overlay Q v (overlay Q w ps) = overlay Q v ps := by
  funext y
  by_cases hy : y ∈ Q <;> simp [overlay, hy]

theorem overlay_denotation (hval : ∀ T U, T.WF → U.WF → T.Equiv U → val T = val U) :
    Denotation (overlay.F c Q val) := by
  refine ⟨fun _ hT => mapProps_wf hT, fun T U hT hU h id => ?_⟩
  simp only [overlay.F, get_mapProps, h id, hval T U hT hU h]

/-! ## The event, forwarded -/

/-- The props of a node at `c` between the forwarded event and the changes: the
values in `T` for a node that was there, and in `T'` for one that arrives. -/
def mixed (c : Level) (Q : List String) (val : Tree → Key → String → Option Val) (T T' : Tree) :
    Key → Props → Props :=
  fun k ps => overlay Q (if (T.get (c, k)).isSome then val T k else val T' k) ps

/-- What `overlayStep` forwards. -/
def forward (c : Level) (Q : List String) (val : Tree → Key → String → Option Val) (T' : Tree) :
    Event → List Event
  | .added l k p ps => [.added l k p (if l = c then overlay Q (val T' k) ps else ps)]
  | .modified l k x old new => if l = c ∧ x ∈ Q then [] else [.modified l k x old new]
  | e => [e]

theorem overlayStep_handle {T T' : Tree} {e : Event} (he : T.apply e = some T') :
    (overlayStep c Q val).handle T e = forward c Q val T' e ++ resync c Q val T T' := by
  simp only [overlayStep, he]
  cases e <;> rfl

theorem mixed_before (T T' : Tree) :
    (overlay.F c Q val T).Equiv (T.mapProps c (mixed c Q val T T')) := by
  intro id
  obtain ⟨l, k⟩ := id
  simp only [overlay.F, get_mapProps]
  cases hg : T.get (l, k) with
  | none => rfl
  | some n =>
    by_cases hl : l = c
    · subst hl; simp [mapNode, mixed, hg]
    · simp [mapNode, hl]

theorem forward_correct {T T' : Tree} {e : Event} (hwf : T.WF) (he : T.apply e = some T') :
    ∃ U, (T.mapProps c (mixed c Q val T T')).applyAll (forward c Q val T' e) = some U ∧
      U.Equiv (T'.mapProps c (mixed c Q val T T')) := by
  cases e with
  | added l k p ps =>
    by_cases hl : l = c
    · subst hl
      have hn := (apply_added.mp he).1
      obtain ⟨U, hU, hE⟩ := mapProps_added (φ := mixed l Q val T T') he
      refine ⟨U, ?_, hE⟩
      simpa [forward, applyAll_single, mixed, hn] using hU
    · obtain ⟨U, hU, hE⟩ := mapProps_forward (s := c) (φ := mixed c Q val T T') hwf he
        (by simp [Event.propsLevel, hl])
      exact ⟨U, by simpa [forward, hl, applyAll_single] using hU, hE⟩
  | removed l k =>
    obtain ⟨U, hU, hE⟩ := mapProps_forward (s := c) (φ := mixed c Q val T T') hwf he
      (by simp [Event.propsLevel])
    exact ⟨U, by simpa [forward, applyAll_single] using hU, hE⟩
  | modified l k x old new =>
    by_cases h : l = c ∧ x ∈ Q
    · obtain ⟨rfl, hx⟩ := h
      refine ⟨T.mapProps l (mixed l Q val T T'), by simp [forward, hx, Tree.applyAll], ?_⟩
      exact mapProps_hidden he fun ps => overlay_set_mem hx _ ps _
    · by_cases hl : l = c
      · subst hl
        have hx : x ∉ Q := fun hx => h ⟨rfl, hx⟩
        obtain ⟨U, hU, hE⟩ := mapProps_modified (φ := mixed l Q val T T') he
          (fun ps => by simp [mixed, overlay, hx]) (fun ps => overlay_set_not_mem hx _ ps _)
        exact ⟨U, by simpa [forward, hx, applyAll_single] using hU, hE⟩
      · obtain ⟨U, hU, hE⟩ := mapProps_forward (s := c) (φ := mixed c Q val T T') hwf he
          (by simp [Event.propsLevel, hl])
        exact ⟨U, by simpa [forward, hl, applyAll_single] using hU, hE⟩
  | placed l k a b =>
    obtain ⟨U, hU, hE⟩ := mapProps_forward (s := c) (φ := mixed c Q val T T') hwf he
      (by simp [Event.propsLevel])
    exact ⟨U, by simpa [forward, applyAll_single] using hU, hE⟩

/-! ## The changes -/

/-- The changes to one node: each name in `L` whose value differs. -/
theorem applyAll_node {k : Key} {a b : String → Option Val} :
    ∀ (L : List String) (V : Tree) (m : Node), L.Nodup → V.get (c, k) = some m →
      (∀ x ∈ L, m.props x = a x) →
      ∃ V', V.applyAll (L.filterMap fun x =>
          if a x = b x then none else some (.modified c k x (a x) (b x))) = some V' ∧
        ∀ id, V'.get id = if id = (c, k)
          then some { m with props := fun x => if x ∈ L then b x else m.props x } else V.get id := by
  intro L
  induction L with
  | nil => intro V m _ hm _; exact ⟨V, rfl, fun id => by split <;> simp_all⟩
  | cons x L ih =>
    intro V m hnd hm hx
    simp only [List.nodup_cons] at hnd
    by_cases hxe : a x = b x
    · obtain ⟨V', hV', hget⟩ := ih V m hnd.2 hm fun y hy => hx y (List.mem_cons_of_mem _ hy)
      refine ⟨V', by simpa [List.filterMap_cons, hxe] using hV', fun id => ?_⟩
      rw [hget]
      split
      · congr 2; funext y
        by_cases hy : y = x
        · subst hy; simp [hnd.1, hx y (List.mem_cons_self ..), hxe]
        · simp [hy]
      · rfl
    · let m1 : Node := { m with props := m.props.set x (b x) }
      have h1 : V.apply (.modified c k x (a x) (b x)) =
          some (V.update (c, k) fun m => { m with props := m.props.set x (b x) }) :=
        apply_modified.mpr ⟨m, hm, hx x (List.mem_cons_self ..), hxe, rfl⟩
      have hm1 : (V.update (c, k) fun m => { m with props := m.props.set x (b x) }).get (c, k) =
          some m1 := by rw [get_update]; simp [hm, m1]
      obtain ⟨V', hV', hget⟩ := ih _ m1 hnd.2 hm1 fun y hy => by
        have : y ≠ x := fun h => hnd.1 (h ▸ hy)
        simp [m1, Props.set, this, hx y (List.mem_cons_of_mem _ hy)]
      refine ⟨V', by simp [hxe, Tree.applyAll, h1, hV'], fun id => ?_⟩
      rw [hget, get_update]
      by_cases hid : id = (c, k)
      · subst hid
        simp only [↓reduceIte, Option.some.injEq]
        congr 1; funext y
        by_cases hy : y = x
        · subst hy; simp [m1, Props.set, hnd.1]
        · simp [m1, Props.set, hy]
      · simp [hid]

/-- The changes to each node in `ks`. -/
theorem applyAll_nodes {a b : Key → String → Option Val} :
    ∀ (ks : List Key) (V : Tree), ks.Nodup →
      (∀ k ∈ ks, ∃ m, V.get (c, k) = some m ∧ ∀ x ∈ Q, m.props x = a k x) →
      ∃ V', V.applyAll (ks.flatMap fun k => (dedup Q).filterMap fun x =>
          if a k x = b k x then none else some (.modified c k x (a k x) (b k x))) = some V' ∧
        ∀ id, V'.get id = if id.1 = c ∧ id.2 ∈ ks
          then (V.get id).map (fun m => { m with props := overlay Q (b id.2) m.props })
          else V.get id := by
  intro ks
  induction ks with
  | nil => intro V _ _; exact ⟨V, rfl, fun id => by simp⟩
  | cons k ks ih =>
    intro V hnd hks
    simp only [List.nodup_cons] at hnd
    obtain ⟨m, hm, hmx⟩ := hks k (List.mem_cons_self ..)
    obtain ⟨V1, hV1, hget1⟩ := applyAll_node (a := a k) (b := b k) (dedup Q) V m (nodup_dedup Q) hm
      fun x hx => hmx x (mem_dedup.mp hx)
    obtain ⟨V', hV', hget⟩ := ih V1 hnd.2 fun k' hk' => by
      have hne : (c, k') ≠ (c, k) := fun h => hnd.1 (by cases h; exact hk')
      rw [hget1]; simp only [hne, ↓reduceIte]
      exact hks k' (List.mem_cons_of_mem _ hk')
    refine ⟨V', by rw [List.flatMap_cons, applyAll_append, hV1]; exact hV', fun id => ?_⟩
    rw [hget, hget1]
    obtain ⟨l, k0⟩ := id
    by_cases hl : l = c
    · subst hl
      by_cases hk : k0 = k
      · subst hk
        simp only [hnd.1, and_false, ↓reduceIte, List.mem_cons, true_or, and_self, hm,
          Option.map_some, Option.some.injEq]
        congr 1; funext y; simp [overlay, mem_dedup]
      · have hne : (l, k0) ≠ (l, k) := fun h => hk (by cases h; rfl)
        simp [hne, hk]
    · simp [hl]

/-- The nodes `resync` changes. -/
def resync.keys (c : Level) (T T' : Tree) : List Key :=
  (T'.filter fun e => e.1.1 = c ∧ (T.get e.1).isSome).map (·.1.2)

theorem mem_resync_keys {T T' : Tree} (hnd : (T'.map (·.1)).Nodup) {k : Key} :
    k ∈ resync.keys c T T' ↔ (T'.get (c, k)).isSome ∧ (T.get (c, k)).isSome := by
  simp only [resync.keys, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨l, k'⟩, n⟩, ⟨hm, hl, hs⟩, rfl⟩
    simp only at hl hs ⊢
    subst hl
    exact ⟨by rw [get_of_mem hnd hm]; rfl, hs⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h1
    exact ⟨((c, k), n), ⟨mem_of_get hn, rfl, h2⟩, rfl⟩

theorem nodup_resync_keys {T T' : Tree} (hnd : (T'.map (·.1)).Nodup) :
    (resync.keys c T T').Nodup := by
  unfold resync.keys List.Nodup
  rw [List.pairwise_map]
  have hf : ((T'.filter fun e => e.1.1 = c ∧ (T.get e.1).isSome).map (·.1)).Nodup :=
    hnd.sublist (List.filter_sublist.map _)
  unfold List.Nodup at hf
  rw [List.pairwise_map] at hf
  refine hf.imp_of_mem fun {a b} ha hb hne hk => hne (Prod.ext ?_ hk)
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  rw [ha.2.1, hb.2.1]

theorem resync_eq (T T' : Tree) :
    resync c Q val T T' = (resync.keys c T T').flatMap fun k => (dedup Q).filterMap fun x =>
      if val T k x = val T' k x then none else some (.modified c k x (val T k x) (val T' k x)) :=
  rfl

/-- The changes take the nodes that were there to their new values. -/
theorem resync_correct {T T' : Tree} (hwf' : T'.WF) :
    ∃ V, (T'.mapProps c (mixed c Q val T T')).applyAll (resync c Q val T T') = some V ∧
      V.Equiv (overlay.F c Q val T') := by
  obtain ⟨V, hV, hget⟩ := applyAll_nodes (Q := Q) (a := val T) (b := val T')
    (resync.keys c T T') (T'.mapProps c (mixed c Q val T T')) (nodup_resync_keys hwf'.nodup)
    fun k hk => by
      obtain ⟨h1, h2⟩ := (mem_resync_keys hwf'.nodup).mp hk
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h1
      exact ⟨_, by rw [get_mapProps, hn]; rfl, fun x hx => by simp [mapNode, mixed, h2, overlay, hx]⟩
  refine ⟨V, by rw [resync_eq]; exact hV, fun id => ?_⟩
  rw [hget]
  obtain ⟨l, k⟩ := id
  simp only [overlay.F, get_mapProps]
  by_cases hl : l = c
  · subst hl
    cases hn : T'.get (l, k) with
    | none => simp
    | some n =>
      by_cases hk : k ∈ resync.keys l T T'
      · have h2 := ((mem_resync_keys hwf'.nodup).mp hk).2
        simp [hk, mapNode, mixed, h2, overlay_overlay]
      · have h2 : (T.get (l, k)).isSome = false := Bool.eq_false_iff.mpr fun h =>
          hk ((mem_resync_keys hwf'.nodup).mpr ⟨by simp [hn], h⟩)
        simp [hk, mapNode, mixed, h2]
  · simp only [hl, false_and, ↓reduceIte]
    congr 1; funext n; simp [mapNode, hl]

/-- **`overlay_correct`.** The step is correct for its denotation, whatever the
values. -/
theorem overlay_correct (c : Level) (Q : List String) (val : Tree → Key → String → Option Val) :
    Correct (overlayStep c Q val) (overlay.F c Q val) := by
  intro T e T' hwf he
  have hwf' := apply_wf hwf he
  rw [overlayStep_handle he, applyAll_append]
  obtain ⟨A, hA, hEA⟩ := forward_correct (Q := Q) (val := val) (c := c) hwf he
  obtain ⟨A', hA', hEA'⟩ := applyAll_equiv (mapProps_wf hwf) (mapProps_wf hwf)
    (mixed_before T T').symm hA
  obtain ⟨V, hV, hEV⟩ := resync_correct (Q := Q) (val := val) (c := c) (T := T) hwf'
  obtain ⟨V', hV', hEV'⟩ := applyAll_equiv (mapProps_wf hwf') (applyAll_wf (mapProps_wf hwf) hA')
    (hEA.symm.trans hEA') hV
  refine ⟨V', ?_, hEV'.symm.trans hEV⟩
  have hA'' : (overlay.F c Q val T).applyAll (forward c Q val T' e) = some A' := hA'
  rw [hA'']; exact hV'

/-! ## Siblings -/

theorem siblings_perm {T U : Tree} (hT : T.WF) (hU : U.WF) (h : T.Equiv U) (p : Option Key) :
    (siblings c T p).Perm (siblings c U p) :=
  ((perm_of_equiv hT hU h).filter _).map _

/-- Siblings have distinct keys. -/
theorem nodup_siblings {T : Tree} (hnd : (T.map (·.1)).Nodup) (p : Option Key) :
    ((siblings c T p).map (·.1)).Nodup := by
  unfold siblings
  rw [List.map_map]
  unfold List.Nodup
  rw [List.pairwise_map]
  have hf : ((T.filter fun e => e.1.1 = c ∧ e.2.parent = p).map (·.1)).Nodup :=
    hnd.sublist (List.filter_sublist.map _)
  unfold List.Nodup at hf
  rw [List.pairwise_map] at hf
  refine hf.imp_of_mem fun {a b} ha hb hne hk => hne (Prod.ext ?_ hk)
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  rw [ha.2.1, hb.2.1]

/-! ## `cumulativeSum` -/

variable {lt : Key × Props → Key × Props → Bool}

theorem cumulativeSum_denotation (c : Level) (lt : Key × Props → Key × Props → Bool)
    (P : List String) : Denotation (cumulativeSum.F c lt P) :=
  overlay_denotation fun T U hT hU h => by
    funext k x
    simp only [cumulativeSum.val, h (c, k)]
    cases U.get (c, k) with
    | none => rfl
    | some n =>
      simp only [Option.map_some, Option.some.injEq]
      exact perm_sum_int (((siblings_perm hT hU h _).filter _).map _)

/-- **`cumulativeSum_correct`.** -/
theorem cumulativeSum_correct (c : Level) (lt : Key × Props → Key × Props → Bool)
    (P : List String) : Correct (cumulativeSumStep c lt P) (cumulativeSum.F c lt P) :=
  overlay_correct _ _ _

/-! ## The order -/

theorem StrictTotal.asymm (hlt : StrictTotal lt) {a b : Key × Props} (h : lt a b = true) :
    lt b a = false :=
  Bool.eq_false_iff.mpr fun h' => by
    have := hlt.trans a b a h h'
    rw [hlt.irrefl] at this
    cases this

/-- In a sorted list, a node and those before it are the ones that are it or come
before it: the TypeScript's prefix of its sorted list. -/
theorem prefix_of_sorted (hlt : StrictTotal lt) {pre post : List (Key × Props)} {x : Key × Props}
    (hs : (pre ++ x :: post).Pairwise fun a b => lt a b = true)
    (hnd : ((pre ++ x :: post).map (·.1)).Nodup) :
    (pre ++ x :: post).filter (fun y => y.1 == x.1 || lt y x) = pre ++ [x] := by
  rw [List.pairwise_append] at hs
  obtain ⟨-, hpost, hcross⟩ := hs
  rw [List.map_append, List.map_cons, List.nodup_append] at hnd
  have hx : x.1 ∉ post.map (·.1) := (List.nodup_cons.mp hnd.2.1).1
  rw [List.filter_append, List.filter_cons]
  have h1 : pre.filter (fun y => y.1 == x.1 || lt y x) = pre :=
    List.filter_eq_self.mpr fun y hy => by simp [hcross y hy x (List.mem_cons_self ..)]
  have h2 : post.filter (fun y => y.1 == x.1 || lt y x) = [] :=
    List.filter_eq_nil_iff.mpr fun y hy => by
      have hxy := List.rel_of_pairwise_cons hpost hy
      have hk : y.1 ≠ x.1 := fun h => hx (List.mem_map.mpr ⟨y, hy, h⟩)
      simp [hk, hlt.asymm hxy]
  simp [h1, h2]

/-- A node's running total is the sum over its prefix of the sorted list. -/
theorem cumulativeSum_val_sorted (hlt : StrictTotal lt) {T : Tree} (hwf : T.WF) {k : Key} {n : Node}
    (hn : T.get (c, k) = some n) {pre post : List (Key × Props)}
    (hperm : (siblings c T n.parent).Perm (pre ++ (k, n.props) :: post))
    (hs : (pre ++ (k, n.props) :: post).Pairwise fun a b => lt a b = true) (x : String) :
    cumulativeSum.val c lt T k x = some (((pre ++ [(k, n.props)]).map fun y => (y.2 x).getD 0).sum) := by
  have hnd := (hperm.map (·.1)).nodup_iff.mp (nodup_siblings hwf.nodup n.parent)
  simp only [cumulativeSum.val, hn, Option.map_some, Option.some.injEq]
  rw [perm_sum_int ((hperm.filter _).map _)]
  have := prefix_of_sorted hlt hs hnd
  simp only at this
  rw [this]

/-! ## `replaceToDelta` -/

theorem latest_cons (y : Key × Props) (l : List (Key × Props)) :
    latest lt (y :: l) = latestStep lt y (latest lt l) := rfl

theorem latest_eq_none {l : List (Key × Props)} : latest lt l = none ↔ l = [] := by
  cases l with
  | nil => simp [latest]
  | cons y l =>
    rw [latest_cons]
    cases latest lt l with
    | none => simp [latestStep]
    | some a => simp only [latestStep]; split <;> simp

/-- The greatest node is in the list, and every other node comes before it. -/
theorem latest_spec (hlt : StrictTotal lt) :
    ∀ {l : List (Key × Props)} {m : Key × Props}, (l.map (·.1)).Nodup → latest lt l = some m →
      m ∈ l ∧ ∀ y ∈ l, y ≠ m → lt y m = true := by
  intro l
  induction l with
  | nil => intro m _ h; simp [latest] at h
  | cons y l ih =>
    intro m hnd h
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [latest_cons] at h
    cases hl : latest lt l with
    | none =>
      rw [hl] at h
      simp only [latestStep, Option.some.injEq] at h
      subst h
      have : l = [] := latest_eq_none.mp hl
      subst this
      simp
    | some a =>
      rw [hl] at h
      obtain ⟨ha, hmax⟩ := ih hnd.2 hl
      simp only [latestStep] at h
      split at h
      · rename_i hay
        cases h
        refine ⟨List.mem_cons_self .., fun z hz hne => ?_⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact absurd rfl hne
        · by_cases hza : z = a
          · subst hza; exact hay
          · exact hlt.trans _ _ _ (hmax z hz hza) hay
      · rename_i hay
        cases h
        refine ⟨List.mem_cons_of_mem _ ha, fun z hz hne => ?_⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · have hk : z.1 ≠ m.1 := fun h => hnd.1 (List.mem_map.mpr ⟨m, ha, h.symm⟩)
          rcases hlt.total z m hk with h | h
          · exact h
          · exact absurd h hay
        · exact hmax z hz hne

/-- Under a strict total order, the greatest node does not depend on the order of
the list. -/
theorem latest_perm (hlt : StrictTotal lt) {l₁ l₂ : List (Key × Props)} (hnd : (l₁.map (·.1)).Nodup)
    (h : l₁.Perm l₂) : latest lt l₁ = latest lt l₂ := by
  have hnd₂ := (h.map (·.1)).nodup_iff.mp hnd
  cases h₁ : latest lt l₁ with
  | none =>
    have := latest_eq_none.mp h₁
    subst this
    exact (latest_eq_none.mpr h.nil_eq.symm).symm
  | some m₁ =>
    cases h₂ : latest lt l₂ with
    | none =>
      have := latest_eq_none.mp h₂
      subst this
      have := latest_eq_none (lt := lt) |>.mpr h.eq_nil
      rw [this] at h₁; cases h₁
    | some m₂ =>
      obtain ⟨hm₁, hmax₁⟩ := latest_spec hlt hnd h₁
      obtain ⟨hm₂, hmax₂⟩ := latest_spec hlt hnd₂ h₂
      by_cases heq : m₁ = m₂
      · rw [heq]
      · have a := hmax₁ m₂ (h.mem_iff.mpr hm₂) (Ne.symm heq)
        have b := hmax₂ m₁ (h.mem_iff.mp hm₁) heq
        rw [hlt.asymm a] at b; cases b

theorem replaceToDelta_denotation (hlt : StrictTotal lt) (c : Level) (D : Deltas) :
    Denotation (replaceToDelta.F c lt D) :=
  overlay_denotation fun T U hT hU h => by
    funext k o
    unfold replaceToDelta.val
    rw [h (c, k)]
    cases U.get (c, k) with
    | none => cases D.find? (·.2 = o) <;> rfl
    | some n =>
      have hp : predecessor c lt T k n = predecessor c lt U k n :=
        latest_perm hlt ((nodup_siblings hT.nodup n.parent).sublist (List.filter_sublist.map _))
          ((siblings_perm hT hU h _).filter _)
      cases D.find? (·.2 = o) with
      | none => rfl
      | some po => obtain ⟨p, q⟩ := po; dsimp only; rw [hp]

/-- **`replaceToDelta_correct`.** -/
theorem replaceToDelta_correct (c : Level) (lt : Key × Props → Key × Props → Bool) (D : Deltas) :
    Correct (replaceToDeltaStep c lt D) (replaceToDelta.F c lt D) :=
  overlay_correct _ _ _

/-- The greatest node of a sorted list is its last. -/
theorem latest_sorted (hlt : StrictTotal lt) :
    ∀ (l : List (Key × Props)), (l.Pairwise fun a b => lt a b = true) → latest lt l = l.getLast?
  | [] => fun _ => rfl
  | [y] => fun _ => rfl
  | y :: z :: zs => fun hs => by
    rw [latest_cons, latest_sorted hlt (z :: zs) (List.pairwise_cons.mp hs).2, List.getLast?_cons_cons]
    cases hg : (z :: zs).getLast? with
    | none => simp at hg
    | some a =>
      have hmem : a ∈ z :: zs := List.mem_of_getLast? hg
      simp [latestStep, hlt.asymm (List.rel_of_pairwise_cons hs hmem)]

/-- In a sorted list, the nodes before a node are its prefix, and its
predecessor is the last of them: the node just before it, as in the
TypeScript's sorted list. -/
theorem latest_of_sorted (hlt : StrictTotal lt) {pre post : List (Key × Props)} {x : Key × Props}
    (hs : (pre ++ x :: post).Pairwise fun a b => lt a b = true) :
    latest lt ((pre ++ x :: post).filter fun y => lt y x) = pre.getLast? := by
  have hs' := hs
  rw [List.pairwise_append] at hs'
  obtain ⟨hpre, hpost, hcross⟩ := hs'
  rw [List.filter_append, List.filter_cons]
  have h1 : pre.filter (fun y => lt y x) = pre :=
    List.filter_eq_self.mpr fun y hy => hcross y hy x (List.mem_cons_self ..)
  have h2 : post.filter (fun y => lt y x) = [] :=
    List.filter_eq_nil_iff.mpr fun y hy => by
      simp [hlt.asymm (List.rel_of_pairwise_cons hpost hy)]
  simp only [h1, h2, hlt.irrefl, Bool.false_eq_true, ↓reduceIte, List.append_nil]
  exact latest_sorted hlt pre hpre

/-- A node's predecessor is the node just before it in the sorted list. -/
theorem predecessor_sorted (hlt : StrictTotal lt) {T : Tree} (hwf : T.WF) {k : Key} {n : Node}
    {pre post : List (Key × Props)}
    (hperm : (siblings c T n.parent).Perm (pre ++ (k, n.props) :: post))
    (hs : (pre ++ (k, n.props) :: post).Pairwise fun a b => lt a b = true) :
    predecessor c lt T k n = pre.getLast? := by
  unfold predecessor
  rw [latest_perm hlt ((nodup_siblings hwf.nodup n.parent).sublist (List.filter_sublist.map _))
    (hperm.filter _)]
  exact latest_of_sorted hlt hs

/-! ## Signatures -/

theorem overlay_keeps (c : Level) (Q : List String) (val : Tree → Key → String → Option Val)
    (σ : Sig) : Keeps (overlayStep c Q val) σ (overlay.sig c Q σ) := by
  intro T e ha hd e' he'
  obtain ⟨T', hT'⟩ := Option.isSome_iff_exists.mp ha
  rw [overlayStep_handle hT'] at he'
  rcases List.mem_append.mp he' with h | h
  · cases e with
    | added => simp only [forward, List.mem_singleton] at h; subst h; trivial
    | removed => simp only [forward, List.mem_singleton] at h; subst h; trivial
    | modified l k x old new =>
      simp only [forward] at h
      split at h
      · cases h
      · simp only [List.mem_singleton] at h; subst h
        show (overlay.sig c Q σ).mutable l x = true
        simp [overlay.sig, show σ.mutable l x = true from hd]
    | placed => simp only [forward, List.mem_singleton] at h; subst h; exact hd
  · simp only [resync, List.mem_flatMap, List.mem_filterMap] at h
    obtain ⟨k, -, x, hx, hif⟩ := h
    split at hif
    · cases hif
    · cases hif
      show (overlay.sig c Q σ).mutable c x = true
      simp [overlay.sig, mem_dedup.mp hx]

/-- `cumulativeSum` declares nothing new: the TypeScript requires each summed
property to be mutable already, and its descriptor transform is the identity. -/
theorem cumulativeSum_keeps (c : Level) (lt : Key × Props → Key × Props → Bool) (P : List String)
    (σ : Sig) (hP : ∀ x ∈ P, σ.mutable c x = true) : Keeps (cumulativeSumStep c lt P) σ σ := by
  intro T e ha hd e' he'
  refine declared_mono (σ := overlay.sig c P σ) (σ' := σ) (fun l x h => ?_) (fun _ h => h) (overlay_keeps c P _ σ T e ha hd e' he')
  simp only [overlay.sig, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rcases h with h | ⟨rfl, hx⟩
  · exact h
  · exact hP x hx

/-- `replaceToDelta` declares its outputs mutable at the events' level
(`addOutputPropertiesToEventNode`). -/
theorem replaceToDelta_keeps (c : Level) (lt : Key × Props → Key × Props → Bool) (D : Deltas)
    (σ : Sig) : Keeps (replaceToDeltaStep c lt D) σ (overlay.sig c (D.map (·.2)) σ) :=
  overlay_keeps _ _ _ σ

end JinagaSpec.Cascade
