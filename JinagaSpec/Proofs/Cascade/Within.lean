import JinagaSpec.Cascade.Within
import JinagaSpec.Proofs.Cascade.Filter
import JinagaSpec.Proofs.Cascade.GroupBy
import JinagaSpec.Proofs.Cascade.Flatten

/-!
# Cascade: a step within a scope is correct

`within_correct`: a root step correct for `F`, with `F` a denotation that
takes the empty tree to itself, is correct within any array, for `F` within
it.

The output's nodes are of three kinds (`get_within_outside`, `get_within_tag`,
`get_within_other`): a node outside the scope is the input's, a node tagged
with anchor `p` is the anchor's view's output, and there is no other. An event
of one anchor's view, back under the anchor, does to the output what it does to
the view, and nothing else (`transport`).
-/
namespace JinagaSpec.Cascade

open within

/-! ## The root row a node is under -/

@[simp] theorem rootOf_root (T : Tree) (k : Key) : T.rootOf ([], k) = some k := rfl

theorem rootOf_step {T : Tree} {l : Level} {k : Key} {m : Node} (hl : l ≠ [])
    (hm : T.get (l, k) = some m) : T.rootOf (l, k) = m.parent.bind fun q => T.rootOf (l.dropLast, q) := by
  obtain ⟨n, hn⟩ : ∃ n, l.length = n + 1 := ⟨l.length - 1, by
    have : l.length ≠ 0 := by simpa using hl
    omega⟩
  simp only [Tree.rootOf, hn, Tree.walk, hm, Option.bind_some, List.length_dropLast, Nat.add_sub_cancel]

/-- In a well-formed tree, every node is under a root row that exists. -/
theorem rootOf_present {T : Tree} (hT : T.WF) :
    ∀ (n : Nat) (l : Level) (k : Key) (m : Node), l.length = n → T.get (l, k) = some m →
      ∃ r, T.rootOf (l, k) = some r ∧ (T.get ([], r)).isSome := by
  intro n
  induction n with
  | zero =>
    intro l k m hl hm
    rw [List.length_eq_zero_iff] at hl; subst hl
    exact ⟨k, rfl, by simp [hm]⟩
  | succ n ih =>
    intro l k m hl hm
    have hne : l ≠ [] := by intro h; subst h; simp at hl
    have hok := hT.parents _ m hm
    cases hq : m.parent with
    | none => rw [hq] at hok; simp [Tree.parentOk, hne] at hok
    | some q =>
      rw [hq] at hok
      simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hok.2
      obtain ⟨r, hr, hroot⟩ := ih _ _ _ (by rw [List.length_dropLast]; omega) hm'
      exact ⟨r, by rw [rootOf_step hne hm, hq, Option.bind_some, hr], hroot⟩

theorem rootOf_wf {T : Tree} (hT : T.WF) {id : Id} {m : Node} (hm : T.get id = some m) :
    ∃ r, T.rootOf id = some r ∧ (T.get ([], r)).isSome :=
  rootOf_present hT _ id.1 id.2 m rfl hm

/-- Trees that agree on the parents of an up-closed set agree on its roots. -/
theorem rootOf_congr {T U : Tree} {S : Id → Prop} (hS : UpClosed T S) (hA : ParentsAgree T U S)
    {id : Id} (h : S id) : T.rootOf id = U.rootOf id :=
  walk_congr hS hA _ _ _ h

/-- A node of a subtree is under the root its top is under. -/
theorem rootOf_of_inSubtree {T : Tree} {x y : Id} (h : inSubtree T x y = true) :
    T.rootOf y = T.rootOf x := by
  rw [inSubtree_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold Tree.rootOf
  have : y.1.length = (y.1.length - x.1.length) + x.1.length := by omega
  rw [this, walk_add, h3, Option.bind_some, up_eq_take]
  rw [show y.1.length - (y.1.length - x.1.length) = x.1.length by omega, h2]

theorem length_dropLast_lt {l : Level} (hl : l ≠ []) : l.dropLast.length < l.length := by
  rw [List.length_dropLast]
  have : l.length ≠ 0 := by simpa using hl
  omega

/-- Moving node `(l, k)` to parent `y`, under root `r`, puts its subtree under
`r` and leaves every other node under its root. -/
theorem rootOf_placed {T : Tree} (hT : T.WF) {l : Level} {k y r : Key} (hl : l ≠ [])
    (hy : (T.get (l.dropLast, y)).isSome) (hr : T.rootOf (l.dropLast, y) = some r) :
    ∀ (n : Nat) (id : Id) (m : Node), id.1.length = n → T.get id = some m →
      (T.update (l, k) fun n => { n with parent := some y }).rootOf id =
        if inSubtree T (l, k) id then some r else T.rootOf id := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro id m hn hm
    obtain ⟨l', k'⟩ := id
    simp only at hn
    by_cases hl' : l' = []
    · subst hl'
      have : inSubtree T (l, k) ([], k') = false := by
        rw [Bool.eq_false_iff]; intro h
        have := (inSubtree_iff.mp h).1
        simp only [List.length_nil, Nat.le_zero, List.length_eq_zero_iff] at this
        exact hl this
      simp [this]
    · have hm' : (T.update (l, k) fun n => { n with parent := some y }).get (l', k') =
          some (if (l', k') = (l, k) then { m with parent := some y } else m) := by
        rw [get_update]; split <;> simp_all
      rw [rootOf_step hl' hm']
      by_cases hz : (l', k') = (l, k)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz
        obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hy
        have hout : inSubtree T (l', k') (l'.dropLast, y) = false := by
          rw [Bool.eq_false_iff]; intro h
          have := (inSubtree_iff.mp h).1
          have := length_dropLast_lt hl
          simp only at *; omega
        simp only [↓reduceIte, Option.bind_some, inSubtree_self]
        rw [ih _ (hn ▸ length_dropLast_lt hl') _ m' rfl hm', hout, hr]
        rfl
      · simp only [hz, ↓reduceIte]
        have hok := hT.parents _ m hm
        cases hq : m.parent with
        | none => rw [hq] at hok; simp [Tree.parentOk, hl'] at hok
        | some q =>
          rw [hq] at hok
          simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
          obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hok.2
          simp only [Option.bind_some]
          rw [ih _ (hn ▸ length_dropLast_lt hl') _ m' rfl hm']
          have hiff : inSubtree T (l, k) (l'.dropLast, q) = inSubtree T (l, k) (l', k') := by
            rw [Bool.eq_iff_iff]
            exact ⟨inSubtree_child hl' hm hq, fun h => inSubtree_parent hm hq h hz⟩
          rw [hiff, rootOf_step hl' hm, hq, Option.bind_some]

/-! ## What the views and the output hold -/

@[simp] theorem tag_inj {p q k j : Key} : Key.tag p k = Key.tag q j ↔ p = q ∧ k = j := by
  simp [Key.tag]

theorem isSome_get_iff {T : Tree} {id : Id} : (T.get id).isSome ↔ id ∈ T.map (·.1) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h
    exact List.mem_map.mpr ⟨_, mem_of_get hn, rfl⟩
  · intro h
    obtain ⟨⟨id', n⟩, hm, he⟩ := List.mem_map.mp h
    simp only at he; subst he
    simp only [Tree.get, Option.isSome_map]
    exact List.find?_isSome.mpr ⟨_, hm, by simp⟩

theorem mem_roots {T : Tree} {p : Key} : p ∈ T.roots ↔ (T.get ([], p)).isSome := by
  rw [isSome_get_iff]
  simp only [Tree.roots, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨l, k⟩, n⟩, ⟨hm, hl⟩, rfl⟩
    simp only at hl; subst hl
    exact ⟨_, hm, rfl⟩
  · rintro ⟨⟨⟨l, k⟩, n⟩, hm, he⟩
    cases he
    exact ⟨_, ⟨hm, rfl⟩, rfl⟩

theorem get_map_viewEntry {a : String} {L : Tree} (hL : ∀ e ∈ L, e.1.1.head? = some a) (l : Level)
    (k : Key) : Tree.get (L.map viewEntry) (l, k) = (L.get (a :: l, k)).map (viewNode l) := by
  induction L with
  | nil => simp
  | cons e L ih =>
    obtain ⟨⟨l', k'⟩, n⟩ := e
    have he := hL _ List.mem_cons_self
    cases l' with
    | nil => simp at he
    | cons b l' =>
      simp only [List.head?_cons, Option.some.injEq] at he
      subst he
      simp only [List.map_cons, viewEntry, get_cons, Prod.mk.injEq, List.cons.injEq, true_and,
        ih fun e h => hL e (List.mem_cons_of_mem _ h)]
      by_cases h : l' = l ∧ k' = k
      · obtain ⟨rfl, rfl⟩ := h; simp
      · simp only [h, ↓reduceIte]

theorem get_view (a : String) (T : Tree) (p : Key) (l : Level) (k : Key) :
    (view a T p).get (l, k) =
      if under a T p (a :: l, k) then (T.get (a :: l, k)).map (viewNode l) else none := by
  unfold view
  rw [get_map_viewEntry (a := a) (fun e he => by
    simp only [List.mem_filter, under, Bool.and_eq_true, beq_iff_eq] at he
    exact he.2.1), get_filter_id]
  split <;> simp

theorem get_embed_tag (o : String) (p : Key) (U : Tree) (l : Level) (k : Key) :
    (embed o p U).get (o :: l, Key.tag p k) = (U.get (l, k)).map (embedNode p l) := by
  induction U with
  | nil => simp [embed]
  | cons e U ih =>
    obtain ⟨⟨l', k'⟩, n⟩ := e
    simp only [embed, List.map_cons, embedEntry, get_cons, Prod.mk.injEq, List.cons.injEq,
      true_and, tag_inj] at ih ⊢
    rw [ih]
    by_cases h : l' = l ∧ k' = k
    · obtain ⟨rfl, rfl⟩ := h; simp
    · simp only [h, ↓reduceIte]

theorem get_embed_other (o : String) (p : Key) (U : Tree) {id : Id}
    (h : ∀ l k, id ≠ (o :: l, Key.tag p k)) : (embed o p U).get id = none := by
  induction U with
  | nil => simp [embed]
  | cons e U ih =>
    obtain ⟨⟨l', k'⟩, n⟩ := e
    simp only [embed, List.map_cons, embedEntry, get_cons] at ih ⊢
    have hne : ¬(o :: l', Key.tag p k') = id := fun he => h l' k' he.symm
    simp only [hne, ↓reduceIte, ih]

theorem get_flatMap_tag (o : String) (G : Key → Tree) (L : List Key) (p : Key) (l : Level)
    (k : Key) : Tree.get (L.flatMap fun q => embed o q (G q)) (o :: l, Key.tag p k) =
      if p ∈ L then ((G p).get (l, k)).map (embedNode p l) else none := by
  induction L with
  | nil => simp
  | cons q L ih =>
    rw [List.flatMap_cons, get_append, ih]
    by_cases hq : q = p
    · subst hq; rw [get_embed_tag]; split <;> simp
    · rw [get_embed_other o q _ (fun l' k' he => hq (tag_inj.mp (Prod.mk.inj he).2).1.symm)]
      simp [Ne.symm hq]

theorem get_flatMap_other (o : String) (G : Key → Tree) (L : List Key) {id : Id}
    (h : ∀ p l k, id ≠ (o :: l, Key.tag p k)) :
    Tree.get (L.flatMap fun q => embed o q (G q)) id = none := by
  induction L with
  | nil => simp
  | cons q L ih => rw [List.flatMap_cons, get_append, get_embed_other o q _ (h q), ih]; rfl

theorem not_outside_tag (a o : String) (l : Level) (k : Key) : outside a o (o :: l, k) = false := by
  simp [outside]

theorem get_within_outside (a o : String) (G : Tree → Tree) (T : Tree) {id : Id}
    (h : outside a o id = true) : (within.F a o G T).get id = T.get id := by
  unfold within.F
  rw [get_append, get_filter_id, get_flatMap_other o _ _ (fun p l k he => by
    rw [he, not_outside_tag] at h; cases h)]
  simp [h]

theorem get_within_tag (a o : String) (G : Tree → Tree) (T : Tree) (p : Key) (l : Level) (k : Key) :
    (within.F a o G T).get (o :: l, Key.tag p k) =
      if (T.get ([], p)).isSome then ((G (view a T p)).get (l, k)).map (embedNode p l) else none := by
  unfold within.F
  rw [get_append, get_filter_id, not_outside_tag, get_flatMap_tag]
  simp [mem_roots]

theorem get_within_other (a o : String) (G : Tree → Tree) (T : Tree) {id : Id}
    (h : outside a o id = false) (h' : ∀ p l k, id ≠ (o :: l, Key.tag p k)) :
    (within.F a o G T).get id = none := by
  unfold within.F
  rw [get_append, get_filter_id, h, get_flatMap_other o _ _ h']
  simp

/-! ## The views and the output are well formed -/

theorem nodup_map_on {α β γ : Type} {L : List α} {f : α → β} {g : α → γ} (hnd : (L.map g).Nodup)
    (hinj : ∀ x ∈ L, ∀ y ∈ L, f x = f y → g x = g y) : (L.map f).Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_map] at *
  exact hnd.imp_of_mem fun hx hy hne he => hne (hinj _ hx _ hy he)

theorem view_wf {a : String} {T : Tree} (hT : T.WF) (p : Key) : (view a T p).WF := by
  refine ⟨?_, fun ⟨l, k⟩ n hn => ?_⟩
  · unfold view
    rw [List.map_map]
    refine nodup_map_on ((List.filter_sublist.map _).nodup hT.nodup) fun x hx y hy he => ?_
    simp only [List.mem_filter, under, Bool.and_eq_true, beq_iff_eq] at hx hy
    obtain ⟨⟨lx, kx⟩, nx⟩ := x
    obtain ⟨⟨ly, ky⟩, ny⟩ := y
    cases lx with
    | nil => simp at hx
    | cons bx lx =>
      cases ly with
      | nil => simp at hy
      | cons byy ly =>
        simp only [List.head?_cons, Option.some.injEq] at hx hy
        obtain ⟨-, rfl, -⟩ := hx
        obtain ⟨-, rfl, -⟩ := hy
        simp only [Function.comp, viewEntry, Prod.mk.injEq] at he
        simp [he.1, he.2]
  · rw [get_view] at hn
    split at hn
    · rename_i hu
      simp only [under, Bool.and_eq_true, beq_iff_eq] at hu
      obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hn
      simp only [viewNode]
      by_cases hl : l = []
      · simp [hl, Tree.parentOk]
      · simp only [hl, ↓reduceIte]
        have hok := hT.parents _ m hm
        cases hq : m.parent with
        | none => rw [hq] at hok; simp [Tree.parentOk] at hok
        | some q =>
          rw [hq] at hok
          simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
            List.dropLast_cons_of_ne_nil hl] at hok ⊢
          refine ⟨hl, ?_⟩
          rw [get_view]
          obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hok.2
          have hr : T.rootOf (a :: l.dropLast, q) = some p := by
            rw [← hu.2, rootOf_step (List.cons_ne_nil a l) hm, hq, Option.bind_some,
              List.dropLast_cons_of_ne_nil hl]
          simp [under, hr, hm']
    · cases hn

/-- A node outside the scope has its parent outside it. -/
theorem outside_dropLast {a o : String} {id : Id} {q : Key} (h : outside a o id = true) :
    outside a o (id.1.dropLast, q) = true := by
  obtain ⟨l, k⟩ := id
  cases l with
  | nil => simp [outside]
  | cons b l =>
    cases l with
    | nil => simp [outside]
    | cons c l =>
      simp only [outside, bne_iff_ne, ne_eq, Bool.and_eq_true] at h ⊢
      rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil c l)]
      simpa using h

/-- Each node of the output is the input's, outside the scope, or tagged with
an anchor; there is no other. -/
theorem tagged_or (o : String) (id : Id) :
    (∃ l p k, id = (o :: l, Key.tag p k)) ∨ ∀ p l k, id ≠ (o :: l, Key.tag p k) := by
  by_cases h : ∃ l p k, id = (o :: l, Key.tag p k)
  · exact Or.inl h
  · exact Or.inr fun p l k he => h ⟨l, p, k, he⟩

theorem nodup_roots {T : Tree} (hnd : (T.map (·.1)).Nodup) : T.roots.Nodup := by
  unfold Tree.roots
  refine nodup_map_on ((List.filter_sublist.map _).nodup hnd) fun x hx y hy he => ?_
  simp only [List.mem_filter, decide_eq_true_eq] at hx hy
  exact Prod.ext (hx.2.trans hy.2.symm) he

theorem nodup_embed (o : String) (p : Key) {U : Tree} (hnd : (U.map (·.1)).Nodup) :
    ((embed o p U).map (·.1)).Nodup := by
  unfold embed
  rw [List.map_map]
  refine nodup_map_on hnd fun x _ y _ he => ?_
  obtain ⟨⟨lx, kx⟩, nx⟩ := x
  obtain ⟨⟨ly, ky⟩, ny⟩ := y
  simp only [Function.comp, embedEntry, Prod.mk.injEq, List.cons.injEq, true_and, tag_inj] at he
  simp [he.1, he.2]

theorem mem_embed_ids {o : String} {p : Key} {U : Tree} {id : Id} (h : id ∈ (embed o p U).map (·.1)) :
    ∃ l k, id = (o :: l, Key.tag p k) := by
  simp only [embed, List.map_map, List.mem_map, Function.comp] at h
  obtain ⟨⟨⟨l, k⟩, n⟩, -, rfl⟩ := h
  exact ⟨l, k, rfl⟩

theorem nodup_flatMap_embed (o : String) (G : Key → Tree) (hG : ∀ p, ((G p).map (·.1)).Nodup) :
    ∀ L : List Key, L.Nodup → ((L.flatMap fun p => embed o p (G p)).map (·.1)).Nodup := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons p L ih =>
    intro hL
    rw [List.nodup_cons] at hL
    rw [List.flatMap_cons, List.map_append, List.nodup_append]
    refine ⟨nodup_embed o p (hG p), ih hL.2, fun x hx y hy hxy => ?_⟩
    subst hxy
    obtain ⟨l, k, rfl⟩ := mem_embed_ids hx
    simp only [List.mem_map, List.mem_flatMap] at hy
    obtain ⟨e, ⟨q, hq, he⟩, heq⟩ := hy
    obtain ⟨l', k', h'⟩ := mem_embed_ids (List.mem_map.mpr ⟨e, he, rfl⟩)
    rw [heq] at h'
    have := (tag_inj.mp (Prod.mk.inj h').2).1
    subst this
    exact hL.1 hq

theorem within_wf {a o : String} {G : Tree → Tree} (hG : Denotation G) {T : Tree} (hT : T.WF) :
    (within.F a o G T).WF := by
  refine ⟨?_, fun id n hn => ?_⟩
  · unfold within.F
    rw [List.map_append, List.nodup_append]
    refine ⟨(List.filter_sublist.map _).nodup hT.nodup,
      nodup_flatMap_embed o _ (fun p => (hG.wf _ (view_wf hT p)).nodup) _ (nodup_roots hT.nodup),
      fun x hx y hy hxy => ?_⟩
    subst hxy
    simp only [List.mem_map, List.mem_flatMap] at hy
    obtain ⟨e, ⟨q, -, he⟩, heq⟩ := hy
    obtain ⟨l, k, h'⟩ := mem_embed_ids (List.mem_map.mpr ⟨e, he, rfl⟩)
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
    simp only [List.mem_filter] at he'
    rw [heq] at h'
    rw [h', not_outside_tag] at he'
    exact absurd he'.2 (by simp)
  · by_cases ho : outside a o id = true
    · rw [get_within_outside a o G T ho] at hn
      have hok := hT.parents id n hn
      cases hq : n.parent with
      | none => rw [hq] at hok; exact hok
      | some q =>
        rw [hq] at hok
        simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true'] at hok ⊢
        refine ⟨hok.1, ?_⟩
        rw [get_within_outside a o G T (outside_dropLast ho)]
        exact hok.2
    · rcases tagged_or o id with ⟨l, p, k, rfl⟩ | hother
      · rw [get_within_tag] at hn
        split at hn
        · rename_i hp
          obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.mp hn
          simp only [embedNode]
          by_cases hl : l = []
          · subst hl
            simp only [↓reduceIte, Tree.parentOk, List.isEmpty_cons, Bool.not_false,
              List.dropLast_singleton, Bool.true_and]
            rw [get_within_outside a o G T (by simp [outside])]; exact hp
          · simp only [hl, ↓reduceIte]
            have hok := (hG.wf _ (view_wf hT p)).parents _ m hm
            cases hq : m.parent with
            | none => rw [hq] at hok; simp [Tree.parentOk, hl] at hok
            | some q =>
              rw [hq] at hok
              simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true',
                List.isEmpty_eq_false_iff] at hok
              simp only [Option.map_some, Tree.parentOk, List.isEmpty_cons, Bool.not_false,
                List.dropLast_cons_of_ne_nil hl, Bool.true_and, get_within_tag, hp, ↓reduceIte,
                Option.isSome_map]
              exact hok.2
        · cases hn
      · rw [get_within_other a o G T (by simpa using ho) hother] at hn; cases hn

theorem rootOf_equiv {T U : Tree} (h : T.Equiv U) (id : Id) : T.rootOf id = U.rootOf id :=
  rootOf_congr (S := fun _ => True) (fun _ _ _ _ _ _ _ => trivial) (fun id _ => by rw [h id]) trivial

theorem view_equiv {a : String} {T U : Tree} (h : T.Equiv U) (p : Key) :
    (view a T p).Equiv (view a U p) := by
  intro ⟨l, k⟩
  rw [get_view, get_view, under, under, rootOf_equiv h, h (a :: l, k)]

theorem within_denotation (a o : String) {G : Tree → Tree} (hG : Denotation G) :
    Denotation (within.F a o G) := by
  refine ⟨fun T hT => within_wf hG hT, fun T U hT hU h id => ?_⟩
  by_cases ho : outside a o id = true
  · rw [get_within_outside a o G T ho, get_within_outside a o G U ho, h id]
  · rcases tagged_or o id with ⟨l, p, k, rfl⟩ | hother
    · rw [get_within_tag, get_within_tag, h ([], p),
        hG.equiv _ _ (view_wf hT p) (view_wf hU p) (view_equiv h p) (l, k)]
    · rw [get_within_other a o G T (by simpa using ho) hother,
        get_within_other a o G U (by simpa using ho) hother]

/-! ## A view's events, under its anchor -/

/-- `Full` holds view `V` under anchor `p` in array `o`: the nodes tagged with
`p` are `V`'s, the anchor exists, and the only nodes below `o` that a node
tagged with `p` can be the parent of are tagged with `p`. -/
structure Embeds (o : String) (p : Key) (Full V : Tree) : Prop where
  get : ∀ l k, Full.get (o :: l, Key.tag p k) = (V.get (l, k)).map (embedNode p l)
  anchor : (Full.get ([], p)).isSome
  closed : ∀ l' k' n j, Full.get (l', k') = some n → l'.head? = some o → 2 ≤ l'.length →
    n.parent = some (Key.tag p j) → ∃ l k, (l', k') = (o :: l, Key.tag p k)

theorem parentOk_embed {o : String} {p : Key} {Full V : Tree} (E : Embeds o p Full V) {l : Level}
    {r : Key} (h : V.parentOk l (some r) = true) :
    Full.parentOk (o :: l) (some (Key.tag p r)) = true := by
  simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h ⊢
  refine ⟨List.cons_ne_nil o l, ?_⟩
  rw [List.dropLast_cons_of_ne_nil h.1, E.get, Option.isSome_map]
  exact h.2

/-- The parent `embedEvent` gives an added node is the one `embedNode` gives it. -/
theorem embed_parent (p : Key) (l : Level) (q : Option Key) (ps : Props) :
    embedNode p l ⟨q, ps⟩ = ⟨if l = [] then some p else q.map (Key.tag p), ps⟩ := rfl

theorem embed_id_ne {o : String} {p : Key} {l l' : Level} {k k' : Key} (h : (l, k) ≠ (l', k')) :
    (o :: l, Key.tag p k) ≠ (o :: l', Key.tag p k') := fun h' => h (by
  simp only [Prod.mk.injEq, List.cons.injEq, true_and, tag_inj] at h'
  rw [h'.1, h'.2])

theorem cons_id_ne {a : String} {l l' : Level} {k k' : Key} (h : ¬(l, k) = (l', k')) :
    (a :: l, k) ≠ (a :: l', k') := fun h' => h (by cases h'; rfl)

theorem transport1 {o : String} {p : Key} {Full V V' : Tree} (hF : Full.WF) (hV : V.WF)
    (E : Embeds o p Full V)
    {e : Event} (h : V.apply e = some V') :
    ∃ Full', Full.apply (embedEvent o p e) = some Full' ∧ Embeds o p Full' V' ∧
      ∀ id, (∀ l k, id ≠ (o :: l, Key.tag p k)) → Full'.get id = Full.get id := by
  have hne_anchor : ∀ l k, (([] : Level), p) ≠ (o :: l, Key.tag p k) := fun l k h => by
    cases (Prod.mk.inj h).1
  cases e with
  | added l k q ps =>
    obtain ⟨hn, hp, rfl⟩ := apply_added.mp h
    have hpar : Full.parentOk (o :: l) (if l = [] then some p else q.map (Key.tag p)) = true := by
      by_cases hl : l = []
      · subst hl
        simp only [↓reduceIte, Tree.parentOk, List.isEmpty_cons, Bool.not_false,
          List.dropLast_singleton, Bool.true_and]
        exact E.anchor
      · simp only [hl, ↓reduceIte]
        cases q with
        | none => simp [Tree.parentOk, hl] at hp
        | some r => exact parentOk_embed E hp
    refine ⟨_, apply_added.mpr ⟨by rw [E.get, hn]; rfl, hpar, rfl⟩, ⟨fun l' k' => ?_, ?_, ?_⟩,
      fun id hid => ?_⟩
    · rw [get_cons, get_cons, E.get]
      by_cases he : (l, k) = (l', k')
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he; simp [embed_parent]
      · simp [he, embed_id_ne (o := o) (p := p) he]
    · simp only [get_cons, Ne.symm (hne_anchor l k), ↓reduceIte]; exact E.anchor
    · intro l' k' n j hg hh h2 hpj
      rw [get_cons] at hg
      split at hg
      · rename_i he; exact ⟨l, k, he.symm⟩
      · exact E.closed l' k' n j hg hh h2 hpj
    · have : ¬(o :: l, Key.tag p k) = id := fun he => hid l k he.symm
      simp only [get_cons, this, ↓reduceIte]
  | removed l k =>
    obtain ⟨hs, hc, rfl⟩ := apply_removed.mp h
    have hch : Full.hasChild (o :: l) (Key.tag p k) = false := by
      rw [Bool.eq_false_iff]; intro h'
      obtain ⟨l', k', m, hm, hl', hd, hpar⟩ := (hasChild_iff hF.nodup _ _).mp h'
      obtain ⟨x, rest, rfl⟩ : ∃ x rest, l' = x :: rest := by
        cases l' with
        | nil => exact absurd rfl hl'
        | cons x rest => exact ⟨x, rest, rfl⟩
      have hrest : rest ≠ [] := by intro hr; subst hr; simp at hd
      rw [List.dropLast_cons_of_ne_nil hrest] at hd
      obtain ⟨hx, hd'⟩ := List.cons.inj hd
      subst hx
      have h2 : 2 ≤ (x :: rest).length := by
        have : rest.length ≠ 0 := by simpa using hrest
        simp only [List.length_cons]; omega
      obtain ⟨m', j, hid⟩ := E.closed _ _ m k hm rfl h2 hpar
      obtain ⟨rfl, rfl⟩ : rest = m' ∧ k' = Key.tag p j := by
        simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hid; exact hid
      rw [E.get] at hm
      obtain ⟨n0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hm
      simp only [embedNode, hrest, ↓reduceIte, Option.map_eq_some_iff, tag_inj] at hpar
      obtain ⟨k0, hk0, -, rfl⟩ := hpar
      have : V.hasChild l k0 = true :=
        (hasChild_iff hV.nodup _ _).mpr ⟨rest, j, n0, hn0, hrest, hd', hk0⟩
      simp [this] at hc
    refine ⟨_, apply_removed.mpr ⟨by rw [E.get, Option.isSome_map]; exact hs, hch, rfl⟩,
      ⟨fun l' k' => ?_, ?_, ?_⟩, fun id hid => ?_⟩
    · rw [get_filter, get_filter, E.get]
      by_cases he : (l', k') = (l, k)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he; simp
      · simp [he, embed_id_ne (o := o) (p := p) he]
    · simp only [get_filter, hne_anchor l k, ↓reduceIte]; exact E.anchor
    · intro l' k' n j hg hh h2 hpj
      rw [get_filter] at hg
      split at hg
      · cases hg
      · exact E.closed l' k' n j hg hh h2 hpj
    · simp only [get_filter, hid l k, ↓reduceIte]
  | modified l k x u v =>
    obtain ⟨n, hn, h1, h2, rfl⟩ := apply_modified.mp h
    refine ⟨_, apply_modified.mpr ⟨embedNode p l n, by rw [E.get, hn]; rfl, h1, h2, rfl⟩,
      ⟨fun l' k' => ?_, ?_, ?_⟩, fun id hid => ?_⟩
    · rw [get_update, get_update, E.get]
      by_cases he : (l', k') = (l, k)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he; simp [hn, embedNode]
      · simp [he, embed_id_ne (o := o) (p := p) he]
    · rw [isSome_get_update]; exact E.anchor
    · intro l' k' m j hg hh h2 hpj
      rw [get_update] at hg
      split at hg
      · rename_i he; exact ⟨l, k, he⟩
      · exact E.closed l' k' m j hg hh h2 hpj
    · simp only [get_update, hid l k, ↓reduceIte]
  | placed l k x y =>
    obtain ⟨n, hn, h1, h2, h3, rfl⟩ := apply_placed.mp h
    have hl : l ≠ [] := by intro hl; subst hl; simp [Tree.parentOk] at h3
    refine ⟨_, apply_placed.mpr ⟨embedNode p l n, by rw [E.get, hn]; rfl,
      by simp [embedNode, hl, h1], by simpa using h2, parentOk_embed E h3, rfl⟩,
      ⟨fun l' k' => ?_, ?_, ?_⟩, fun id hid => ?_⟩
    · rw [get_update, get_update, E.get]
      by_cases he : (l', k') = (l, k)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he; simp [hn, embedNode, hl]
      · simp [he, embed_id_ne (o := o) (p := p) he]
    · rw [isSome_get_update]; exact E.anchor
    · intro l' k' m j hg hh h2 hpj
      rw [get_update] at hg
      split at hg
      · rename_i he; exact ⟨l, k, he⟩
      · exact E.closed l' k' m j hg hh h2 hpj
    · simp only [get_update, hid l k, ↓reduceIte]

/-- `transport1` for a sequence of events. -/
theorem transport {o : String} {p : Key} :
    ∀ (es : List Event) {Full V V' : Tree}, Full.WF → V.WF → Embeds o p Full V →
      V.applyAll es = some V' →
      ∃ Full', Full.applyAll (es.map (embedEvent o p)) = some Full' ∧ Embeds o p Full' V' ∧
        ∀ id, (∀ l k, id ≠ (o :: l, Key.tag p k)) → Full'.get id = Full.get id := by
  intro es
  induction es with
  | nil => intro Full V V' _ _ E h; cases h; exact ⟨Full, rfl, E, fun _ _ => rfl⟩
  | cons e es ih =>
    intro Full V V' hF hV E h
    simp only [Tree.applyAll, Option.bind_eq_some_iff] at h
    obtain ⟨V1, h1, h2⟩ := h
    obtain ⟨F1, hF1, E1, fr1⟩ := transport1 hF hV E h1
    obtain ⟨F2, hF2, E2, fr2⟩ := ih (apply_wf hF hF1) (apply_wf hV h1) E1 h2
    refine ⟨F2, ?_, E2, fun id hid => (fr2 id hid).trans (fr1 id hid)⟩
    simp only [List.map_cons, Tree.applyAll, hF1, Option.bind_some]
    exact hF2

/-! ## The output holds each anchor's view -/

theorem embeds_within (a o : String) (G : Tree → Tree) (T : Tree) {p : Key}
    (hp : (T.get ([], p)).isSome) : Embeds o p (within.F a o G T) (G (view a T p)) := by
  refine ⟨fun l k => by rw [get_within_tag]; simp [hp], ?_, fun l' k' n j hg hh h2 hpj => ?_⟩
  · rw [get_within_outside a o G T (by simp [outside])]; exact hp
  · have ho : outside a o (l', k') = false := by simp [outside, hh]
    rcases tagged_or o (l', k') with ⟨l, q, k, he⟩ | hother
    · rw [he, get_within_tag] at hg
      split at hg
      · obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.mp hg
        have hl : l ≠ [] := by
          intro hl; subst hl
          obtain ⟨rfl, -⟩ := Prod.mk.inj he
          simp at h2
        simp only [embedNode, hl, ↓reduceIte, Option.map_eq_some_iff, tag_inj] at hpj
        obtain ⟨_, _, rfl, _⟩ := hpj
        exact ⟨l, k, he⟩
      · cases hg
    · rw [get_within_other a o G T ho hother] at hg; cases hg

/-- Another anchor's region is untouched by changes to `p`'s. -/
theorem embeds_other {o : String} {p q : Key} {Full Full' V U : Tree} (E : Embeds o q Full V)
    (E' : Embeds o p Full' U) (hpq : p ≠ q)
    (hfr : ∀ id, (∀ l k, id ≠ (o :: l, Key.tag p k)) → Full'.get id = Full.get id) :
    Embeds o q Full' V := by
  have hne : ∀ l k l' k', (o :: l, Key.tag q k) ≠ (o :: l', Key.tag p k') := fun l k l' k' h =>
    hpq (tag_inj.mp (Prod.mk.inj h).2).1.symm
  refine ⟨fun l k => by rw [hfr _ (hne l k)]; exact E.get l k,
    by rw [hfr _ (fun l k h => by cases (Prod.mk.inj h).1)]; exact E.anchor,
    fun l' k' n j hg hh h2 hpj => ?_⟩
  by_cases hin : ∃ l k, (l', k') = (o :: l, Key.tag p k)
  · obtain ⟨l, k, he⟩ := hin
    rw [he, E'.get] at hg
    obtain ⟨m, -, rfl⟩ := Option.map_eq_some_iff.mp hg
    have hl : l ≠ [] := by
      intro hl; subst hl; obtain ⟨rfl, -⟩ := Prod.mk.inj he; simp at h2
    simp only [embedNode, hl, ↓reduceIte, Option.map_eq_some_iff, tag_inj] at hpj
    obtain ⟨_, _, h, _⟩ := hpj
    exact absurd h hpq
  · rw [hfr _ (fun l k h => hin ⟨l, k, h⟩)] at hg
    exact E.closed l' k' n j hg hh h2 hpj

/-- Step `S`'s events for a sequence of view events, back under the anchor,
take the anchor's region to `S`'s output for the view after them, and leave the
rest of the output alone. -/
theorem lift_step {o : String} {S : Step} {G : Tree → Tree} (hS : Correct S G) (hG : Denotation G)
    {p : Key} {Full V V' : Tree} (hF : Full.WF) (hV : V.WF) (E : Embeds o p Full (G V))
    {es : List Event} (h : V.applyAll es = some V') :
    ∃ Full' U, Full.applyAll ((run S V es).map (embedEvent o p)) = some Full' ∧ Full'.WF ∧
      Embeds o p Full' U ∧ U.Equiv (G V') ∧
      ∀ id, (∀ l k, id ≠ (o :: l, Key.tag p k)) → Full'.get id = Full.get id := by
  obtain ⟨U, hU, hUe⟩ := run_correct hS hG es V V' hV h
  obtain ⟨Full', h1, E', fr⟩ := transport _ hF (hG.wf V hV) E hU
  exact ⟨Full', U, h1, applyAll_wf hF h1, E', hUe, fr⟩

/-- The output agrees with the output for `T'` wherever `T'` changes no root,
no node outside the scope, and no anchor's view, except those in `X`. -/
theorem within_get_eq {a o : String} {G : Tree → Tree} (hG : Denotation G) {T T' : Tree}
    (hT : T.WF) (hT' : T'.WF) (X : Key → Prop)
    (hroot : ∀ q, ¬X q → T.get ([], q) = T'.get ([], q))
    (hout : ∀ id, outside a o id = true → T.get id = T'.get id)
    (hview : ∀ q, ¬X q → (view a T q).Equiv (view a T' q)) :
    ∀ id, (∀ q l k, X q → id ≠ (o :: l, Key.tag q k)) →
      (within.F a o G T).get id = (within.F a o G T').get id := by
  intro id hid
  by_cases ho : outside a o id = true
  · rw [get_within_outside a o G T ho, get_within_outside a o G T' ho, hout id ho]
  · rcases tagged_or o id with ⟨l, q, k, rfl⟩ | hother
    · have hq : ¬X q := fun hx => hid q l k hx rfl
      rw [get_within_tag, get_within_tag, hroot q hq,
        hG.equiv _ _ (view_wf hT q) (view_wf hT' q) (hview q hq) (l, k)]
    · rw [get_within_other a o G T (by simpa using ho) hother,
        get_within_other a o G T' (by simpa using ho) hother]

/-! ## An event below the scope, in its anchor's view -/

theorem view_get_eq {a : String} {T T' : Tree} (q : Key) {l : Level} {k : Key}
    (hg : T.get (a :: l, k) = T'.get (a :: l, k))
    (hr : (T.get (a :: l, k)).isSome → T.rootOf (a :: l, k) = T'.rootOf (a :: l, k)) :
    (view a T q).get (l, k) = (view a T' q).get (l, k) := by
  rw [get_view, get_view]
  cases h : T.get (a :: l, k) with
  | none => rw [← hg, h]; simp
  | some n => rw [← hg, h, under, under, hr (by simp [h])]

/-- Two trees whose nodes are the same and under the same roots, but at `z`. -/
theorem view_equiv_except {a : String} {T T' : Tree} (q : Key) (z : Id)
    (hg : ∀ x, x ≠ z → T.get x = T'.get x)
    (hr : ∀ x, x ≠ z → (T.get x).isSome → T.rootOf x = T'.rootOf x)
    (hz : (view a T q).get (z.1.tail, z.2) = (view a T' q).get (z.1.tail, z.2)) :
    (view a T q).Equiv (view a T' q) := by
  intro ⟨l, k⟩
  by_cases h : (a :: l, k) = z
  · subst h; exact hz
  · exact view_get_eq q (hg _ h) (hr _ h)

theorem not_under_of_rootOf {a : String} {T : Tree} {p q : Key} {id : Id} (h : T.rootOf id = some p)
    (hpq : p ≠ q) : under a T q id = false := by
  simp [under, h, hpq]

theorem view_added {a : String} {T T' : Tree} (hT : T.WF) {m : Level} {k : Key} {q : Option Key}
    {ps : Props} (h : T.apply (.added (a :: m) k q ps) = some T') {p : Key}
    (hp : (q.bind fun r => T.rootOf ((a :: m).dropLast, r)) = some p) :
    ∃ V', (view a T p).apply (viewEvent (.added (a :: m) k q ps)) = some V' ∧
      V'.Equiv (view a T' p) ∧ ∀ q', q' ≠ p → (view a T q').Equiv (view a T' q') := by
  obtain ⟨hn, hpar, rfl⟩ := apply_added.mp h
  obtain ⟨r, rfl⟩ : ∃ r, q = some r := by
    cases q with
    | none => simp at hp
    | some r => exact ⟨r, rfl⟩
  simp only [Option.bind_some] at hp
  have hr : ∀ x, (T.get x).isSome →
      T.rootOf x = Tree.rootOf (((a :: m, k), ⟨some r, ps⟩) :: T) x := fun x hx =>
    rootOf_congr (upClosed_present hT) (fun x' hx' => by
      have : ¬(a :: m, k) = x' := fun he => by rw [← he, hn] at hx'; cases hx'
      simp only [get_cons, this, ↓reduceIte]) hx
  have hpar' := hpar
  simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true'] at hpar'
  have hz : Tree.rootOf (((a :: m, k), ⟨some r, ps⟩) :: T) (a :: m, k) = some p := by
    rw [rootOf_step (m := ⟨some r, ps⟩) (List.cons_ne_nil a m) (by rw [get_cons]; simp)]
    simp only [Option.bind_some]
    rw [← hr _ hpar'.2, hp]
  have hother : ∀ x, x ≠ (a :: m, k) → T.get x = Tree.get (((a :: m, k), ⟨some r, ps⟩) :: T) x :=
    fun x hx => by simp only [get_cons, Ne.symm hx, ↓reduceIte]
  refine ⟨_, apply_added.mpr ⟨?_, ?_, rfl⟩, fun ⟨l, k'⟩ => ?_, fun q' hq' => ?_⟩
  · rw [get_view]; simp [hn]
  · simp only [List.tail_cons]
    by_cases hm : m = []
    · simp [hm, Tree.parentOk]
    · simp only [hm, ↓reduceIte, Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true',
        List.isEmpty_eq_false_iff]
      refine ⟨hm, ?_⟩
      rw [List.dropLast_cons_of_ne_nil hm] at hpar' hp
      rw [get_view]
      simp [under, hp, hpar'.2]
  · rw [get_cons]
    by_cases he : (m, k) = (l, k')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [get_view a (((a :: m, k), ⟨some r, ps⟩) :: T)]
      simp only [under, hz, get_cons, viewNode, List.head?_cons, beq_self_eq_true, Bool.and_self,
        ↓reduceIte, Option.map_some, List.tail_cons]
      by_cases hm : m = [] <;> simp [hm]
    · simp only [List.tail_cons, he, ↓reduceIte]
      exact view_get_eq p (hother _ (fun h' => he (by cases h'; rfl))) (hr _)
  · refine view_equiv_except q' (a :: m, k) hother (fun x _ hx => hr x hx) ?_
    rw [get_view, get_view]
    simp [hn, not_under_of_rootOf hz (Ne.symm hq')]

theorem view_removed {a : String} {T T' : Tree} (hT : T.WF) {m : Level} {k : Key}
    (h : T.apply (.removed (a :: m) k) = some T') {p : Key} (hp : T.rootOf (a :: m, k) = some p) :
    ∃ V', (view a T p).apply (viewEvent (.removed (a :: m) k)) = some V' ∧
      V'.Equiv (view a T' p) ∧ ∀ q', q' ≠ p → (view a T q').Equiv (view a T' q') := by
  have hT' := apply_wf hT h
  obtain ⟨hs, hc, rfl⟩ := apply_removed.mp h
  have hother : ∀ x, x ≠ (a :: m, k) → T.get x = Tree.get (T.filter (·.1 != (a :: m, k))) x :=
    fun x hx => by simp only [get_filter, hx, ↓reduceIte]
  have hr : ∀ x, x ≠ (a :: m, k) → (T.get x).isSome →
      T.rootOf x = Tree.rootOf (T.filter (·.1 != (a :: m, k))) x := fun x hx hs' =>
    (rootOf_congr (upClosed_present hT') (fun x' hx' => by
      rw [get_filter] at hx' ⊢
      split <;> simp_all) (by rw [← hother x hx]; exact hs')).symm
  have hch : (view a T p).hasChild m k = false := by
    rw [Bool.eq_false_iff]; intro h'
    obtain ⟨l', k', n, hn, hl', hd, hpar⟩ := (hasChild_iff (view_wf hT p).nodup _ _).mp h'
    rw [get_view] at hn
    split at hn
    · obtain ⟨n0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
      simp only [viewNode, hl', ↓reduceIte] at hpar
      have : T.hasChild (a :: m) k = true := (hasChild_iff hT.nodup _ _).mpr
        ⟨a :: l', k', n0, hn0, List.cons_ne_nil a l', by rw [List.dropLast_cons_of_ne_nil hl', hd], hpar⟩
      simp [this] at hc
    · cases hn
  refine ⟨_, apply_removed.mpr ⟨?_, hch, rfl⟩, fun ⟨l, k'⟩ => ?_, fun q' hq' => ?_⟩
  · rw [get_view]; simp [under, hp, hs]
  · rw [get_filter]
    split
    · rename_i he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [get_view _ (T.filter _)]; simp [get_filter]
    · rename_i he
      have hne := cons_id_ne (a := a) he
      exact view_get_eq p (hother _ hne) (hr _ hne)
  · refine view_equiv_except q' (a :: m, k) hother hr ?_
    rw [get_view, get_view]
    simp [not_under_of_rootOf hp (Ne.symm hq'), get_filter]

theorem view_modified {a : String} {T T' : Tree} {m : Level} {k : Key} {x : String}
    {u v : Option Val} (h : T.apply (.modified (a :: m) k x u v) = some T') {p : Key}
    (hp : T.rootOf (a :: m, k) = some p) :
    ∃ V', (view a T p).apply (viewEvent (.modified (a :: m) k x u v)) = some V' ∧
      V'.Equiv (view a T' p) ∧ ∀ q', q' ≠ p → (view a T q').Equiv (view a T' q') := by
  obtain ⟨n, hn, h1, h2, rfl⟩ := apply_modified.mp h
  have hr : ∀ x', T.rootOf x' =
      Tree.rootOf (T.update (a :: m, k) fun n => { n with props := n.props.set x v }) x' := fun x' =>
    rootOf_congr (S := fun _ => True) (fun _ _ _ _ _ _ _ => trivial)
      (fun x'' _ => by rw [get_update]; split <;> simp_all) trivial
  have hother : ∀ x', x' ≠ (a :: m, k) →
      T.get x' = Tree.get (T.update (a :: m, k) fun n => { n with props := n.props.set x v }) x' :=
    fun x' hx => by simp only [get_update, hx, ↓reduceIte]
  refine ⟨_, apply_modified.mpr ⟨viewNode m n, by rw [get_view]; simp [under, hp, hn], h1, h2, rfl⟩,
    fun ⟨l, k'⟩ => ?_, fun q' hq' => ?_⟩
  · rw [get_update]
    split
    · rename_i he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [get_view, get_view _ (T.update _ _)]
      simp [under, hp, ← hr, hn, get_update, viewNode]
    · rename_i he
      have hne := cons_id_ne (a := a) he
      exact view_get_eq p (hother _ hne) (fun _ => hr _)
  · refine view_equiv_except q' (a :: m, k) hother (fun x' _ _ => hr x') ?_
    rw [get_view, get_view]
    simp [under, ← hr, hp, Ne.symm hq']

theorem view_placed {a : String} {T T' : Tree} (hT : T.WF) {m : Level} {k x y : Key}
    (h : T.apply (.placed (a :: m) k x y) = some T') {p : Key} (hp : T.rootOf (a :: m, k) = some p)
    (hp' : T.rootOf ((a :: m).dropLast, y) = some p) :
    ∃ V', (view a T p).apply (viewEvent (.placed (a :: m) k x y)) = some V' ∧
      V'.Equiv (view a T' p) ∧ ∀ q', q' ≠ p → (view a T q').Equiv (view a T' q') := by
  obtain ⟨n, hn, h1, h2, h3, rfl⟩ := apply_placed.mp h
  have h3' := h3
  simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true'] at h3'
  have hm : m ≠ [] := by
    intro hm; subst hm
    rw [rootOf_step (List.cons_ne_nil a []) hn, h1] at hp
    simp at hp hp'
    exact h2 (hp.trans hp'.symm)
  have hr : ∀ x', (T.get x').isSome →
      T.rootOf x' = Tree.rootOf (T.update (a :: m, k) fun n => { n with parent := some y }) x' := by
    intro x' hx'
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hx'
    rw [rootOf_placed hT (List.cons_ne_nil a m) h3'.2 hp' _ x' n' rfl hn']
    split
    · rename_i hin; rw [rootOf_of_inSubtree hin, hp]
    · rfl
  have hother : ∀ x', x' ≠ (a :: m, k) →
      T.get x' = Tree.get (T.update (a :: m, k) fun n => { n with parent := some y }) x' :=
    fun x' hx => by simp only [get_update, hx, ↓reduceIte]
  have hz' : Tree.rootOf (T.update (a :: m, k) fun n => { n with parent := some y }) (a :: m, k) = some p := by
    rw [← hr _ (by simp [hn]), hp]
  refine ⟨_, apply_placed.mpr ⟨viewNode m n, by rw [get_view]; simp [under, hp, hn],
    by simp [viewNode, hm, h1], h2, ?_, rfl⟩, fun ⟨l, k'⟩ => ?_, fun q' hq' => ?_⟩
  · simp only [List.tail_cons, Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff]
    refine ⟨hm, ?_⟩
    rw [List.dropLast_cons_of_ne_nil hm] at hp' h3'
    rw [get_view]
    simp [under, hp', h3'.2]
  · rw [get_update]
    split
    · rename_i he
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [get_view, get_view _ (T.update _ _)]
      simp [under, hp, hz', hn, get_update, viewNode, hm]
    · rename_i he
      have hne := cons_id_ne (a := a) he
      exact view_get_eq p (hother _ hne) (hr _)
  · refine view_equiv_except q' (a :: m, k) hother (fun x' _ hx' => hr x' hx') ?_
    rw [get_view, get_view]
    simp [not_under_of_rootOf hp (Ne.symm hq'), not_under_of_rootOf hz' (Ne.symm hq')]

/-! ## A move to another anchor -/

theorem head_of_inSubtree {T : Tree} {a : String} {m : Level} {k : Key} {x : Id}
    (h : inSubtree T (a :: m, k) x = true) : ∃ l, x.1 = a :: l := by
  obtain ⟨h1, h2, -⟩ := inSubtree_iff.mp h
  obtain ⟨l, k'⟩ := x
  cases l with
  | nil => simp at h1
  | cons b l =>
    simp only [List.length_cons, List.take_succ_cons, List.cons.injEq] at h2
    exact ⟨l, by rw [h2.1]⟩

theorem viewEntry_cons (a : String) (l : Level) (k : Key) (n : Node) :
    viewEntry ((a :: l, k), n) = ((l, k), viewNode l n) := rfl

/-- The nodes of a subtree, as their view holds them, keep their order by depth. -/
theorem pairwise_viewEntry {a : String} {L : List (Id × Node)} {R : Nat → Nat → Prop}
    (hR : ∀ i j, R i j → R (i - 1) (j - 1)) (hhead : ∀ e ∈ L, ∃ l, e.1.1 = a :: l)
    (h : L.Pairwise fun x y => R x.1.1.length y.1.1.length) :
    (L.map viewEntry).Pairwise fun x y => R x.1.1.length y.1.1.length := by
  rw [List.pairwise_map]
  refine h.imp_of_mem fun {x y} hx hy hxy => ?_
  obtain ⟨lx, hlx⟩ := hhead x hx
  obtain ⟨ly, hly⟩ := hhead y hy
  obtain ⟨⟨lx', kx⟩, nx⟩ := x
  obtain ⟨⟨ly', ky⟩, ny⟩ := y
  simp only at hlx hly
  subst hlx hly
  simpa [viewEntry_cons] using hR _ _ hxy

theorem mem_viewSub {T : Tree} {a : String} {m : Level} {k : Key} {le : Id × Node → Id × Node → Bool}
    {l : Level} {k' : Key} :
    (l, k') ∈ (((T.filter (inSubtree T (a :: m, k) ·.1)).mergeSort le).map viewEntry).map (·.1) ↔
      (T.get (a :: l, k')).isSome ∧ inSubtree T (a :: m, k) (a :: l, k') = true := by
  rw [isSome_get_iff]
  simp only [List.map_map, List.mem_map, mem_subtreeList, Function.comp]
  constructor
  · rintro ⟨e, ⟨hm, hs⟩, he⟩
    obtain ⟨l', hl'⟩ := head_of_inSubtree hs
    obtain ⟨⟨le', ke⟩, ne⟩ := e
    simp only at hl'; subst hl'
    simp only [viewEntry_cons, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨⟨_, hm, rfl⟩, hs⟩
  · rintro ⟨⟨e, hm, he⟩, hs⟩
    refine ⟨e, ⟨hm, he ▸ hs⟩, ?_⟩
    obtain ⟨⟨le', ke⟩, ne⟩ := e
    simp only at he; obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    rfl

/-- A node moved to a parent under another anchor takes its subtree out of the
first anchor's view and into the second's, and leaves every other view alone. -/
theorem view_moved {a : String} {T T' : Tree} (hT : T.WF) {m : Level} {k x y : Key}
    (h : T.apply (.placed (a :: m) k x y) = some T') {pa pb : Key}
    (hpa : T.rootOf (a :: m, k) = some pa) (hpb : T.rootOf ((a :: m).dropLast, y) = some pb)
    (hne : pa ≠ pb) :
    (∃ V, (view a T pa).applyAll ((evict T (a :: m, k)).map viewEvent) = some V ∧
      V.Equiv (view a T' pa)) ∧
    (∃ V, (view a T pb).applyAll ((admit T' (a :: m, k)).map viewEvent) = some V ∧
      V.Equiv (view a T' pb)) ∧
    ∀ q, q ≠ pa → q ≠ pb → (view a T q).Equiv (view a T' q) := by
  have hT' := apply_wf hT h
  obtain ⟨n, hn, h1, h2, h3, hU⟩ := apply_placed.mp h
  have h3' := h3
  simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true'] at h3'
  -- Where each node of the new tree is.
  have hget : ∀ x', x' ≠ (a :: m, k) → T'.get x' = T.get x' := fun x' hx => by
    simp only [hU, get_update, hx, ↓reduceIte]
  have hroot : ∀ x', (T.get x').isSome →
      T'.rootOf x' = if inSubtree T (a :: m, k) x' then some pb else T.rootOf x' := fun x' hx' => by
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hx'
    rw [hU]; exact rootOf_placed hT (List.cons_ne_nil a m) h3'.2 hpb _ x' n' rfl hn'
  have hsub : ∀ x', inSubtree T (a :: m, k) x' = true → T.rootOf x' = some pa := fun x' hs =>
    (rootOf_of_inSubtree hs).trans hpa
  have hzs : (T.get (a :: m, k)).isSome := by simp [hn]
  have hins : ∀ x', inSubtree T' (a :: m, k) x' = inSubtree T (a :: m, k) x' := fun ⟨l', k'⟩ => by
    unfold inSubtree
    by_cases hlen : (a :: m).length ≤ l'.length
    · rw [walk_congr_deep (d := (a :: m).length) (U := T) (fun w hw => by
        have : w ≠ (a :: m, k) := fun he => by rw [he] at hw; simp at hw
        rw [hget w this]) _ _ _ (by simp only; omega)]
    · have : ¬(m.length + 1 ≤ l'.length) := by simpa using hlen
      simp [this]
  -- A view's node at `(l', k')` is in the subtree, and under `pb` now, or under
  -- the root it was under, with the same value.
  have hcase : ∀ q l' k', ((T.get (a :: l', k')).isSome ∧ inSubtree T (a :: m, k) (a :: l', k') = true ∧
        (view a T q).get (l', k') = (if q = pa then (T.get (a :: l', k')).map (viewNode l') else none) ∧
        (view a T' q).get (l', k') = (if q = pb then (T'.get (a :: l', k')).map (viewNode l') else none)) ∨
      (view a T q).get (l', k') = (view a T' q).get (l', k') := by
    intro q l' k'
    by_cases hs : (T.get (a :: l', k')).isSome ∧ inSubtree T (a :: m, k) (a :: l', k') = true
    · refine Or.inl ⟨hs.1, hs.2, ?_, ?_⟩
      · rw [get_view, under, hsub _ hs.2]
        by_cases hq : q = pa
        · subst hq; simp
        · simp [hq, Ne.symm hq]
      · rw [get_view, under, hroot _ hs.1]
        simp only [hs.2, ↓reduceIte]
        by_cases hq : q = pb
        · subst hq; simp
        · simp [hq, Ne.symm hq]
    · right
      have hz : (a :: l', k') ≠ (a :: m, k) := fun he => hs ⟨he ▸ hzs, he ▸ inSubtree_self T _⟩
      refine view_get_eq q (hget _ hz).symm fun hx => ?_
      rw [hroot _ hx]
      simp only [show ¬inSubtree T (a :: m, k) (a :: l', k') = true from fun hin => hs ⟨hx, hin⟩,
        ↓reduceIte, Bool.false_eq_true]
  have hhead : ∀ (U : Tree) (le : Id × Node → Id × Node → Bool),
      ∀ e ∈ (U.filter (inSubtree U (a :: m, k) ·.1)).mergeSort le, ∃ l, e.1.1 = a :: l :=
    fun U le e he => head_of_inSubtree (mem_subtreeList.mp he).2
  have hnodup : ∀ (U : Tree), U.WF → ∀ le : Id × Node → Id × Node → Bool,
      ((((U.filter (inSubtree U (a :: m, k) ·.1)).mergeSort le).map viewEntry).map (·.1)).Nodup := by
    intro U hU le
    rw [List.map_map]
    refine nodup_map_on (nodup_subtreeList hU _ le) fun e he e' he' heq => ?_
    obtain ⟨l1, h1⟩ := hhead U le e he
    obtain ⟨l2, h2⟩ := hhead U le e' he'
    obtain ⟨⟨l1', k1⟩, n1⟩ := e
    obtain ⟨⟨l2', k2⟩, n2⟩ := e'
    simp only at h1 h2; subst h1 h2
    simp only [Function.comp, viewEntry_cons, Prod.mk.injEq] at heq
    simp [heq.1, heq.2]
  have hgetSub : ∀ (U : Tree), U.WF → ∀ (le : Id × Node → Id × Node → Bool) l' k' n',
      U.get (a :: l', k') = some n' → inSubtree U (a :: m, k) (a :: l', k') = true →
      Tree.get (((U.filter (inSubtree U (a :: m, k) ·.1)).mergeSort le).map viewEntry) (l', k') =
        some (viewNode l' n') := fun U hU le l' k' n' hg hs =>
    get_of_mem (hnodup U hU le)
      (List.mem_map.mpr ⟨((a :: l', k'), n'), mem_subtreeList.mpr ⟨mem_of_get hg, hs⟩, rfl⟩)
  refine ⟨?_, ?_, fun q hqa hqb => fun ⟨l', k'⟩ => ?_⟩
  · -- Out of `pa`'s view, children first.
    let le : Id × Node → Id × Node → Bool := fun a b => b.1.1.length ≤ a.1.1.length
    have hev : (evict T (a :: m, k)).map viewEvent =
        ((((T.filter (inSubtree T (a :: m, k) ·.1)).mergeSort le).map viewEntry).map
          fun e => .removed e.1.1 e.1.2) := by
      unfold evict
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun e he => ?_
      obtain ⟨l0, h0⟩ := hhead T le e he
      obtain ⟨⟨l0', k0⟩, n0⟩ := e
      simp only at h0; subst h0
      rfl
    obtain ⟨X, hX, hXg⟩ := removeAll _ (view a T pa) (view_wf hT pa)
      (pairwise_viewEntry (R := fun i j => j ≤ i) (fun i j h => by omega) (hhead T le)
        (List.pairwise_mergeSort (fun a b c hab hbc => by simp only [le, decide_eq_true_eq] at *; omega)
          (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) _ |>.imp
          fun h => by simpa [le] using h))
      (hnodup T hT le)
      (fun e he => by
        obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
        obtain ⟨l0, h0⟩ := hhead T le e0 he0
        obtain ⟨hm0, hs0⟩ := mem_subtreeList.mp he0
        obtain ⟨⟨l0', k0⟩, n0⟩ := e0
        simp only at h0; subst h0
        rw [viewEntry_cons, get_view]
        simp [under, hsub _ hs0, get_of_mem hT.nodup hm0])
      (fun e he l'' k'' m'' hg hl'' hd hp => by
        obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
        obtain ⟨l0, h0⟩ := hhead T le e0 he0
        obtain ⟨-, hs0⟩ := mem_subtreeList.mp he0
        obtain ⟨⟨l0', k0⟩, n0⟩ := e0
        simp only at h0; subst h0
        simp only [viewEntry_cons] at hd hp
        rw [get_view] at hg
        split at hg
        · obtain ⟨n1, hn1, rfl⟩ := Option.map_eq_some_iff.mp hg
          simp only [viewNode, hl'', ↓reduceIte] at hp
          refine mem_viewSub.mpr ⟨by simp [hn1], inSubtree_child (List.cons_ne_nil a l'') hn1 hp ?_⟩
          rw [List.dropLast_cons_of_ne_nil hl'', hd]; exact hs0
        · cases hg)
    refine ⟨X, hev ▸ hX, fun ⟨l', k'⟩ => ?_⟩
    rw [hXg]
    split
    · rename_i hin
      obtain ⟨hs1, hs2⟩ := mem_viewSub.mp hin
      rw [get_view, under, hroot _ hs1]
      simp [hs2, Ne.symm hne]
    · rename_i hnin
      rcases hcase pa l' k' with ⟨hs1, hs2, -, -⟩ | h
      · exact absurd (mem_viewSub.mpr ⟨hs1, hs2⟩) hnin
      · exact h
  · -- Into `pb`'s view, parents first.
    let le : Id × Node → Id × Node → Bool := fun a b => a.1.1.length ≤ b.1.1.length
    let L := (((T'.filter (inSubtree T' (a :: m, k) ·.1)).mergeSort le).map viewEntry)
    have had : (admit T' (a :: m, k)).map viewEvent =
        L.map fun e => .added e.1.1 e.1.2 e.2.parent e.2.props := by
      unfold admit
      rw [List.map_map, List.map_map]
      refine List.map_congr_left fun e he => ?_
      obtain ⟨l0, h0⟩ := hhead T' le e he
      obtain ⟨⟨l0', k0⟩, n0⟩ := e
      simp only at h0; subst h0
      rfl
    have hmemL : ∀ l' k', (l', k') ∈ L.map (·.1) ↔
        (T.get (a :: l', k')).isSome ∧ inSubtree T (a :: m, k) (a :: l', k') = true := by
      intro l' k'
      rw [mem_viewSub, hins]
      rw [show (T'.get (a :: l', k')).isSome = (T.get (a :: l', k')).isSome by
        rw [hU]; exact isSome_get_update _ _ _ _]
    have hBnone : ∀ id, id ∈ L.map (·.1) → (view a T pb).get id = none := fun ⟨l', k'⟩ h => by
      obtain ⟨hs1, hs2⟩ := (hmemL l' k').mp h
      rw [get_view, under, hsub _ hs2]
      simp [hne]
    -- The new view is the old one with the subtree's nodes added.
    have hnew : ∀ l' k', (view a T' pb).get (l', k') =
        (Tree.get L (l', k')).or ((view a T pb).get (l', k')) := by
      intro l' k'
      by_cases hs : (T.get (a :: l', k')).isSome ∧ inSubtree T (a :: m, k) (a :: l', k') = true
      · obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp
          (show (T'.get (a :: l', k')).isSome by rw [hU, isSome_get_update]; exact hs.1)
        rw [get_view a T' pb, under, hroot _ hs.1,
          hgetSub T' hT' le l' k' n' hn' (by rw [hins]; exact hs.2)]
        simp [hs.2, hn']
      · rw [get_eq_none_of_not_mem (fun h => hs ((hmemL l' k').mp h)), Option.none_or]
        rcases hcase pb l' k' with ⟨hs1, hs2, -, -⟩ | h
        · exact absurd ⟨hs1, hs2⟩ hs
        · exact h.symm
    obtain ⟨X, hX, hXg⟩ := addAll L (view a T pb) (view_wf hT pb)
      (pairwise_viewEntry (R := fun i j => i ≤ j) (fun i j h => by omega) (hhead T' le)
        (List.pairwise_mergeSort (fun a b c hab hbc => by simp only [le, decide_eq_true_eq] at *; omega)
          (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) _ |>.imp
          fun h => by simpa [le] using h))
      (hnodup T' hT' le)
      (fun e he => hBnone e.1 (List.mem_map_of_mem he))
      (fun e he => by
        have hE : (view a T pb ++ L).Equiv (view a T' pb) := fun ⟨l', k'⟩ => by
          rw [get_append, hnew]
          cases hL : Tree.get L (l', k') with
          | none => simp
          | some v =>
            rw [hBnone _ (isSome_get_iff.mp (by simp [hL]))]
            rfl
        rw [parentOk_congr hE]
        exact (view_wf hT' pb).parents e.1 e.2 (by
          rw [← hE, get_append, hBnone _ (List.mem_map_of_mem he), Option.none_or]
          exact get_of_mem (hnodup T' hT' le) he))
    refine ⟨X, had ▸ hX, fun ⟨l', k'⟩ => by rw [hXg, hnew]⟩
  · rcases hcase q l' k' with ⟨-, -, h1, h2⟩ | h
    · rw [h1, h2]; simp [hqa, hqb]
    · exact h

/-! ## Events outside the scope -/

theorem apply_get_at {T T' U U' : Tree} {e : Event} (hT : T.apply e = some T') (hU : U.apply e = some U')
    (h : T.get e.id = U.get e.id) : T'.get e.id = U'.get e.id := by
  cases e with
  | added l k q ps =>
    obtain ⟨-, -, rfl⟩ := apply_added.mp hT; obtain ⟨-, -, rfl⟩ := apply_added.mp hU
    simp [Event.id, get_cons]
  | removed l k =>
    obtain ⟨-, -, rfl⟩ := apply_removed.mp hT; obtain ⟨-, -, rfl⟩ := apply_removed.mp hU
    simp [Event.id, get_filter]
  | modified l k x u v =>
    obtain ⟨-, -, -, -, rfl⟩ := apply_modified.mp hT; obtain ⟨-, -, -, -, rfl⟩ := apply_modified.mp hU
    simp only [Event.id] at h ⊢; simp [get_update, h]
  | placed l k x y =>
    obtain ⟨-, -, -, -, -, rfl⟩ := apply_placed.mp hT; obtain ⟨-, -, -, -, -, rfl⟩ := apply_placed.mp hU
    simp only [Event.id] at h ⊢; simp [get_update, h]

theorem empty_wf : Tree.WF [] := ⟨List.nodup_nil, by simp⟩

/-- `G` of a view with no nodes has no nodes. -/
theorem G_view_none {a : String} {G : Tree → Tree} (hG : Denotation G) (h0 : G [] = []) {T : Tree}
    (hT : T.WF) {p : Key} (hnone : ∀ id, (view a T p).get id = none) (id : Id) :
    (G (view a T p)).get id = none := by
  rw [hG.equiv _ [] (view_wf hT p) empty_wf hnone id, h0]; rfl

/-- A root that does not exist has an empty view. -/
theorem view_none_of_absent {a : String} {T : Tree} (hT : T.WF) {p : Key} (hp : T.get ([], p) = none)
    (id : Id) : (view a T p).get id = none := by
  obtain ⟨l, k⟩ := id
  rw [get_view]
  split
  · rename_i hu
    simp only [under, Bool.and_eq_true, beq_iff_eq] at hu
    cases hg : T.get (a :: l, k) with
    | none => rfl
    | some n =>
      obtain ⟨r, hr, hroot⟩ := rootOf_wf hT hg
      rw [hu.2] at hr; cases hr
      simp [hp] at hroot
  · rfl

/-- A node under root `p` in array `a` has an ancestor among `p`'s children in `a`. -/
theorem child_of_under {a : String} {T : Tree} (hT : T.WF) {p : Key} :
    ∀ (n : Nat) (l : Level) (k : Key) (m : Node), l.length = n → T.get (a :: l, k) = some m →
      T.rootOf (a :: l, k) = some p → ∃ j m', T.get ([a], j) = some m' ∧ m'.parent = some p := by
  intro n
  induction n with
  | zero =>
    intro l k m hl hm hr
    rw [List.length_eq_zero_iff] at hl; subst hl
    rw [rootOf_step (List.cons_ne_nil a []) hm] at hr
    cases hq : m.parent with
    | none => rw [hq] at hr; cases hr
    | some q => rw [hq] at hr; simp at hr; subst hr; exact ⟨k, m, hm, hq⟩
  | succ n ih =>
    intro l k m hl hm hr
    have hl' : l ≠ [] := by intro h; subst h; simp at hl
    have hok := hT.parents _ m hm
    rw [rootOf_step (List.cons_ne_nil a l) hm] at hr
    cases hq : m.parent with
    | none => rw [hq] at hok; simp [Tree.parentOk] at hok
    | some q =>
      rw [hq] at hok hr
      simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
      simp only [Option.bind_some] at hr
      rw [List.dropLast_cons_of_ne_nil hl'] at hok hr
      obtain ⟨m', hm'⟩ := Option.isSome_iff_exists.mp hok.2
      exact ih _ _ _ (by rw [List.length_dropLast]; omega) hm' hr

/-- A root with no children has an empty view. -/
theorem view_none_of_noChild {a : String} {T : Tree} (hT : T.WF) {p : Key}
    (hc : T.hasChild [] p = false) (id : Id) : (view a T p).get id = none := by
  obtain ⟨l, k⟩ := id
  rw [get_view]
  split
  · rename_i hu
    simp only [under, Bool.and_eq_true, beq_iff_eq] at hu
    cases hg : T.get (a :: l, k) with
    | none => rfl
    | some n =>
      obtain ⟨j, m', hm', hp⟩ := child_of_under hT _ l k n rfl hg hu.2
      have : T.hasChild [] p = true :=
        (hasChild_iff hT.nodup _ _).mpr ⟨[a], j, m', hm', List.cons_ne_nil a [], rfl, hp⟩
      simp [this] at hc
  · rfl

/-! ## The cases of the theorem -/

/-- An event below the scope, in one anchor's view. -/
theorem inside_one {a o : String} {S : Step} {G : Tree → Tree} (hS : Correct S G) (hG : Denotation G)
    {T T' : Tree} (hT : T.WF) (hT' : T'.WF) {p : Key} (hp : (T.get ([], p)).isSome) {e : Event}
    {V' : Tree} (hva : (view a T p).apply (viewEvent e) = some V') (hVe : V'.Equiv (view a T' p))
    (hoth : ∀ q, q ≠ p → (view a T q).Equiv (view a T' q))
    (hout : ∀ id, outside a o id = true → T.get id = T'.get id)
    (hroot : ∀ q, T.get ([], q) = T'.get ([], q)) :
    ∃ U, (within.F a o G T).applyAll (within.lift a o S T p [e]) = some U ∧
      U.Equiv (within.F a o G T') := by
  have hV := view_wf (a := a) hT p
  have hap : (view a T p).applyAll ([e].map viewEvent) = some V' := by
    simp [Tree.applyAll, hva]
  obtain ⟨Full', U0, h1, -, E', hU0, fr⟩ :=
    lift_step hS hG (within_wf hG hT) hV (embeds_within a o G T hp) hap
  refine ⟨Full', h1, fun id => ?_⟩
  by_cases hid : ∃ l k, id = (o :: l, Key.tag p k)
  · obtain ⟨l, k, rfl⟩ := hid
    rw [E'.get, hU0, hG.equiv _ _ (apply_wf hV hva) (view_wf hT' p) hVe, get_within_tag, ← hroot p]
    simp [hp]
  · rw [fr _ (fun l k h => hid ⟨l, k, h⟩)]
    exact within_get_eq hG hT hT' (· = p) (fun q _ => hroot q) hout hoth id
      (fun q l k hq h => hid ⟨l, k, hq ▸ h⟩)

/-- A move from anchor `pa`'s view to `pb`'s. -/
theorem inside_move {a o : String} {S : Step} {G : Tree → Tree} (hS : Correct S G) (hG : Denotation G)
    {T T' : Tree} (hT : T.WF) (hT' : T'.WF) {pa pb : Key} (hne : pa ≠ pb)
    (hpa : (T.get ([], pa)).isSome) (hpb : (T.get ([], pb)).isSome) {ea eb : List Event}
    {Va Vb : Tree} (hva : (view a T pa).applyAll (ea.map viewEvent) = some Va)
    (hVa : Va.Equiv (view a T' pa)) (hvb : (view a T pb).applyAll (eb.map viewEvent) = some Vb)
    (hVb : Vb.Equiv (view a T' pb))
    (hoth : ∀ q, q ≠ pa → q ≠ pb → (view a T q).Equiv (view a T' q))
    (hout : ∀ id, outside a o id = true → T.get id = T'.get id)
    (hroot : ∀ q, T.get ([], q) = T'.get ([], q)) :
    ∃ U, (within.F a o G T).applyAll (within.lift a o S T pa ea ++ within.lift a o S T pb eb) = some U ∧
      U.Equiv (within.F a o G T') := by
  have hVa0 := view_wf (a := a) hT pa
  have hVb0 := view_wf (a := a) hT pb
  obtain ⟨F1, U1, h1, hF1, E1, hU1, fr1⟩ :=
    lift_step hS hG (within_wf hG hT) hVa0 (embeds_within a o G T hpa) hva
  have Eb := embeds_other (embeds_within a o G T hpb) E1 hne fr1
  obtain ⟨F2, U2, h2, -, E2, hU2, fr2⟩ := lift_step hS hG hF1 hVb0 Eb hvb
  refine ⟨F2, by rw [applyAll_append]; simp only [within.lift] at h1 h2 ⊢; rw [h1]; exact h2,
    fun id => ?_⟩
  by_cases hidb : ∃ l k, id = (o :: l, Key.tag pb k)
  · obtain ⟨l, k, rfl⟩ := hidb
    rw [E2.get, hU2, hG.equiv _ _ (applyAll_wf hVb0 hvb) (view_wf hT' pb) hVb, get_within_tag, ← hroot pb]
    simp [hpb]
  · rw [fr2 _ (fun l k h => hidb ⟨l, k, h⟩)]
    by_cases hida : ∃ l k, id = (o :: l, Key.tag pa k)
    · obtain ⟨l, k, rfl⟩ := hida
      rw [E1.get, hU1, hG.equiv _ _ (applyAll_wf hVa0 hva) (view_wf hT' pa) hVa, get_within_tag,
        ← hroot pa]
      simp [hpa]
    · rw [fr1 _ (fun l k h => hida ⟨l, k, h⟩)]
      exact within_get_eq hG hT hT' (fun q => q = pa ∨ q = pb) (fun q _ => hroot q) hout
        (fun q hq => hoth q (fun h => hq (Or.inl h)) (fun h => hq (Or.inr h))) id
        (fun q l k hq h => by
          rcases hq with rfl | rfl
          · exact hida ⟨l, k, h⟩
          · exact hidb ⟨l, k, h⟩)

/-- An event not below array `a` leaves every view alone. -/
theorem view_unchanged {a : String} {T T' : Tree} {e : Event} (he : T.apply e = some T')
    (ho : e.id.1.head? ≠ some a) (q : Key) : (view a T q).Equiv (view a T' q) := by
  have hne : ∀ l k, (a :: l, k) ≠ e.id := fun l k h => ho (by rw [← h]; rfl)
  intro ⟨l, k⟩
  refine view_get_eq q (apply_same he _ (hne l k)).symm fun _ => ?_
  by_cases hr : e.id.1 = []
  · unfold Tree.rootOf
    refine walk_congr_deep (d := 0) (fun z hz => ?_) _ _ _ (by simp)
    have : z ≠ e.id := fun h => by rw [h, hr] at hz; simp at hz
    rw [apply_same he _ this]
  · refine rootOf_congr (S := fun x => x.1.head? = some a ∨ x.1 = [])
      (fun l' k' m q' hs _ _ => ?_) (fun x hx => ?_) (Or.inl rfl)
    · rcases hs with hs | hs
      · cases l' with
        | nil => simp at hs
        | cons b l' =>
          cases l' with
          | nil => exact Or.inr rfl
          | cons c l' =>
            left
            rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil c l')]
            exact hs
      · subst hs; exact Or.inr rfl
    · have : x ≠ e.id := fun h => by
        rcases hx with hx | hx
        · rw [h] at hx; exact ho hx
        · rw [h] at hx; exact hr hx
      rw [apply_same he _ this]

/-- An event below `o`, where `o` is not `a`, changes nothing of the output. -/
theorem within_dropped {a o : String} {G : Tree → Tree} (hG : Denotation G) {T T' : Tree} (hT : T.WF)
    (hT' : T'.WF) {e : Event} (he : T.apply e = some T') (ho : e.id.1.head? = some o) (hoa : o ≠ a) :
    (within.F a o G T).Equiv (within.F a o G T') := by
  have hne : ∀ id, outside a o id = true → id ≠ e.id := fun id h hid => by
    rw [hid] at h; simp [outside, ho] at h
  exact fun id => within_get_eq hG hT hT' (fun _ => False)
    (fun q _ => (apply_same he _ (fun h => by rw [← h] at ho; simp at ho)).symm)
    (fun id h => (apply_same he _ (hne id h)).symm)
    (fun q _ => view_unchanged he (by rw [ho]; simp [hoa]) q) id (fun _ _ _ h => h.elim)

/-- An event outside the scope and outside `o` passes through. -/
theorem within_forward {a o : String} {G : Tree → Tree} (hG : Denotation G) (h0 : G [] = []) {T T' : Tree}
    (hT : T.WF) (hT' : T'.WF) {e : Event} (he : T.apply e = some T')
    (ho : outside a o e.id = true) {Full' : Tree} (hF : (within.F a o G T).apply e = some Full')
    (hempty : ∀ q, (T.get ([], q)).isSome ≠ (T'.get ([], q)).isSome → ∀ id, (view a T q).get id = none) :
    Full'.Equiv (within.F a o G T') := by
  have hoa : e.id.1.head? ≠ some a := by
    intro h; simp [outside, h] at ho
  have hview := view_unchanged (a := a) he hoa
  intro id
  by_cases hid : id = e.id
  · subst hid
    rw [get_within_outside a o G T' ho]
    exact apply_get_at hF he (get_within_outside a o G T ho)
  · rw [apply_same hF _ hid]
    by_cases hout : outside a o id = true
    · rw [get_within_outside a o G T hout, get_within_outside a o G T' hout, apply_same he _ hid]
    · rcases tagged_or o id with ⟨l, q, k, rfl⟩ | hother
      · rw [get_within_tag, get_within_tag]
        by_cases hq : (T.get ([], q)).isSome = (T'.get ([], q)).isSome
        · rw [hq, hG.equiv _ _ (view_wf hT q) (view_wf hT' q) (hview q) (l, k)]
        · have h1 := G_view_none hG h0 hT (hempty q hq)
          have h2 := G_view_none hG h0 hT' fun id => by
            rw [← hview q id]; exact hempty q hq id
          simp [h1, h2]
      · rw [get_within_other a o G T (by simpa using hout) hother,
          get_within_other a o G T' (by simpa using hout) hother]

/-! ## The theorem -/

theorem parentOk_within {a o : String} {G : Tree → Tree} {T : Tree} {l : Level} {k : Key}
    {q : Option Key} (ho : outside a o (l, k) = true) (h : T.parentOk l q = true) :
    (within.F a o G T).parentOk l q = true := by
  cases q with
  | none => exact h
  | some r =>
    simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true'] at h ⊢
    exact ⟨h.1, by rw [get_within_outside a o G T (outside_dropLast (q := r) ho)]; exact h.2⟩

/-- A node outside the scope with no children in the input has none in the output. -/
theorem hasChild_within {a o : String} {G : Tree → Tree} (hG : Denotation G) (h0 : G [] = [])
    {T : Tree} (hT : T.WF) {l : Level} {k : Key} (ho : outside a o (l, k) = true)
    (hc : T.hasChild l k = false) : (within.F a o G T).hasChild l k = false := by
  rw [Bool.eq_false_iff]; intro h
  obtain ⟨l', k', n, hn, hl', hd, hp⟩ := (hasChild_iff (within_wf hG hT).nodup _ _).mp h
  by_cases ho' : outside a o (l', k') = true
  · rw [get_within_outside a o G T ho'] at hn
    have : T.hasChild l k = true := (hasChild_iff hT.nodup _ _).mpr ⟨l', k', n, hn, hl', hd, hp⟩
    simp [this] at hc
  · rcases tagged_or o (l', k') with ⟨l'', q, j, he⟩ | hother
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      rw [get_within_tag] at hn
      split at hn
      · obtain ⟨n0, hn0, rfl⟩ := Option.map_eq_some_iff.mp hn
        by_cases hl'' : l'' = []
        · subst hl''
          simp only [List.dropLast_singleton] at hd; subst hd
          simp only [embedNode, ↓reduceIte, Option.some.injEq] at hp; subst hp
          have hc' : T.hasChild [] q = false := hc
          rw [G_view_none hG h0 hT (view_none_of_noChild hT hc')] at hn0
          cases hn0
        · rw [List.dropLast_cons_of_ne_nil hl''] at hd
          subst hd
          simp [outside] at ho
      · cases hn
    · rw [get_within_other a o G T (by simpa using ho') hother] at hn; cases hn

/-- `S` within array `a`, its output in array `o`, is correct for `F` within
it, when `S` is correct for `F`, `F` is a denotation, and `F` of the empty tree
is empty. -/
theorem within_correct (a o : String) {S : Step} {G : Tree → Tree} (hS : Correct S G)
    (hG : Denotation G) (h0 : G [] = []) : Correct (within a o S) (within.F a o G) := by
  intro T e T' hT he
  have hT' := apply_wf hT he
  have hout : e.level.head? = some a → ∀ id, outside a o id = true → T.get id = T'.get id :=
    fun hl id hid => (apply_same he _ (fun h => by
      rw [h] at hid; cases e <;> simp_all [outside, Event.id, Event.level])).symm
  have hroot : e.level ≠ [] → ∀ q, T.get ([], q) = T'.get ([], q) := fun hl q =>
    (apply_same he _ (fun h => by cases e <;> simp_all [Event.id, Event.level])).symm
  by_cases hin : (e.level.head? == some a) = true
  · obtain ⟨m, hm⟩ : ∃ m, e.level = a :: m := by
      cases hl : e.level with
      | nil => rw [hl] at hin; simp at hin
      | cons b m => rw [hl] at hin; simp at hin; exact ⟨m, by rw [hin]⟩
    have hin' : e.level.head? = some a := by simpa using hin
    cases e with
    | added l k q ps =>
      simp only [Event.level] at hm hin'; subst hm
      obtain ⟨hn, hpar, -⟩ := apply_added.mp he
      obtain ⟨r, rfl⟩ : ∃ r, q = some r := by
        cases q with
        | none => simp [Tree.parentOk] at hpar
        | some r => exact ⟨r, rfl⟩
      have hpar' := hpar
      simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true'] at hpar'
      obtain ⟨pm, hpm⟩ := Option.isSome_iff_exists.mp hpar'.2
      obtain ⟨p, hrp, hpp⟩ := rootOf_wf hT hpm
      have hstep : (within a o S).handle T (.added (a :: m) k (some r) ps) =
          within.lift a o S T p [.added (a :: m) k (some r) ps] := by
        simp [within, Event.level, hrp]
      rw [hstep]
      obtain ⟨V', hva, hVe, hoth⟩ := view_added hT he (by simpa using hrp)
      exact inside_one hS hG hT hT' hpp hva hVe hoth (hout rfl) (hroot (by simp [Event.level]))
    | removed l k =>
      simp only [Event.level] at hm hin'; subst hm
      obtain ⟨hs, -, -⟩ := apply_removed.mp he
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨p, hrp, hpp⟩ := rootOf_wf hT hn
      have hstep : (within a o S).handle T (.removed (a :: m) k) =
          within.lift a o S T p [.removed (a :: m) k] := by
        simp [within, Event.level, hrp]
      rw [hstep]
      obtain ⟨V', hva, hVe, hoth⟩ := view_removed hT he hrp
      exact inside_one hS hG hT hT' hpp hva hVe hoth (hout rfl) (hroot (by simp [Event.level]))
    | modified l k x u v =>
      simp only [Event.level] at hm hin'; subst hm
      obtain ⟨n, hn, -⟩ := apply_modified.mp he
      obtain ⟨p, hrp, hpp⟩ := rootOf_wf hT hn
      have hstep : (within a o S).handle T (.modified (a :: m) k x u v) =
          within.lift a o S T p [.modified (a :: m) k x u v] := by
        simp [within, Event.level, hrp]
      rw [hstep]
      obtain ⟨V', hva, hVe, hoth⟩ := view_modified he hrp
      exact inside_one hS hG hT hT' hpp hva hVe hoth (hout rfl) (hroot (by simp [Event.level]))
    | placed l k x y =>
      simp only [Event.level] at hm hin'; subst hm
      obtain ⟨n, hn, -, -, h3, hU⟩ := apply_placed.mp he
      have h3' := h3
      simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true'] at h3'
      obtain ⟨py, hpy⟩ := Option.isSome_iff_exists.mp h3'.2
      obtain ⟨p, hrp, hpp⟩ := rootOf_wf hT hn
      obtain ⟨p', hrp', hpp'⟩ := rootOf_wf hT hpy
      by_cases hpq : p = p'
      · subst hpq
        have hstep : (within a o S).handle T (.placed (a :: m) k x y) =
            within.lift a o S T p [.placed (a :: m) k x y] := by
          simp [within, Event.level, hrp, hrp']
        rw [hstep]
        obtain ⟨V', hva, hVe, hoth⟩ := view_placed hT he hrp hrp'
        exact inside_one hS hG hT hT' hpp hva hVe hoth (hout rfl) (hroot (by simp [Event.level]))
      · have hstep : (within a o S).handle T (.placed (a :: m) k x y) =
            within.lift a o S T p (evict T (a :: m, k)) ++
              within.lift a o S T p' (admit T' (a :: m, k)) := by
          simp [within, Event.level, hrp, hrp', hpq, hU]
        rw [hstep]
        obtain ⟨⟨Va, hva, hVa⟩, ⟨Vb, hvb, hVb⟩, hoth⟩ := view_moved hT he hrp hrp' hpq
        exact inside_move hS hG hT hT' hpq hpp hpp' hva hVa hvb hVb hoth (hout rfl) (hroot (by simp [Event.level]))
  · by_cases hdo : (e.level.head? == some o) = true
    · have hoa : o ≠ a := fun h => hin (by rw [← h]; exact hdo)
      have hdo' : e.level.head? = some o := by simpa using hdo
      refine ⟨within.F a o G T, by simp [within, hdo', hoa, Tree.applyAll], within_dropped hG hT hT' he ?_ hoa⟩
      cases e <;> simpa [Event.id, Event.level] using hdo
    · have hin' : ¬e.level.head? = some a := by simpa using hin
      have hdo' : ¬e.level.head? = some o := by simpa using hdo
      have ho : outside a o e.id = true := by
        cases e <;> simp_all [outside, Event.id, Event.level]
      have hstep : (within a o S).handle T e = [e] := by simp [within, hin', hdo']
      rw [hstep]
      suffices ∃ Full', (within.F a o G T).apply e = some Full' ∧
          ∀ q, (T.get ([], q)).isSome ≠ (T'.get ([], q)).isSome → ∀ id, (view a T q).get id = none by
        obtain ⟨Full', hF, hempty⟩ := this
        exact ⟨Full', by simp [Tree.applyAll, hF], within_forward hG h0 hT hT' he ho hF hempty⟩
      cases e with
      | added l k q ps =>
        simp only [Event.id] at ho
        obtain ⟨hn, hpar, rfl⟩ := apply_added.mp he
        refine ⟨_, apply_added.mpr ⟨by rw [get_within_outside a o G T ho]; exact hn,
          parentOk_within ho hpar, rfl⟩, fun q' hq' id => view_none_of_absent hT ?_ id⟩
        by_cases h : (l, k) = ([], q')
        · rw [← h]; exact hn
        · simp [get_cons, h] at hq'
      | removed l k =>
        simp only [Event.id] at ho
        obtain ⟨hs, hc, rfl⟩ := apply_removed.mp he
        refine ⟨_, apply_removed.mpr ⟨by rw [get_within_outside a o G T ho]; exact hs,
          hasChild_within hG h0 hT ho hc, rfl⟩, fun q' hq' id => view_none_of_noChild hT ?_ id⟩
        by_cases h : ([], q') = (l, k)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hc
        · simp [get_filter, h] at hq'
      | modified l k x u v =>
        simp only [Event.id] at ho
        obtain ⟨n, hn, h1, h2, rfl⟩ := apply_modified.mp he
        refine ⟨_, apply_modified.mpr ⟨n, by rw [get_within_outside a o G T ho]; exact hn, h1, h2, rfl⟩,
          fun q' hq' => absurd (isSome_get_update _ _ _ _).symm hq'⟩
      | placed l k x y =>
        simp only [Event.id] at ho
        obtain ⟨n, hn, h1, h2, h3, rfl⟩ := apply_placed.mp he
        refine ⟨_, apply_placed.mpr ⟨n, by rw [get_within_outside a o G T ho]; exact hn, h1, h2,
          parentOk_within ho h3, rfl⟩, fun q' hq' => absurd (isSome_get_update _ _ _ _).symm hq'⟩

/-! ## `groupBy`, `filter` and `flatten` below the root -/

/-- `.in(a).groupBy(G, o)`: each root row's items of `a` grouped apart. -/
theorem groupBy_within_correct (a o : String) (G : List String) :
    Correct (within a o (groupBy G a)) (within.F a o (groupBy.F G a)) :=
  within_correct a o (groupBy_correct G a) (groupBy_denotation G a) (by simp [groupBy.F, dedup])

/-- `.in(a).filter(P)`: each root row's items of `a` that pass `P`, with their subtrees. -/
theorem filter_within_correct (a : String) (P : Props → Bool) (deps : List String)
    (hdeps : ∀ ps p v, p ∉ deps → P (ps.set p v) = P ps) :
    Correct (within a a (filterStep P deps)) (within.F a a (filter.F P)) :=
  within_correct a a (filter_correct P deps hdeps) (filter_denotation P) rfl

/-- `.in(a).flatten(P, C, O)`: each root row's arrays `P` and `C` below `a` merged. -/
theorem flatten_within_correct (a P C O : String) (I : List String) (hPO : P ≠ O) :
    Correct (within a a (flattenStep P C O I)) (within.F a a (flatten.F P C O I)) :=
  within_correct a a (flatten_correct P C O I hPO) (flatten_denotation hPO) rfl

end JinagaSpec.Cascade
