import JinagaSpec.Proofs.Cascade.Aggregate

/-!
# Cascade: `filter` at the root

A node is in the output when its root ancestor passes the predicate. An event
can change the visibility of one node and its subtree, and of nothing else
(`visible_other`). When that subtree becomes visible the step adds it, parents
first, with current values; when it becomes hidden the step removes it,
children first. The change that caused either is not forwarded, because the
added nodes already carry it.
-/
namespace JinagaSpec.Cascade

variable {P : Props → Bool}

/-! ## Walking up parents -/

/-- A set of nodes that contains the parent of each of its nodes in `T`. -/
def UpClosed (T : Tree) (S : Id → Prop) : Prop :=
  ∀ l k m q, S (l, k) → T.get (l, k) = some m → m.parent = some q → S (l.dropLast, q)

/-- Two trees give the same parents to the nodes of `S`. -/
def ParentsAgree (T U : Tree) (S : Id → Prop) : Prop :=
  ∀ id, S id → (T.get id).map (·.parent) = (U.get id).map (·.parent)

/-- A walk reads only the parents along its path. -/
theorem walk_congr {T U : Tree} {S : Id → Prop} (hS : UpClosed T S) (hA : ParentsAgree T U S) :
    ∀ n l k, S (l, k) → T.walk n l k = U.walk n l k := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro l k hs
    have h := hA (l, k) hs
    simp only [Tree.walk]
    cases hT : T.get (l, k) with
    | none =>
      rw [hT] at h
      cases hU : U.get (l, k) with
      | none => rfl
      | some _ => rw [hU] at h; cases h
    | some m =>
      rw [hT] at h
      cases hU : U.get (l, k) with
      | none => rw [hU] at h; cases h
      | some m' =>
        rw [hU] at h
        simp only [Option.map_some, Option.some.injEq] at h
        simp only [Option.bind_some, ← h]
        cases hq : m.parent with
        | none => rfl
        | some q => exact ih _ _ (hS l k m q hs hT hq)

/-- The level `n` parents up. -/
def up : Nat → Level → Level
  | 0, l => l
  | n + 1, l => up n l.dropLast

/-- Walking `a + b` parents is walking `a`, then `b`. -/
theorem walk_add (T : Tree) : ∀ (a b : Nat) (l : Level) (k : Key),
    T.walk (a + b) l k = (T.walk a l k).bind fun k' => T.walk b (up a l) k' := by
  intro a
  induction a with
  | zero => intro b l k; simp [Tree.walk, up]
  | succ a ih =>
    intro b l k
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [Tree.walk, up]
    cases T.get (l, k) with
    | none => rfl
    | some m =>
      simp only [Option.bind_some]
      cases m.parent with
      | none => rfl
      | some q => exact ih b _ q

theorem up_eq_take : ∀ (n : Nat) (l : Level), up n l = l.take (l.length - n)
  | 0, l => by simp [up]
  | n + 1, l => by
    rw [up, up_eq_take n, List.dropLast_eq_take, List.take_take, List.length_take]
    congr 1; omega

/-- A walk of `n` steps reads only nodes deeper than `l.length - n`, so trees
that give those nodes the same parents agree on it. -/
theorem walk_congr_deep {T U : Tree} {d : Nat}
    (hA : ∀ z : Id, d < z.1.length → (T.get z).map (·.parent) = (U.get z).map (·.parent)) :
    ∀ n l k, n + d ≤ l.length → T.walk n l k = U.walk n l k := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro l k hn
    have h := hA (l, k) (by simp only; omega)
    simp only [Tree.walk]
    cases hT : T.get (l, k) with
    | none =>
      rw [hT] at h
      cases hU : U.get (l, k) with
      | none => rfl
      | some _ => rw [hU] at h; cases h
    | some m =>
      rw [hT] at h
      cases hU : U.get (l, k) with
      | none => rw [hU] at h; cases h
      | some m' =>
        rw [hU] at h
        simp only [Option.map_some, Option.some.injEq] at h
        simp only [Option.bind_some, ← h]
        cases m.parent with
        | none => rfl
        | some q => exact ih _ _ (by rw [List.length_dropLast]; omega)

/-! ## Visibility -/

theorem get_filter_id (T : Tree) (q : Id → Bool) (id : Id) :
    Tree.get (T.filter fun e => q e.1) id = if q id then T.get id else none := by
  induction T with
  | nil => simp
  | cons e T ih =>
    obtain ⟨id', n⟩ := e
    by_cases hq : q id' = true
    · simp only [List.filter_cons, hq, ↓reduceIte, get_cons, ih]
      by_cases h : id' = id
      · subst h; simp [hq]
      · simp [h]
    · simp only [List.filter_cons, hq, Bool.false_eq_true, ↓reduceIte, ih]
      by_cases h : id' = id
      · subst h; simp [hq]
      · simp [h, get_cons]

theorem get_filterF (T : Tree) (id : Id) :
    (filter.F P T).get id = if visible P T id then T.get id else none :=
  get_filter_id T _ id

theorem visible_absent {T : Tree} {id : Id} (h : T.get id = none) : visible P T id = false := by
  obtain ⟨l, k⟩ := id
  unfold visible
  cases l with
  | nil => simp [Tree.walk, h]
  | cons x l => simp [Tree.walk, h]

/-- A node is as visible as its parent. -/
theorem visible_parent {T : Tree} {l : Level} {k q : Key} {m : Node} (hl : l ≠ [])
    (hm : T.get (l, k) = some m) (hq : m.parent = some q) :
    visible P T (l, k) = visible P T (l.dropLast, q) := by
  unfold visible
  obtain ⟨n, hn⟩ : ∃ n, l.length = n + 1 := ⟨l.length - 1, by
    have : l.length ≠ 0 := by simpa using hl
    omega⟩
  simp only [hn, Tree.walk, hm, Option.bind_some, hq, List.length_dropLast, Nat.add_sub_cancel]

theorem visible_root {T : Tree} (k : Key) :
    visible P T ([], k) = (T.get ([], k)).any (P ·.props) := by
  simp [visible, Tree.walk]

/-! ## Subtrees -/

theorem inSubtree_iff {T : Tree} {x y : Id} :
    inSubtree T x y = true ↔ x.1.length ≤ y.1.length ∧ y.1.take x.1.length = x.1 ∧
      T.walk (y.1.length - x.1.length) y.1 y.2 = some x.2 := by
  simp [inSubtree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc]

/-- Every node of a subtree is as visible as its top. -/
theorem visible_of_inSubtree {T : Tree} {x y : Id} (h : inSubtree T x y = true) :
    visible P T y = visible P T x := by
  rw [inSubtree_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  unfold visible
  have : y.1.length = (y.1.length - x.1.length) + x.1.length := by omega
  rw [this, walk_add, h3, Option.bind_some, up_eq_take]
  rw [show y.1.length - (y.1.length - x.1.length) = x.1.length by omega, h2]

/-- A child of a node of a subtree is in the subtree. -/
theorem inSubtree_child {T : Tree} {x : Id} {l : Level} {k k' : Key} {m : Node} (hl : l ≠ [])
    (hm : T.get (l, k) = some m) (hp : m.parent = some k')
    (h : inSubtree T x (l.dropLast, k') = true) : inSubtree T x (l, k) = true := by
  rw [inSubtree_iff] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  simp only [List.length_dropLast] at h1 h2 h3
  have hlen : l.length ≠ 0 := by simpa using hl
  refine ⟨by simp only; omega, ?_, ?_⟩
  · simp only
    rw [List.dropLast_eq_take, List.take_take,
      show min x.1.length (l.length - 1) = x.1.length by omega] at h2
    exact h2
  · simp only
    rw [show l.length - x.1.length = (l.length - 1 - x.1.length) + 1 by omega, Tree.walk, hm,
      Option.bind_some, hp, Option.bind_some, h3]

/-- The parent of a node of a subtree, other than its top, is in the subtree. -/
theorem inSubtree_parent {T : Tree} {x : Id} {l : Level} {k q : Key} {m : Node}
    (hm : T.get (l, k) = some m) (hp : m.parent = some q)
    (h : inSubtree T x (l, k) = true) (hne : (l, k) ≠ x) : inSubtree T x (l.dropLast, q) = true := by
  rw [inSubtree_iff] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  simp only at h1 h2 h3 ⊢
  have hlt : x.1.length < l.length := by
    rcases Nat.lt_or_eq_of_le h1 with h | h
    · exact h
    · exfalso
      rw [h, Nat.sub_self] at h3
      simp only [Tree.walk, Option.some.injEq] at h3
      rw [h, List.take_length] at h2
      exact hne (Prod.ext h2 h3)
  rw [List.length_dropLast]
  refine ⟨by omega, ?_, ?_⟩
  · rw [List.dropLast_eq_take, List.take_take, show min x.1.length (l.length - 1) = x.1.length by omega, h2]
  · rw [show l.length - x.1.length = (l.length - 1 - x.1.length) + 1 by omega, Tree.walk, hm,
      Option.bind_some, hp, Option.bind_some] at h3
    exact h3

/-! ## Adding and removing a subtree -/

theorem get_eq_none_of_not_mem {T : Tree} {id : Id} (h : id ∉ T.map (·.1)) : T.get id = none := by
  cases hg : T.get id with
  | none => rfl
  | some n => exact absurd (List.mem_map.mpr ⟨(id, n), mem_of_get hg, rfl⟩) h

/-- Adding nodes parents first succeeds when each node's parent is present or
added earlier. -/
theorem addAll : ∀ (L : List (Id × Node)) (B : Tree), B.WF →
    L.Pairwise (fun a b => a.1.1.length ≤ b.1.1.length) →
    (L.map (·.1)).Nodup →
    (∀ e ∈ L, B.get e.1 = none) →
    (∀ e ∈ L, (B ++ L).parentOk e.1.1 e.2.parent = true) →
    ∃ X, B.applyAll (L.map fun e => .added e.1.1 e.1.2 e.2.parent e.2.props) = some X ∧
      ∀ id, X.get id = (Tree.get L id).or (B.get id) := by
  intro L
  induction L with
  | nil => intro B _ _ _ _ _; exact ⟨B, rfl, fun id => by simp⟩
  | cons e L ih =>
    intro B hB hsort hnd hnew hpar
    obtain ⟨⟨l, k⟩, n⟩ := e
    simp only [List.map_cons, List.nodup_cons, List.pairwise_cons] at hnd hsort
    have hpar0 : B.parentOk l n.parent = true := by
      have h := hpar ((l, k), n) List.mem_cons_self
      cases hq : n.parent with
      | none => rw [hq] at h; exact h
      | some q =>
        rw [hq] at h
        simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
          get_append, Option.isSome_or] at h ⊢
        refine ⟨h.1, ?_⟩
        rcases Bool.or_eq_true_iff.mp h.2 with h2 | h2
        · exact h2
        · exfalso
          obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h2
          rcases List.mem_cons.mp (mem_of_get hm) with he | he
          · have := congrArg (fun e : Id × Node => e.1.1.length) he
            simp only [List.length_dropLast] at this
            have : l.length ≠ 0 := by simpa using h.1
            omega
          · have := hsort.1 _ he
            simp only at this
            rw [List.length_dropLast] at this
            have : l.length ≠ 0 := by simpa using h.1
            omega
    have happ : B.apply (.added l k n.parent n.props) = some (((l, k), n) :: B) :=
      apply_added.mpr ⟨hnew _ List.mem_cons_self, hpar0, rfl⟩
    have hB' := apply_wf hB happ
    obtain ⟨X, hX, hXg⟩ := ih (((l, k), n) :: B) hB' hsort.2 hnd.2
      (fun e he => by
        rw [get_cons]
        have : (l, k) ≠ e.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem he)
        simp [this, hnew e (List.mem_cons_of_mem _ he)])
      (fun e he => by
        rw [parentOk_congr (U := B ++ ((l, k), n) :: L) (fun id => ?_)]
        · exact hpar e (List.mem_cons_of_mem _ he)
        · rw [get_append, get_append, get_cons, get_cons]
          by_cases h : (l, k) = id
          · subst h; simp [hnew _ List.mem_cons_self]
          · simp [h])
    refine ⟨X, by simp only [List.map_cons, Tree.applyAll, happ, Option.bind_some]; exact hX,
      fun id => ?_⟩
    rw [hXg, get_cons, get_cons]
    by_cases h : (l, k) = id
    · subst h; simp [get_eq_none_of_not_mem hnd.1]
    · simp [h]

/-- Removing nodes children first succeeds when the list holds every child of
its nodes. -/
theorem removeAll : ∀ (L : List (Id × Node)) (B : Tree), B.WF →
    L.Pairwise (fun a b => b.1.1.length ≤ a.1.1.length) →
    (L.map (·.1)).Nodup →
    (∀ e ∈ L, (B.get e.1).isSome) →
    (∀ e ∈ L, ∀ l' k' m, B.get (l', k') = some m → l' ≠ [] → l'.dropLast = e.1.1 →
      m.parent = some e.1.2 → (l', k') ∈ L.map (·.1)) →
    ∃ X, B.applyAll (L.map fun e => .removed e.1.1 e.1.2) = some X ∧
      ∀ id, X.get id = if id ∈ L.map (·.1) then none else B.get id := by
  intro L
  induction L with
  | nil => intro B _ _ _ _ _; exact ⟨B, rfl, fun id => by simp⟩
  | cons e L ih =>
    intro B hB hsort hnd hin hclose
    obtain ⟨⟨l, k⟩, n⟩ := e
    simp only [List.map_cons, List.nodup_cons, List.pairwise_cons] at hnd hsort
    have hch : B.hasChild l k = false := by
      rw [Bool.eq_false_iff]; intro h
      obtain ⟨l', k', m, hm, hl', hd, hp⟩ := (hasChild_iff hB.nodup l k).mp h
      have hmem := hclose ((l, k), n) List.mem_cons_self l' k' m hm hl' hd hp
      have hlen : l'.length = l.length + 1 := by
        rw [← hd, List.length_dropLast]
        have : l'.length ≠ 0 := by simpa using hl'
        omega
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with he | he
      · have := congrArg (fun e => e.1.length) he; simp at this; omega
      · obtain ⟨e', he', heq⟩ := List.mem_map.mp he
        have := hsort.1 e' he'
        rw [heq] at this; simp only at this; omega
    have happ : B.apply (.removed l k) = some (B.filter (·.1 != (l, k))) :=
      apply_removed.mpr ⟨hin _ List.mem_cons_self, hch, rfl⟩
    obtain ⟨X, hX, hXg⟩ := ih _ (apply_wf hB happ) hsort.2 hnd.2
      (fun e he => by
        rw [get_filter]
        have : e.1 ≠ (l, k) := fun h => hnd.1 (h ▸ List.mem_map_of_mem he)
        simp [this, hin e (List.mem_cons_of_mem _ he)])
      (fun e he l' k' m hm hl' hd hp => by
        rw [get_filter] at hm
        split at hm
        · cases hm
        · rename_i hne
          have := hclose e (List.mem_cons_of_mem _ he) l' k' m hm hl' hd hp
          simp only [List.map_cons, List.mem_cons] at this
          rcases this with h | h
          · exact absurd h hne
          · exact h)
    refine ⟨X, by simp only [List.map_cons, Tree.applyAll, happ, Option.bind_some]; exact hX,
      fun id => ?_⟩
    rw [hXg, get_filter]
    by_cases h : id = (l, k)
    · subst h; simp
    · simp only [h, ↓reduceIte]
      split <;> split <;> simp_all

/-! ## The output is well formed -/

theorem filterF_wf {T : Tree} (hwf : T.WF) : (filter.F P T).WF := by
  refine ⟨(List.filter_sublist.map _).nodup hwf.nodup, fun id n hn => ?_⟩
  rw [get_filterF] at hn
  split at hn
  · rename_i hv
    have hp := hwf.parents id n hn
    cases hq : n.parent with
    | none => rw [hq] at hp; exact hp
    | some q =>
      rw [hq] at hp
      simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff]
        at hp ⊢
      refine ⟨hp.1, ?_⟩
      rw [get_filterF]
      obtain ⟨l, k⟩ := id
      rw [← visible_parent hp.1 hn hq, ite_eq_left hv]
      exact hp.2
  · cases hn

/-! ## Walks over a set closed upward -/

theorem walk_mem {T : Tree} {S : Id → Prop} (hS : UpClosed T S) :
    ∀ n l k r, n = l.length → S (l, k) → T.walk n l k = some r → S ([], r) := by
  intro n
  induction n with
  | zero =>
    intro l k r hn hs h
    have : l = [] := List.eq_nil_of_length_eq_zero hn.symm
    subst this; simp only [Tree.walk, Option.some.injEq] at h; subst h; exact hs
  | succ n ih =>
    intro l k r hn hs h
    simp only [Tree.walk] at h
    cases hm : T.get (l, k) with
    | none => rw [hm] at h; cases h
    | some m =>
      rw [hm, Option.bind_some] at h
      cases hq : m.parent with
      | none => rw [hq] at h; cases h
      | some q =>
        rw [hq, Option.bind_some] at h
        exact ih _ _ r (by rw [List.length_dropLast]; omega) (hS l k m q hs hm hq) h

/-- Visibility reads the parents along a node's path and its root's props. -/
theorem visible_congr {T U : Tree} {S : Id → Prop} (hS : UpClosed T S) (hA : ParentsAgree T U S)
    (hR : ∀ r, S ([], r) → (T.get ([], r)).any (P ·.props) = (U.get ([], r)).any (P ·.props))
    {y : Id} (hy : S y) : visible P T y = visible P U y := by
  obtain ⟨l, k⟩ := y
  unfold visible
  rw [← walk_congr hS hA _ _ _ hy]
  cases h : T.walk l.length l k with
  | none => rfl
  | some r => exact hR r (walk_mem hS _ _ _ r rfl hy h)

/-- The nodes of a well-formed tree are closed upward. -/
theorem upClosed_present {T : Tree} (hwf : T.WF) : UpClosed T fun z => (T.get z).isSome := by
  intro l k m q _ hm hq
  have := hwf.parents _ _ hm
  rw [hq] at this
  simp only [Tree.parentOk, Bool.and_eq_true] at this
  exact this.2

/-- The nodes outside a subtree are closed upward. -/
theorem upClosed_outside {T : Tree} (hwf : T.WF) (x : Id) :
    UpClosed T fun z => inSubtree T x z = false := by
  intro l k m q hs hm hq
  rw [Bool.eq_false_iff] at hs ⊢
  intro h
  by_cases hl : l = []
  · subst hl
    have := hwf.parents _ _ hm
    rw [hq] at this
    simp [Tree.parentOk] at this
  · exact hs (inSubtree_child hl hm hq h)

/-! ## An event that changes one node -/

theorem inSubtree_self (T : Tree) (x : Id) : inSubtree T x x = true := by
  rw [inSubtree_iff]; simp [Tree.walk]

/-- What a change at node `x` does: the tree changes only at `x`, visibility
changes only at or below `x`, and the subtree below `x` is the same. -/
structure Local (P : Props → Bool) (T T' : Tree) (x : Id) : Prop where
  only : ∀ y, y ≠ x → T'.get y = T.get y
  outside : ∀ y, inSubtree T x y = false → visible P T' y = visible P T y
  subtree : ∀ y, inSubtree T' x y = inSubtree T x y
  below : ∀ y, inSubtree T x y = true →
    visible P T y = visible P T x ∧ visible P T' y = visible P T' x

/-- Changing one node, its props or its parent, is local to its subtree. -/
theorem local_update {T : Tree} (hwf : T.WF) (x : Id) (f : Node → Node) :
    Local P T (T.update x f) x := by
  have only : ∀ y, y ≠ x → (T.update x f).get y = T.get y := fun y hy => by
    rw [get_update]; simp [hy]
  have subtree : ∀ y, inSubtree (T.update x f) x y = inSubtree T x y := by
    intro y
    simp only [inSubtree]
    by_cases hl : x.1.length ≤ y.1.length
    · rw [walk_congr_deep (d := x.1.length) (U := T) (fun z hz => by
        rw [only z (fun h => by subst h; omega)]) _ _ _ (by omega)]
    · simp [hl]
  refine ⟨only, fun y hy => ?_, subtree, fun y hy => ?_⟩
  · refine (visible_congr (upClosed_outside hwf x) (fun z hz => ?_) (fun r hr => ?_) hy).symm
    · have : z ≠ x := fun h => by subst h; simp [inSubtree_self] at hz
      rw [only z this]
    · have : ([], r) ≠ x := fun h => by subst h; simp [inSubtree_self] at hr
      rw [only _ this]
  · exact ⟨visible_of_inSubtree hy, visible_of_inSubtree (by rw [subtree]; exact hy)⟩

/-- The output, when a change leaves a subtree hidden before and after. -/
theorem hidden_equiv {T T' : Tree} {x : Id} (hL : Local P T T' x)
    (h1 : visible P T x = false) (h2 : visible P T' x = false) :
    (filter.F P T).Equiv (filter.F P T') := by
  intro y
  rw [get_filterF, get_filterF]
  cases hs : inSubtree T x y
  · rw [hL.outside y hs]
    by_cases hy : y = x
    · subst hy; simp [inSubtree_self] at hs
    · rw [hL.only y hy]
  · obtain ⟨b1, b2⟩ := hL.below y hs
    simp [b1, b2, h1, h2]

/-- Visibility is the same everywhere after a change that leaves its node's
visibility alone. -/
theorem visible_same {T T' : Tree} {x : Id} (hL : Local P T T' x)
    (h : visible P T' x = visible P T x) (y : Id) : visible P T' y = visible P T y := by
  cases hs : inSubtree T x y
  · exact hL.outside y hs
  · obtain ⟨b1, b2⟩ := hL.below y hs; rw [b1, b2, h]

/-- A visible node keeps its visibility: the change passes through. -/
theorem forward_equiv {T T' : Tree} {x : Id} (hL : Local P T T' x)
    (h : visible P T' x = visible P T x) {U : Tree}
    (hU : ∀ y, U.get y = if y = x then (if visible P T x then T'.get x else none)
      else (filter.F P T).get y) :
    U.Equiv (filter.F P T') := by
  intro y
  rw [hU, get_filterF T' y, visible_same hL h y]
  by_cases hy : y = x
  · subst hy; simp
  · simp [hy, get_filterF, hL.only y hy]

/-! ## Adding and removing a subtree in the output -/

theorem mem_subtreeList {T : Tree} {x : Id} {le : Id × Node → Id × Node → Bool} {e : Id × Node} :
    e ∈ (T.filter (inSubtree T x ·.1)).mergeSort le ↔ e ∈ T ∧ inSubtree T x e.1 = true := by
  simp [List.mem_mergeSort, List.mem_filter]

theorem nodup_subtreeList {T : Tree} (hwf : T.WF) (x : Id) (le : Id × Node → Id × Node → Bool) :
    (((T.filter (inSubtree T x ·.1)).mergeSort le).map (·.1)).Nodup :=
  (((List.mergeSort_perm _ le).map _).nodup_iff).mpr ((List.filter_sublist.map _).nodup hwf.nodup)

/-- **Admitting** a subtree that becomes visible. -/
theorem admit_correct {T T' : Tree} {x : Id} (hwf : T.WF) (hwf' : T'.WF) (hL : Local P T T' x)
    (h1 : visible P T x = false) (h2 : visible P T' x = true) :
    ∃ U, (filter.F P T).applyAll (admit T' x) = some U ∧ U.Equiv (filter.F P T') := by
  let le : Id × Node → Id × Node → Bool := fun a b => a.1.1.length ≤ b.1.1.length
  let L := (T'.filter (inSubtree T' x ·.1)).mergeSort le
  have hnd := nodup_subtreeList hwf' x le
  have hgetL : ∀ e ∈ L, Tree.get L e.1 = some e.2 := fun e he => get_of_mem hnd he
  have hmemL : ∀ y n, T'.get y = some n → inSubtree T' x y = true → (y, n) ∈ L := fun y n hn hs =>
    mem_subtreeList.mpr ⟨mem_of_get hn, hs⟩
  have hFTnone : ∀ y, inSubtree T' x y = true → (filter.F P T).get y = none := fun y hs => by
    rw [hL.subtree] at hs
    rw [get_filterF, (hL.below y hs).1, h1]; rfl
  obtain ⟨X, hX, hXg⟩ := addAll L (filter.F P T) (filterF_wf hwf)
    (List.pairwise_mergeSort (fun a b c hab hbc => by simp only [le, decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) _ |>.imp
      fun h => by simpa [le] using h)
    hnd
    (fun e he => hFTnone e.1 (mem_subtreeList.mp he).2)
    (fun ⟨⟨l, k⟩, n⟩ he => by
      obtain ⟨hm, hs⟩ := mem_subtreeList.mp he
      have hn := get_of_mem hwf'.nodup hm
      have hp := hwf'.parents _ _ hn
      cases hq : n.parent with
      | none => rw [hq] at hp; exact hp
      | some q =>
        rw [hq] at hp
        simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true',
          List.isEmpty_eq_false_iff] at hp ⊢
        refine ⟨hp.1, ?_⟩
        obtain ⟨m, hm'⟩ := Option.isSome_iff_exists.mp hp.2
        rw [get_append]
        by_cases hx : (l, k) = x
        · -- The parent of the top is outside the subtree, so already in the output.
          have hout : inSubtree T x (l.dropLast, q) = false := by
            rw [Bool.eq_false_iff]; intro hin
            rw [inSubtree_iff, ← hx] at hin
            obtain ⟨hlen, -, -⟩ := hin
            simp only [List.length_dropLast] at hlen
            have : l.length ≠ 0 := by simpa using hp.1
            omega
          have hv : visible P T (l.dropLast, q) = true := by
            rw [← hL.outside _ hout, ← visible_parent hp.1 hn hq, hx]; exact h2
          have hne : (l.dropLast, q) ≠ x := fun h => by
            rw [← h] at hout; simp [inSubtree_self] at hout
          rw [get_filterF, hv, ite_eq_left rfl, ← hL.only _ hne, hm']
          rfl
        · have hpar := inSubtree_parent hn hq hs hx
          rw [hgetL _ (hmemL _ m hm' hpar)]
          simp)
  refine ⟨X, hX, fun y => ?_⟩
  rw [hXg, get_filterF T' y]
  cases hs : inSubtree T' x y
  · have hnone : Tree.get L y = none := get_eq_none_of_not_mem fun hm => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      rw [(mem_subtreeList.mp he).2] at hs; cases hs
    rw [hL.subtree] at hs
    rw [hnone, Option.none_or, get_filterF, hL.outside y hs]
    by_cases hy : y = x
    · subst hy; simp [inSubtree_self] at hs
    · rw [hL.only y hy]
  · rw [hFTnone y hs, Option.or_none]
    have hb := (hL.below y (by rw [← hL.subtree]; exact hs)).2
    rw [hb, h2, ite_eq_left rfl]
    cases hn : T'.get y with
    | none =>
      exact get_eq_none_of_not_mem fun hm => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        rw [get_of_mem hwf'.nodup (mem_subtreeList.mp he).1] at hn; cases hn
    | some n => exact hgetL _ (hmemL y n hn hs)

/-- **Evicting** a subtree that becomes hidden. -/
theorem evict_correct {T T' : Tree} {x : Id} (hwf : T.WF) (hL : Local P T T' x)
    (h1 : visible P T x = true) (h2 : visible P T' x = false) :
    ∃ U, (filter.F P T).applyAll (evict T x) = some U ∧ U.Equiv (filter.F P T') := by
  let le : Id × Node → Id × Node → Bool := fun a b => b.1.1.length ≤ a.1.1.length
  let L := (T.filter (inSubtree T x ·.1)).mergeSort le
  have hnd := nodup_subtreeList hwf x le
  obtain ⟨X, hX, hXg⟩ := removeAll L (filter.F P T) (filterF_wf hwf)
    (List.pairwise_mergeSort (fun a b c hab hbc => by simp only [le, decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) _ |>.imp
      fun h => by simpa [le] using h)
    hnd
    (fun e he => by
      obtain ⟨hm, hs⟩ := mem_subtreeList.mp he
      rw [get_filterF, (hL.below e.1 hs).1, h1, ite_eq_left rfl, get_of_mem hwf.nodup hm]; rfl)
    (fun e he l' k' m hm hl' hd hp => by
      obtain ⟨-, hs⟩ := mem_subtreeList.mp he
      rw [get_filterF] at hm
      split at hm
      · refine List.mem_map.mpr ⟨((l', k'), m), mem_subtreeList.mpr ⟨mem_of_get hm, ?_⟩, rfl⟩
        exact inSubtree_child hl' hm hp (by rw [hd]; exact hs)
      · cases hm)
  refine ⟨X, hX, fun y => ?_⟩
  rw [hXg, get_filterF T' y]
  cases hs : inSubtree T x y
  · have hnot : y ∉ L.map (·.1) := fun hm => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
      rw [(mem_subtreeList.mp he).2] at hs; cases hs
    rw [ite_eq_right hnot, get_filterF, hL.outside y hs]
    by_cases hy : y = x
    · subst hy; simp [inSubtree_self] at hs
    · rw [hL.only y hy]
  · rw [(hL.below y hs).2, h2]
    simp only [Bool.false_eq_true, ↓reduceIte, ite_eq_left_iff]
    intro hnot
    rw [get_filterF, (hL.below y hs).1, h1, ite_eq_left rfl]
    cases hn : T.get y with
    | none => rfl
    | some n => exact absurd (List.mem_map.mpr ⟨(y, n), mem_subtreeList.mpr ⟨mem_of_get hn, hs⟩, rfl⟩) hnot

/-! ## The step -/

theorem inSubtree_shorter {T : Tree} {x y : Id} (h : y.1.length < x.1.length) :
    inSubtree T x y = false := by
  rw [Bool.eq_false_iff]; intro hin
  rw [inSubtree_iff] at hin; omega

/-- A node's visibility, after a change that leaves its parent and, for a root,
its predicate alone. -/
theorem visible_unchanged {T : Tree} (hwf : T.WF) {l : Level} {k : Key} {n : Node}
    (hn : T.get (l, k) = some n) (f : Node → Node) (hpar : (f n).parent = n.parent)
    (hroot : l = [] → P (f n).props = P n.props) :
    visible P (T.update (l, k) f) (l, k) = visible P T (l, k) := by
  by_cases hl : l = []
  · subst hl
    rw [visible_root, visible_root, get_update]; simp [hn, hroot rfl]
  · have hp := hwf.parents _ _ hn
    cases hq : n.parent with
    | none => rw [hq] at hp; simp [Tree.parentOk, hl] at hp
    | some q =>
      have hn' : (T.update (l, k) f).get (l, k) = some (f n) := by rw [get_update]; simp [hn]
      rw [visible_parent hl hn' (hpar.trans hq), visible_parent hl hn hq,
        (local_update (P := P) hwf (l, k) f).outside _ (inSubtree_shorter (by
          simp only [List.length_dropLast]
          have : l.length ≠ 0 := by simpa using hl
          omega))]

/-- **`filter_correct`.** The step is correct when `P` reads only the
properties in `deps`. -/
theorem filter_correct (P : Props → Bool) (deps : List String)
    (hdeps : ∀ ps p v, p ∉ deps → P (ps.set p v) = P ps) :
    Correct (filterStep P deps) (filter.F P) := by
  intro T e T' hwf he
  have hwf' := apply_wf hwf he
  simp only [filterStep, he]
  cases e with
  | added l k p ps =>
    obtain ⟨hn, hp, rfl⟩ := apply_added.mp he
    have hother : ∀ y, y ≠ (l, k) → visible P (((l, k), ⟨p, ps⟩) :: T) y = visible P T y := by
      intro y hy
      have hget : ∀ z, z ≠ (l, k) → Tree.get (((l, k), ⟨p, ps⟩) :: T) z = T.get z := fun z hz => by
        rw [get_cons]; simp [Ne.symm hz]
      by_cases hs : (T.get y).isSome
      · refine (visible_congr (upClosed_present hwf) (fun z hz => ?_) (fun r hr => ?_) hs).symm
        · rw [hget z fun h => by subst h; simp [hn] at hz]
        · rw [hget _ fun h => by rw [h] at hr; simp [hn] at hr]
      · simp only [Option.not_isSome_iff_eq_none] at hs
        rw [visible_absent hs, visible_absent (by rw [hget y hy]; exact hs)]
    by_cases hv : visible P (((l, k), ⟨p, ps⟩) :: T) (l, k) = true
    · simp only [hv, ↓reduceIte, applyAll_single]
      refine ⟨_, apply_added.mpr ⟨by rw [get_filterF]; simp [hn], ?_, rfl⟩, fun y => ?_⟩
      · cases p with
        | none => exact hp
        | some q =>
          simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true',
            List.isEmpty_eq_false_iff] at hp ⊢
          refine ⟨hp.1, ?_⟩
          have hne : (l.dropLast, q) ≠ (l, k) := fun h => by
            have := congrArg (fun z : Id => z.1.length) h
            simp only [List.length_dropLast] at this
            have : l.length ≠ 0 := by simpa using hp.1
            omega
          have hnode : Tree.get (((l, k), ⟨some q, ps⟩) :: T) (l, k) = some ⟨some q, ps⟩ := by
            rw [get_cons]; simp
          rw [get_filterF, ← hother _ hne, ← visible_parent hp.1 hnode rfl, hv, ite_eq_left rfl]
          exact hp.2
      · rw [get_cons, get_filterF, get_filterF]
        by_cases hy : (l, k) = y
        · subst hy; simp [hv, get_cons]
        · simp only [hy, ↓reduceIte, hother y (Ne.symm hy), get_cons]
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, rfl, fun y => ?_⟩
      rw [get_filterF, get_filterF]
      by_cases hy : y = (l, k)
      · subst hy; simp [hn, hv]
      · rw [hother y hy, get_cons]; simp [Ne.symm hy]
  | removed l k =>
    obtain ⟨hs, hc, rfl⟩ := apply_removed.mp he
    have hother : ∀ y, y ≠ (l, k) → visible P (T.filter (·.1 != (l, k))) y = visible P T y := by
      intro y hy
      have hget : ∀ z, z ≠ (l, k) → Tree.get (T.filter (·.1 != (l, k))) z = T.get z := fun z hz => by
        rw [get_filter]; simp [hz]
      by_cases hs' : (Tree.get (T.filter (·.1 != (l, k))) y).isSome
      · refine visible_congr (upClosed_present hwf') (fun z hz => ?_) (fun r hr => ?_) hs'
        · have : z ≠ (l, k) := fun h => by subst h; simp [get_filter] at hz
          rw [hget z this]
        · have : ([], r) ≠ (l, k) := fun h => by rw [h] at hr; simp [get_filter] at hr
          rw [hget _ this]
      · simp only [Option.not_isSome_iff_eq_none] at hs'
        rw [visible_absent hs', visible_absent (by rw [← hget y hy]; exact hs')]
    by_cases hv : visible P T (l, k) = true
    · simp only [hv, ↓reduceIte, applyAll_single]
      have hFwf := filterF_wf (P := P) hwf
      refine ⟨_, apply_removed.mpr ⟨by rw [get_filterF]; simpa [hv] using hs, ?_, rfl⟩, fun y => ?_⟩
      · rw [Bool.eq_false_iff]; intro h
        obtain ⟨l', k', m, hm, h1, h2, h3⟩ := (hasChild_iff hFwf.nodup l k).mp h
        rw [get_filterF] at hm; split at hm
        · exact absurd ((hasChild_iff hwf.nodup l k).mpr ⟨l', k', m, hm, h1, h2, h3⟩) (by simp [hc])
        · cases hm
      · rw [get_filter, get_filterF, get_filterF]
        by_cases hy : y = (l, k)
        · subst hy; simp [get_filter]
        · simp only [hy, ↓reduceIte, hother y hy, get_filter]
    · simp only [hv, Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, rfl, fun y => ?_⟩
      rw [get_filterF, get_filterF]
      by_cases hy : y = (l, k)
      · subst hy; simp [hv, get_filter]
      · rw [hother y hy, get_filter]; simp [hy]
  | modified l k p old new =>
    obtain ⟨n, hn, h1, h2, rfl⟩ := apply_modified.mp he
    let f : Node → Node := fun n => { n with props := n.props.set p new }
    have hL := local_update (P := P) hwf (l, k) f
    have hforward : visible P T (l, k) = true → visible P (T.update (l, k) f) (l, k) = true →
        ∃ U, (filter.F P T).applyAll [.modified l k p old new] = some U ∧
          U.Equiv (filter.F P (T.update (l, k) f)) := by
      intro hv1 hv2
      rw [applyAll_single]
      have hFn : (filter.F P T).get (l, k) = some n := by rw [get_filterF, hv1, ite_eq_left rfl, hn]
      refine ⟨_, apply_modified.mpr ⟨n, hFn, h1, h2, rfl⟩, forward_equiv hL (hv2.trans hv1.symm) ?_⟩
      intro y
      rw [get_update]
      by_cases hy : y = (l, k)
      · subst hy; simp [hFn, hv1, get_update, hn, f]
      · simp [hy]
    by_cases hr : l = [] ∧ p ∈ deps
    · obtain ⟨rfl, hpd⟩ := hr
      simp only [hpd, and_self, ↓reduceIte]
      split <;> rename_i hv1 hv2
      · exact hforward hv1 hv2
      · exact admit_correct hwf hwf' hL hv1 hv2
      · exact evict_correct hwf hL hv1 hv2
      · exact ⟨_, rfl, hidden_equiv hL hv1 hv2⟩
    · simp only [hr, ↓reduceIte]
      have hsame : visible P (T.update (l, k) f) (l, k) = visible P T (l, k) :=
        visible_unchanged hwf hn f rfl fun hl => hdeps _ _ _ fun hp => hr ⟨hl, hp⟩
      cases hv1 : visible P T (l, k)
      · exact ⟨_, rfl, hidden_equiv hL hv1 (hsame.trans hv1)⟩
      · exact hforward hv1 (hsame.trans hv1)
  | placed l k a b =>
    obtain ⟨n, hn, h1, h2, h3, rfl⟩ := apply_placed.mp he
    let f : Node → Node := fun n => { n with parent := some b }
    have hL := local_update (P := P) hwf (l, k) f
    have hl : l ≠ [] := fun h => by subst h; simp [Tree.parentOk] at h3
    dsimp only
    split <;> rename_i hv1 hv2
    rotate_left
    · exact admit_correct hwf hwf' hL hv1 hv2
    · exact evict_correct hwf hL hv1 hv2
    · exact ⟨_, rfl, hidden_equiv hL hv1 hv2⟩
    · rw [applyAll_single]
      have hFn : (filter.F P T).get (l, k) = some n := by rw [get_filterF, hv1, ite_eq_left rfl, hn]
      have hb : ((filter.F P T).get (l.dropLast, b)).isSome := by
        simp only [Tree.parentOk, Bool.and_eq_true] at h3
        have hn' : (T.update (l, k) f).get (l, k) = some (f n) := by rw [get_update]; simp [hn]
        rw [get_filterF, ← hL.outside _ (inSubtree_shorter (by
            simp only [List.length_dropLast]
            have : l.length ≠ 0 := by simpa using hl
            omega)),
          ← visible_parent hl hn' rfl, hv2, ite_eq_left rfl]
        exact h3.2
      refine ⟨_, apply_placed.mpr ⟨n, hFn, h1, h2, by simp [Tree.parentOk, hl, hb], rfl⟩,
        forward_equiv hL (hv2.trans hv1.symm) fun y => ?_⟩
      rw [get_update]
      by_cases hy : y = (l, k)
      · subst hy; simp [hFn, hv1, get_update, hn, f]
      · simp [hy]

end JinagaSpec.Cascade
