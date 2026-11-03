import JinagaSpec.Cascade.Session
import JinagaSpec.Proofs.Cascade.Tree

/-!
# Cascade: the output session follows the tree

Nested arrays that hold a tree hold every node where the placement index locates
it (`located`). So an event the tree accepts, located through the index, applies
to the arrays, and the arrays then hold the new tree (`session_apply`).
-/
namespace JinagaSpec.Cascade

/-! ## Entries and the tree they hold -/

theorem holds_iff {A : Arrays} {l : Level} {kp : List Key} {k : Key} :
    A.holds l kp k = true ↔ ∃ e ∈ A, e.segmentPath = l ∧ e.keyPath = kp ∧ e.key = k := by
  simp [Arrays.holds, and_assoc]

theorem tree_get_of_mem {A : Arrays} (hnd : (A.map (·.id)).Nodup) {e : Located} (he : e ∈ A) :
    A.tree.get e.id = some e.node := by
  apply get_of_mem
  · have : A.tree.map (·.1) = A.map (·.id) := by simp [Arrays.tree, Function.comp_def]
    rwa [this]
  · exact List.mem_map.mpr ⟨e, he, rfl⟩

theorem mem_of_tree_get {A : Arrays} {id : Id} {n : Node} (h : A.tree.get id = some n) :
    ∃ e ∈ A, e.id = id ∧ e.node = n := by
  obtain ⟨e, he, hx⟩ := List.mem_map.mp (mem_of_get h)
  exact ⟨e, he, (Prod.mk.inj hx).1, (Prod.mk.inj hx).2⟩

theorem eq_of_id {A : Arrays} (hnd : (A.map (·.id)).Nodup) {e f : Located} (he : e ∈ A) (hf : f ∈ A)
    (h : e.id = f.id) : e = f := by
  induction A with
  | nil => simp at he
  | cons x A ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp he with h1 | h1 <;> rcases List.mem_cons.mp hf with h2 | h2
    · rw [h1, h2]
    · subst h1; exact absurd ⟨f, h2, h.symm⟩ hnd.1
    · subst h2; exact absurd ⟨e, h1, h⟩ hnd.1
    · exact ih hnd.2 h1 h2

/-! ## The index locates every entry -/

theorem ancestors_nil (T : Tree) : T.ancestors [] none = some [] := rfl

theorem ancestors_some {T : Tree} {l : Level} (hl : l ≠ []) (q : Key) :
    T.ancestors l (some q) =
      (T.get (l.dropLast, q)).bind fun m => (T.ancestors l.dropLast m.parent).map (· ++ [q]) := by
  have : l.length = l.dropLast.length + 1 := by
    rw [List.length_dropLast]; have := List.length_pos_iff.mpr hl; omega
  unfold Tree.ancestors; rw [this]; rfl

/-- Nested arrays that hold `T` hold each node where `T`'s parents locate it. -/
theorem located {A : Arrays} {T : Tree} (hA : A.Holds T) :
    ∀ e ∈ A, T.ancestors e.segmentPath e.keyPath.getLast? = some e.keyPath := by
  suffices ∀ n, ∀ e ∈ A, e.keyPath.length = n →
      T.ancestors e.segmentPath e.keyPath.getLast? = some e.keyPath from
    fun e he => this _ e he rfl
  intro n
  induction n with
  | zero =>
    intro e he hn
    have hl := (hA.nested e he).1
    rw [List.length_eq_zero_iff.mp hn] at hl ⊢
    rw [List.length_eq_zero_iff.mp hl.symm]; rfl
  | succ n ih =>
    intro e he hn
    obtain ⟨hlen, hp⟩ := hA.nested e he
    obtain ⟨kp, q, hkp⟩ : ∃ kp q, e.keyPath = kp ++ [q] := by
      rcases List.eq_nil_or_concat e.keyPath with h | ⟨kp, q, h⟩
      · rw [h] at hn; simp at hn
      · exact ⟨kp, q, by rw [h, List.concat_eq_append]⟩
    simp only [Arrays.parentHeld, hkp, List.getLast?_concat, List.dropLast_concat,
      Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hp
    obtain ⟨hl, hh⟩ := hp
    obtain ⟨g, hg, hgs, hgk, hgq⟩ := holds_iff.mp hh
    have hget : T.get (e.segmentPath.dropLast, q) = some g.node := by
      rw [← hA.equiv, ← tree_get_of_mem hA.nodup hg, Located.id, hgs, hgq]
    have hgn : g.keyPath.length = n := by
      rw [hkp] at hn; simp at hn; rw [hgk]; exact hn
    have := ih g hg hgn
    rw [hkp, List.getLast?_concat, ancestors_some hl, hget]
    simp only [Option.bind_some, Located.node]
    rw [← hgs, this, hgk]; rfl

/-! ## Parents, and what lies within a node -/

theorem exists_concat {xs : List Key} (h : xs ≠ []) : ∃ ys y, xs = ys ++ [y] := by
  rcases List.eq_nil_or_concat xs with h' | ⟨ys, y, h'⟩
  · exact absurd h' h
  · exact ⟨ys, y, by rw [h', List.concat_eq_append]⟩

theorem parentHeld_nil (A : Arrays) : A.parentHeld [] [] = true := rfl

theorem parentHeld_decomp {A : Arrays} {l : Level} {kp : List Key} (h : A.parentHeld l kp = true)
    (hkp : kp ≠ []) :
    ∃ g ∈ A, l ≠ [] ∧ g.segmentPath = l.dropLast ∧ kp = g.keyPath ++ [g.key] := by
  obtain ⟨kp', q, rfl⟩ := exists_concat hkp
  simp only [Arrays.parentHeld, List.getLast?_concat, List.dropLast_concat,
    Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨g, hg, hgs, hgk, hgq⟩ := holds_iff.mp h.2
  exact ⟨g, hg, h.1, hgs, by rw [hgk, hgq]⟩

theorem parentHeld_of {A : Arrays} {l : Level} {kp : List Key} {g : Located} (hg : g ∈ A)
    (hl : l ≠ []) (hs : g.segmentPath = l.dropLast) (hk : kp = g.keyPath ++ [g.key]) :
    A.parentHeld l kp = true := by
  subst hk
  simp only [Arrays.parentHeld, List.getLast?_concat, List.dropLast_concat,
    Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff]
  exact ⟨hl, holds_iff.mpr ⟨g, hg, hs, rfl, rfl⟩⟩

theorem parentHeld_mono {A B : Arrays} (hAB : ∀ e ∈ A, e ∈ B) {l : Level} {kp : List Key}
    (h : A.parentHeld l kp = true) : B.parentHeld l kp = true := by
  by_cases hkp : kp = []
  · subst hkp; exact h
  · obtain ⟨g, hg, hl, hs, hk⟩ := parentHeld_decomp h hkp
    exact parentHeld_of (hAB g hg) hl hs hk

/-- The entry that holds an entry's parent. -/
theorem parent_entry {A : Arrays} {T : Tree} (hA : A.Holds T) {e : Located} (he : e ∈ A)
    (hne : e.keyPath ≠ []) :
    ∃ g ∈ A, e.segmentPath ≠ [] ∧ g.segmentPath = e.segmentPath.dropLast ∧
      e.keyPath = g.keyPath ++ [g.key] :=
  parentHeld_decomp (hA.nested e he).2 hne

theorem parentHeld_root {A : Arrays} {T : Tree} (hA : A.Holds T) {e : Located} (he : e ∈ A)
    (hkp : e.keyPath = []) (B : Arrays) : B.parentHeld e.segmentPath e.keyPath = true := by
  have hl := (hA.nested e he).1
  rw [hkp, List.length_nil, eq_comm, List.length_eq_zero_iff] at hl
  rw [hkp, hl]; rfl

theorem isAt_iff {e : Located} {l : Level} {kp : List Key} {k : Key} :
    e.isAt l kp k = true ↔ e.segmentPath = l ∧ e.keyPath = kp ∧ e.key = k := by
  simp [Located.isAt, and_assoc]

theorem isBelow_iff {e : Located} {l : Level} {kp : List Key} {k : Key} :
    e.isBelow l kp k = true ↔ l <+: e.segmentPath ∧ kp ++ [k] <+: e.keyPath := by
  simp [Located.isBelow, List.isPrefixOf_iff_prefix]

theorem within_iff {e : Located} {l : Level} {kp : List Key} {k : Key} :
    e.within l kp k = true ↔ e.isAt l kp k = true ∨ e.isBelow l kp k = true := by
  simp [Located.within]

theorem within_length {e : Located} {l : Level} {kp : List Key} {k : Key}
    (h : e.within l kp k = true) : kp.length ≤ e.keyPath.length := by
  rcases within_iff.mp h with h | h
  · rw [(isAt_iff.mp h).2.1]; exact Nat.le_refl _
  · have := (isBelow_iff.mp h).2.length_le; simp at this; omega

/-- Below whatever holds an entry's parent, the entry lies too. -/
theorem parent_below {e g : Located} {l : Level} {kp : List Key} {k : Key}
    (hs : g.segmentPath = e.segmentPath.dropLast) (hk : e.keyPath = g.keyPath ++ [g.key])
    (h : g.within l kp k = true) : e.isBelow l kp k = true := by
  rw [isBelow_iff]
  rcases within_iff.mp h with h | h
  · obtain ⟨h1, h2, h3⟩ := isAt_iff.mp h
    refine ⟨?_, ?_⟩
    · rw [← h1, hs]; exact List.dropLast_prefix _
    · rw [hk, h2, h3]; exact List.prefix_refl _
  · obtain ⟨h1, h2⟩ := isBelow_iff.mp h
    refine ⟨h1.trans ?_, h2.trans ?_⟩
    · rw [hs]; exact List.dropLast_prefix _
    · rw [hk]; exact List.prefix_append _ _

/-- What holds the parent of an entry below a node lies within that node. -/
theorem below_parent {e g : Located} {l : Level} {kp : List Key} {k : Key}
    (hlen : kp.length = l.length) (hel : e.keyPath.length = e.segmentPath.length)
    (hs : g.segmentPath = e.segmentPath.dropLast) (hk : e.keyPath = g.keyPath ++ [g.key])
    (h : e.isBelow l kp k = true) : g.within l kp k = true := by
  obtain ⟨h1, h2⟩ := isBelow_iff.mp h
  have hl2 := h2.length_le
  have hg : g.keyPath.length + 1 = e.keyPath.length := by rw [hk]; simp
  have hd : e.segmentPath.dropLast.length + 1 = e.segmentPath.length := by
    rw [List.length_dropLast]; simp at hl2; omega
  rw [within_iff]
  by_cases hc : e.keyPath.length = kp.length + 1
  · left
    have heq : kp ++ [k] = g.keyPath ++ [g.key] := by
      rw [← hk]; exact h2.eq_of_length (by simp [hc])
    obtain ⟨h3, h4⟩ := List.append_inj' heq rfl
    have h5 : l = e.segmentPath.dropLast :=
      (List.prefix_of_prefix_length_le h1 (List.dropLast_prefix _) (by omega)).eq_of_length
        (by omega)
    rw [isAt_iff]
    exact ⟨by rw [hs, h5], h3.symm, (List.singleton_inj.mp h4).symm⟩
  · right
    rw [isBelow_iff]
    simp at hl2
    refine ⟨?_, ?_⟩
    · rw [hs]; exact List.prefix_of_prefix_length_le h1 (List.dropLast_prefix _) (by omega)
    · refine List.prefix_of_prefix_length_le h2 ?_ (by simp; omega)
      rw [hk]; exact List.prefix_append _ _

/-! ## How the index locates an event -/

theorem located_get {A : Arrays} {T : Tree} (hA : A.Holds T) {l : Level} {k : Key} {n : Node}
    (h : T.get (l, k) = some n) :
    ∃ e ∈ A, e.segmentPath = l ∧ e.key = k ∧ e.node = n ∧ T.ancestors l n.parent = some e.keyPath := by
  rw [← hA.equiv] at h
  obtain ⟨e, he, hid, hn⟩ := mem_of_tree_get h
  obtain ⟨hs, hk⟩ := Prod.mk.inj hid
  refine ⟨e, he, hs, hk, hn, ?_⟩
  rw [← hn, ← hs]; exact located hA e he

theorem ancestors_parent {A : Arrays} {T : Tree} (hA : A.Holds T) {l : Level} {p : Option Key}
    (hp : T.parentOk l p = true) :
    ∃ kp, T.ancestors l p = some kp ∧ A.parentHeld l kp = true ∧ kp.length = l.length ∧
      kp.getLast? = p := by
  cases p with
  | none =>
    simp only [Tree.parentOk, List.isEmpty_iff] at hp
    subst hp; exact ⟨[], rfl, rfl, rfl, rfl⟩
  | some q =>
    simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      Option.isSome_iff_exists] at hp
    obtain ⟨hl, m, hm⟩ := hp
    obtain ⟨g, hg, hgs, hgq, hgn, hanc⟩ := located_get hA hm
    refine ⟨g.keyPath ++ [q], ?_, parentHeld_of hg hl hgs (by rw [hgq]), ?_, by simp⟩
    · rw [ancestors_some hl, hm]; simp [hanc]
    · have := (hA.nested g hg).1
      rw [hgs, List.length_dropLast] at this
      have := List.length_pos_iff.mpr hl
      simp; omega

/-- Within nested arrays, the node at `e0`'s location is `e0`. -/
theorem isAt_iff_id {A : Arrays} {T : Tree} (hA : A.Holds T) {e0 e : Located} {l : Level} {k : Key}
    (he0 : e0 ∈ A) (hs : e0.segmentPath = l) (hk : e0.key = k) (he : e ∈ A) :
    e.isAt l e0.keyPath k = true ↔ e.id = (l, k) := by
  constructor
  · intro h; obtain ⟨h1, -, h3⟩ := isAt_iff.mp h; simp [Located.id, h1, h3]
  · intro h
    rw [eq_of_id hA.nodup he he0 (h.trans (by simp [Located.id, hs, hk]))]
    simp [Located.isAt, hs, hk]

theorem holds_map_eq {A : Arrays} {φ : Located → Located}
    (hφ : ∀ e ∈ A, (φ e).segmentPath = e.segmentPath ∧ (φ e).keyPath = e.keyPath ∧ (φ e).key = e.key)
    (l : Level) (kp : List Key) (k : Key) : Arrays.holds (A.map φ) l kp k = A.holds l kp k := by
  rw [Bool.eq_iff_iff, holds_iff, holds_iff]
  constructor
  · rintro ⟨e', he', h1, h2, h3⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
    obtain ⟨a, b, c⟩ := hφ e he
    exact ⟨e, he, by rw [← a]; exact h1, by rw [← b]; exact h2, by rw [← c]; exact h3⟩
  · rintro ⟨e, he, h1, h2, h3⟩
    obtain ⟨a, b, c⟩ := hφ e he
    exact ⟨φ e, List.mem_map_of_mem he, by rw [a]; exact h1, by rw [b]; exact h2, by rw [c]; exact h3⟩

theorem parentHeld_map_eq {A : Arrays} {φ : Located → Located}
    (hφ : ∀ e ∈ A, (φ e).segmentPath = e.segmentPath ∧ (φ e).keyPath = e.keyPath ∧ (φ e).key = e.key)
    (l : Level) (kp : List Key) : Arrays.parentHeld (A.map φ) l kp = A.parentHeld l kp := by
  unfold Arrays.parentHeld; split <;> simp [holds_map_eq hφ]

/-- A map that keeps each entry's id, and changes the node at `x` by `f`, takes
the tree to `T.update x f`. -/
theorem Arrays.Holds.map_update {A : Arrays} {T : Tree} (hA : A.Holds T) (φ : Located → Located)
    (hid : ∀ e ∈ A, (φ e).id = e.id)
    (hnest : ∀ e ∈ A, (φ e).keyPath.length = (φ e).segmentPath.length ∧
      Arrays.parentHeld (A.map φ) (φ e).segmentPath (φ e).keyPath = true)
    (x : Id) (f : Node → Node)
    (hnode : ∀ e ∈ A, (φ e).node = if e.id = x then f e.node else e.node) :
    Arrays.Holds (A.map φ) (T.update x f) := by
  refine ⟨?_, ?_, ?_⟩
  · have : (A.map φ).map (·.id) = A.map (·.id) := by
      rw [List.map_map]; exact List.map_congr_left fun e he => hid e he
    rw [this]
    exact hA.nodup
  · intro e' he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
    exact hnest e he
  · have htree : Arrays.tree (A.map φ) = A.tree.update x f := by
      simp only [Arrays.tree, Tree.update, List.map_map]
      apply List.map_congr_left
      intro e he
      simp only [Function.comp_apply, hid e he, hnode e he, beq_iff_eq]
      by_cases h : e.id = x <;> simp [h]
    intro id
    rw [htree, get_update, get_update, hA.equiv]

/-! ## Each event keeps the arrays holding the tree -/

theorem session_added {A : Arrays} {T T' : Tree} (hA : A.Holds T) {l : Level} {k : Key}
    {p : Option Key} {ps : Props} (h : T.apply (.added l k p ps) = some T') :
    ∃ A', (T.locate (.added l k p ps)).bind A.run = some A' ∧ A'.Holds T' := by
  obtain ⟨hn, hp, rfl⟩ := apply_added.mp h
  obtain ⟨kp, hkp, hph, hlen, hlast⟩ := ancestors_parent hA hp
  have mono : ∀ {l' kp'}, A.parentHeld l' kp' = true →
      Arrays.parentHeld (⟨l, kp, k, ps⟩ :: A) l' kp' = true :=
    parentHeld_mono fun e he => List.mem_cons_of_mem _ he
  refine ⟨⟨l, kp, k, ps⟩ :: A, by simp [Tree.locate, Arrays.run, hkp, Arrays.addNode, hph], ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, hA.nodup⟩
    rintro ⟨f, hf, hid⟩
    have := tree_get_of_mem hA.nodup hf
    rw [hid, hA.equiv] at this
    simp [Located.id, hn] at this
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨hlen, mono hph⟩
    · exact ⟨(hA.nested e he).1, mono (hA.nested e he).2⟩
  · intro id
    show Tree.get ((_, _) :: A.tree) id = Tree.get (((l, k), ⟨p, ps⟩) :: T) id
    rw [get_cons, get_cons, hA.equiv]
    simp [Located.id, Located.node, hlast]

theorem session_removed {A : Arrays} {T T' : Tree} (hA : A.Holds T) {l : Level} {k : Key}
    (h : T.apply (.removed l k) = some T') :
    ∃ A', (T.locate (.removed l k)).bind A.run = some A' ∧ A'.Holds T' := by
  obtain ⟨hs, hc, rfl⟩ := apply_removed.mp h
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨e0, he0, h0s, h0k, -, hanc⟩ := located_get hA hn
  have hlen0 : e0.keyPath.length = l.length := by rw [← h0s]; exact (hA.nested e0 he0).1
  have hph : A.parentHeld l e0.keyPath = true := by rw [← h0s]; exact (hA.nested e0 he0).2
  refine ⟨A.filter fun e => !e.within l e0.keyPath k,
    by simp [Tree.locate, Arrays.run, hn, hanc, Arrays.removeNode, hph], ?_, ?_, ?_⟩
  · exact hA.nodup.sublist (List.filter_sublist.map _)
  · intro e he
    obtain ⟨heA, hw⟩ := List.mem_filter.mp he
    refine ⟨(hA.nested e heA).1, ?_⟩
    by_cases hkp : e.keyPath = []
    · exact parentHeld_root hA heA hkp _
    · obtain ⟨g, hg, hsne, hgs, hgk⟩ := parent_entry hA heA hkp
      refine parentHeld_of (List.mem_filter.mpr ⟨hg, ?_⟩) hsne hgs hgk
      cases hgw : g.within l e0.keyPath k
      · rfl
      · have := parent_below hgs hgk hgw
        simp [Located.within, this] at hw
  · -- The node has no children, so nothing lies below it.
    have nobelow : ∀ m, ∀ e ∈ A, e.keyPath.length = m → e.isBelow l e0.keyPath k = false := by
      intro m
      induction m using Nat.strongRecOn with
      | ind m ih =>
        intro e he hm
        cases hb : e.isBelow l e0.keyPath k
        · rfl
        · exfalso
          have hne : e.keyPath ≠ [] := by
            have := (isBelow_iff.mp hb).2.length_le
            intro h0; rw [h0] at this; simp at this
          obtain ⟨g, hg, hsne, hgs, hgk⟩ := parent_entry hA he hne
          rcases within_iff.mp (below_parent hlen0 (hA.nested e he).1 hgs hgk hb) with ha | hb'
          · obtain ⟨g1, -, g3⟩ := isAt_iff.mp ha
            have hget : T.get e.id = some e.node := by
              rw [← hA.equiv]; exact tree_get_of_mem hA.nodup he
            have : T.hasChild l k = true := by
              refine List.any_eq_true.mpr ⟨(e.id, e.node), mem_of_get hget, ?_⟩
              simp [Located.id, Located.node, hsne, ← hgs, g1, hgk, g3]
            rw [hc] at this; contradiction
          · have hlt : g.keyPath.length < m := by rw [← hm, hgk]; simp
            rw [ih _ hlt g hg rfl] at hb'; contradiction
    have hP : ∀ e ∈ A, e.within l e0.keyPath k = (e.id == (l, k)) := by
      intro e he
      rw [Located.within, nobelow _ e he rfl, Bool.or_false]
      rw [Bool.eq_iff_iff, isAt_iff_id hA he0 h0s h0k he, beq_iff_eq]
    have hf : (A.filter fun e => !e.within l e0.keyPath k) = A.filter fun e => e.id != (l, k) :=
      List.filter_congr fun e he => by rw [hP e he]; rfl
    have htree : Arrays.tree (A.filter fun e => e.id != (l, k)) = A.tree.filter (·.1 != (l, k)) := by
      simp [Arrays.tree, List.filter_map, Function.comp_def]
    intro id
    rw [hf, htree, get_filter, get_filter, hA.equiv]

theorem session_modified {A : Arrays} {T T' : Tree} (hA : A.Holds T) {l : Level} {k : Key}
    {p : String} {old new : Option Val} (h : T.apply (.modified l k p old new) = some T') :
    ∃ A', (T.locate (.modified l k p old new)).bind A.run = some A' ∧ A'.Holds T' := by
  obtain ⟨n, hn, -, -, rfl⟩ := apply_modified.mp h
  obtain ⟨e0, he0, h0s, h0k, -, hanc⟩ := located_get hA hn
  have hh : A.holds l e0.keyPath k = true := holds_iff.mpr ⟨e0, he0, h0s, rfl, h0k⟩
  refine ⟨A.map fun e => if e.isAt l e0.keyPath k then { e with props := e.props.set p new } else e,
    by simp [Tree.locate, Arrays.run, hn, hanc, Arrays.modifyNode, hh], ?_⟩
  have hφ : ∀ e ∈ A,
      (if e.isAt l e0.keyPath k then { e with props := e.props.set p new } else e).segmentPath =
        e.segmentPath ∧
      (if e.isAt l e0.keyPath k then { e with props := e.props.set p new } else e).keyPath =
        e.keyPath ∧
      (if e.isAt l e0.keyPath k then { e with props := e.props.set p new } else e).key = e.key := by
    intro e _; split <;> simp
  apply hA.map_update _ ?_ ?_ (l, k) (fun n => { n with props := n.props.set p new }) ?_
  · intro e _; split <;> rfl
  · intro e he
    rw [parentHeld_map_eq hφ, (hφ e he).1, (hφ e he).2.1]
    exact hA.nested e he
  · intro e he
    by_cases hat : e.isAt l e0.keyPath k = true
    · simp [hat, (isAt_iff_id hA he0 h0s h0k he).mp hat, Located.node]
    · have : e.id ≠ (l, k) := fun h => hat ((isAt_iff_id hA he0 h0s h0k he).mpr h)
      simp [hat, this]

theorem session_placed {A : Arrays} {T T' : Tree} (hA : A.Holds T) {l : Level} {k : Key}
    {a b : Key} (h : T.apply (.placed l k a b) = some T') :
    ∃ A', (T.locate (.placed l k a b)).bind A.run = some A' ∧ A'.Holds T' := by
  obtain ⟨n, hn, -, -, hpb, rfl⟩ := apply_placed.mp h
  obtain ⟨e0, he0, h0s, h0k, -, hanc⟩ := located_get hA hn
  obtain ⟨kp₂, hkp₂, hph₂, hlen₂, hlast₂⟩ := ancestors_parent hA hpb
  have hlen0 : e0.keyPath.length = l.length := by rw [← h0s]; exact (hA.nested e0 he0).1
  have hh : A.holds l e0.keyPath k = true := holds_iff.mpr ⟨e0, he0, h0s, rfl, h0k⟩
  refine ⟨A.map fun e => if e.within l e0.keyPath k
      then { e with keyPath := kp₂ ++ e.keyPath.drop e0.keyPath.length } else e,
    by simp [Tree.locate, Arrays.run, hn, hanc, hkp₂, Arrays.moveNode, hh, hph₂], ?_⟩
  -- What lies strictly below the moved node has its parent within it too.
  have hB : ∀ e ∈ A, e.within l e0.keyPath k = true → e.isAt l e0.keyPath k = false →
      ∃ g ∈ A, e.segmentPath ≠ [] ∧ g.segmentPath = e.segmentPath.dropLast ∧
        e.keyPath = g.keyPath ++ [g.key] ∧ g.within l e0.keyPath k = true := by
    intro e he hw hna
    have hb : e.isBelow l e0.keyPath k = true := by simpa [Located.within, hna] using hw
    have hne : e.keyPath ≠ [] := by
      have := (isBelow_iff.mp hb).2.length_le
      intro h0; rw [h0] at this; simp at this
    obtain ⟨g, hg, hsne, hgs, hgk⟩ := parent_entry hA he hne
    exact ⟨g, hg, hsne, hgs, hgk, below_parent hlen0 (hA.nested e he).1 hgs hgk hb⟩
  have hshift : ∀ g : Located, g.within l e0.keyPath k = true →
      kp₂ ++ (g.keyPath ++ [g.key]).drop e0.keyPath.length =
        (kp₂ ++ g.keyPath.drop e0.keyPath.length) ++ [g.key] := by
    intro g hw
    rw [List.drop_append_of_le_length (within_length hw)]; simp
  apply hA.map_update _ ?_ ?_ (l, k) (fun n => { n with parent := some b }) ?_
  · intro e _; split <;> rfl
  · intro e he
    by_cases hw : e.within l e0.keyPath k = true
    · simp only [hw, ↓reduceIte]
      by_cases hat : e.isAt l e0.keyPath k = true
      · have : e = e0 := eq_of_id hA.nodup he he0
          (((isAt_iff_id hA he0 h0s h0k he).mp hat).trans (by simp [Located.id, h0s, h0k]))
        subst this
        simp only [List.drop_length, List.append_nil]
        refine ⟨by rw [hlen₂, h0s], ?_⟩
        rw [h0s]
        by_cases hk2 : kp₂ = []
        · subst hk2
          have : l = [] := by rw [List.length_nil] at hlen₂; exact List.length_eq_zero_iff.mp hlen₂.symm
          subst this; rfl
        · obtain ⟨g, hg, hl, hgs, hgk⟩ := parentHeld_decomp hph₂ hk2
          have hpos := List.length_pos_iff.mpr hl
          have hgw : g.within l e.keyPath k = false := by
            cases h' : g.within l e.keyPath k
            · rfl
            · exfalso
              rcases within_iff.mp h' with h' | h'
              · have := congrArg List.length ((isAt_iff.mp h').1.symm.trans hgs)
                simp at this; omega
              · have := (isBelow_iff.mp h').1.length_le
                rw [hgs] at this; simp at this; omega
          exact parentHeld_of (List.mem_map.mpr ⟨g, hg, by simp [hgw]⟩) hl hgs hgk
      · obtain ⟨g, hg, hsne, hgs, hgk, hgw⟩ := hB e he hw (by simpa using hat)
        refine ⟨?_, ?_⟩
        · have h1 := within_length hw
          have h2 := (hA.nested e he).1
          simp; omega
        · show Arrays.parentHeld _ e.segmentPath (kp₂ ++ e.keyPath.drop e0.keyPath.length) = true
          rw [hgk, hshift g hgw]
          exact parentHeld_of (g := { g with keyPath := kp₂ ++ g.keyPath.drop e0.keyPath.length })
            (List.mem_map.mpr ⟨g, hg, by simp [hgw]⟩) hsne hgs rfl
    · simp only [hw, Bool.false_eq_true, ↓reduceIte]
      refine ⟨(hA.nested e he).1, ?_⟩
      by_cases hkp : e.keyPath = []
      · exact parentHeld_root hA he hkp _
      · obtain ⟨g, hg, hsne, hgs, hgk⟩ := parent_entry hA he hkp
        have hgw : g.within l e0.keyPath k = false := by
          cases h' : g.within l e0.keyPath k
          · rfl
          · exact absurd (within_iff.mpr (Or.inr (parent_below hgs hgk h'))) hw
        exact parentHeld_of (List.mem_map.mpr ⟨g, hg, by simp [hgw]⟩) hsne hgs hgk
  · intro e he
    by_cases hid : e.id = (l, k)
    · have : e = e0 := eq_of_id hA.nodup he he0 (hid.trans (by simp [Located.id, h0s, h0k]))
      subst this
      have hw : e.within l e.keyPath k = true := by
        simp [Located.within, Located.isAt, h0s, h0k]
      simp [hid, hw, Located.node, hlast₂]
    · have hat : e.isAt l e0.keyPath k = false := by
        cases h' : e.isAt l e0.keyPath k
        · rfl
        · exact absurd ((isAt_iff_id hA he0 h0s h0k he).mp h') hid
      simp only [hid, ↓reduceIte]
      by_cases hw : e.within l e0.keyPath k = true
      · obtain ⟨g, hg, hsne, hgs, hgk, hgw⟩ := hB e he hw hat
        simp only [hw, ↓reduceIte, Located.node]
        rw [hgk, hshift g hgw]; simp
      · simp [hw]

theorem session_step {A : Arrays} {T T' : Tree} {e : Event} (hA : A.Holds T)
    (h : T.apply e = some T') : ∃ A', (T.locate e).bind A.run = some A' ∧ A'.Holds T' := by
  cases e with
  | added => exact session_added hA h
  | removed => exact session_removed hA h
  | modified => exact session_modified hA h
  | placed => exact session_placed hA h

/-- Nested arrays that hold a tree follow it: an event the tree accepts is
located through the tree's parents, the located operation runs on the arrays,
and they then hold the new tree. -/
theorem session_apply {A : Arrays} {T T' : Tree} {e : Event} (hA : A.Holds T)
    (h : T.apply e = some T') :
    ∃ op, T.locate e = some op ∧ ∃ A', A.run op = some A' ∧ A'.Holds T' := by
  obtain ⟨A', h1, h2⟩ := session_step hA h
  obtain ⟨op, hop, hrun⟩ := Option.bind_eq_some_iff.mp h1
  exact ⟨op, hop, A', hrun, h2⟩

/-! ## The session keeps its invariant -/

theorem replay_snoc {T I I' : Tree} {ops : List Pending} {e : Event} {op : Pending}
    (hR : Replay T ops I) (ha : I.apply e = some I') (hl : I.locate e = some op) :
    Replay T (ops ++ [op]) I' := by
  induction hR with
  | nil => exact .cons ha hl (.nil _)
  | cons h1 h2 _ ih => exact .cons h1 h2 (ih ha hl)

/-- Running the queue on arrays that hold the flushed tree drops nothing, and
leaves arrays that hold the index. -/
theorem replay_run {A : Arrays} {T I : Tree} {ops : List Pending} (hA : A.Holds T)
    (hR : Replay T ops I) : ∃ A', A.runAll ops = some A' ∧ A'.Holds I := by
  induction hR generalizing A with
  | nil => exact ⟨A, rfl, hA⟩
  | cons ha hl _ ih =>
    obtain ⟨op', hop', A₁, hrun, hA₁⟩ := session_apply hA ha
    rw [hl, Option.some.injEq] at hop'
    subst hop'
    obtain ⟨A', h', hA'⟩ := ih hA₁
    exact ⟨A', by simp [Arrays.runAll, hrun, h'], hA'⟩

/-- Queueing an event the index accepts locates it, and keeps the invariant. In
particular, a callback from a flush that queues a child of the node just queued
finds its parent: the placement was recorded before the push that flushed. -/
theorem inv_enqueue {S : Session} {e : Event} {I' : Tree} (hS : S.Inv)
    (ha : S.index.apply e = some I') :
    ∃ S', S.enqueue e = some S' ∧ S'.Inv ∧ S'.index = I' := by
  obtain ⟨T₀, hA, hR⟩ := hS
  obtain ⟨A', -, hA'⟩ := replay_run hA hR
  obtain ⟨op, hop, -⟩ := session_apply hA' ha
  exact ⟨{ S with queue := S.queue ++ [op], index := I' }, by simp [Session.enqueue, hop, ha],
    ⟨T₀, hA, replay_snoc hR ha hop⟩, rfl⟩

/-- A flush drops no operation, and leaves arrays that hold the index. -/
theorem inv_flush {S : Session} (hS : S.Inv) :
    ∃ S', S.flush = some S' ∧ S'.Inv ∧ S'.arrays.Holds S.index ∧ S'.index = S.index := by
  obtain ⟨T₀, hA, hR⟩ := hS
  obtain ⟨A', hrun, hA'⟩ := replay_run hA hR
  exact ⟨{ S with arrays := A', queue := [] }, by simp [Session.flush, hrun],
    ⟨S.index, hA', .nil _⟩, hA', rfl⟩

theorem inv_empty : (⟨[], [], []⟩ : Session).Inv :=
  ⟨[], ⟨List.nodup_nil, fun _ h => by simp at h, fun _ => rfl⟩, .nil _⟩

/-- Recording the placement after the push is wrong: a flush at the push calls
back before the placement is recorded, and a child queued from the callback finds
no parent and is dropped. Recording first, it is located. -/
theorem record_before_push (ps : Props) :
    let row := Event.added [] (.row 1) none ps
    let child := Event.added ["items"] (.child (.row 1) 0) (some (.row 1)) ps
    let S : Session := ⟨[], [], []⟩
    (∃ S₁ S₂ S₃, S.enqueue row = some S₁ ∧ S₁.flush = some S₂ ∧ S₂.enqueue child = some S₃) ∧
    (∃ S₂, ({ S with queue := [.add [] [] (.row 1) ps] } : Session).flush = some S₂ ∧
      S₂.enqueue child = none) :=
  ⟨⟨_, _, _, rfl, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

end JinagaSpec.Cascade
