import JinagaSpec.Proofs.Cascade.Filter
import JinagaSpec.Cascade.Input

/-!
# Cascade: the input

`nodeKey_inj`: composed keys are unique, so a natural key need only be unique
among its siblings. `input_correct`: the input step's events are always
accepted, and they take the input to exactly what it received: a refused orphan
leaves no trace, and a removed row takes its subtree with it. `ops_correct` and
`ops_order_independent` carry the pipeline theorems from events to what a caller
does.
-/
namespace JinagaSpec.Cascade

noncomputable section

/-! ## Composed keys are unique -/

theorem nodeKey_concat (r : Nat) (xs : List Nat) (x : Nat) :
    nodeKey r (xs ++ [x]) = .child (nodeKey r xs) x := by
  simp [nodeKey, List.foldl_append]

/-- **`nodeKey_inj`.** Two rows have the same key only when they have the same
natural keys. -/
theorem nodeKey_inj : ∀ (n : Nat) (r r' : Nat) (xs ys : List Nat), xs.length = n →
    nodeKey r xs = nodeKey r' ys → r = r' ∧ xs = ys := by
  intro n
  induction n with
  | zero =>
    intro r r' xs ys hn h
    have : xs = [] := List.eq_nil_of_length_eq_zero hn
    subst this
    rcases List.eq_nil_or_concat ys with rfl | ⟨ys', y, rfl⟩
    · simp only [nodeKey, List.foldl_nil, Key.row.injEq] at h; exact ⟨h, rfl⟩
    · rw [List.concat_eq_append, nodeKey_concat] at h; simp [nodeKey] at h
  | succ n ih =>
    intro r r' xs ys hn h
    rcases List.eq_nil_or_concat xs with rfl | ⟨xs', x, rfl⟩
    · simp at hn
    rw [List.concat_eq_append] at hn h ⊢
    rcases List.eq_nil_or_concat ys with rfl | ⟨ys', y, rfl⟩
    · rw [nodeKey_concat] at h; simp [nodeKey] at h
    rw [List.concat_eq_append] at h ⊢
    rw [nodeKey_concat, nodeKey_concat, Key.child.injEq] at h
    obtain ⟨hr, hxs⟩ := ih r r' xs' ys' (by simp at hn; omega) h.1
    exact ⟨hr, by rw [hxs, h.2]⟩

/-! ## A subtree hangs from a present node -/

/-- A present node below `x` means `x` is present. -/
theorem present_of_inSubtree {T : Tree} (hwf : T.WF) {x : Id} :
    ∀ (n : Nat) (y : Id), y.1.length = n → inSubtree T x y = true → (T.get y).isSome →
      (T.get x).isSome := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ⟨l, k⟩ hn hs hy
    by_cases hx : (l, k) = x
    · rw [← hx]; exact hy
    · obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hy
      have hp := hwf.parents _ _ hm
      cases hq : m.parent with
      | none =>
        -- A root is its own subtree only when it is the top.
        rw [hq] at hp
        simp only [Tree.parentOk, List.isEmpty_iff] at hp
        subst hp
        rw [inSubtree_iff] at hs
        obtain ⟨h1, h2, h3⟩ := hs
        simp only [List.length_nil, Nat.le_zero, List.length_eq_zero_iff] at h1
        simp only [h1, List.length_nil, Nat.sub_self, Tree.walk, Option.some.injEq] at h3
        exact absurd (Prod.ext h1.symm h3) hx
      | some q =>
        rw [hq] at hp
        simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true',
          List.isEmpty_eq_false_iff] at hp
        have hl : l.length ≠ 0 := by simpa using hp.1
        have hlt : l.dropLast.length < n := by
          rw [List.length_dropLast]; simp only at hn; omega
        exact ih _ hlt (l.dropLast, q) rfl (inSubtree_parent hm hq hs hx) hp.2

/-- Removing a present node's subtree, children first. -/
theorem evict_all {T : Tree} (hwf : T.WF) (x : Id) :
    ∃ U, T.applyAll (evict T x) = some U ∧
      ∀ y, U.get y = if inSubtree T x y then none else T.get y := by
  let le : Id × Node → Id × Node → Bool := fun a b => b.1.1.length ≤ a.1.1.length
  let L := (T.filter (inSubtree T x ·.1)).mergeSort le
  obtain ⟨X, hX, hXg⟩ := removeAll L T hwf
    (List.pairwise_mergeSort (fun a b c hab hbc => by simp only [le, decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) _ |>.imp
      fun h => by simpa [le] using h)
    (nodup_subtreeList hwf x le)
    (fun e he => by rw [get_of_mem hwf.nodup (mem_subtreeList.mp he).1]; rfl)
    (fun e he l' k' m hm hl' hd hp => List.mem_map.mpr
      ⟨((l', k'), m), mem_subtreeList.mpr ⟨mem_of_get hm,
        inSubtree_child hl' hm hp (by rw [hd]; exact (mem_subtreeList.mp he).2)⟩, rfl⟩)
  refine ⟨X, hX, fun y => ?_⟩
  rw [hXg]
  cases hs : inSubtree T x y
  · rw [ite_eq_right]; · rfl
    intro hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    rw [(mem_subtreeList.mp he).2] at hs; cases hs
  · simp only [ite_true]
    split
    · rfl
    · rename_i hnot
      cases hn : T.get y with
      | none => rfl
      | some n => exact absurd (List.mem_map.mpr ⟨(y, n), mem_subtreeList.mpr ⟨mem_of_get hn, hs⟩, rfl⟩) hnot

/-! ## The input step -/

theorem get_outside (T : Tree) (x y : Id) :
    Tree.get (T.filter fun e => !inSubtree T x e.1) y =
      if inSubtree T x y then none else T.get y := by
  rw [get_filter_id T (fun id => !inSubtree T x id) y]
  cases inSubtree T x y <;> rfl

theorem receive_wf {T : Tree} (hwf : T.WF) {op : Op} (hfresh : Fresh T op) :
    (T.receive op).WF := by
  cases op with
  | add l r rest ps =>
    simp only [Tree.receive]
    split
    · rename_i ha
      simp only [accepts, Bool.and_eq_true] at ha
      exact apply_wf hwf (apply_added.mpr ⟨hfresh, ha.2, rfl⟩)
    · exact hwf
  | remove l r rest =>
    refine ⟨(List.filter_sublist.map _).nodup hwf.nodup, fun id n hn => ?_⟩
    simp only [Tree.receive] at hn ⊢
    rw [get_outside] at hn
    split at hn
    · cases hn
    · rename_i hout
      have hp := hwf.parents id n hn
      cases hq : n.parent with
      | none => rw [hq] at hp; exact hp
      | some q =>
        rw [hq] at hp
        simp only [Tree.parentOk, Bool.and_eq_true, Bool.not_eq_true',
          List.isEmpty_eq_false_iff] at hp ⊢
        refine ⟨hp.1, ?_⟩
        rw [get_outside]
        have : inSubtree T (l, nodeKey r rest) (id.1.dropLast, q) = false := by
          rw [Bool.eq_false_iff]; intro h
          obtain ⟨l', k'⟩ := id
          exact hout (inSubtree_child hp.1 hn hq h)
        simp [this, hp.2]

/-- **`input_correct`.** The input step's events are always accepted, and they
take the input to what it received. -/
theorem input_correct {T : Tree} (hwf : T.WF) {op : Op} (hfresh : Fresh T op) :
    ∃ U, T.applyAll (input.handle T op) = some U ∧ U.Equiv (T.receive op) := by
  cases op with
  | add l r rest ps =>
    simp only [input.handle, Tree.receive]
    split
    · rename_i ha
      simp only [accepts, Bool.and_eq_true] at ha
      exact ⟨_, by rw [applyAll_single]; exact apply_added.mpr ⟨hfresh, ha.2, rfl⟩,
        Tree.Equiv.refl _⟩
    · exact ⟨T, rfl, Tree.Equiv.refl _⟩
  | remove l r rest =>
    simp only [input.handle, Tree.receive]
    split
    · obtain ⟨U, hU, hUg⟩ := evict_all hwf (l, nodeKey r rest)
      exact ⟨U, hU, fun y => by rw [hUg, get_outside]⟩
    · rename_i habs
      refine ⟨T, rfl, fun y => ?_⟩
      rw [get_outside]
      cases hs : inSubtree T (l, nodeKey r rest) y
      · rfl
      · simp only [↓reduceIte]
        cases hy : T.get y with
        | none => rfl
        | some _ => exact absurd (present_of_inSubtree hwf _ y rfl hs (by simp [hy])) habs

/-- A child that arrives before its parent is refused and leaves no trace
(jinaga/jinaga-cascade-core#31). -/
theorem orphan_refused {T : Tree} {l : Level} {r : Nat} {rest : List Nat} {ps : Props}
    (h : accepts T l r rest = false) :
    input.handle T (.add l r rest ps) = [] ∧ T.receive (.add l r rest ps) = T := by
  simp [input.handle, Tree.receive, h]

/-! ## From what a caller does to the output -/

/-- What the input holds after a sequence of operations. -/
def Tree.receiveAll (T : Tree) : List Op → Tree
  | [] => T
  | op :: ops => (T.receive op).receiveAll ops

/-- Each operation keeps the caller's contract where it applies. -/
def FreshAll (T : Tree) : List Op → Prop
  | [] => True
  | op :: ops => Fresh T op ∧ FreshAll (T.receive op) ops

theorem receiveAll_wf : ∀ (ops : List Op) (T : Tree), T.WF → FreshAll T ops →
    (T.receiveAll ops).WF
  | [], _, hT, _ => hT
  | _ :: ops, _, hT, ⟨hf, hr⟩ => receiveAll_wf ops _ (receive_wf hT hf) hr

/-- Run a step over what a caller does. -/
def runOps (S : Step) : Tree → List Op → List Event
  | _, [] => []
  | T, op :: ops => run S T (input.handle T op) ++ runOps S (T.receive op) ops

/-- **`ops_correct`.** A correct pipeline, fed what a caller does, holds its
denotation of what the input received. -/
theorem ops_correct {S : Step} {F : Tree → Tree} (hS : Correct S F) (hF : Denotation F) :
    ∀ (ops : List Op) (T : Tree), T.WF → FreshAll T ops →
      ∃ U, (F T).applyAll (runOps S T ops) = some U ∧ U.Equiv (F (T.receiveAll ops)) := by
  intro ops
  induction ops with
  | nil => intro T _ _; exact ⟨F T, rfl, Tree.Equiv.refl _⟩
  | cons op ops ih =>
    intro T hT ⟨hfresh, hrest⟩
    obtain ⟨V, hV, hVe⟩ := input_correct hT hfresh
    have hR := receive_wf hT hfresh
    have hVwf := applyAll_wf hT hV
    obtain ⟨W, hW, hWe⟩ := run_correct hS hF _ T V hT hV
    have hWe' := hWe.trans (hF.equiv V _ hVwf hR hVe)
    obtain ⟨X, hX, hXe⟩ := ih _ hR hrest
    obtain ⟨X', hX', hX'e⟩ := applyAll_equiv (hF.wf _ hR) (applyAll_wf (hF.wf T hT) hW) hWe'.symm hX
    exact ⟨X', by rw [runOps, applyAll_append, hW, Option.bind_some]; exact hX',
      hX'e.symm.trans hXe⟩

/-- **`ops_order_independent`.** Two sequences of operations that leave the
input holding the same rows produce the same output. -/
theorem ops_order_independent {S : Step} {F : Tree → Tree} (hS : Correct S F)
    (hF : Denotation F) {T : Tree} {ops₁ ops₂ : List Op} (hT : T.WF)
    (h₁ : FreshAll T ops₁) (h₂ : FreshAll T ops₂)
    (h : (T.receiveAll ops₁).Equiv (T.receiveAll ops₂)) :
    ∃ U₁ U₂, (F T).applyAll (runOps S T ops₁) = some U₁ ∧
      (F T).applyAll (runOps S T ops₂) = some U₂ ∧ U₁.Equiv U₂ := by
  obtain ⟨U₁, hU₁, hU₁e⟩ := ops_correct hS hF ops₁ T hT h₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := ops_correct hS hF ops₂ T hT h₂
  exact ⟨U₁, U₂, hU₁, hU₂, hU₁e.trans ((hF.equiv _ _ (receiveAll_wf ops₁ T hT h₁)
    (receiveAll_wf ops₂ T hT h₂) h).trans hU₂e.symm)⟩

end

end JinagaSpec.Cascade
