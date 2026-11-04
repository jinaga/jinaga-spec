import JinagaSpec.Cascade.Enrich
import JinagaSpec.Proofs.Cascade.Ordered
import JinagaSpec.Proofs.Cascade.Sources

/-!
# Cascade: `enrich`

`enrich_correct`: the join's events take its output to its output after any
event in any source, when the primary and secondary sources differ.
`enrich_denotation`: its output depends only on what the sources hold, not on
the order of their lists, so with `Join.order_independent` it does not depend on
the order primary and secondary rows arrive in, nor on how they interleave.
-/
namespace JinagaSpec.Cascade

/-! ## Maps built from lists of keys -/

theorem CMap.ofFn_congr {α β : Type} [Encode α] [DecidableEq α] {ks ks' : List α} {f g : α → Option β}
    (hk : ∀ x, x ∈ ks ↔ x ∈ ks') (hv : ∀ x ∈ ks, f x = g x) : CMap.ofFn ks f = CMap.ofFn ks' g :=
  CMap.ext fun x => by
    rw [CMap.get_ofFn, CMap.get_ofFn]
    by_cases h : x ∈ ks
    · simp only [h, (hk x).mp h, ↓reduceIte]; exact hv x h
    · have h' : x ∉ ks' := fun h' => h ((hk x).mpr h')
      simp only [h, h', ↓reduceIte]

/-! ## A copy depends only on what the tree holds -/

section copy

variable {T U : Tree} (hp : T.Perm U) (hg : ∀ id, T.get id = U.get id)
include hp

theorem mem_arraysOf (l : Level) (k : Key) (a : String) : a ∈ T.arraysOf l k ↔ a ∈ U.arraysOf l k := by
  simp only [Tree.arraysOf, mem_dedup]
  exact ((hp.filter _).filterMap _).mem_iff

theorem mem_keysIn (l : Level) (k : Key) (a : String) (ck : Key) :
    ck ∈ T.keysIn l k a ↔ ck ∈ U.keysIn l k a :=
  ((hp.filter _).filterMap _).mem_iff

include hg in
theorem copy_congr : ∀ (n : Nat) (l : Level) (k : Key) (ps : Props), T.copy n l k ps = U.copy n l k ps := by
  intro n
  induction n with
  | zero => intro l k ps; rfl
  | succ n ih =>
    intro l k ps
    simp only [Tree.copy]
    congr 1
    apply CMap.ofFn_congr
    · intro x; simp [mem_dedup, List.mem_map, mem_arraysOf hp]
    · intro x _
      cases x with
      | str a =>
        simp only
        by_cases ha : a ∈ T.arraysOf l k
        · simp only [ha, (mem_arraysOf hp l k a).mp ha, ↓reduceIte]
          congr 2
          exact CMap.ofFn_congr (mem_keysIn hp l k a) fun ck _ => by
            rw [hg]; congr 1; funext c; exact ih _ _ _
        · have ha' : a ∉ U.arraysOf l k := fun h => ha ((mem_arraysOf hp l k a).mpr h)
          simp only [ha, ha', ↓reduceIte]
      | _ => rfl

end copy

/-! ## A row's value depends only on what the sources hold -/

/-- A permutation has the same only element. -/
theorem onlyOne_perm {α : Type} {l₁ l₂ : List α} (h : l₁.Perm l₂) : onlyOne l₁ = onlyOne l₂ := by
  rcases l₁ with _ | ⟨r, _ | ⟨r', t⟩⟩
  · rw [← h.nil_eq]
  · rw [List.perm_singleton.mp h.symm]
  · rcases l₂ with _ | ⟨x, _ | ⟨y, u⟩⟩
    · exact absurd h.length_eq (by simp)
    · exact absurd h.length_eq (by simp)
    · rfl

theorem enrich_val_congr {s : Level} {K CK : List String} {w : Option Val} {Tq Uq T U : Tree}
    (hTq : Tq.WF) (hUq : Uq.WF) (hq : Tq.Equiv Uq) (h : T.Equiv U) :
    enrich.val s K CK w Tq T = enrich.val s K CK w Uq U := by
  funext k x
  have hp := perm_of_equiv hTq hUq hq
  unfold enrich.val
  rw [h (s, k)]
  cases U.get (s, k) with
  | none => rfl
  | some n =>
    simp only
    have hm : (enrich.matches K CK Tq n.props).Perm (enrich.matches K CK Uq n.props) := by
      unfold enrich.matches; split
      · exact hp.filter _
      · exact List.Perm.refl _
    rw [onlyOne_perm hm, hp.length_eq]
    cases onlyOne (enrich.matches K CK Uq n.props) with
    | none => rfl
    | some r => simp only; rw [copy_congr hp hq]

/-- **`enrich_denotation`.** -/
theorem enrich_denotation (p q : Source) (s : Level) (as : String) (K CK : List String) (w : Option Val) :
    JDenotation (enrich.F p q s as K CK w) := by
  refine ⟨fun F hF => (mapProps_wf (hF p) : (overlay.F s [as] _ (F p)).WF), fun F H hF hH h id => ?_⟩
  simp only [enrich.F, overlay.F, get_mapProps, h p id,
    enrich_val_congr (hF q) (hH q) (h q) (h p)]

/-! ## A secondary event: each primary row takes its new value -/

theorem mem_retarget_keys {s : Level} {T : Tree} (hnd : (T.map (·.1)).Nodup) {k : Key} :
    k ∈ (T.filter fun e => e.1.1 = s).map (·.1.2) ↔ (T.get (s, k)).isSome := by
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨l, k'⟩, n⟩, ⟨hm, hl⟩, rfl⟩
    simp only at hl ⊢; subst hl
    rw [get_of_mem hnd hm]; rfl
  · intro h
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h
    exact ⟨((s, k), n), ⟨mem_of_get hn, rfl⟩, rfl⟩

theorem nodup_retarget_keys {s : Level} {T : Tree} (hnd : (T.map (·.1)).Nodup) :
    ((T.filter fun e => e.1.1 = s).map (·.1.2)).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  have hf : ((T.filter fun e => e.1.1 = s).map (·.1)).Nodup := hnd.sublist (List.filter_sublist.map _)
  unfold List.Nodup at hf
  rw [List.pairwise_map] at hf
  refine hf.imp_of_mem fun {a b} ha hb hne hk => hne (Prod.ext ?_ hk)
  simp only [List.mem_filter, decide_eq_true_eq] at ha hb
  rw [ha.2, hb.2]

/-- The changes take every node at `s` from values `a` to values `b`. -/
theorem retarget_correct {s : Level} {Q : List String} {a b : Key → String → Option Val} {T : Tree}
    (hwf : T.WF) :
    ∃ V, (T.mapProps s fun k ps => overlay Q (a k) ps).applyAll (retarget s Q a b T) = some V ∧
      V.Equiv (T.mapProps s fun k ps => overlay Q (b k) ps) := by
  obtain ⟨V, hV, hget⟩ := applyAll_nodes (c := s) (Q := Q) (a := a) (b := b)
    ((T.filter fun e => e.1.1 = s).map (·.1.2)) (T.mapProps s fun k ps => overlay Q (a k) ps)
    (nodup_retarget_keys hwf.nodup) fun k hk => by
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp ((mem_retarget_keys hwf.nodup).mp hk)
      exact ⟨_, by rw [get_mapProps, hn]; rfl, fun x hx => by simp [mapNode, overlay, hx]⟩
  refine ⟨V, hV, fun id => ?_⟩
  rw [hget]
  obtain ⟨l, k⟩ := id
  simp only [get_mapProps]
  by_cases hl : l = s
  · subst hl
    cases hn : T.get (l, k) with
    | none => simp
    | some n =>
      have hk : k ∈ (T.filter fun e => e.1.1 = l).map (·.1.2) :=
        (mem_retarget_keys hwf.nodup).mpr (by simp [hn])
      simp [hk, mapNode, overlay_overlay]
  · simp only [hl, false_and, ↓reduceIte]
    congr 1; funext n; simp [mapNode, hl]

/-! ## Correctness -/

/-- **`enrich_correct`.** When the primary and secondary sources differ, the
join's events keep its output equal to its denotation. -/
theorem enrich_correct {p q : Source} (hpq : p ≠ q) (s : Level) (as : String) (K CK : List String)
    (w : Option Val) : JCorrect (enrich p q s as K CK w) (enrich.F p q s as K CK w) := by
  intro F e F' hF he
  obtain ⟨T', h1, rfl⟩ := Forest.apply_eq he
  obtain ⟨src, ev⟩ := e
  simp only at h1 ⊢
  by_cases hp : src = p
  · subst hp
    have hq : q ≠ src := Ne.symm hpq
    have : enrich.F src q s as K CK w (F.set src T') =
        overlay.F s [as] (enrich.val s K CK w (F q)) T' := by
      simp only [enrich.F, Forest.set_self, Forest.set_other F hq]
    rw [this]
    simp only [enrich, ↓reduceIte]
    exact overlay_correct s [as] _ (F src) ev T' (hF src) h1
  · by_cases hq : src = q
    · subst hq
      have : enrich.F p src s as K CK w (F.set src T') =
          (F p).mapProps s fun k ps => overlay [as] (enrich.val s K CK w T' (F p) k) ps := by
        simp only [enrich.F, overlay.F, Forest.set_self, Forest.set_other F hpq]
      rw [this]
      simp only [enrich, hp, ↓reduceIte, h1]
      exact retarget_correct (hF p)
    · have : enrich.F p q s as K CK w (F.set src T') = enrich.F p q s as K CK w F := by
        simp only [enrich.F, Forest.set_other F (Ne.symm hp), Forest.set_other F (Ne.symm hq)]
      rw [this]
      simp only [enrich, hp, hq, ↓reduceIte]
      exact ⟨_, rfl, Tree.Equiv.refl _⟩

end JinagaSpec.Cascade
