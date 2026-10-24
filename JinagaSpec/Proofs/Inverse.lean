import JinagaSpec.Inverse
import JinagaSpec.Proofs.Basic

/-!
# `shakeTree` cannot loop

jinaga.js's `shakeTree` has one loop whose length is not fixed in advance: it
moves a match with no path condition to the bottom, and looks at the match
that takes its place, until it finds one with a path condition or comes back
to the match it started from (jinaga/jinaga.js#132 was this loop running
forever, before the return was detected). The port bounds it by the length of
the suffix it rotates.

`settle_bound`: that bound is never what stops it. Moving path conditions
between matches never changes which matches there are or their order, so the
suffix of names rotates by one each time and comes back to its first name
within its length. `shakeTree_bound` lifts this to all of `shakeTree`: the
TypeScript loop runs at most once per match in the suffix, for every input.

`relocateConditions` has no such loop: it visits each match once, and moves a
condition only to a later match.
-/
namespace JinagaSpec

/-- A step that keeps an invariant and never fails with `e`. -/
def Keeps (P : List Match → Prop) (e : InverseError)
    (step : List Match → Except InverseError (List Match)) : Prop :=
  ∀ ms, P ms → step ms ≠ .error e ∧ ∀ ms', step ms = .ok ms' → P ms'

/-- A fold of such steps is such a step. -/
theorem foldlM_keeps {β : Type} {P : List Match → Prop} {e : InverseError}
    {step : List Match → β → Except InverseError (List Match)} :
    ∀ {l : List β}, (∀ b ∈ l, Keeps P e (step · b)) → Keeps P e (l.foldlM step ·)
  | [], _, ms, hp => by
    refine ⟨by simp [pure, Except.pure], fun ms' h => ?_⟩
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hp
  | b :: l, h, ms, hp => by
    obtain ⟨hne, hok⟩ := h b (by simp) ms hp
    simp only [List.foldlM_cons]
    cases hs : step ms b with
    | error e' => exact ⟨by simpa [bind, Except.bind, hs] using hne, by simp [bind, Except.bind]⟩
    | ok ms1 =>
      simpa [bind, Except.bind] using
        foldlM_keeps (fun b' hb' => h b' (List.mem_cons_of_mem _ hb')) ms1 (hok ms1 hs)

theorem pure_keeps (P : List Match → Prop) (e : InverseError) : Keeps P e pure := by
  intro ms hp
  refine ⟨by simp [pure, Except.pure], fun ms' h => ?_⟩
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact h ▸ hp

/-- Replacing a match's conditions keeps its name. -/
theorem names_updateFirst (n : Name) (cs : Match → List Condition) :
    ∀ ms : List Match, names (updateFirst n (fun x => .mk x.unknown (cs x)) ms) = names ms
  | [] => rfl
  | m :: rest => by
    have := names_updateFirst n cs rest
    unfold updateFirst
    split <;> simp_all [names]

theorem findMatch_error {ms : List Match} {l : Name} {e : InverseError}
    (h : findMatch ms l = .error e) : e = .labelNotFound l := by
  unfold findMatch at h; split at h <;> simp_all

/-- Moving a path condition keeps the names, and fails only on a missing label. -/
theorem invertAndMovePathCondition_keeps (N : List Name) (label : Name) (pc : PathCondition) :
    Keeps (names · = N) .boundReached (invertAndMovePathCondition · label pc) := by
  intro ms hp
  unfold invertAndMovePathCondition
  cases h1 : findMatch ms label with
  | error e => cases findMatch_error h1; simp [bind, Except.bind, h1]
  | ok m =>
    cases h2 : findMatch ms pc.labelRight with
    | error e => cases findMatch_error h2; simp [bind, Except.bind, h1, h2]
    | ok _ =>
      refine ⟨by simp [bind, Except.bind, pure, Except.pure, h1, h2], fun ms' h => ?_⟩
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, h1, h2] at h
      rw [← h, names_updateFirst, names_updateFirst, hp]

theorem pullTags_keeps (N : List Name) (i : Nat) :
    Keeps (names · = N) .boundReached (pullTags · i) := by
  intro ms hp
  refine foldlM_keeps (fun j _ x hx => foldlM_keeps (fun c _ y hy => ?_) x hx) ms hp
  cases c with
  | path pc =>
    by_cases hc : (pc.labelRight == (ms.getD i default).unknown.name) = true
    · simp only [hc, ite_true]
      exact invertAndMovePathCondition_keeps N _ pc y hy
    · simp only [hc, Bool.false_eq_true, ite_false]
      exact pure_keeps _ _ y hy
  | existential => exact pure_keeps _ _ y hy

/-- Rotate left by one. -/
def rot (l : List Name) : List Name := l.drop 1 ++ l.take 1

theorem names_rotateAt (ms : List Match) (i : Nat) (hi : i < ms.length) :
    (names (rotateAt ms i)).drop i = rot ((names ms).drop i) := by
  simp only [rotateAt, names, rot, List.map_append, List.map_take, List.map_drop, List.drop_drop,
    List.append_assoc]
  rw [List.drop_left' (by simp; omega), Nat.add_comm]

/-- The name at `i` heads the suffix from `i`. -/
theorem head?_drop_names (ms : List Match) (i : Nat) (hi : i < ms.length) :
    ((names ms).drop i).head? = some (ms.getD i default).unknown.name := by
  simp [names, List.head?_drop, List.getD_eq_getElem?_getD, hi]

/-- If `first` is among the first `b + 1` names but is not the first, one more
rotation leaves it among the first `b`. -/
theorem mem_take_rot {L : List Name} {first : Name} {b : Nat} (h : first ∈ L.take (b + 1))
    (hhead : L.head? ≠ some first) : first ∈ (rot L).take b := by
  cases L with
  | nil => simp at h
  | cons y ys =>
    simp only [List.take_succ_cons, List.mem_cons, List.head?_cons, ne_eq, Option.some.injEq] at h hhead
    rcases h with rfl | h
    · exact absurd rfl hhead
    · simp only [rot, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
        List.take_append]
      exact List.mem_append_left _ h

theorem length_rotateAt (ms : List Match) (i : Nat) : (rotateAt ms i).length = ms.length := by
  simp only [rotateAt, List.length_append, List.length_take, List.length_drop]
  omega

/-- `first` is among the first `b` names of the rotated suffix, so `settle`
comes back to it before its bound runs out. It keeps the number of matches. -/
theorem settle_bound (i : Nat) (first : Name) :
    ∀ (b : Nat) (ms : List Match), i < ms.length → first ∈ (rot ((names ms).drop i)).take b →
      settle ms i first b ≠ .error .boundReached ∧
        ∀ ms', settle ms i first b = .ok ms' → ms'.length = ms.length
  | 0, _, _, hmem => by simp at hmem
  | b + 1, ms, hi, hmem => by
    unfold settle
    split
    · simp
    obtain ⟨hne, hok⟩ := pullTags_keeps (names ms) i ms rfl
    cases hp : pullTags ms i with
    | error e => simpa [bind, Except.bind, hp] using hne
    | ok ms1 =>
      have hn : names ms1 = names ms := hok ms1 hp
      have hlen : ms1.length = ms.length := by simpa [names] using congrArg List.length hn
      have hrot : (names (rotateAt ms1 i)).drop i = rot ((names ms).drop i) := by
        rw [names_rotateAt _ _ (by omega), hn]
      simp only [bind, Except.bind]
      split
      · simp
      rename_i hfirst
      have hlen' : i < (rotateAt ms1 i).length := by rw [length_rotateAt]; omega
      have ih := settle_bound i first b _ hlen' (by
        rw [hrot]
        refine mem_take_rot hmem ?_
        rw [← hrot, head?_drop_names _ _ hlen']
        simpa using hfirst)
      exact ⟨ih.1, fun ms' h => by rw [ih.2 ms' h, length_rotateAt, hlen]⟩

/-- `shakeTree` never stops for want of rotations. -/
theorem shakeTree_bound (ms : List Match) (label : Name) : shakeTree ms label ≠ .error .boundReached := by
  unfold shakeTree
  cases h1 : findMatch ms label with
  | error e => cases findMatch_error h1; simp [bind, Except.bind]
  | ok m =>
    simp only [bind, Except.bind]
    obtain ⟨hne, -⟩ := foldlM_keeps (P := (names · = names (m :: ms.erase m))) (e := .boundReached)
      (l := m.conditions) (step := fun ms c => match c with
        | .path pc => invertAndMovePathCondition ms label pc
        | .existential .. => pure ms) (fun c _ => by
        cases c with
        | path pc => exact invertAndMovePathCondition_keeps _ label pc
        | existential => exact pure_keeps _ _) (m :: ms.erase m) rfl
    split
    · rename_i h; exact fun heq => hne (h.trans heq)
    rename_i ms1 _
    -- Each `settle` starts at a position inside the list, and keeps its length.
    refine (foldlM_keeps (P := fun x => x.length = ms1.length) (fun i hi x hx => ?_) ms1 rfl).1
    have hi : i < x.length := by simp [List.mem_range'] at hi; omega
    have hhead := head?_drop_names x i hi
    have hlen : ((names x).drop i).length = x.length - i := by simp [names]
    refine (settle_bound i _ _ x hi ?_).imp id fun h x' hx' => (h x' hx').trans hx
    generalize (names x).drop i = L at hhead hlen ⊢
    cases L with
    | nil => simp at hhead
    | cons y ys =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      rw [rot, List.take_of_length_le (by simp at hlen ⊢; omega)]
      simp [hhead]

end JinagaSpec
