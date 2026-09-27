import JinagaSpec.Proofs.Basic

/-!
# Splitting the pivot's path conditions

A path condition that walks predecessors becomes a head match that binds a split
label, and a tail condition that joins to it. The two say the same thing: the
head enumerates the facts the predecessor walk reaches, and the tail asks
whether the successor walk reaches any of them.
-/
namespace JinagaSpec

private theorem step_mem_type {g : Graph} {role : Role} {r p : FactId}
    (h : p ∈ g.step role r) :
    ∃ f ∈ g, f.id = p ∧ f.type = role.predecessorType := by
  unfold Graph.step at h
  split at h
  · simp at h
  · simp only [List.mem_filter, List.mem_map] at h
    obtain ⟨_, hp⟩ := h
    revert hp
    cases hf : g.factOf p with
    | none => simp
    | some f =>
      intro hp
      simp only [beq_iff_eq] at hp
      unfold Graph.factOf at hf
      have h1 := List.find?_some hf
      have h2 := List.mem_of_find?_eq_some hf
      simp only [beq_iff_eq] at h1
      exact ⟨f, h2, h1, hp⟩

private theorem walk_mem_type {g : Graph} {last : Role} :
    ∀ (R : List Role) (r a : FactId), a ∈ g.walk r R → R.getLast? = some last →
      ∃ f ∈ g, f.id = a ∧ f.type = last.predecessorType := by
  intro R
  induction R with
  | nil => intro r a _ h; simp at h
  | cons role rest ih =>
    intro r a ha hlast
    simp only [Graph.walk, List.mem_flatMap] at ha
    obtain ⟨p, hp, hap⟩ := ha
    cases rest with
    | nil =>
      simp only [Graph.walk, List.mem_singleton] at hap
      subst hap
      have : role = last := by simpa using hlast
      subst this
      exact step_mem_type hp
    | cons r2 rest2 =>
      apply ih p a hap
      simpa [List.getLast?_cons_cons] using hlast

/-- Every split label is reserved, and the tail's paths join only labels the
pivot joined or the split labels. -/
theorem splitPaths_names (i : Nat) :
    ∀ (ps : List PathCondition),
      (∀ m ∈ (splitPaths i ps).1, isReserved m.unknown.name = true) ∧
      (∀ c ∈ (splitPaths i ps).2,
        c.labelRight ∈ ps.map (·.labelRight) ∨
        c.labelRight ∈ (splitPaths i ps).1.map (·.unknown.name)) := by
  intro ps
  induction ps generalizing i with
  | nil => simp [splitPaths]
  | cons c cs ih =>
    cases hl : c.rolesRight.getLast? with
    | none =>
      obtain ⟨ih1, ih2⟩ := ih (i + 1)
      simp only [splitPaths, hl]
      refine ⟨ih1, ?_⟩
      intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · left; simp
      · rcases ih2 c' hc' with h | h
        · left; exact List.mem_cons_of_mem _ h
        · right; exact h
    | some last =>
      obtain ⟨ih1, ih2⟩ := ih (i + 1)
      simp only [splitPaths, hl]
      refine ⟨?_, ?_⟩
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact isReserved_splitLabel i
        · exact ih1 m hm
      · intro c' hc'
        rcases List.mem_cons.mp hc' with rfl | hc'
        · right; simp
        · rcases ih2 c' hc' with h | h
          · left; exact List.mem_cons_of_mem _ h
          · right; exact List.mem_cons_of_mem _ h

/-- The head matches of a split numbered from `i` bind split labels numbered
`i` or later. -/
theorem splitPaths_head_index :
    ∀ (ps : List PathCondition) (i : Nat), ∀ m ∈ (splitPaths i ps).1,
      ∃ j, i ≤ j ∧ m.unknown.name = splitLabel j := by
  intro ps
  induction ps with
  | nil => intro i m hm; simp [splitPaths] at hm
  | cons c cs ih =>
    intro i m hm
    cases hl : c.rolesRight.getLast? with
    | none =>
      simp only [splitPaths, hl] at hm
      obtain ⟨j, hj, hn⟩ := ih (i + 1) m hm
      exact ⟨j, by omega, hn⟩
    | some last =>
      simp only [splitPaths, hl] at hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨i, Nat.le_refl _, rfl⟩
      · obtain ⟨j, hj, hn⟩ := ih (i + 1) m hm
        exact ⟨j, by omega, hn⟩

private theorem pathHolds_agree {g : Graph} {c : PathCondition} {u : Name} {f : FactId}
    {e e' : Env} (h : e' c.labelRight = e c.labelRight ∨ c.labelRight = u) :
    c.holds g (e'.bind u f) u = c.holds g (e.bind u f) u := by
  have h1 : (e'.bind u f) u = (e.bind u f) u := by simp [Env.bind]
  have h2 : (e'.bind u f) c.labelRight = (e.bind u f) c.labelRight := by
    by_cases hh : c.labelRight = u
    · simp [Env.bind, hh]
    · rcases h with h | h
      · simp [Env.bind, hh, h]
      · exact absurd h hh
  unfold PathCondition.holds
  rw [h1, h2]

private theorem allHold_bind_irrel {g : Graph} {u name : Name} {f x : FactId} {e : Env}
    (_hnu : name ≠ u) :
    ∀ (ps : List PathCondition), (∀ c ∈ ps, c.labelRight ≠ name) →
      allHold g ((e.bind name x).bind u f) u (ps.map .path) =
        allHold g (e.bind u f) u (ps.map .path) := by
  intro ps
  induction ps with
  | nil => intro _; simp [allHold]
  | cons c cs ih =>
    intro hl
    have h1 : c.holds g ((e.bind name x).bind u f) u = c.holds g (e.bind u f) u := by
      apply pathHolds_agree
      left
      simp [Env.bind, hl c (by simp)]
    have h2 := ih (fun c' h => hl c' (List.mem_cons_of_mem _ h))
    simp only [List.map_cons, allHold, holds, h1, h2]

/-- The split preserves the pivot's path conditions. The unknown `u` is bound to
`f`. Some way of binding the split labels makes the tail's paths hold exactly
when the pivot's paths held.

It needs that no pivot condition joins the pivot to itself (the original reads
`f` for `u`, but the head runs before `u` is bound), and that every label the
conditions join, and `u`, is ordinary, so that no split label is one of them. -/
theorem splitPaths_correct (g : Graph) (u : Name) (f : FactId) :
    ∀ (i : Nat) (ps : List PathCondition) (e : Env),
      (∀ c ∈ ps, c.labelRight ≠ u) →
      (∀ x ∈ u :: ps.map (·.labelRight), isReserved x = false) →
      ((∃ e' ∈ evalMatches g e (splitPaths i ps).1,
          allHold g (e'.bind u f) u ((splitPaths i ps).2.map .path) = true) ↔
        allHold g (e.bind u f) u (ps.map .path) = true) := by
  intro i ps
  induction ps generalizing i with
  | nil => intro e _ _; simp [splitPaths, evalMatches, allHold]
  | cons c cs ih =>
    intro e hne hres
    have hne' : ∀ c' ∈ cs, c'.labelRight ≠ u := fun c' h => hne c' (List.mem_cons_of_mem _ h)
    have hu : isReserved u = false := hres u (by simp)
    have hlr : isReserved c.labelRight = false := hres _ (by simp)
    have hcne : c.labelRight ≠ u := hne c (by simp)
    have hres' : ∀ x ∈ u :: cs.map (·.labelRight), isReserved x = false := by
      intro x hx
      apply hres
      simp only [List.mem_cons, List.map_cons] at hx ⊢
      rcases hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    cases hl : c.rolesRight.getLast? with
    | none =>
      obtain ⟨hn1, _⟩ := splitPaths_names (i + 1) cs
      have key : ∀ e' ∈ evalMatches g e (splitPaths (i + 1) cs).1,
          c.holds g (e'.bind u f) u = c.holds g (e.bind u f) u := by
        intro e' he'
        apply pathHolds_agree
        left
        apply evalMatches_frame he'
        intro hmem
        obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hmem
        have := hn1 m hm
        rw [hmn, hlr] at this
        exact absurd this (by simp)
      have ih' := ih (i + 1) e hne' hres'
      simp only [splitPaths, hl, List.map_cons, allHold, holds]
      constructor
      · rintro ⟨e', he', h⟩
        rw [key e' he'] at h
        have h' := (Bool.and_eq_true _ _).mp h
        exact (Bool.and_eq_true _ _).mpr ⟨h'.1, ih'.mp ⟨e', he', h'.2⟩⟩
      · intro h
        have h' := (Bool.and_eq_true _ _).mp h
        obtain ⟨e', he', hq⟩ := ih'.mpr h'.2
        refine ⟨e', he', ?_⟩
        rw [key e' he']
        exact (Bool.and_eq_true _ _).mpr ⟨h'.1, hq⟩
    | some last =>
      have hnu : splitLabel i ≠ u := by
        intro h; have := isReserved_splitLabel i; rw [h, hu] at this; simp at this
      have hnlr : c.labelRight ≠ splitLabel i := by
        intro h; have := isReserved_splitLabel i; rw [← h, hlr] at this; simp at this
      have hcs_name : ∀ c' ∈ cs, c'.labelRight ≠ splitLabel i := by
        intro c' hc' h
        have h1 : isReserved c'.labelRight = false :=
          hres _ (by
            simp only [List.mem_cons, List.map_cons]; right; right
            exact List.mem_map_of_mem (f := fun x => x.labelRight) hc')
        have := isReserved_splitLabel i
        rw [← h, h1] at this; simp at this
      have hnot : ∀ m ∈ (splitPaths (i + 1) cs).1, m.unknown.name ≠ splitLabel i := by
        intro m hm h
        obtain ⟨j, hj, hn⟩ := splitPaths_head_index cs (i + 1) m hm
        rw [hn] at h
        have := splitLabel_injective h
        omega
      have ih' := ih (i + 1)
      simp only [splitPaths, hl, List.map_cons, allHold, holds]
      simp only [mem_evalMatches_cons]
      cases hr : e c.labelRight with
      | none =>
        have hL : c.holds g (e.bind u f) u = false := by
          unfold PathCondition.holds
          simp [Env.bind, hcne, hr]
        constructor
        · rintro ⟨e', ⟨f', hf', hty, hh, he'⟩, hall⟩
          exfalso
          simp [allHold, holds, PathCondition.holds, Env.bind, hnlr, hr] at hh
        · intro h
          rw [hL] at h
          simp at h
      | some r =>
        have hR : (e.bind u f) c.labelRight = some r := by simp [Env.bind, hcne, hr]
        have hhead : ∀ f' : Fact,
            allHold g (e.bind (splitLabel i) f'.id) (splitLabel i)
              [.path { rolesLeft := [], labelRight := c.labelRight, rolesRight := c.rolesRight }] = true
            ↔ f'.id ∈ g.walk r c.rolesRight := by
          intro f'
          simp [allHold, holds, PathCondition.holds, Env.bind, hnlr, hr, Graph.walk]
        have htail : ∀ (e' : Env) (x : FactId), e' (splitLabel i) = some x →
            (PathCondition.holds g (e'.bind u f) u
              { rolesLeft := c.rolesLeft, labelRight := splitLabel i, rolesRight := [] } = true
            ↔ x ∈ g.walk f c.rolesLeft) := by
          intro e' x hx
          have : (e'.bind u f) (splitLabel i) = some x := by simp [Env.bind, hnu, hx]
          simp [PathCondition.holds, Env.bind, Graph.walk, hnu, hx]
        have horig : c.holds g (e.bind u f) u = true ↔
            ∃ a, a ∈ g.walk f c.rolesLeft ∧ a ∈ g.walk r c.rolesRight := by
          have hcu : ¬ c.labelRight = u := hcne
          simp [PathCondition.holds, Env.bind, hcu, hr]
        constructor
        · rintro ⟨e', ⟨f', hf', hty, hh, he'⟩, hall⟩
          have hall' := (Bool.and_eq_true _ _).mp hall
          have hname' : e' (splitLabel i) = some f'.id := by
            rw [evalMatches_frame he' (splitLabel i)]
            · simp [Env.bind]
            · intro hmem
              obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hmem
              exact hnot m hm hmn
          have h1 := (htail e' f'.id hname').mp hall'.1
          have h2 := (hhead f').mp hh
          refine (Bool.and_eq_true _ _).mpr ⟨horig.mpr ⟨_, h1, h2⟩, ?_⟩
          rw [← allHold_bind_irrel (e := e) (x := f'.id) hnu cs hcs_name]
          exact (ih' (e.bind (splitLabel i) f'.id) hne' hres').mp ⟨e', he', hall'.2⟩
        · intro h
          have h' := (Bool.and_eq_true _ _).mp h
          obtain ⟨a, ha1, ha2⟩ := horig.mp h'.1
          obtain ⟨f', hf', hid, hty⟩ := walk_mem_type c.rolesRight r a ha2 hl
          have hrest : allHold g ((e.bind (splitLabel i) f'.id).bind u f) u (cs.map .path) = true := by
            rw [allHold_bind_irrel hnu cs hcs_name]; exact h'.2
          obtain ⟨e', he', hq⟩ := (ih' (e.bind (splitLabel i) f'.id) hne' hres').mpr hrest
          have hname' : e' (splitLabel i) = some f'.id := by
            rw [evalMatches_frame he' (splitLabel i)]
            · simp [Env.bind]
            · intro hmem
              obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hmem
              exact hnot m hm hmn
          refine ⟨e', ⟨f', hf', hty, (hhead f').mpr (hid ▸ ha2), he'⟩, ?_⟩
          exact (Bool.and_eq_true _ _).mpr
            ⟨(htail e' f'.id hname').mpr (hid ▸ ha1), hq⟩

end JinagaSpec
