import JinagaSpec.Proofs.Basic

/-!
# Splitting the pivot's path conditions

A path condition that walks predecessors becomes a head match that binds a
split label, and a tail condition that joins to it. The two say the same thing:
the head enumerates the facts the predecessor walk reaches, and the tail asks
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

/-- Every split label is fresh, and the tail's paths join only labels the
pivot joined or the split labels. -/
theorem splitPaths_names (taken : List Name) :
    ∀ (ps : List PathCondition),
      (∀ m ∈ (splitPaths taken ps).1, m.unknown.name ∉ taken) ∧
      (∀ c ∈ (splitPaths taken ps).2,
        c.labelRight ∈ ps.map (·.labelRight) ∨
        c.labelRight ∈ (splitPaths taken ps).1.map (·.unknown.name)) := by
  intro ps
  induction ps generalizing taken with
  | nil => simp [splitPaths]
  | cons c cs ih =>
    cases hl : c.rolesRight.getLast? with
    | none =>
      obtain ⟨ih1, ih2⟩ := ih taken
      simp only [splitPaths, hl]
      refine ⟨ih1, ?_⟩
      intro c' hc'
      rcases List.mem_cons.mp hc' with rfl | hc'
      · left; simp
      · rcases ih2 c' hc' with h | h
        · left; exact List.mem_cons_of_mem _ h
        · right; exact h
    | some last =>
      obtain ⟨ih1, ih2⟩ := ih (freshLabel taken :: taken)
      simp only [splitPaths, hl]
      refine ⟨?_, ?_⟩
      · intro m hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact freshLabel_not_mem taken
        · intro hmem
          exact ih1 m hm (List.mem_cons_of_mem _ hmem)
      · intro c' hc'
        rcases List.mem_cons.mp hc' with rfl | hc'
        · right; simp
        · rcases ih2 c' hc' with h | h
          · left; exact List.mem_cons_of_mem _ h
          · right; exact List.mem_cons_of_mem _ h

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

/-- The split preserves the pivot's path conditions. The unknown `u` is bound
to `f`. Some way of binding the split labels makes the tail's paths hold
exactly when the pivot's paths held.

The statement needs `hne`: a pivot condition that joins the pivot to itself
reads `f` in the original but `e u` in the head, and `e u` need not be `f`.
Counterexample without `hne`: `g = [{id := 0, type := "T", predecessors := [("r", 0)]}]`,
`u = "u"`, `f = 0`, `taken = ["u"]`, `e = fun _ => none`, and
`ps = [{rolesLeft := [], labelRight := "u", rolesRight := [{name := "r", predecessorType := "T"}]}]`. -/
theorem splitPaths_correct (g : Graph) (u : Name) (f : FactId) :
    ∀ (ps : List PathCondition) (taken : List Name) (e : Env),
      (∀ c ∈ ps, c.labelRight ≠ u) →
      (∀ x ∈ u :: ps.map (·.labelRight), x ∈ taken) →
      ((∃ e' ∈ evalMatches g e (splitPaths taken ps).1,
          allHold g (e'.bind u f) u ((splitPaths taken ps).2.map .path) = true) ↔
        allHold g (e.bind u f) u (ps.map .path) = true) := by
  intro ps
  induction ps with
  | nil => intro taken e _ _; simp [splitPaths, evalMatches, allHold]
  | cons c cs ih =>
    intro taken e hne htaken
    have hne' : ∀ c' ∈ cs, c'.labelRight ≠ u := fun c' h => hne c' (List.mem_cons_of_mem _ h)
    have hu : u ∈ taken := htaken u (by simp)
    have hlr : c.labelRight ∈ taken := htaken _ (by simp)
    have hcne : c.labelRight ≠ u := hne c (by simp)
    cases hl : c.rolesRight.getLast? with
    | none =>
      have htaken' : ∀ x ∈ u :: cs.map (·.labelRight), x ∈ taken := by
        intro x hx
        apply htaken
        simp only [List.mem_cons, List.map_cons] at hx ⊢
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      obtain ⟨hn1, _⟩ := splitPaths_names taken cs
      have key : ∀ e' ∈ evalMatches g e (splitPaths taken cs).1,
          c.holds g (e'.bind u f) u = c.holds g (e.bind u f) u := by
        intro e' he'
        apply pathHolds_agree
        left
        apply evalMatches_frame he'
        intro hmem
        obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hmem
        exact hn1 m hm (hmn ▸ hlr)
      have ih' := ih taken e hne' htaken'
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
      obtain ⟨name, hname⟩ : ∃ n, n = freshLabel taken := ⟨_, rfl⟩
      have hnt : name ∉ taken := hname ▸ freshLabel_not_mem taken
      have hnu : name ≠ u := fun h => hnt (h ▸ hu)
      have hnlr : c.labelRight ≠ name := fun h => hnt (h ▸ hlr)
      have htaken' : ∀ x ∈ u :: cs.map (·.labelRight), x ∈ name :: taken := by
        intro x hx
        apply List.mem_cons_of_mem
        apply htaken
        simp only [List.mem_cons, List.map_cons] at hx ⊢
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      have hcs_name : ∀ c' ∈ cs, c'.labelRight ≠ name := by
        intro c' hc' h
        exact hnt (h ▸ htaken c'.labelRight
          (by simp only [List.mem_cons, List.map_cons]; right; right; exact List.mem_map_of_mem (f := fun x => x.labelRight) hc'))
      obtain ⟨hn1, _⟩ := splitPaths_names (name :: taken) cs
      have ih' := ih (name :: taken)
      simp only [splitPaths, hl, ← hname, List.map_cons, allHold, holds]
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
            allHold g (e.bind name f'.id) name
              [.path { rolesLeft := [], labelRight := c.labelRight, rolesRight := c.rolesRight }] = true
            ↔ f'.id ∈ g.walk r c.rolesRight := by
          intro f'
          simp [allHold, holds, PathCondition.holds, Env.bind, hnlr, hr, Graph.walk]
        have htail : ∀ (e' : Env) (x : FactId), e' name = some x →
            (PathCondition.holds g (e'.bind u f) u
              { rolesLeft := c.rolesLeft, labelRight := name, rolesRight := [] } = true
            ↔ x ∈ g.walk f c.rolesLeft) := by
          intro e' x hx
          have : (e'.bind u f) name = some x := by simp [Env.bind, hnu, hx]
          simp [PathCondition.holds, Env.bind, Graph.walk, hnu, hx]
        have horig : c.holds g (e.bind u f) u = true ↔
            ∃ a, a ∈ g.walk f c.rolesLeft ∧ a ∈ g.walk r c.rolesRight := by
          have hcu : ¬ c.labelRight = u := hcne
          simp [PathCondition.holds, Env.bind, hcu, hr]
        constructor
        · rintro ⟨e', ⟨f', hf', hty, hh, he'⟩, hall⟩
          have hall' := (Bool.and_eq_true _ _).mp hall
          have hname' : e' name = some f'.id := by
            rw [evalMatches_frame he' name]
            · simp [Env.bind]
            · intro hmem
              obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hmem
              exact hn1 m hm (hmn ▸ List.mem_cons_self)
          have h1 := (htail e' f'.id hname').mp hall'.1
          have h2 := (hhead f').mp hh
          refine (Bool.and_eq_true _ _).mpr ⟨horig.mpr ⟨_, h1, h2⟩, ?_⟩
          rw [← allHold_bind_irrel (e := e) (x := f'.id) hnu cs hcs_name]
          exact (ih' (e.bind name f'.id) hne' htaken').mp ⟨e', he', hall'.2⟩
        · intro h
          have h' := (Bool.and_eq_true _ _).mp h
          obtain ⟨a, ha1, ha2⟩ := horig.mp h'.1
          obtain ⟨f', hf', hid, hty⟩ := walk_mem_type c.rolesRight r a ha2 hl
          have hrest : allHold g ((e.bind name f'.id).bind u f) u (cs.map .path) = true := by
            rw [allHold_bind_irrel hnu cs hcs_name]; exact h'.2
          obtain ⟨e', he', hq⟩ := (ih' (e.bind name f'.id) hne' htaken').mpr hrest
          have hname' : e' name = some f'.id := by
            rw [evalMatches_frame he' name]
            · simp [Env.bind]
            · intro hmem
              obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hmem
              exact hn1 m hm (hmn ▸ List.mem_cons_self)
          refine ⟨e', ⟨f', hf', hty, (hhead f').mpr (hid ▸ ha2), he'⟩, ?_⟩
          exact (Bool.and_eq_true _ _).mpr
            ⟨(htail e' f'.id hname').mpr (hid ▸ ha1), hq⟩

end JinagaSpec
