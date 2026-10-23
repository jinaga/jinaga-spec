import JinagaSpec.Candidates
import JinagaSpec.Proofs.Fresh
import JinagaSpec.Proofs.Main
import JinagaSpec.Proofs.Derivation
import JinagaSpec.Proofs.Maintain

/-!
# Layers 2 and 3: every change is touched, so the candidates cover it

**Layer 2.** Compare a list of matches on `g` and on `g ++ [f]`, from the same
environment. Take a solution on one graph that is not a solution on the other.
Walk its matches in order to the first that differs. Either that match is bound
to `f` itself, which can only happen on the new graph, or one of its conditions
answers differently on the two graphs. A path condition cannot (layer 1), so it
is an existential condition, and its matches have a solution on one graph that
they do not have on the other. That is the same situation, one level down. The
recursion ends, because the specification is finite, at a match bound to `f`.

**Layer 3.** Each step of that argument is one of the choices `touchMatches`
makes, so the inverse it builds has the changed solution as a solution, on the
new graph. At a level that gained, every condition holds on the new graph, so
nothing needs to change. At a level that lost, the conditions held on the old
graph. The path conditions still hold on the new graph (layer 1), and the
existential conditions were dropped.

The mutual induction below is both layers at once: `gainedMatches` and
`lostMatches` say that a changed solution is a solution of one of the inverses,
and their proofs are the walk just described.

Throughout, the environment binds `f` only under `pinLabel`, and the matches
never mention `pinLabel`, which `WellFormed` gives because it is reserved.
-/
namespace JinagaSpec

mutual
  /-- Every unknown the matches declare, at any depth. -/
  def declaredInMatches : List Match → List Name
    | [] => []
    | .mk u cs :: rest => u.name :: declaredInConditions cs ++ declaredInMatches rest

  def declaredInConditions : List Condition → List Name
    | [] => []
    | c :: cs => declaredInCondition c ++ declaredInConditions cs

  def declaredInCondition : Condition → List Name
    | .path _ => []
    | .existential _ ms => declaredInMatches ms
end

mutual
  theorem declaredInMatches_ordinary :
      ∀ (ms : List Match) (A : List Name), WellNamedMatches A ms →
        ∀ x ∈ declaredInMatches ms, isReserved x = false
    | [], _, _, _, hx => by simp [declaredInMatches] at hx
    | .mk u cs :: rest, A, ⟨_, hord, hcs, hrest⟩, x, hx => by
      simp only [declaredInMatches, List.mem_cons, List.mem_append] at hx
      rcases hx with (rfl | hx) | hx
      · exact hord
      · exact declaredInConditions_ordinary cs _ hcs x hx
      · exact declaredInMatches_ordinary rest _ hrest x hx

  theorem declaredInConditions_ordinary :
      ∀ (cs : List Condition) (A : List Name), WellNamedConditions A cs →
        ∀ x ∈ declaredInConditions cs, isReserved x = false
    | [], _, _, _, hx => by simp [declaredInConditions] at hx
    | c :: cs, A, ⟨hc, hcs⟩, x, hx => by
      simp only [declaredInConditions, List.mem_append] at hx
      rcases hx with hx | hx
      · exact declaredInCondition_ordinary c A hc x hx
      · exact declaredInConditions_ordinary cs A hcs x hx

  theorem declaredInCondition_ordinary :
      ∀ (c : Condition) (A : List Name), WellNamedCondition A c →
        ∀ x ∈ declaredInCondition c, isReserved x = false
    | .path _, _, _, _, hx => by simp [declaredInCondition] at hx
    | .existential _ ms, A, h, x, hx => declaredInMatches_ordinary ms A h x hx
end

theorem isReserved_pinLabel : isReserved pinLabel = true := by simp [isReserved, pinLabel]

variable {g : Graph} {f : Fact}

/-- `f` is bound under `pinLabel`, and under no other label. -/
structure PinOnly (f : Fact) (env : Env) : Prop where
  pin : env pinLabel = some f.id
  only : ∀ y, env y = some f.id → y = pinLabel

theorem PinOnly.bind {env : Env} (h : PinOnly f env) {u : Name} (hu : u ≠ pinLabel) {id : FactId}
    (hid : id ≠ f.id) : PinOnly f (env.bind u id) where
  pin := by simp [Env.bind, Ne.symm hu, h.pin]
  only y hy := by
    by_cases hyu : y = u
    · subst hyu; simp [Env.bind] at hy; exact absurd hy hid
    · exact h.only y (by simpa [Env.bind, hyu] using hy)

/-- A path condition answers the same on both graphs, unless it is at `f`. -/
theorem holds_path_fresh (hf : Fresh g f) {env : Env} (hpin : PinOnly f env) {u : Name}
    (hu : env u ≠ some f.id) (pc : PathCondition) (hr : pc.labelRight ≠ pinLabel) :
    holds (g ++ [f]) env u (.path pc) = holds g env u (.path pc) := by
  simp only [holds]
  exact pathHolds_fresh hf pc hu fun h => hr (hpin.only _ h)

/-- What held on the old graph still holds on the new one, once a lost level
drops its existential conditions. -/
theorem allHold_relax (hf : Fresh g f) {env : Env} (hpin : PinOnly f env) {u : Name}
    (hu : env u ≠ some f.id) :
    ∀ (cs : List Condition), pinLabel ∉ usedInConditions cs → allHold g env u cs = true →
      allHold (g ++ [f]) env u (relax false cs) = true
  | [], _, _ => rfl
  | .path pc :: cs, hn, h => by
    simp only [usedInConditions, usedInCondition, List.mem_append, List.mem_singleton, not_or] at hn
    simp only [allHold, Bool.and_eq_true] at h
    have : relax false (.path pc :: cs) = .path pc :: relax false cs := by
      simp [relax, Condition.isPath]
    rw [this, allHold, holds_path_fresh hf hpin hu pc (Ne.symm hn.1), h.1,
      allHold_relax hf hpin hu cs hn.2 h.2]
    rfl
  | .existential e ms :: cs, hn, h => by
    simp only [usedInConditions, List.mem_append, not_or] at hn
    simp only [allHold, Bool.and_eq_true] at h
    have : relax false (.existential e ms :: cs) = relax false cs := by
      simp [relax, Condition.isPath]
    rw [this]
    exact allHold_relax hf hpin hu cs hn.2 h.2

theorem evalMatches_relax (hf : Fresh g f) :
    ∀ (ms : List Match) {env e3 : Env}, PinOnly f env → pinLabel ∉ usedInMatches ms →
      pinLabel ∉ declaredInMatches ms → e3 ∈ evalMatches g env ms →
      e3 ∈ evalMatches (g ++ [f]) env (relaxMatches false ms)
  | [], _, _, _, _, _, h => by simpa [relaxMatches, evalMatches] using h
  | .mk u cs :: rest, env, e3, hpin, hu, hd, h => by
    simp only [usedInMatches, declaredInMatches, List.mem_append, List.mem_cons, not_or] at hu hd
    obtain ⟨x, hx, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
    have hid := hf.idNew x hx
    have hpin' := hpin.bind (Ne.symm hd.1.1) hid
    have hrest := evalMatches_relax hf rest hpin' hu.2 hd.2 hr
    simp only [relaxMatches, Bool.false_eq_true, ite_false, List.map_cons] at hrest ⊢
    exact mem_evalMatches_cons.mpr ⟨x, List.mem_append_left _ hx, ht,
      allHold_relax hf hpin' (by simp [Env.bind, hid]) cs hu.1 hc, hrest⟩

mutual
  /-- A solution gained by adding `f` is a solution, on the new graph, of an
  inverse for gained results. -/
  theorem gainedMatches (hf : Fresh g f) :
      ∀ (ms : List Match) {env e3 : Env}, PinOnly f env → pinLabel ∉ usedInMatches ms →
        pinLabel ∉ declaredInMatches ms → e3 ∈ evalMatches (g ++ [f]) env ms →
        e3 ∉ evalMatches g env ms → ∃ t ∈ touchMatches true ms, e3 ∈ evalMatches (g ++ [f]) env t.2
    | [], _, _, _, _, _, h, hn => by simp [evalMatches] at h hn; exact absurd h hn
    | .mk u cs :: rest, env, e3, hpin, hu, hd, h, hn => by
      simp only [usedInMatches, declaredInMatches, List.mem_append, List.mem_cons, not_or] at hu hd
      obtain ⟨x, hx, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
      by_cases hxf : x.id = f.id
      · -- `f` itself: pin it.
        refine ⟨(u, .mk u (pinCondition :: cs) :: rest), by simp [touchMatches],
          mem_evalMatches_cons.mpr ⟨x, hx, ht, ?_, hr⟩⟩
        rw [hxf] at hc ⊢
        simp [allHold, hc, holds, pinCondition, PathCondition.holds, Env.bind, Graph.walk, hpin.pin]
      have hxg : x ∈ g := by
        rcases List.mem_append.mp hx with hx | hx
        · exact hx
        · simp at hx; exact absurd (hx ▸ rfl) hxf
      have hpin' := hpin.bind (Ne.symm hd.1.1) hxf
      have hu' : (env.bind u.name x.id) u.name ≠ some f.id := by simp [Env.bind, hxf]
      cases hcg : allHold g (env.bind u.name x.id) u.name cs
      · -- A condition changed its answer: go into it.
        obtain ⟨t, htm, hct⟩ := gainedConditions hf cs hpin' hu' hu.1 hd.1.2 hc hcg
        refine ⟨(t.1, .mk u t.2 :: rest), ?_, mem_evalMatches_cons.mpr ⟨x, hx, ht, hct, hr⟩⟩
        simp only [touchMatches, ite_true, relaxMatches, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨t, htm, rfl⟩)
      · -- The match is the same: the change is in the matches after it.
        obtain ⟨t, htm, het⟩ := gainedMatches hf rest hpin' hu.2 hd.2 hr
          fun h' => hn (mem_evalMatches_cons.mpr ⟨x, hxg, ht, hcg, h'⟩)
        refine ⟨(t.1, .mk u cs :: t.2), ?_, mem_evalMatches_cons.mpr ⟨x, hx, ht, hc, het⟩⟩
        simp only [touchMatches, ite_true, relax, List.mem_append, List.mem_map]
        exact Or.inr ⟨t, htm, rfl⟩

  /-- A solution lost by adding `f` is a solution, on the new graph, of an
  inverse for lost results. -/
  theorem lostMatches (hf : Fresh g f) :
      ∀ (ms : List Match) {env e3 : Env}, PinOnly f env → pinLabel ∉ usedInMatches ms →
        pinLabel ∉ declaredInMatches ms → e3 ∈ evalMatches g env ms →
        e3 ∉ evalMatches (g ++ [f]) env ms → ∃ t ∈ touchMatches false ms, e3 ∈ evalMatches (g ++ [f]) env t.2
    | [], _, _, _, _, _, h, hn => by simp [evalMatches] at h hn; exact absurd h hn
    | .mk u cs :: rest, env, e3, hpin, hu, hd, h, hn => by
      simp only [usedInMatches, declaredInMatches, List.mem_append, List.mem_cons, not_or] at hu hd
      obtain ⟨x, hx, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
      have hxf := hf.idNew x hx
      have hx' : x ∈ g ++ [f] := List.mem_append_left _ hx
      have hpin' := hpin.bind (Ne.symm hd.1.1) hxf
      have hu' : (env.bind u.name x.id) u.name ≠ some f.id := by simp [Env.bind, hxf]
      cases hcg : allHold (g ++ [f]) (env.bind u.name x.id) u.name cs
      · -- A condition changed its answer: go into it; the matches after it relax.
        obtain ⟨t, htm, hct⟩ := lostConditions hf cs hpin' hu' hu.1 hd.1.2 hc hcg
        refine ⟨(t.1, .mk u t.2 :: relaxMatches false rest), ?_, mem_evalMatches_cons.mpr
          ⟨x, hx', ht, hct, evalMatches_relax hf rest hpin' hu.2 hd.2 hr⟩⟩
        simp only [touchMatches, Bool.false_eq_true, ite_false, List.nil_append, List.mem_append,
          List.mem_map]
        exact Or.inl ⟨t, htm, rfl⟩
      · -- The match is the same: the change is in the matches after it.
        obtain ⟨t, htm, het⟩ := lostMatches hf rest hpin' hu.2 hd.2 hr
          fun h' => hn (mem_evalMatches_cons.mpr ⟨x, hx', ht, hcg, h'⟩)
        refine ⟨(t.1, .mk u (relax false cs) :: t.2), ?_, mem_evalMatches_cons.mpr
          ⟨x, hx', ht, allHold_relax hf hpin' hu' cs hu.1 hc, het⟩⟩
        simp only [touchMatches, Bool.false_eq_true, ite_false, List.nil_append, List.mem_append,
          List.mem_map]
        exact Or.inr ⟨t, htm, rfl⟩

  theorem gainedConditions (hf : Fresh g f) :
      ∀ (cs : List Condition) {env : Env} {u : Name}, PinOnly f env → env u ≠ some f.id →
        pinLabel ∉ usedInConditions cs → pinLabel ∉ declaredInConditions cs →
        allHold (g ++ [f]) env u cs = true → allHold g env u cs = false →
        ∃ t ∈ touchConditions true cs, allHold (g ++ [f]) env u t.2 = true
    | [], _, _, _, _, _, _, _, hn => by simp [allHold] at hn
    | c :: cs, env, u, hpin, hu, hus, hds, h, hn => by
      simp only [usedInConditions, declaredInConditions, List.mem_append, not_or] at hus hds
      simp only [allHold, Bool.and_eq_true, Bool.and_eq_false_iff] at h hn
      by_cases hcg : holds g env u c = true
      · obtain ⟨t, htm, hct⟩ := gainedConditions hf cs hpin hu hus.2 hds.2 h.2
          (hn.resolve_left (by simp [hcg]))
        refine ⟨(t.1, c :: t.2), ?_, by simp [allHold, h.1, hct]⟩
        simp only [touchConditions, relax, ite_true, List.mem_append, List.mem_map]
        exact Or.inr ⟨t, htm, rfl⟩
      · obtain ⟨t, htm, hct⟩ := flipCondition hf c hpin hu hus.1 hds.1 (by simp [hcg, h.1])
        rw [h.1] at htm
        refine ⟨(t.1, t.2 :: cs), ?_, by simp [allHold, hct, h.2]⟩
        simp only [touchConditions, relax, ite_true, List.mem_append, List.mem_map]
        exact Or.inl ⟨t, htm, rfl⟩

  theorem lostConditions (hf : Fresh g f) :
      ∀ (cs : List Condition) {env : Env} {u : Name}, PinOnly f env → env u ≠ some f.id →
        pinLabel ∉ usedInConditions cs → pinLabel ∉ declaredInConditions cs →
        allHold g env u cs = true → allHold (g ++ [f]) env u cs = false →
        ∃ t ∈ touchConditions false cs, allHold (g ++ [f]) env u t.2 = true
    | [], _, _, _, _, _, _, _, hn => by simp [allHold] at hn
    | c :: cs, env, u, hpin, hu, hus, hds, h, hn => by
      simp only [usedInConditions, declaredInConditions, List.mem_append, not_or] at hus hds
      simp only [allHold, Bool.and_eq_true, Bool.and_eq_false_iff] at h hn
      by_cases hcg : holds (g ++ [f]) env u c = true
      · obtain ⟨t, htm, hct⟩ := lostConditions hf cs hpin hu hus.2 hds.2 h.2
          (hn.resolve_left (by simp [hcg]))
        refine ⟨(t.1, relax false [c] ++ t.2), ?_, ?_⟩
        · simp only [touchConditions, List.mem_append, List.mem_map]
          exact Or.inr ⟨t, htm, rfl⟩
        · cases c with
          | path pc => simp [relax, Condition.isPath, allHold, hcg, hct]
          | existential => simpa [relax, Condition.isPath] using hct
      · obtain ⟨t, htm, hct⟩ := flipCondition hf c hpin hu hus.1 hds.1 (by simp [hcg, h.1])
        simp only [Bool.not_eq_true] at hcg
        rw [hcg] at htm
        refine ⟨(t.1, t.2 :: relax false cs), ?_, ?_⟩
        · simp only [touchConditions, List.mem_append, List.mem_map]
          exact Or.inl ⟨t, htm, rfl⟩
        · simp [allHold, hct, allHold_relax hf hpin hu cs hus.2 h.2]

  /-- A condition that answers differently on the two graphs is an existential
  condition, and its matches gained or lost a solution: go into it. -/
  theorem flipCondition (hf : Fresh g f) :
      ∀ (c : Condition) {env : Env} {u : Name}, PinOnly f env → env u ≠ some f.id →
        pinLabel ∉ usedInCondition c → pinLabel ∉ declaredInCondition c →
        holds g env u c ≠ holds (g ++ [f]) env u c →
        ∃ t ∈ touchCondition (holds (g ++ [f]) env u c) c, holds (g ++ [f]) env u t.2 = true
    | .path pc, _, _, hpin, hu, hus, _, hne => by
      simp only [usedInCondition, List.mem_singleton] at hus
      exact absurd (holds_path_fresh hf hpin hu pc (Ne.symm hus)).symm hne
    | .existential b ms, env, u, hpin, hu, hus, hds, hne => by
      simp only [usedInCondition, declaredInCondition] at hus hds
      -- The rewritten condition is `exists`, so a solution of its matches makes it hold.
      have hex : ∀ ms' e4, e4 ∈ evalMatches (g ++ [f]) env ms' →
          holds (g ++ [f]) env u (.existential true ms') = true := by
        intro ms' e4 h
        cases hE : evalMatches (g ++ [f]) env ms' with
        | nil => rw [hE] at h; simp at h
        | cons => simp [holds, hE]
      have hv : holds (g ++ [f]) env u (.existential b ms) =
          (b == !(evalMatches (g ++ [f]) env ms).isEmpty) := rfl
      simp only [holds] at hne
      rw [hv]
      cases hA : evalMatches (g ++ [f]) env ms with
      | nil =>
        cases hB : evalMatches g env ms with
        | nil => rw [hA, hB] at hne; exact absurd rfl hne
        | cons e4 _ =>
          obtain ⟨t, htm, het⟩ := lostMatches hf ms (e3 := e4) hpin hus hds
            (by rw [hB]; exact List.mem_cons_self) (by rw [hA]; simp)
          refine ⟨(t.1, .existential true t.2), ?_, hex _ _ het⟩
          cases b <;> exact List.mem_map.mpr ⟨t, htm, rfl⟩
      | cons e4 _ =>
        cases hB : evalMatches g env ms with
        | cons => rw [hA, hB] at hne; exact absurd rfl hne
        | nil =>
          obtain ⟨t, htm, het⟩ := gainedMatches hf ms (e3 := e4) hpin hus hds
            (by rw [hA]; exact List.mem_cons_self) (by rw [hB]; simp)
          refine ⟨(t.1, .existential true t.2), ?_, hex _ _ het⟩
          cases b <;> exact List.mem_map.mpr ⟨t, htm, rfl⟩
end

/-- **`candidates_complete`.** For a well-formed specification and a fresh fact,
the candidates include every result the fact adds or removes. With
`maintain_correct`, a stream that re-checks these candidates after each
insertion holds exactly the specification's results. -/
theorem candidates_complete (s : Specification) (hwf : WellFormed s) (hf : Fresh g f) (env : Env) :
    Covers s env g f (candidates s env g f) := by
  intro r
  unfold candidates
  split
  · -- `f` is one of the givens: every result old and new is a candidate.
    by_cases h1 : r ∈ s.evaluate g env <;> by_cases h2 : r ∈ s.evaluate (g ++ [f]) env <;> simp_all
  rename_i hgiv
  let givens := s.given.map (·.name)
  have hgivOrd : ∀ x ∈ givens, isReserved x = false := by
    intro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    exact hwf.givensOrdinary l hl
  -- Bind `f` under `pinLabel`, and forget every label but the givens.
  have hag : Agree givens env (pinEnv s env f) := by
    intro x hx
    have : x ≠ pinLabel := fun h => by simpa [h, isReserved_pinLabel] using hgivOrd x hx
    simp [pinEnv, Env.bind, Env.restrictTo, this, hx, givens]
  have hsame : ∀ G, r ∈ s.evaluate G env ↔ r ∈ s.evaluate G (pinEnv s env f) := fun G => by
    simp only [Specification.evaluate, List.mem_map]
    exact exists_projection_iff hwf.inScope hag (fun x hx => List.mem_append.mpr (hwf.projected x hx)) r
  have hpin : PinOnly f (pinEnv s env f) := by
    refine ⟨by simp [pinEnv, Env.bind], fun y hy => ?_⟩
    by_cases hyp : y = pinLabel
    · exact hyp
    · simp only [pinEnv, Env.bind, hyp, ite_false, Env.restrictTo] at hy
      split at hy
      · rename_i hc
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
        exact absurd (List.any_eq_true.mpr ⟨l, hl, by simp [hy]⟩) hgiv
      · simp at hy
  have hus : pinLabel ∉ usedInMatches s.matchList := fun h => by
    simpa [isReserved_pinLabel] using
      usedInMatches_ordinary s.matchList givens hwf.inScope hwf.wellNamed hgivOrd _ h
  have hds : pinLabel ∉ declaredInMatches s.matchList := fun h => by
    simpa [isReserved_pinLabel] using declaredInMatches_ordinary s.matchList givens hwf.wellNamed _ h
  -- A changed solution is a solution of an inverse, and projects to the same result.
  have hfound : ∀ t ∈ touchMatches true s.matchList ++ touchMatches false s.matchList,
      ∀ e3 ∈ evalMatches (g ++ [f]) (pinEnv s env f) t.2, s.projection.labels.map e3 = r →
      r ∈ (inverses s).flatMap (·.evaluate (g ++ [f]) (pinEnv s env f)) := by
    intro t ht e3 he3 hr
    exact List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨t, ht, rfl⟩, List.mem_map.mpr ⟨e3, he3, hr⟩⟩
  rw [hsame g, hsame (g ++ [f])]
  by_cases h1 : r ∈ s.evaluate g (pinEnv s env f) <;>
    by_cases h2 : r ∈ s.evaluate (g ++ [f]) (pinEnv s env f)
  · exact Or.inl (iff_of_true h1 h2)
  · -- Lost.
    obtain ⟨e3, he3, hr⟩ := List.mem_map.mp h1
    obtain ⟨t, ht, het⟩ := lostMatches hf s.matchList hpin hus hds he3
      fun h => h2 (List.mem_map.mpr ⟨e3, h, hr⟩)
    exact Or.inr (hfound t (List.mem_append_right _ ht) e3 het hr)
  · -- Gained.
    obtain ⟨e3, he3, hr⟩ := List.mem_map.mp h2
    obtain ⟨t, ht, het⟩ := gainedMatches hf s.matchList hpin hus hds he3
      fun h => h1 (List.mem_map.mpr ⟨e3, h, hr⟩)
    exact Or.inr (hfound t (List.mem_append_left _ ht) e3 het hr)
  · exact Or.inl (iff_of_false h1 h2)

/-- **A stream is its specification's result.** Start from a read of the
result, and after each fact arrives re-check the candidates: the stream then
holds exactly the specification's results on the replica's graph, provided
each fact is fresh when it arrives. -/
theorem stream_correct (s : Specification) (hwf : WellFormed s) (env : Env) :
    ∀ (fs : List Fact) (g : Graph) (held : List Row),
      (∀ r, r ∈ held ↔ r ∈ s.evaluate g env) →
      (∀ pre f post, fs = pre ++ f :: post → Fresh (g ++ pre) f) →
      ∀ r, r ∈ (fs.foldl (maintainStep s env (candidates s env)) (g, held)).2 ↔ r ∈ s.evaluate (g ++ fs) env :=
  fun fs g held hheld hfresh =>
    maintain_correct s env (candidates s env) fs g held hheld
      fun pre f post h => candidates_complete s hwf (hfresh pre f post h) env

end JinagaSpec
