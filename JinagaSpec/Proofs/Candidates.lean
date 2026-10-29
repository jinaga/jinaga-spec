import JinagaSpec.Candidates
import JinagaSpec.Proofs.Fresh
import JinagaSpec.Proofs.Main
import JinagaSpec.Proofs.Derivation

/-!
# Layers 2 and 3: every change is touched, so the candidates cover it

A batch `B` of fresh facts arrives in `g`. A single fact is the batch `[f]`.

**Layer 2.** Compare a list of matches on `g` and on `g ++ B`, from the same
environment. Take a solution on one graph that is not a solution on the other.
Walk its matches in order to the first that differs. Either that match is bound
to a fact of `B`, which can only happen on the new graph, or one of its
conditions answers differently on the two graphs. A path condition cannot
(layer 1), so it is an existential condition, and its matches have a solution
on one graph that they do not have on the other. That is the same situation,
one level down. The recursion ends, because the specification is finite, at a
match bound to a fact of `B`. The facts of `B` may name each other: the walk
stops at the first one it meets, and never reads a condition below it.

**Layer 3.** Each step of that argument is one of the choices `touchMatches`
makes, so the inverse it builds, given the fact the walk stopped at, has the
changed solution as a solution on the new graph. At a level that gained, every
condition holds on the new graph, so nothing needs to change. At a level that
lost, the conditions held on the old graph. The path conditions still hold on
the new graph (layer 1), and the existential conditions were dropped.

The mutual induction below is both layers at once: `gainedMatches` and
`lostMatches` say that a changed solution is a solution of one of the inverses,
given some fact of `B`, and their proofs are the walk just described.

Throughout, the environment binds a fact of `B` only under `pinLabel`, and the
matches never mention `pinLabel`, which `WellFormed` gives because it is
reserved. The walk learns which fact to pin only when it reaches it, so it
reads each level with the pin unbound and binds it on the way back up: the
level's own conditions never read it (`AgreeOff`).
-/
namespace JinagaSpec

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

/-! ## Reading with the pin bound or not -/

/-- Two environments that differ at most at `pinLabel`. -/
def AgreeOff (e1 e2 : Env) : Prop := ∀ y, y ≠ pinLabel → e1 y = e2 y

theorem AgreeOff.symm {e1 e2 : Env} (h : AgreeOff e1 e2) : AgreeOff e2 e1 :=
  fun y hy => (h y hy).symm

theorem AgreeOff.bind {e1 e2 : Env} (h : AgreeOff e1 e2) (n : Name) (id : FactId) :
    AgreeOff (e1.bind n id) (e2.bind n id) := by
  intro y hy
  simp only [Env.bind]
  split
  · rfl
  · exact h y hy

theorem AgreeOff.pin (env : Env) (id : FactId) : AgreeOff (env.bind pinLabel id) env := by
  intro y hy
  simp [Env.bind, hy]

theorem Env.bind_comm {env : Env} {a b : Name} (h : a ≠ b) (x y : FactId) :
    (env.bind a x).bind b y = (env.bind b y).bind a x := by
  funext n
  simp only [Env.bind]
  split <;> split <;> simp_all

mutual
  /-- Matches that never mention `pinLabel` read the same whatever it is bound to. -/
  theorem evalMatches_agreeOff {G : Graph} :
      ∀ (ms : List Match) {env1 env2 e1 : Env}, AgreeOff env1 env2 → pinLabel ∉ usedInMatches ms →
        e1 ∈ evalMatches G env1 ms → ∃ e2 ∈ evalMatches G env2 ms, AgreeOff e1 e2
    | [], _, env2, _, h, _, he => by
      simp only [evalMatches, List.mem_singleton] at he
      subst he
      exact ⟨env2, by simp [evalMatches], h⟩
    | .mk u cs :: rest, _, _, _, h, hu, he => by
      simp only [usedInMatches, List.mem_append, not_or] at hu
      obtain ⟨x, hx, ht, hc, hr⟩ := mem_evalMatches_cons.mp he
      obtain ⟨e2, he2, hag⟩ := evalMatches_agreeOff rest (h.bind u.name x.id) hu.2 hr
      refine ⟨e2, mem_evalMatches_cons.mpr ⟨x, hx, ht, ?_, he2⟩, hag⟩
      rw [← allHold_agreeOff cs (h.bind u.name x.id) (by simp [Env.bind]) hu.1]
      exact hc

  theorem allHold_agreeOff {G : Graph} :
      ∀ (cs : List Condition) {env1 env2 : Env} {u : Name}, AgreeOff env1 env2 → env1 u = env2 u →
        pinLabel ∉ usedInConditions cs → allHold G env1 u cs = allHold G env2 u cs
    | [], _, _, _, _, _, _ => rfl
    | c :: cs, _, _, _, h, hu, hn => by
      simp only [usedInConditions, List.mem_append, not_or] at hn
      simp only [allHold, holds_agreeOff c h hu hn.1, allHold_agreeOff cs h hu hn.2]

  theorem holds_agreeOff {G : Graph} :
      ∀ (c : Condition) {env1 env2 : Env} {u : Name}, AgreeOff env1 env2 → env1 u = env2 u →
        pinLabel ∉ usedInCondition c → holds G env1 u c = holds G env2 u c
    | .path pc, _, _, _, h, hu, hn => by
      simp only [usedInCondition, List.mem_singleton] at hn
      simp only [holds, PathCondition.holds, hu, h _ (Ne.symm hn)]
    | .existential _ ms, env1, env2, _, h, _, hn => by
      simp only [usedInCondition] at hn
      have : (evalMatches G env1 ms).isEmpty = (evalMatches G env2 ms).isEmpty := by
        rw [Bool.eq_iff_iff]
        simp only [List.isEmpty_iff, List.eq_nil_iff_forall_not_mem]
        constructor
        · intro h1 e2 he2
          obtain ⟨e1, he1, _⟩ := evalMatches_agreeOff ms h.symm hn he2
          exact h1 e1 he1
        · intro h2 e1 he1
          obtain ⟨e2, he2, _⟩ := evalMatches_agreeOff ms h hn he1
          exact h2 e2 he2
      simp only [holds, this]
end

/-! ## The walk -/

variable {g : Graph} {B : List Fact}

/-- Only `pinLabel` may bind a fact of `B`. -/
def PinOnly (B : List Fact) (env : Env) : Prop :=
  ∀ y, y ≠ pinLabel → ∀ id, env y = some id → Outside B id

theorem PinOnly.bind {env : Env} (h : PinOnly B env) (u : Name) {id : FactId} (hid : Outside B id) :
    PinOnly B (env.bind u id) := by
  intro y hy i hi
  by_cases hyu : y = u
  · simp only [Env.bind, hyu, ite_true, Option.some.injEq] at hi
    exact hi ▸ hid
  · exact h y hy i (by simpa [Env.bind, hyu] using hi)

theorem PinOnly.pin {env : Env} (h : PinOnly B env) (id : FactId) : PinOnly B (env.bind pinLabel id) :=
  fun y hy i hi => h y hy i (by simpa [Env.bind, hy] using hi)

/-- A path condition answers the same on both graphs, unless it is at a fact of `B`. -/
theorem holds_path_fresh (hf : Fresh g B) {env : Env} (hpin : PinOnly B env) {u : Name}
    (hu : u ≠ pinLabel) (pc : PathCondition) (hr : pc.labelRight ≠ pinLabel) :
    holds (g ++ B) env u (.path pc) = holds g env u (.path pc) :=
  pathHolds_fresh hf pc (hpin u hu) (hpin _ hr)

/-- What held on the old graph still holds on the new one, once a lost level
drops its existential conditions. -/
theorem allHold_relax (hf : Fresh g B) {env : Env} (hpin : PinOnly B env) {u : Name}
    (hu : u ≠ pinLabel) :
    ∀ (cs : List Condition), pinLabel ∉ usedInConditions cs → allHold g env u cs = true →
      allHold (g ++ B) env u (relax false cs) = true
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

theorem evalMatches_relax (hf : Fresh g B) :
    ∀ (ms : List Match) {env e3 : Env}, PinOnly B env → pinLabel ∉ usedInMatches ms →
      pinLabel ∉ declaredInMatches ms → e3 ∈ evalMatches g env ms →
      e3 ∈ evalMatches (g ++ B) env (relaxMatches false ms)
  | [], _, _, _, _, _, h => by simpa [relaxMatches, evalMatches] using h
  | .mk u cs :: rest, env, e3, hpin, hu, hd, h => by
    simp only [usedInMatches, declaredInMatches, List.mem_append, List.mem_cons, not_or] at hu hd
    obtain ⟨x, hx, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
    have hpin' := hpin.bind u.name (hf.idNew x hx)
    have hrest := evalMatches_relax hf rest hpin' hu.2 hd.2 hr
    simp only [relaxMatches, Bool.false_eq_true, ite_false, List.map_cons] at hrest ⊢
    exact mem_evalMatches_cons.mpr ⟨x, List.mem_append_left _ hx, ht,
      allHold_relax hf hpin' (Ne.symm hd.1.1) cs hu.1 hc, hrest⟩

mutual
  /-- A solution gained by adding `B` is a solution, on the new graph, of an
  inverse for gained results, given some fact of `B`. -/
  theorem gainedMatches (hf : Fresh g B) :
      ∀ (ms : List Match) {env e3 : Env}, PinOnly B env → pinLabel ∉ usedInMatches ms →
        pinLabel ∉ declaredInMatches ms → e3 ∈ evalMatches (g ++ B) env ms →
        e3 ∉ evalMatches g env ms → ∃ b ∈ B, ∃ t ∈ touchMatches true ms,
          ∃ e ∈ evalMatches (g ++ B) (env.bind pinLabel b.id) t.2, AgreeOff e3 e
    | [], _, _, _, _, _, h, hn => by simp [evalMatches] at h hn; exact absurd h hn
    | .mk u cs :: rest, env, e3, hpin, hu, hd, h, hn => by
      simp only [usedInMatches, declaredInMatches, List.mem_append, List.mem_cons, not_or] at hu hd
      obtain ⟨x, hx, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
      have hup : u.name ≠ pinLabel := Ne.symm hd.1.1
      have hcomm := fun id => Env.bind_comm (env := env) hd.1.1 id x.id
      have hcs : ∀ id, allHold (g ++ B) ((env.bind u.name x.id).bind pinLabel id) u.name cs =
          allHold (g ++ B) (env.bind u.name x.id) u.name cs := fun id =>
        allHold_agreeOff cs (AgreeOff.pin _ id) (by simp [Env.bind, hup]) hu.1
      by_cases hxB : x ∈ B
      · -- A fact of the batch: pin it.
        obtain ⟨e, he, hag⟩ := evalMatches_agreeOff rest (AgreeOff.pin _ x.id).symm hu.2 hr
        refine ⟨x, hxB, (u, .mk u (pinCondition :: cs) :: rest), by simp [touchMatches], e,
          mem_evalMatches_cons.mpr ⟨x, hx, ht, ?_, hcomm x.id ▸ he⟩, hag⟩
        rw [hcomm, allHold, hcs, hc]
        simp [holds, pinCondition, PathCondition.holds, Env.bind, Graph.walk, hup]
      have hxg : x ∈ g := (List.mem_append.mp hx).resolve_right hxB
      have hpin' := hpin.bind u.name (hf.idNew x hxg)
      cases hcg : allHold g (env.bind u.name x.id) u.name cs
      · -- A condition changed its answer: go into it.
        obtain ⟨b, hb, t, htm, hct⟩ := gainedConditions hf cs hpin' hup hu.1 hd.1.2 hc hcg
        obtain ⟨e, he, hag⟩ := evalMatches_agreeOff rest (AgreeOff.pin _ b.id).symm hu.2 hr
        refine ⟨b, hb, (t.1, .mk u t.2 :: rest), ?_, e,
          mem_evalMatches_cons.mpr ⟨x, hx, ht, hcomm b.id ▸ hct, hcomm b.id ▸ he⟩, hag⟩
        simp only [touchMatches, ite_true, relaxMatches, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨t, htm, rfl⟩)
      · -- The match is the same: the change is in the matches after it.
        obtain ⟨b, hb, t, htm, e, he, hag⟩ := gainedMatches hf rest hpin' hu.2 hd.2 hr
          fun h' => hn (mem_evalMatches_cons.mpr ⟨x, hxg, ht, hcg, h'⟩)
        refine ⟨b, hb, (t.1, .mk u cs :: t.2), ?_, e,
          mem_evalMatches_cons.mpr ⟨x, hx, ht, by rw [hcomm, hcs, hc], hcomm b.id ▸ he⟩, hag⟩
        simp only [touchMatches, ite_true, relax, List.mem_append, List.mem_map]
        exact Or.inr ⟨t, htm, rfl⟩

  /-- A solution lost by adding `B` is a solution, on the new graph, of an
  inverse for lost results, given some fact of `B`. -/
  theorem lostMatches (hf : Fresh g B) :
      ∀ (ms : List Match) {env e3 : Env}, PinOnly B env → pinLabel ∉ usedInMatches ms →
        pinLabel ∉ declaredInMatches ms → e3 ∈ evalMatches g env ms →
        e3 ∉ evalMatches (g ++ B) env ms → ∃ b ∈ B, ∃ t ∈ touchMatches false ms,
          ∃ e ∈ evalMatches (g ++ B) (env.bind pinLabel b.id) t.2, AgreeOff e3 e
    | [], _, _, _, _, _, h, hn => by simp [evalMatches] at h hn; exact absurd h hn
    | .mk u cs :: rest, env, e3, hpin, hu, hd, h, hn => by
      simp only [usedInMatches, declaredInMatches, List.mem_append, List.mem_cons, not_or] at hu hd
      obtain ⟨x, hx, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
      have hup : u.name ≠ pinLabel := Ne.symm hd.1.1
      have hcomm := fun id => Env.bind_comm (env := env) hd.1.1 id x.id
      have hx' : x ∈ g ++ B := List.mem_append_left _ hx
      have hpin' := hpin.bind u.name (hf.idNew x hx)
      cases hcg : allHold (g ++ B) (env.bind u.name x.id) u.name cs
      · -- A condition changed its answer: go into it; the matches after it relax.
        obtain ⟨b, hb, t, htm, hct⟩ := lostConditions hf cs hpin' hup hu.1 hd.1.2 hc hcg
        obtain ⟨e, he, hag⟩ := evalMatches_agreeOff rest (AgreeOff.pin _ b.id).symm hu.2 hr
        refine ⟨b, hb, (t.1, .mk u t.2 :: relaxMatches false rest), ?_, e, mem_evalMatches_cons.mpr
          ⟨x, hx', ht, hcomm b.id ▸ hct,
            hcomm b.id ▸ evalMatches_relax hf rest (hpin'.pin b.id) hu.2 hd.2 he⟩, hag⟩
        simp only [touchMatches, Bool.false_eq_true, ite_false, List.nil_append, List.mem_append,
          List.mem_map]
        exact Or.inl ⟨t, htm, rfl⟩
      · -- The match is the same: the change is in the matches after it.
        obtain ⟨b, hb, t, htm, e, he, hag⟩ := lostMatches hf rest hpin' hu.2 hd.2 hr
          fun h' => hn (mem_evalMatches_cons.mpr ⟨x, hx', ht, hcg, h'⟩)
        have hc' : allHold g ((env.bind u.name x.id).bind pinLabel b.id) u.name cs = true := by
          rw [allHold_agreeOff cs (AgreeOff.pin _ b.id) (by simp [Env.bind, hup]) hu.1, hc]
        refine ⟨b, hb, (t.1, .mk u (relax false cs) :: t.2), ?_, e, mem_evalMatches_cons.mpr
          ⟨x, hx', ht, hcomm b.id ▸ allHold_relax hf (hpin'.pin b.id) hup cs hu.1 hc',
            hcomm b.id ▸ he⟩, hag⟩
        simp only [touchMatches, Bool.false_eq_true, ite_false, List.nil_append, List.mem_append,
          List.mem_map]
        exact Or.inr ⟨t, htm, rfl⟩

  theorem gainedConditions (hf : Fresh g B) :
      ∀ (cs : List Condition) {env : Env} {u : Name}, PinOnly B env → u ≠ pinLabel →
        pinLabel ∉ usedInConditions cs → pinLabel ∉ declaredInConditions cs →
        allHold (g ++ B) env u cs = true → allHold g env u cs = false →
        ∃ b ∈ B, ∃ t ∈ touchConditions true cs, allHold (g ++ B) (env.bind pinLabel b.id) u t.2 = true
    | [], _, _, _, _, _, _, _, hn => by simp [allHold] at hn
    | c :: cs, env, u, hpin, hu, hus, hds, h, hn => by
      simp only [usedInConditions, declaredInConditions, List.mem_append, not_or] at hus hds
      simp only [allHold, Bool.and_eq_true, Bool.and_eq_false_iff] at h hn
      have hpu : ∀ id, (env.bind pinLabel id) u = env u := by simp [Env.bind, hu]
      by_cases hcg : holds g env u c = true
      · obtain ⟨b, hb, t, htm, hct⟩ := gainedConditions hf cs hpin hu hus.2 hds.2 h.2
          (hn.resolve_left (by simp [hcg]))
        refine ⟨b, hb, (t.1, c :: t.2), ?_, ?_⟩
        · simp only [touchConditions, relax, ite_true, List.mem_append, List.mem_map]
          exact Or.inr ⟨t, htm, rfl⟩
        · rw [allHold, hct, holds_agreeOff c (AgreeOff.pin _ b.id) (hpu b.id) hus.1, h.1]
          rfl
      · obtain ⟨b, hb, t, htm, hct⟩ := flipCondition hf c hpin hu hus.1 hds.1 (by simp [hcg, h.1])
        rw [h.1] at htm
        refine ⟨b, hb, (t.1, t.2 :: cs), ?_, ?_⟩
        · simp only [touchConditions, relax, ite_true, List.mem_append, List.mem_map]
          exact Or.inl ⟨t, htm, rfl⟩
        · rw [allHold, hct, allHold_agreeOff cs (AgreeOff.pin _ b.id) (hpu b.id) hus.2, h.2]
          rfl

  theorem lostConditions (hf : Fresh g B) :
      ∀ (cs : List Condition) {env : Env} {u : Name}, PinOnly B env → u ≠ pinLabel →
        pinLabel ∉ usedInConditions cs → pinLabel ∉ declaredInConditions cs →
        allHold g env u cs = true → allHold (g ++ B) env u cs = false →
        ∃ b ∈ B, ∃ t ∈ touchConditions false cs, allHold (g ++ B) (env.bind pinLabel b.id) u t.2 = true
    | [], _, _, _, _, _, _, _, hn => by simp [allHold] at hn
    | c :: cs, env, u, hpin, hu, hus, hds, h, hn => by
      simp only [usedInConditions, declaredInConditions, List.mem_append, not_or] at hus hds
      simp only [allHold, Bool.and_eq_true, Bool.and_eq_false_iff] at h hn
      have hpu : ∀ id, (env.bind pinLabel id) u = env u := by simp [Env.bind, hu]
      by_cases hcg : holds (g ++ B) env u c = true
      · obtain ⟨b, hb, t, htm, hct⟩ := lostConditions hf cs hpin hu hus.2 hds.2 h.2
          (hn.resolve_left (by simp [hcg]))
        have hc' : holds (g ++ B) (env.bind pinLabel b.id) u c = true := by
          rw [holds_agreeOff c (AgreeOff.pin _ b.id) (hpu b.id) hus.1, hcg]
        refine ⟨b, hb, (t.1, relax false [c] ++ t.2), ?_, ?_⟩
        · simp only [touchConditions, List.mem_append, List.mem_map]
          exact Or.inr ⟨t, htm, rfl⟩
        · cases c with
          | path pc => simp [relax, Condition.isPath, allHold, hc', hct]
          | existential => simpa [relax, Condition.isPath] using hct
      · obtain ⟨b, hb, t, htm, hct⟩ := flipCondition hf c hpin hu hus.1 hds.1 (by simp [hcg, h.1])
        simp only [Bool.not_eq_true] at hcg
        rw [hcg] at htm
        have hcs : allHold g (env.bind pinLabel b.id) u cs = true := by
          rw [allHold_agreeOff cs (AgreeOff.pin _ b.id) (hpu b.id) hus.2, h.2]
        refine ⟨b, hb, (t.1, t.2 :: relax false cs), ?_, ?_⟩
        · simp only [touchConditions, List.mem_append, List.mem_map]
          exact Or.inl ⟨t, htm, rfl⟩
        · simp [allHold, hct, allHold_relax hf (hpin.pin b.id) hu cs hus.2 hcs]

  /-- A condition that answers differently on the two graphs is an existential
  condition, and its matches gained or lost a solution: go into it. -/
  theorem flipCondition (hf : Fresh g B) :
      ∀ (c : Condition) {env : Env} {u : Name}, PinOnly B env → u ≠ pinLabel →
        pinLabel ∉ usedInCondition c → pinLabel ∉ declaredInCondition c →
        holds g env u c ≠ holds (g ++ B) env u c →
        ∃ b ∈ B, ∃ t ∈ touchCondition (holds (g ++ B) env u c) c,
          holds (g ++ B) (env.bind pinLabel b.id) u t.2 = true
    | .path pc, _, _, hpin, hu, hus, _, hne => by
      simp only [usedInCondition, List.mem_singleton] at hus
      exact absurd (holds_path_fresh hf hpin hu pc (Ne.symm hus)).symm hne
    | .existential b ms, env, u, hpin, hu, hus, hds, hne => by
      simp only [usedInCondition, declaredInCondition] at hus hds
      have hv : holds (g ++ B) env u (.existential b ms) =
          (b == !(evalMatches (g ++ B) env ms).isEmpty) := rfl
      simp only [holds] at hne
      rw [hv]
      cases hA : evalMatches (g ++ B) env ms with
      | nil =>
        cases hB : evalMatches g env ms with
        | nil => rw [hA, hB] at hne; exact absurd rfl hne
        | cons e4 _ =>
          obtain ⟨f, hf', t, htm, e, het, -⟩ := lostMatches hf ms (e3 := e4) hpin hus hds
            (by rw [hB]; exact List.mem_cons_self) (by rw [hA]; simp)
          refine ⟨f, hf', (t.1, .existential true t.2), ?_, holds_exists.mpr ⟨e, het⟩⟩
          cases b <;> exact List.mem_map.mpr ⟨t, htm, rfl⟩
      | cons e4 _ =>
        cases hB : evalMatches g env ms with
        | cons => rw [hA, hB] at hne; exact absurd rfl hne
        | nil =>
          obtain ⟨f, hf', t, htm, e, het, -⟩ := gainedMatches hf ms (e3 := e4) hpin hus hds
            (by rw [hA]; exact List.mem_cons_self) (by rw [hB]; simp)
          refine ⟨f, hf', (t.1, .existential true t.2), ?_, holds_exists.mpr ⟨e, het⟩⟩
          cases b <;> exact List.mem_map.mpr ⟨t, htm, rfl⟩
end

/-! ## From results to solutions -/

section Results

variable {s : Specification}

/-- Environments that agree on the givens have the same results. -/
theorem evaluate_agree (hwf : WellFormed s) {G : Graph} {env1 env2 : Env}
    (h : Agree (s.given.map (·.name)) env1 env2) (r : Row) :
    r ∈ s.evaluate G env1 ↔ r ∈ s.evaluate G env2 := by
  simp only [Specification.evaluate, List.mem_map]
  exact exists_projection_iff hwf.inScope h (fun x hx => List.mem_append.mpr (hwf.projected x hx)) r

/-- No given, top-level unknown or projected label is the pin. -/
theorem WellFormed.not_pin (hwf : WellFormed s) {x : Name}
    (hx : x ∈ s.given.map (·.name) ∨ x ∈ names s.matchList) : x ≠ pinLabel := fun h => by
  have : isReserved x = false := by
    rcases hx with hx | hx <;> obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    · exact hwf.givensOrdinary m hm
    · exact wellNamed_ordinary hwf.wellNamed m hm
  simp [h, isReserved_pinLabel] at this

theorem WellFormed.pin_unused (hwf : WellFormed s) : pinLabel ∉ usedInMatches s.matchList := fun h => by
  simpa [isReserved_pinLabel] using usedInMatches_ordinary s.matchList _ hwf.inScope hwf.wellNamed
    (fun x hx => by obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx; exact hwf.givensOrdinary l hl) _ h

theorem WellFormed.pin_undeclared (hwf : WellFormed s) : pinLabel ∉ declaredInMatches s.matchList :=
  fun h => by simpa [isReserved_pinLabel] using declaredInMatches_ordinary s.matchList _ hwf.wellNamed _ h

/-- The new fact's environment agrees with the subscription's on the givens. -/
theorem pinEnv_agree (hwf : WellFormed s) (env : Env) (f : Fact) :
    Agree (s.given.map (·.name)) (pinEnv s env f) env := fun x hx => by
  simp [pinEnv, Env.bind, hwf.not_pin (Or.inl hx), Env.restrictTo, hx]

/-- When no fact of the batch is a given, the givens bind none of them. -/
theorem pinOnly_restrict {env : Env}
    (hgiv : ∀ f ∈ B, ¬ (s.given.any (env ·.name == some f.id)) = true) :
    PinOnly B (env.restrictTo (s.given.map (·.name))) := by
  intro y _ id hid b hb heq
  simp only [Env.restrictTo] at hid
  split at hid
  · rename_i hc
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
    exact hgiv b hb (List.any_eq_true.mpr ⟨l, hl, by simp [hid, heq]⟩)
  · simp at hid

/-- Solutions that agree off the pin project to the same result. -/
theorem WellFormed.project_agreeOff (hwf : WellFormed s) {e1 e2 : Env} (h : AgreeOff e1 e2) :
    s.projection.labels.map e1 = s.projection.labels.map e2 :=
  List.map_congr_left fun x hx => h x (hwf.not_pin (hwf.projected x hx))

end Results

/-- **`inverses_complete`.** For a well-formed specification and a fresh batch
none of whose facts is one of the subscription's givens, every result the batch
adds is a result of one of the inverses for gained results, and every result it
removes is a result of one of the inverses for lost results, given one of the
batch's facts, read on the new graph. -/
theorem inverses_complete (s : Specification) (hwf : WellFormed s) (hf : Fresh g B) (env : Env)
    (hgiv : ∀ f ∈ B, ¬ (s.given.any (env ·.name == some f.id)) = true) (r : Row) :
    (r ∉ s.evaluate g env → r ∈ s.evaluate (g ++ B) env →
      ∃ f ∈ B, ∃ ι ∈ inversesFor true s, r ∈ ι.evaluate (g ++ B) (pinEnv s env f)) ∧
    (r ∈ s.evaluate g env → r ∉ s.evaluate (g ++ B) env →
      ∃ f ∈ B, ∃ ι ∈ inversesFor false s, r ∈ ι.evaluate (g ++ B) (pinEnv s env f)) := by
  -- Forget every label but the givens. The pin is bound once the walk finds it.
  have hsame := fun G => evaluate_agree (G := G) hwf (Env.restrictTo_agree (s.given.map (·.name)) env).symm r
  -- A changed solution is a solution of an inverse, and projects to the same result.
  have hfound : ∀ gained, ∀ t ∈ touchMatches gained s.matchList, ∀ f ∈ B,
      ∀ e3, ∀ e ∈ evalMatches (g ++ B) (pinEnv s env f) t.2, AgreeOff e3 e →
      s.projection.labels.map e3 = r →
      ∃ f ∈ B, ∃ ι ∈ inversesFor gained s, r ∈ ι.evaluate (g ++ B) (pinEnv s env f) :=
    fun _ t ht f hf e3 e he hag hr => ⟨f, hf, _, List.mem_map.mpr ⟨t, ht, rfl⟩,
      List.mem_map.mpr ⟨e, he, hr ▸ (hwf.project_agreeOff hag).symm⟩⟩
  rw [hsame g, hsame (g ++ B)]
  constructor
  · intro h1 h2
    obtain ⟨e3, he3, hr⟩ := List.mem_map.mp h2
    obtain ⟨b, hb, t, ht, e, he, hag⟩ := gainedMatches hf s.matchList (pinOnly_restrict hgiv)
      hwf.pin_unused hwf.pin_undeclared he3 fun h => h1 (List.mem_map.mpr ⟨e3, h, hr⟩)
    exact hfound true t ht b hb e3 e he hag hr
  · intro h1 h2
    obtain ⟨e3, he3, hr⟩ := List.mem_map.mp h1
    obtain ⟨b, hb, t, ht, e, he, hag⟩ := lostMatches hf s.matchList (pinOnly_restrict hgiv)
      hwf.pin_unused hwf.pin_undeclared he3 fun h => h2 (List.mem_map.mpr ⟨e3, h, hr⟩)
    exact hfound false t ht b hb e3 e he hag hr

end JinagaSpec
