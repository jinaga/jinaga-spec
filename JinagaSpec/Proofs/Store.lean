import JinagaSpec.Store
import JinagaSpec.Proofs.Derivation
import JinagaSpec.Proofs.Main
import JinagaSpec.Proofs.Hoist

/-!
# The store's boundary is exact

`store_denies`: a rule whose tail is given the fact under authorization admits
nobody, ever. `store_correct`: a rule whose tail is not means, on the store,
exactly what the whole specification means on the graph that holds the fact.
Together, `tailReadsGiven` is exactly the condition the constructor in
`jinaga.js` must check.

The argument for `store_correct` has two parts. First, every id a well-formed
specification's *own* matches bind, while running the head on `authGraph store
f`, is either the id of a fact in `store`, or (only for the given itself) `f.id`
(`Basic.lean`'s `evalMatches_frame` says the given is never rebound, and the
retyping keeps `f` out of every ordinary type's candidates and out of every
walk that takes at least one step). Second, once every tail given is known to
be in `store`, the tail's own evaluation on `store` and on `authGraph store f`
agree, because a walk that starts inside a closed store never leaves it, and
`f` is never among an ordinary type's candidates either.
-/
namespace JinagaSpec

/-- `id` is the id of a fact in `store`. -/
def InStore (store : Graph) (id : FactId) : Prop := ∃ ff ∈ store, ff.id = id

theorem Graph.mem_of_factOf_eq_some {g : Graph} {id : FactId} {fact : Fact}
    (h : g.factOf id = some fact) : fact ∈ g := by
  unfold Graph.factOf at h
  exact List.mem_of_find?_eq_some h

section AuthGraph

variable {store : Graph} {f : Fact}

/-- `authGraph` agrees with `store` on any id `store` already has a fact for. -/
theorem factOf_authGraph_of_mem {id : FactId} (h : InStore store id) :
    (Graph.authGraph store f).factOf id = store.factOf id := by
  obtain ⟨ff, hff, rfl⟩ := h
  unfold Graph.authGraph Graph.factOf
  rw [List.find?_append]
  cases hs : store.find? (fun x => x.id == ff.id) with
  | none =>
    exfalso
    rw [List.find?_eq_none] at hs
    exact hs ff hff (by simp)
  | some x => simp

/-- Every raw predecessor id a step considers, before its own type filter, is
the id of a fact in a closed store. -/
theorem step_sub_store (hclosed : store.closed) (role : Role) {id : FactId} :
    ∀ p ∈ store.step role id, InStore store p := by
  unfold Graph.step
  cases hfo : store.factOf id with
  | none => simp
  | some fact =>
    have hmem : fact ∈ store := Graph.mem_of_factOf_eq_some hfo
    intro p hp
    have hp' : p ∈ (fact.predecessors.filter fun x => x.1 == role.name).map Prod.snd :=
      (List.mem_filter.mp hp).1
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
    exact hclosed fact hmem q (List.mem_filter.mp hq).1

/-- A step from an id already in a closed store agrees whether it is taken on
`store` or on `authGraph store f`. -/
theorem step_authGraph_eq (hclosed : store.closed) (role : Role) {id : FactId}
    (h : InStore store id) :
    (Graph.authGraph store f).step role id = store.step role id := by
  unfold Graph.step
  rw [factOf_authGraph_of_mem h]
  cases hfo : store.factOf id with
  | none => rfl
  | some fact =>
    have hmem : fact ∈ store := Graph.mem_of_factOf_eq_some hfo
    congr 1
    apply List.filter_congr
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hqmem : q ∈ fact.predecessors := (List.mem_filter.mp hq).1
    rw [factOf_authGraph_of_mem (hclosed fact hmem q hqmem)]

/-- A walk that starts at an id already in a closed store agrees whether it
runs on `store` or on `authGraph store f`, and never leaves the store. -/
theorem walk_authGraph_eq (hclosed : store.closed) :
    ∀ (R : List Role) {id : FactId}, InStore store id →
      Graph.walk (Graph.authGraph store f) id R = Graph.walk store id R ∧
        ∀ a ∈ Graph.walk store id R, InStore store a
  | [], id, h => ⟨rfl, by simpa [Graph.walk] using h⟩
  | role :: rest, id, h => by
    have hstep_eq := step_authGraph_eq (f := f) hclosed role h
    have hstep_sub := step_sub_store hclosed role (id := id)
    refine ⟨?_, ?_⟩
    · show Graph.walk (Graph.authGraph store f) id (role :: rest) = _
      unfold Graph.walk
      rw [hstep_eq]
      apply flatMap_congr
      intro p hp
      exact (walk_authGraph_eq hclosed rest (hstep_sub p hp)).1
    · show ∀ a ∈ Graph.walk store id (role :: rest), InStore store a
      unfold Graph.walk
      intro a ha
      simp only [List.mem_flatMap] at ha
      obtain ⟨p, hp, ha⟩ := ha
      exact (walk_authGraph_eq hclosed rest (hstep_sub p hp)).2 a ha

/-- A step taken from `f` itself, on `authGraph store f`, lands in the store:
`f`'s own predecessors are already there, by hypothesis. -/
theorem step_from_f_sub_store {store : Graph} {f : Fact} (hfnotin : ¬ InStore store f.id)
    (hfpred : ∀ p ∈ f.predecessors, InStore store p.2) (role : Role) :
    ∀ p ∈ (Graph.authGraph store f).step role f.id, InStore store p := by
  have hfactof : (Graph.authGraph store f).factOf f.id = some ({ f with type := batchType }) := by
    unfold Graph.authGraph Graph.factOf
    rw [List.find?_append]
    cases hs : store.find? (fun x => x.id == f.id) with
    | none => simp
    | some x =>
      exact absurd ⟨x, List.mem_of_find?_eq_some hs, by simpa using List.find?_some hs⟩ hfnotin
  unfold Graph.step
  rw [hfactof]
  intro p hp
  have hp' : p ∈ (f.predecessors.filter fun x => x.1 == role.name).map Prod.snd :=
    (List.mem_filter.mp hp).1
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp'
  exact hfpred q (List.mem_filter.mp hq).1

/-- A walk of at least one step, starting at `f` itself on `authGraph store f`,
never reaches outside the store: the first step lands in the store
(`step_from_f_sub_store`), and every step after that stays there
(`walk_authGraph_eq`). This is the retyping's other half: `f` is reachable, but
nothing it reaches is `f` again. -/
theorem walk_from_f_sub_store {store : Graph} {f : Fact} (hclosed : store.closed)
    (hfnotin : ¬ InStore store f.id) (hfpred : ∀ p ∈ f.predecessors, InStore store p.2)
    (role : Role) (rest : List Role) :
    ∀ a ∈ Graph.walk (Graph.authGraph store f) f.id (role :: rest), InStore store a := by
  intro a ha
  unfold Graph.walk at ha
  simp only [List.mem_flatMap] at ha
  obtain ⟨p, hp, ha⟩ := ha
  have hp' := step_from_f_sub_store hfnotin hfpred role p hp
  rw [(walk_authGraph_eq (f := f) hclosed rest hp').1] at ha
  exact (walk_authGraph_eq (f := f) hclosed rest hp').2 a ha

end AuthGraph

/-! ## Ordinary types keep `f` out of a candidate list -/

theorem ordinaryTypesMatches_append {ms1 ms2 : List Match} :
    OrdinaryTypesMatches (ms1 ++ ms2) ↔ OrdinaryTypesMatches ms1 ∧ OrdinaryTypesMatches ms2 := by
  induction ms1 with
  | nil => simp [OrdinaryTypesMatches]
  | cons m ms ih =>
    obtain ⟨u, cs⟩ := m
    simp only [List.cons_append, OrdinaryTypesMatches, ih]
    grind

/-- A fact `authGraph store f` has of a type other than the reserved batch type
is a fact of `store`: the only fact `authGraph` adds is `f` itself, retyped to
the batch type. -/
theorem mem_authGraph_of_ne_batch {store : Graph} {f : Fact} {ff : Fact}
    (h : ff ∈ Graph.authGraph store f) (ht : ff.type ≠ batchType) : ff ∈ store := by
  unfold Graph.authGraph at h
  rcases List.mem_append.mp h with h | h
  · exact h
  · simp only [List.mem_singleton] at h
    subst h
    exact absurd rfl ht

/-- Every id an ordinary-typed list of matches binds, while running on
`authGraph store f`, is the id of a fact in `store`: the candidate for an
ordinary type can never be `f` itself, whatever the rest of the environment
says. -/
theorem ordinary_binds_store {store : Graph} {f : Fact} :
    ∀ (ms : List Match), OrdinaryTypesMatches ms →
      ∀ (env' e2 : Env), e2 ∈ evalMatches (Graph.authGraph store f) env' ms →
        ∀ x ∈ ms.map (·.unknown.name), ∃ id, e2 x = some id ∧ InStore store id
  | [], _, _, _, _, x, hx => absurd hx (by simp)
  | .mk u cs :: rest, hord, env', e2, he2, x, hx => by
    obtain ⟨hu, -, hordRest⟩ : u.type ≠ batchType ∧ OrdinaryTypesConditions cs ∧
        OrdinaryTypesMatches rest := hord
    obtain ⟨fct, hfctmem, hty, -, he2'⟩ := mem_evalMatches_cons.mp he2
    have hfctne : fct.type ≠ batchType := by rw [hty]; exact hu
    have hfctStore : fct ∈ store := mem_authGraph_of_ne_batch hfctmem hfctne
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · by_cases hshadow : u.name ∈ rest.map (·.unknown.name)
      · exact ordinary_binds_store rest hordRest _ e2 he2' u.name hshadow
      · refine ⟨fct.id, ?_, fct, hfctStore, rfl⟩
        show e2 u.name = some fct.id
        rw [evalMatches_frame he2' u.name hshadow]
        simp [Env.bind]
    · exact ordinary_binds_store rest hordRest _ e2 he2' x hx

/-! ## The tail's own evaluation agrees on `store` and on `authGraph store f` -/

/-- Every label `env` binds is the id of a fact in a closed `store`. Threaded
through `evalMatches`, this is exactly what lets the tail run on `store` alone. -/
def EnvClosed (store : Graph) (env : Env) : Prop := ∀ x id, env x = some id → InStore store id

theorem EnvClosed.bind {store : Graph} {env : Env} (h : EnvClosed store env) {name : Name}
    {id : FactId} (hid : InStore store id) : EnvClosed store (env.bind name id) := by
  intro x xid hx
  simp only [Env.bind] at hx
  split at hx
  · exact (Option.some.inj hx) ▸ hid
  · exact h x xid hx

section EvalAgree

variable {store : Graph} {f : Fact}

mutual
  theorem evalMatches_authGraph_agree (hclosed : store.closed) (hfnotin : ¬ InStore store f.id) :
      ∀ (ms : List Match), OrdinaryTypesMatches ms → ∀ (env' : Env), EnvClosed store env' →
        evalMatches (Graph.authGraph store f) env' ms = evalMatches store env' ms
    | [], _, _, _ => by simp [evalMatches]
    | .mk u cs :: rest, hord, env', hclosedEnv => by
      obtain ⟨hu, hordCs, hordRest⟩ : u.type ≠ batchType ∧ OrdinaryTypesConditions cs ∧
          OrdinaryTypesMatches rest := hord
      have hfilter : (Graph.authGraph store f).filter (fun ff => ff.type == u.type) =
          store.filter (fun ff => ff.type == u.type) := by
        unfold Graph.authGraph
        rw [List.filter_append]
        have hnil : ([({ f with type := batchType } : Fact)]).filter
            (fun ff => ff.type == u.type) = [] := by
          have hne : (({ f with type := batchType } : Fact).type == u.type) = false := by
            simp only [beq_eq_false_iff_ne]
            exact fun h => hu h.symm
          simp [List.filter, hne]
        simp [hnil]
      have hbody : ∀ fct ∈ store.filter (fun ff => ff.type == u.type),
          (let env'' := env'.bind u.name fct.id
           if allHold (Graph.authGraph store f) env'' u.name cs = true
           then evalMatches (Graph.authGraph store f) env'' rest else []) =
          (let env'' := env'.bind u.name fct.id
           if allHold store env'' u.name cs = true then evalMatches store env'' rest else []) := by
        intro fct hfct
        have hfctStore : InStore store fct.id := ⟨fct, (List.mem_filter.mp hfct).1, rfl⟩
        have hclosedEnv' := hclosedEnv.bind (name := u.name) hfctStore
        have hcAgree : allHold (Graph.authGraph store f) (env'.bind u.name fct.id) u.name cs =
            allHold store (env'.bind u.name fct.id) u.name cs :=
          allHold_authGraph_agree hclosed hfnotin cs hordCs u.name (env'.bind u.name fct.id) hclosedEnv'
        simp only [hcAgree]
        by_cases hh : allHold store (env'.bind u.name fct.id) u.name cs = true
        · simp only [hh, ite_true]
          exact evalMatches_authGraph_agree hclosed hfnotin rest hordRest
            (env'.bind u.name fct.id) hclosedEnv'
        · have hh' : allHold store (env'.bind u.name fct.id) u.name cs = false := by
            simpa using hh
          simp [hh']
      calc evalMatches (Graph.authGraph store f) env' (.mk u cs :: rest)
          = ((Graph.authGraph store f).filter (fun ff => ff.type == u.type)).flatMap
              (fun fct => let env'' := env'.bind u.name fct.id
                if allHold (Graph.authGraph store f) env'' u.name cs = true
                then evalMatches (Graph.authGraph store f) env'' rest else []) := rfl
        _ = (store.filter (fun ff => ff.type == u.type)).flatMap
              (fun fct => let env'' := env'.bind u.name fct.id
                if allHold (Graph.authGraph store f) env'' u.name cs = true
                then evalMatches (Graph.authGraph store f) env'' rest else []) := by rw [hfilter]
        _ = (store.filter (fun ff => ff.type == u.type)).flatMap
              (fun fct => let env'' := env'.bind u.name fct.id
                if allHold store env'' u.name cs = true then evalMatches store env'' rest else []) :=
            flatMap_congr hbody
        _ = evalMatches store env' (.mk u cs :: rest) := rfl

  theorem allHold_authGraph_agree (hclosed : store.closed) (hfnotin : ¬ InStore store f.id) :
      ∀ (cs : List Condition), OrdinaryTypesConditions cs → ∀ (u : Name) (env' : Env),
        EnvClosed store env' →
        allHold (Graph.authGraph store f) env' u cs = allHold store env' u cs
    | [], _, _, _, _ => by simp [allHold]
    | c :: cs, hord, u, env', hclosedEnv => by
      obtain ⟨hc, hcs⟩ : OrdinaryTypesCondition c ∧ OrdinaryTypesConditions cs := hord
      have h1 := holds_authGraph_agree hclosed hfnotin c hc u env' hclosedEnv
      have h2 := allHold_authGraph_agree hclosed hfnotin cs hcs u env' hclosedEnv
      calc allHold (Graph.authGraph store f) env' u (c :: cs)
          = (holds (Graph.authGraph store f) env' u c && allHold (Graph.authGraph store f) env' u cs) := rfl
        _ = (holds store env' u c && allHold store env' u cs) := by rw [h1, h2]
        _ = allHold store env' u (c :: cs) := rfl

  theorem holds_authGraph_agree (hclosed : store.closed) (hfnotin : ¬ InStore store f.id) :
      ∀ (c : Condition), OrdinaryTypesCondition c → ∀ (u : Name) (env' : Env), EnvClosed store env' →
        holds (Graph.authGraph store f) env' u c = holds store env' u c
    | .path pc, _, u, env', hclosedEnv => by
      cases hU : env' u with
      | none => simp [holds, PathCondition.holds, hU]
      | some uid =>
        cases hR : env' pc.labelRight with
        | none => simp [holds, PathCondition.holds, hU, hR]
        | some rid =>
          have hUin : InStore store uid := hclosedEnv u uid hU
          have hRin : InStore store rid := hclosedEnv pc.labelRight rid hR
          have e1 := (walk_authGraph_eq (f := f) hclosed pc.rolesLeft hUin).1
          have e2 := (walk_authGraph_eq (f := f) hclosed pc.rolesRight hRin).1
          simp [holds, PathCondition.holds, hU, hR, e1, e2]
    | .existential e ms, hord, u, env', hclosedEnv => by
      have hme : evalMatches (Graph.authGraph store f) env' ms = evalMatches store env' ms :=
        evalMatches_authGraph_agree hclosed hfnotin ms hord env' hclosedEnv
      simp [holds, hme]
end

end EvalAgree

/-! ## Locating the given -/

/-- No given a well-formed specification declares is a label its own head
splits into. -/
theorem given_notin_headMatchList {s : Specification} (hwf : WellFormed s) {g0 : Label}
    (hg0 : g0 ∈ s.given) :
    g0.name ∉ (splitBeforeFirstSuccessor s).head.matchList.map (·.unknown.name) := by
  have hg0given : g0.name ∈ s.given.map (·.name) := List.mem_map_of_mem hg0
  unfold splitBeforeFirstSuccessor
  generalize hspan : s.matchList.span matchIsDeterministic = sp
  obtain ⟨before, rest⟩ := sp
  have hs : s.matchList = before ++ rest := by
    have h := span_loop_append matchIsDeterministic s.matchList []
    unfold List.span at hspan
    rw [hspan] at h
    simpa using h.symm
  have hbefore_wf : WellNamedMatches (s.given.map (·.name)) before := by
    have h := hwf.wellNamed
    rw [hs, wellNamedMatches_append] at h
    exact h.1
  have hg0notin_before : g0.name ∉ before.map (·.unknown.name) := by
    intro hmem
    exact (wellNamed_names_notin hbefore_wf g0.name hmem) hg0given
  cases rest with
  | nil =>
    show g0.name ∉ s.matchList.map (·.unknown.name)
    rw [hs]
    simpa using hg0notin_before
  | cons pivot after =>
    show g0.name ∉ (splitAt s before pivot after).head.matchList.map (·.unknown.name)
    unfold splitAt
    rcases hsp : splitPaths 0 (pathsOf pivot.conditions) with ⟨sm, tps⟩
    simp only [List.map_append, List.mem_append]
    rintro (h | h)
    · exact hg0notin_before h
    · obtain ⟨m, hm, hmn⟩ := List.mem_map.mp h
      have hres : isReserved m.unknown.name = true := (splitPaths_names 0 (pathsOf pivot.conditions)).1 m (hsp ▸ hm)
      have hord : isReserved g0.name = false := hwf.givensOrdinary g0 hg0
      rw [hmn] at hres
      rw [hres] at hord
      exact absurd hord (by simp)

/-! ## The head's split matches also bind into the store -/

/-- Either `f` itself, or the id of a fact in the store: what a label in scope
at the pivot is safely bound to. Only the given itself can be `f`; every other
label already in scope is `InStore`. -/
def SafeId (store : Graph) (f : Fact) (id : FactId) : Prop := id = f.id ∨ InStore store id

/-- Every id a split match binds, while its head runs on `authGraph store f`,
is the id of a fact in the store: its own path condition needs its candidate's
id to be in the walk from whatever the pivot's original path condition joined,
and that walk (of at least one step, since the split only makes a match when
the walk is nonempty) never reaches outside the store, whether it starts at a
label already there or at `f` itself. -/
theorem splitPaths_head_binds_store {store : Graph} {f : Fact} (hclosed : store.closed)
    (hfnotin : ¬ InStore store f.id) (hfpred : ∀ p ∈ f.predecessors, InStore store p.2) :
    ∀ (i : Nat) (ps : List PathCondition) (eB : Env),
      (∀ c ∈ ps, isReserved c.labelRight = false) →
      (∀ c ∈ ps, ∃ id, eB c.labelRight = some id ∧ SafeId store f id) →
      ∀ (e2 : Env), e2 ∈ evalMatches (Graph.authGraph store f) eB (splitPaths i ps).1 →
        ∀ x ∈ (splitPaths i ps).1.map (·.unknown.name), ∃ id, e2 x = some id ∧ InStore store id
  | _, [], _, _, _, _, _, x, hx => by simp [splitPaths] at hx
  | i, c :: cs, eB, hres, hsafe, e2, he2, x, hx => by
    have hres' : ∀ c' ∈ cs, isReserved c'.labelRight = false :=
      fun c' h => hres c' (List.mem_cons_of_mem _ h)
    have hsafe' : ∀ c' ∈ cs, ∃ id, eB c'.labelRight = some id ∧ SafeId store f id :=
      fun c' h => hsafe c' (List.mem_cons_of_mem _ h)
    cases hl : c.rolesRight.getLast? with
    | none =>
      simp only [splitPaths, hl] at hx he2
      exact splitPaths_head_binds_store hclosed hfnotin hfpred (i + 1) cs eB hres' hsafe' e2 he2 x hx
    | some last =>
      simp only [splitPaths, hl, List.map_cons, List.mem_cons] at hx
      simp only [splitPaths, hl] at he2
      obtain ⟨fct, -, -, hc, he2'⟩ := mem_evalMatches_cons.mp he2
      obtain ⟨cid, hceB, hsafeC⟩ := hsafe c List.mem_cons_self
      have hcRes : isReserved c.labelRight = false := hres c List.mem_cons_self
      have hnlr : c.labelRight ≠ splitLabel i := by
        intro h
        rw [h, isReserved_splitLabel] at hcRes
        exact absurd hcRes (by simp)
      have hbindC : (eB.bind (splitLabel i) fct.id) c.labelRight = some cid := by
        simp [Env.bind, hnlr, hceB]
      have hbindU : (eB.bind (splitLabel i) fct.id) (splitLabel i) = some fct.id := by
        simp [Env.bind]
      have hcondTrue : ((Graph.authGraph store f).walk fct.id []).any
          (fun a => ((Graph.authGraph store f).walk cid c.rolesRight).contains a) = true := by
        have hc' := hc
        simp only [allHold, holds, PathCondition.holds, hbindU, hbindC, Bool.and_true] at hc'
        exact hc'
      have hmemwalk : fct.id ∈ (Graph.authGraph store f).walk cid c.rolesRight := by
        rw [List.any_eq_true] at hcondTrue
        obtain ⟨a, ha, hcontains⟩ := hcondTrue
        simp only [Graph.walk, List.mem_singleton] at ha
        subst ha
        simpa using hcontains
      have hne : c.rolesRight ≠ [] := by
        intro h; rw [h] at hl; simp at hl
      obtain ⟨role0, rest0, hrr⟩ := List.exists_cons_of_ne_nil hne
      have hfctInStore : InStore store fct.id := by
        rw [hrr] at hmemwalk
        rcases hsafeC with hfid | hstoreid
        · subst hfid
          exact walk_from_f_sub_store hclosed hfnotin hfpred role0 rest0 fct.id hmemwalk
        · rw [(walk_authGraph_eq (f := f) hclosed (role0 :: rest0) hstoreid).1] at hmemwalk
          exact (walk_authGraph_eq (f := f) hclosed (role0 :: rest0) hstoreid).2 fct.id hmemwalk
      rcases hx with rfl | hx
      · have hfresh : splitLabel i ∉ (splitPaths (i + 1) cs).1.map (·.unknown.name) := by
          intro hmem
          obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hmem
          obtain ⟨j, hj, hn⟩ := splitPaths_head_index cs (i + 1) m hm
          rw [hn] at hmn
          exact absurd (splitLabel_injective hmn) (by omega)
        refine ⟨fct.id, ?_, hfctInStore⟩
        show e2 (splitLabel i) = some fct.id
        rw [evalMatches_frame he2' (splitLabel i) hfresh]
        exact hbindU
      · have hsafeC' : ∀ c' ∈ cs, ∃ id, (eB.bind (splitLabel i) fct.id) c'.labelRight = some id ∧
            SafeId store f id := by
          intro c' hc'
          obtain ⟨id, heq, hor⟩ := hsafe' c' hc'
          refine ⟨id, ?_, hor⟩
          have hne' : c'.labelRight ≠ splitLabel i := by
            intro h
            have hres2 := hres' c' hc'
            rw [h, isReserved_splitLabel] at hres2
            exact absurd hres2 (by simp)
          simp [Env.bind, hne', heq]
        exact splitPaths_head_binds_store hclosed hfnotin hfpred (i + 1) cs
          (eB.bind (splitLabel i) fct.id) hres' hsafeC' e2 he2' x hx

/-! ## Every label in scope at the pivot is safely bound -/

/-- Every label in scope at the pivot is bound, by the time the head reaches
it, to a safe id: the given itself is `f`, and everything else is an ordinary
match's own candidate, which `ordinary_binds_store` puts in the store. -/
theorem safeAt_before {s : Specification} {g0 : Label} (hg : s.given = [g0])
    {before : List Match} {store : Graph} {f : Fact} {env eB : Env}
    (hordBefore : OrdinaryTypesMatches before) (henv : env g0.name = some f.id)
    (hg0notin : g0.name ∉ before.map (·.unknown.name))
    (heB : eB ∈ evalMatches (Graph.authGraph store f) env before) :
    ∀ x ∈ scopeAt s before, ∃ id, eB x = some id ∧ SafeId store f id := by
  intro x hx
  unfold scopeAt at hx
  rw [hg] at hx
  rw [mem_scopeAfter] at hx
  rcases hx with hx | hx
  · obtain ⟨id, heq, hInStore⟩ := ordinary_binds_store before hordBefore env eB heB x hx
    exact ⟨id, heq, Or.inr hInStore⟩
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
    subst hx
    refine ⟨f.id, ?_, Or.inl rfl⟩
    rw [evalMatches_frame heB g0.name hg0notin]
    exact henv

/-! ## Ordinary types survive the tail's own rewriting -/

theorem ordinaryTypesConditions_append {cs1 cs2 : List Condition} :
    OrdinaryTypesConditions (cs1 ++ cs2) ↔ OrdinaryTypesConditions cs1 ∧ OrdinaryTypesConditions cs2 := by
  induction cs1 with
  | nil => simp [OrdinaryTypesConditions]
  | cons c cs ih => simp only [List.cons_append, OrdinaryTypesConditions, ih]; grind

theorem ordinaryTypesConditions_existentialsOf {cs : List Condition}
    (h : OrdinaryTypesConditions cs) : OrdinaryTypesConditions (existentialsOf cs) := by
  induction cs with
  | nil => simpa [existentialsOf] using h
  | cons c cs ih =>
    obtain ⟨hc, hcs⟩ : OrdinaryTypesCondition c ∧ OrdinaryTypesConditions cs := h
    cases c with
    | path p => simpa [existentialsOf_cons_path] using ih hcs
    | existential e ms => rw [existentialsOf_cons_ex]; exact ⟨hc, ih hcs⟩

theorem ordinaryTypesConditions_map_path {ps : List PathCondition} :
    OrdinaryTypesConditions (ps.map .path) := by
  induction ps with
  | nil => simp [OrdinaryTypesConditions]
  | cons p ps ih => simp [OrdinaryTypesConditions, OrdinaryTypesCondition, ih]

/-- Rewriting the pivot's path conditions for the tail does not touch any
unknown's type: only the head's split matches, whose own binding never needs
an ordinary type (`splitPaths_head_binds_store`), are new. -/
theorem ordinaryTypesMatches_tailMatchesAt {pivot : Match} {tps : List PathCondition}
    {after : List Match} (h : OrdinaryTypesMatches (pivot :: after)) :
    OrdinaryTypesMatches (tailMatchesAt pivot tps after) := by
  obtain ⟨u, cs⟩ := pivot
  obtain ⟨hu, hcs, hafter⟩ : u.type ≠ batchType ∧ OrdinaryTypesConditions cs ∧
      OrdinaryTypesMatches after := h
  refine ⟨hu, ?_, hafter⟩
  show OrdinaryTypesConditions (tps.map .path ++ existentialsOf cs)
  rw [ordinaryTypesConditions_append]
  exact ⟨ordinaryTypesConditions_map_path, ordinaryTypesConditions_existentialsOf hcs⟩

/-! ## Shared by both algorithms' boundary theorems

`store_denies`/`store_denies_hoist` and `store_correct`/`store_correct_hoist`
each differ from their sibling only in which algorithm (`splitBeforeFirstSuccessor`
or `hoist`) produces the head and tail; the argument once the pieces it produces
are in hand is identical. `store_denies_of` and `tailGiven_pointwise` state that
shared argument once, each parameterized over exactly what the two algorithms
produce differently. -/

/-- A rule whose tail is given the fact under authorization admits nobody,
given only that `split`'s head never rebinds it: every head tuple then seeds
the tail with `f.id`, which the store does not have. -/
theorem store_denies_of {s : Specification} {g0 : Label} {store : Graph} {f : Fact} {env : Env}
    (split : Specification → Split)
    (hgnotin : g0.name ∉ (split s).head.matchList.map (·.unknown.name))
    (hfnotin : ¬ InStore store f.id) (henv : env g0.name = some f.id)
    (h : tailReadsGiven (split s) g0.name = true) :
    (split s).evaluateStore store f env = [] := by
  have hFactNone : store.factOf f.id = none := by
    cases hfo : store.factOf f.id with
    | none => rfl
    | some fact =>
      have hmem : fact ∈ store := Graph.mem_of_factOf_eq_some hfo
      have heq : fact.id = f.id := by
        have h1 := hfo
        unfold Graph.factOf at h1
        simpa using List.find?_some h1
      exact absurd ⟨fact, hmem, heq⟩ hfnotin
  unfold tailReadsGiven at h
  cases htail : (split s).tail with
  | none => rw [htail] at h; simp at h
  | some tail =>
    rw [htail] at h
    simp only [List.any_eq_true, beq_iff_eq] at h
    obtain ⟨l, hl, hln⟩ := h
    unfold Split.evaluateStore
    rw [htail]
    apply List.flatMap_eq_nil_iff.mpr
    intro tuple htuple
    have htg : tuple g0.name = env g0.name := evalMatches_frame htuple g0.name hgnotin
    have hcontains : (tail.given.map (·.name)).contains l.name = true := by
      rw [List.contains_iff_mem]
      exact List.mem_map_of_mem hl
    have hlval : (tuple.restrictTo (tail.given.map (·.name))) l.name = some f.id := by
      simp only [Env.restrictTo, hcontains, ite_true]
      rw [hln, htg]
      exact henv
    show (if (tail.given.all fun l => match (tuple.restrictTo (tail.given.map (·.name))) l.name with
            | some id => store.hasFact id
            | none => false) = true
          then tail.evaluate store (tuple.restrictTo (tail.given.map (·.name)))
          else []) = []
    split
    · rename_i hcondTrue
      exfalso
      rw [List.all_eq_true] at hcondTrue
      have hbad := hcondTrue l hl
      simp [hlval, Graph.hasFact, hFactNone] at hbad
    · rfl

/-- Once every tail given a head hands the tail is known to be in the store,
the guard `evaluateStore` checks on it always passes, and the tail's own
evaluation then agrees on `store` and on `authGraph store f`
(`evalMatches_authGraph_agree`). -/
theorem tailGiven_pointwise {store : Graph} {f : Fact} {env : Env}
    (hclosed : store.closed) (hfnotin : ¬ InStore store f.id)
    (headMatches : List Match) (tailGiven : List Label) (tailMatches : List Match) (proj : Projection)
    (hordTail : OrdinaryTypesMatches tailMatches)
    (hheadStore : ∀ tuple ∈ evalMatches (Graph.authGraph store f) env headMatches,
      ∀ l ∈ tailGiven, ∃ id, tuple l.name = some id ∧ InStore store id) :
    ∀ tuple ∈ evalMatches (Graph.authGraph store f) env headMatches,
      (if tailGiven.all (fun l => match (tuple.restrictTo (tailGiven.map (·.name))) l.name with
            | some id => store.hasFact id
            | none => false) = true
        then Specification.evaluate (Specification.mk tailGiven tailMatches proj) store
              (tuple.restrictTo (tailGiven.map (·.name)))
        else [])
      = Specification.evaluate (Specification.mk tailGiven tailMatches proj)
          (Graph.authGraph store f) (tuple.restrictTo (tailGiven.map (·.name))) := by
  intro tuple htuple
  have hallTrue : tailGiven.all (fun l => match (tuple.restrictTo (tailGiven.map (·.name))) l.name with
      | some id => store.hasFact id
      | none => false) = true := by
    rw [List.all_eq_true]
    intro l hl
    obtain ⟨id, heq, hInStore⟩ := hheadStore tuple htuple l hl
    have hcontains : (tailGiven.map (·.name)).contains l.name = true := by
      rw [List.contains_iff_mem]
      exact List.mem_map_of_mem hl
    have hrestr : (tuple.restrictTo (tailGiven.map (·.name))) l.name = some id := by
      simp only [Env.restrictTo, hcontains, ite_true]
      exact heq
    rw [hrestr]
    obtain ⟨ff, hff, hffeq⟩ := hInStore
    show store.hasFact id = true
    unfold Graph.hasFact
    exact List.find?_isSome.mpr ⟨ff, hff, by simp [hffeq]⟩
  simp only [hallTrue, ite_true]
  have hclosedEnv : EnvClosed store (tuple.restrictTo (tailGiven.map (·.name))) := by
    intro x xid hx
    have hxmemBool : (tailGiven.map (·.name)).contains x = true := by
      cases hc : (tailGiven.map (·.name)).contains x with
      | true => rfl
      | false =>
        exfalso
        have hxnone : (tuple.restrictTo (tailGiven.map (·.name))) x = none := by
          unfold Env.restrictTo
          rw [hc]
          simp
        rw [hxnone] at hx
        simp at hx
    have hxmem : x ∈ tailGiven.map (·.name) := List.contains_iff_mem.mp hxmemBool
    obtain ⟨l, hl, hln⟩ := List.mem_map.mp hxmem
    obtain ⟨id, heq, hInStore⟩ := hheadStore tuple htuple l hl
    have hxval : (tuple.restrictTo (tailGiven.map (·.name))) x = some id := by
      simp only [Env.restrictTo, hxmemBool, ite_true]
      rw [← hln]
      exact heq
    rw [hxval] at hx
    exact (Option.some.inj hx) ▸ hInStore
  unfold Specification.evaluate
  congr 1
  exact (evalMatches_authGraph_agree hclosed hfnotin tailMatches hordTail _ hclosedEnv).symm

/-! ## The boundary theorems -/

section Boundary

variable {s : Specification} {g0 : Label} {store : Graph} {f : Fact} {env : Env}

/-- A rule whose tail is given the fact under authorization admits nobody: the
head never rebinds the given (it is not one of its own declared labels), so
every head tuple seeds the tail with `f.id`, which the store does not have. -/
theorem store_denies (hwf : WellFormed s) (hg : s.given = [g0]) (_hord : OrdinaryTypes s)
    (_hclosed : store.closed) (hfnotin : ¬ InStore store f.id)
    (_hfpred : ∀ p ∈ f.predecessors, InStore store p.2) (henv : env g0.name = some f.id)
    (h : tailReadsGiven (splitBeforeFirstSuccessor s) g0.name = true) :
    (splitBeforeFirstSuccessor s).evaluateStore store f env = [] :=
  store_denies_of splitBeforeFirstSuccessor
    (given_notin_headMatchList hwf (by rw [hg]; simp)) hfnotin henv h

/-- A rule whose tail is not given the fact under authorization means, on the
store, exactly what the whole specification means on `authGraph store f`: every
tail given the head hands it is already in the store (`ordinary_binds_store` for
labels the "before" matches bind, `splitPaths_head_binds_store` for the head's
own split labels), so the guard `evaluateStore` checks always passes, and once
it does, the tail's own evaluation agrees on `store` and on `authGraph store f`
(`evalMatches_authGraph_agree`). -/
theorem store_correct (hwf : WellFormed s) (hg : s.given = [g0]) (hord : OrdinaryTypes s)
    (hclosed : store.closed) (hfnotin : ¬ InStore store f.id)
    (hfpred : ∀ p ∈ f.predecessors, InStore store p.2) (henv : env g0.name = some f.id)
    (h : tailReadsGiven (splitBeforeFirstSuccessor s) g0.name = false) (r : List (Option FactId)) :
    r ∈ (splitBeforeFirstSuccessor s).evaluateStore store f env ↔
      r ∈ s.evaluate (Graph.authGraph store f) env := by
  rw [← split_correct s hwf (Graph.authGraph store f) env r]
  rcases hspan : s.matchList.span matchIsDeterministic with ⟨before, rest⟩
  cases rest with
  | nil =>
    have hsplit_eq : splitBeforeFirstSuccessor s = { head := s, tail := none } := by
      rw [splitBeforeFirstSuccessor, hspan]
    rw [hsplit_eq]
    simp [Split.evaluateStore, Split.evaluate]
  | cons pivot after =>
    have hs : s.matchList = before ++ pivot :: after := by
      have h1 := span_loop_append matchIsDeterministic s.matchList []
      unfold List.span at hspan
      rw [hspan] at h1
      simpa using h1.symm
    have hsplit_eq : splitBeforeFirstSuccessor s = splitAt s before pivot after := by
      rw [splitBeforeFirstSuccessor, hspan]
    rcases hsp : splitPaths 0 (pathsOf pivot.conditions) with ⟨sm, tps⟩
    let tailMatches := tailMatchesAt pivot tps after
    let tailGiven := tailGivenAt s (before ++ sm) tailMatches
    have htail_eq : (splitAt s before pivot after).tail =
        some { given := tailGiven, matchList := tailMatches, projection := s.projection } := by
      unfold splitAt
      simp only [hsp]
      rfl
    have hhead_eq : (splitAt s before pivot after).head =
        { given := s.given, matchList := before ++ sm,
          projection := .composite (tailGiven.map fun l => { name := l.name, label := l.name }) } := by
      unfold splitAt
      simp only [hsp]
      rfl
    rw [hsplit_eq] at h ⊢
    unfold tailReadsGiven at h
    rw [htail_eq] at h
    rw [List.any_eq_false] at h
    have hgn : ∀ l ∈ tailGiven, l.name ≠ g0.name := by
      intro l hl heq
      exact h l hl (by simp [heq])
    -- `before`'s own unknowns, and every split label, are ordinary or bind into
    -- the store, and the given itself is `f`.
    have hordBoth : OrdinaryTypesMatches before ∧ OrdinaryTypesMatches (pivot :: after) := by
      have h1 : OrdinaryTypesMatches s.matchList := hord
      rw [hs, ordinaryTypesMatches_append] at h1
      exact h1
    have hg0notin_before : g0.name ∉ before.map (·.unknown.name) := by
      have h1 := given_notin_headMatchList (s := s) hwf (g0 := g0) (by rw [hg]; simp)
      rw [hsplit_eq, hhead_eq] at h1
      simp only [List.map_append, List.mem_append] at h1
      intro hmem
      exact h1 (Or.inl hmem)
    have hpivotScoped := pivot_scoped hwf hs
    have hpivotOrd := pivot_labels_ordinary hwf hs
    -- Every id the head binds for a label the tail is given is in the store.
    have hheadStore : ∀ tuple ∈ evalMatches (Graph.authGraph store f) env (before ++ sm),
        ∀ l ∈ tailGiven, ∃ id, tuple l.name = some id ∧ InStore store id := by
      intro tuple htuple l hl
      have hlmem : l = g0 ∨ l ∈ (before ++ sm).map (·.unknown) := by
        have h1 := hl
        change l ∈ tailGivenAt s (before ++ sm) tailMatches at h1
        unfold tailGivenAt at h1
        simp only [List.mem_filter, List.mem_append, hg, List.mem_singleton] at h1
        exact h1.1
      have hlname : l.name ∈ before.map (·.unknown.name) ++ sm.map (·.unknown.name) := by
        rcases hlmem with rfl | hlmem
        · exact absurd rfl (hgn l hl)
        · simp only [List.map_append, List.mem_append] at hlmem ⊢
          rcases hlmem with hlmem | hlmem
          · obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hlmem
            exact Or.inl (hmn ▸ List.mem_map_of_mem hm)
          · obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hlmem
            exact Or.inr (hmn ▸ List.mem_map_of_mem hm)
      obtain ⟨eB, heB, htupleSm⟩ := mem_evalMatches_append.mp htuple
      have hsafe : ∀ c ∈ pathsOf pivot.conditions, ∃ id, eB c.labelRight = some id ∧ SafeId store f id :=
        fun c hc => safeAt_before hg hordBoth.1 henv hg0notin_before heB c.labelRight (hpivotScoped.1 c hc)
      have hres : ∀ c ∈ pathsOf pivot.conditions, isReserved c.labelRight = false :=
        fun c hc => hpivotOrd c.labelRight (List.mem_cons_of_mem _ (List.mem_map_of_mem hc))
      rw [List.mem_append] at hlname
      rcases hlname with hlname | hlname
      · have hlord : isReserved l.name = false := by
          obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hlname
          exact hmn ▸ wellNamed_ordinary (by
            have h1 := hwf.wellNamed
            rw [hs, wellNamedMatches_append] at h1
            exact h1.1) m hm
        have hsmres : l.name ∉ sm.map (·.unknown.name) := by
          intro hmem
          obtain ⟨m, hm, hmn⟩ := List.mem_map.mp hmem
          have := (splitPaths_names 0 (pathsOf pivot.conditions)).1 m (hsp ▸ hm)
          rw [hmn] at this
          rw [hlord] at this
          exact absurd this (by simp)
        have hframe : tuple l.name = eB l.name := evalMatches_frame htupleSm l.name hsmres
        obtain ⟨id, heq, hInStore⟩ := ordinary_binds_store before hordBoth.1 env eB heB l.name hlname
        exact ⟨id, hframe ▸ heq, hInStore⟩
      · exact splitPaths_head_binds_store hclosed hfnotin hfpred 0 (pathsOf pivot.conditions) eB
          hres hsafe tuple (hsp ▸ htupleSm) l.name (hsp ▸ hlname)
    simp only [Split.evaluateStore, Split.evaluate, htail_eq, hhead_eq]
    exact Iff.of_eq (congrArg (r ∈ ·) (flatMap_congr
      (tailGiven_pointwise hclosed hfnotin (before ++ sm) tailGiven tailMatches s.projection
        (ordinaryTypesMatches_tailMatchesAt hordBoth.2) hheadStore)))

end Boundary

/-! ## The boundary theorems, for `hoist`

The same two theorems, for `hoist` in place of `splitBeforeFirstSuccessor`.
Hoisting only ever rewrites conditions, never a match's own unknown or its
type, so `OrdinaryTypes` survives it outright (`hoistMatches_ordinaryTypes`);
and every id the (possibly much deeper) head binds is still in the store, by
the same argument as `splitPaths_head_binds_store`, generalized to
`hoistMatches`/`hoistConditions`/`hoistCondition`'s own recursion
(`hoistMatches_head_binds_store`). -/

mutual
  /-- Hoisting rewrites only conditions: a match's own unknown, and its type,
  survive at any depth. -/
  theorem hoistMatches_ordinaryTypes (scope : List Name) (i : Nat) (pos : Bool) :
      ∀ (ms : List Match), OrdinaryTypesMatches ms → OrdinaryTypesMatches (hoistMatches scope i pos ms).2.2
    | [], _ => by simp [hoistMatches, OrdinaryTypesMatches]
    | .mk u cs :: rest, h => by
      obtain ⟨hu, hcs, hrest⟩ : u.type ≠ batchType ∧ OrdinaryTypesConditions cs ∧
          OrdinaryTypesMatches rest := h
      rcases hgenC : hoistConditions scope i pos cs with ⟨i1, headCs, cs'⟩
      rcases hgenM : hoistMatches scope i1 pos rest with ⟨i2, headRest, rest'⟩
      have heq : (hoistMatches scope i pos (.mk u cs :: rest)).2.2 = .mk u cs' :: rest' := by
        show (hoistMatches scope i pos (.mk u cs :: rest)).2.2 = _
        unfold hoistMatches; simp [hgenC, hgenM]
      rw [heq]
      refine ⟨hu, ?_, ?_⟩
      · have h1 := hoistConditions_ordinaryTypes scope i pos cs hcs
        rw [hgenC] at h1; simpa using h1
      · have h2 := hoistMatches_ordinaryTypes scope i1 pos rest hrest
        rw [hgenM] at h2; simpa using h2

  theorem hoistConditions_ordinaryTypes (scope : List Name) (i : Nat) (pos : Bool) :
      ∀ (cs : List Condition), OrdinaryTypesConditions cs →
        OrdinaryTypesConditions (hoistConditions scope i pos cs).2.2
    | [], _ => by simp [hoistConditions, OrdinaryTypesConditions]
    | c :: cs, h => by
      obtain ⟨hc, hcs⟩ : OrdinaryTypesCondition c ∧ OrdinaryTypesConditions cs := h
      rcases hgenc : hoistCondition scope i pos c with ⟨i1, headC, c'⟩
      rcases hgencs : hoistConditions scope i1 pos cs with ⟨i2, headCs, cs'⟩
      have heq : (hoistConditions scope i pos (c :: cs)).2.2 = c' :: cs' := by
        show (hoistConditions scope i pos (c :: cs)).2.2 = _
        unfold hoistConditions; simp [hgenc, hgencs]
      rw [heq]
      refine ⟨?_, ?_⟩
      · have h1 := hoistCondition_ordinaryTypes scope i pos c hc
        rw [hgenc] at h1; simpa using h1
      · have h2 := hoistConditions_ordinaryTypes scope i1 pos cs hcs
        rw [hgencs] at h2; simpa using h2

  theorem hoistCondition_ordinaryTypes (scope : List Name) (i : Nat) (pos : Bool) :
      ∀ (c : Condition), OrdinaryTypesCondition c → OrdinaryTypesCondition (hoistCondition scope i pos c).2.2
    | .path pc, _ => by
      show OrdinaryTypesCondition (hoistCondition scope i pos (.path pc)).2.2
      unfold hoistCondition
      match pos, pc.rolesRight.getLast?, scope.contains pc.labelRight with
      | true, some _, true => trivial
      | true, none, _ => trivial
      | true, some _, false => trivial
      | false, _, _ => trivial
    | .existential e ms, h => by
      have hms : OrdinaryTypesMatches ms := h
      rcases hgenM : hoistMatches scope i (pos && e) ms with ⟨i1, headMs, ms'⟩
      have heq : (hoistCondition scope i pos (.existential e ms)).2.2 = .existential e ms' := by
        show (hoistCondition scope i pos (.existential e ms)).2.2 = _
        unfold hoistCondition; simp [hgenM]
      rw [heq]
      show OrdinaryTypesMatches ms'
      have h1 := hoistMatches_ordinaryTypes scope i (pos && e) ms hms
      rw [hgenM] at h1
      simpa using h1
end

/-- No given a well-formed specification declares is a label `hoist`'s own head
splits into: every hoisted head match binds a reserved name (`hoistMatches_reserved`),
and no given is reserved. -/
theorem given_notin_headMatchList_hoist {s : Specification} (hwf : WellFormed s) {g0 : Label}
    (hg0 : g0 ∈ s.given) :
    g0.name ∉ (hoist s).head.matchList.map (·.unknown.name) := by
  have hg0given : g0.name ∈ s.given.map (·.name) := List.mem_map_of_mem hg0
  unfold hoist
  generalize hspan : s.matchList.span matchIsDeterministic = sp
  obtain ⟨before, rest⟩ := sp
  have hs : s.matchList = before ++ rest := by
    have h := span_loop_append matchIsDeterministic s.matchList []
    unfold List.span at hspan
    rw [hspan] at h
    simpa using h.symm
  have hbefore_wf : WellNamedMatches (s.given.map (·.name)) before := by
    have h := hwf.wellNamed
    rw [hs, wellNamedMatches_append] at h
    exact h.1
  have hg0notin_before : g0.name ∉ before.map (·.unknown.name) := by
    intro hmem
    exact (wellNamed_names_notin hbefore_wf g0.name hmem) hg0given
  cases rest with
  | nil =>
    show g0.name ∉ s.matchList.map (·.unknown.name)
    rw [hs]
    simpa using hg0notin_before
  | cons pivot after =>
    show g0.name ∉ (hoistAt s before pivot after).head.matchList.map (·.unknown.name)
    unfold hoistAt
    rcases hgenM : hoistMatches (scopeAt s before) 0 true (pivot :: after) with ⟨n, hm, tailMatches⟩
    simp only [hgenM, List.map_append, List.mem_append]
    rintro (h | h)
    · exact hg0notin_before h
    · obtain ⟨m, hm', hmn⟩ := List.mem_map.mp h
      have hres : isReserved m.unknown.name = true :=
        hoistMatches_reserved (scopeAt s before) 0 true (pivot :: after) m (by rw [hgenM]; exact hm')
      have hord : isReserved g0.name = false := hwf.givensOrdinary g0 hg0
      rw [hmn] at hres
      rw [hres] at hord
      exact absurd hord (by simp)

mutual
  /-- Every id a hoisted head match binds, while its head runs on
  `authGraph store f`, is the id of a fact in the store, at any depth: the same
  argument as `splitPaths_head_binds_store`, generalized to `hoistMatches`'s own
  recursion. The eligibility scope stays fixed throughout, so the same safety
  hypothesis (`hsafe`) threads through every level unchanged; only the
  environment it is checked against grows, as each level's own hoisted matches
  run in turn. -/
  theorem hoistMatches_head_binds_store {store : Graph} {f : Fact} (hclosed : store.closed)
      (hfnotin : ¬ InStore store f.id) (hfpred : ∀ p ∈ f.predecessors, InStore store p.2) :
      ∀ (scope : List Name), (∀ x ∈ scope, isReserved x = false) →
        ∀ (i : Nat) (pos : Bool) (ms : List Match) (eB : Env),
          (∀ x ∈ scope, ∃ id, eB x = some id ∧ SafeId store f id) →
          ∀ (e2 : Env), e2 ∈ evalMatches (Graph.authGraph store f) eB (hoistMatches scope i pos ms).2.1 →
            ∀ x ∈ (hoistMatches scope i pos ms).2.1.map (·.unknown.name), ∃ id, e2 x = some id ∧ InStore store id
    | scope, _, i, pos, [], eB, _, e2, _, x, hx => by simp [hoistMatches] at hx
    | scope, hordScope, i, pos, .mk u cs :: rest, eB, hsafe, e2, he2, x, hx => by
      rcases hgenC : hoistConditions scope i pos cs with ⟨i1, headCs, cs'⟩
      rcases hgenM : hoistMatches scope i1 pos rest with ⟨i2, headRest, rest'⟩
      have heq : (hoistMatches scope i pos (.mk u cs :: rest)).2.1 = headCs ++ headRest := by
        show (hoistMatches scope i pos (.mk u cs :: rest)).2.1 = _
        unfold hoistMatches; simp [hgenC, hgenM]
      rw [heq] at he2 hx
      obtain ⟨eC, heC, heR⟩ := mem_evalMatches_append.mp he2
      rw [List.map_append, List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨id, hidEq, hInStore⟩ := hoistConditions_head_binds_store hclosed hfnotin hfpred scope
          hordScope i pos cs eB hsafe eC (by rw [hgenC]; exact heC) x (by rw [hgenC]; exact hx)
        refine ⟨id, ?_, hInStore⟩
        have hxnotHeadRest : x ∉ headRest.map (·.unknown.name) :=
          hoistIndex_disjoint
            (fun m hm => by
              obtain ⟨j, -, hj2, hn⟩ := hoistConditions_index scope i pos cs m (by rw [hgenC]; exact hm)
              rw [hgenC] at hj2; simp only at hj2; exact ⟨j, hj2, hn⟩)
            (fun m hm => by
              obtain ⟨j, hj1, -, hn⟩ := hoistMatches_index scope i1 pos rest m (by rw [hgenM]; exact hm)
              exact ⟨j, hj1, hn⟩)
            x hx
        rw [evalMatches_frame heR x hxnotHeadRest]
        exact hidEq
      · have hsafeC : ∀ y ∈ scope, ∃ id, eC y = some id ∧ SafeId store f id := by
          intro y hy
          obtain ⟨id, heq2, hor⟩ := hsafe y hy
          refine ⟨id, ?_, hor⟩
          have hynotin : y ∉ headCs.map (·.unknown.name) := by
            intro hmem
            obtain ⟨mM, hmM, hmMn⟩ := List.mem_map.mp hmem
            have hres := hoistConditions_reserved scope i pos cs mM (by rw [hgenC]; exact hmM)
            rw [hmMn, hordScope y hy] at hres
            exact absurd hres (by simp)
          rw [evalMatches_frame heC y hynotin]
          exact heq2
        exact hoistMatches_head_binds_store hclosed hfnotin hfpred scope hordScope i1 pos rest eC hsafeC e2
          (by rw [hgenM]; exact heR) x (by rw [hgenM]; exact hx)

  theorem hoistConditions_head_binds_store {store : Graph} {f : Fact} (hclosed : store.closed)
      (hfnotin : ¬ InStore store f.id) (hfpred : ∀ p ∈ f.predecessors, InStore store p.2) :
      ∀ (scope : List Name), (∀ x ∈ scope, isReserved x = false) →
        ∀ (i : Nat) (pos : Bool) (cs : List Condition) (eB : Env),
          (∀ x ∈ scope, ∃ id, eB x = some id ∧ SafeId store f id) →
          ∀ (e2 : Env), e2 ∈ evalMatches (Graph.authGraph store f) eB (hoistConditions scope i pos cs).2.1 →
            ∀ x ∈ (hoistConditions scope i pos cs).2.1.map (·.unknown.name), ∃ id, e2 x = some id ∧ InStore store id
    | scope, _, i, pos, [], eB, _, e2, _, x, hx => by simp [hoistConditions] at hx
    | scope, hordScope, i, pos, c :: cs, eB, hsafe, e2, he2, x, hx => by
      rcases hgenc : hoistCondition scope i pos c with ⟨i1, headC, c'⟩
      rcases hgencs : hoistConditions scope i1 pos cs with ⟨i2, headCs, cs'⟩
      have heq : (hoistConditions scope i pos (c :: cs)).2.1 = headC ++ headCs := by
        show (hoistConditions scope i pos (c :: cs)).2.1 = _
        unfold hoistConditions; simp [hgenc, hgencs]
      rw [heq] at he2 hx
      obtain ⟨eD, heD, heCs⟩ := mem_evalMatches_append.mp he2
      rw [List.map_append, List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨id, hidEq, hInStore⟩ := hoistCondition_head_binds_store hclosed hfnotin hfpred scope
          hordScope i pos c eB hsafe eD (by rw [hgenc]; exact heD) x (by rw [hgenc]; exact hx)
        refine ⟨id, ?_, hInStore⟩
        have hxnotHeadCs : x ∉ headCs.map (·.unknown.name) :=
          hoistIndex_disjoint
            (fun m hm => by
              obtain ⟨j, -, hj2, hn⟩ := hoistCondition_index scope i pos c m (by rw [hgenc]; exact hm)
              rw [hgenc] at hj2; simp only at hj2; exact ⟨j, hj2, hn⟩)
            (fun m hm => by
              obtain ⟨j, hj1, -, hn⟩ := hoistConditions_index scope i1 pos cs m (by rw [hgencs]; exact hm)
              exact ⟨j, hj1, hn⟩)
            x hx
        rw [evalMatches_frame heCs x hxnotHeadCs]
        exact hidEq
      · have hsafeD : ∀ y ∈ scope, ∃ id, eD y = some id ∧ SafeId store f id := by
          intro y hy
          obtain ⟨id, heq2, hor⟩ := hsafe y hy
          refine ⟨id, ?_, hor⟩
          have hynotin : y ∉ headC.map (·.unknown.name) := by
            intro hmem
            obtain ⟨mM, hmM, hmMn⟩ := List.mem_map.mp hmem
            have hres := hoistCondition_reserved scope i pos c mM (by rw [hgenc]; exact hmM)
            rw [hmMn, hordScope y hy] at hres
            exact absurd hres (by simp)
          rw [evalMatches_frame heD y hynotin]
          exact heq2
        exact hoistConditions_head_binds_store hclosed hfnotin hfpred scope hordScope i1 pos cs eD hsafeD e2
          (by rw [hgencs]; exact heCs) x (by rw [hgencs]; exact hx)

  theorem hoistCondition_head_binds_store {store : Graph} {f : Fact} (hclosed : store.closed)
      (hfnotin : ¬ InStore store f.id) (hfpred : ∀ p ∈ f.predecessors, InStore store p.2) :
      ∀ (scope : List Name), (∀ x ∈ scope, isReserved x = false) →
        ∀ (i : Nat) (pos : Bool) (c : Condition) (eB : Env),
          (∀ x ∈ scope, ∃ id, eB x = some id ∧ SafeId store f id) →
          ∀ (e2 : Env), e2 ∈ evalMatches (Graph.authGraph store f) eB (hoistCondition scope i pos c).2.1 →
            ∀ x ∈ (hoistCondition scope i pos c).2.1.map (·.unknown.name), ∃ id, e2 x = some id ∧ InStore store id
    | scope, hordScope, i, pos, .path pc, eB, hsafe, e2, he2, x, hx => by
      revert e2 he2 x hx
      show ∀ (e2 : Env), e2 ∈ evalMatches (Graph.authGraph store f) eB (hoistCondition scope i pos (.path pc)).2.1 →
        ∀ x ∈ (hoistCondition scope i pos (.path pc)).2.1.map (·.unknown.name),
          ∃ id, e2 x = some id ∧ InStore store id
      unfold hoistCondition
      match pos, hl : pc.rolesRight.getLast?, hcont : scope.contains pc.labelRight with
      | true, some last, true =>
        intro e2 he2 x hx
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hx
        subst hx
        have hsc : pc.labelRight ∈ scope := by
          simpa only [List.contains_eq_mem, decide_eq_true_eq] using hcont
        obtain ⟨cid, hceB, hsafeC⟩ := hsafe pc.labelRight hsc
        have hnlr : pc.labelRight ≠ splitLabel i := by
          intro h
          have hcRes := hordScope pc.labelRight hsc
          rw [h, isReserved_splitLabel] at hcRes
          exact absurd hcRes (by simp)
        obtain ⟨fct, -, -, hc, he2'⟩ := mem_evalMatches_cons.mp he2
        have hbindC : (eB.bind (splitLabel i) fct.id) pc.labelRight = some cid := by
          simp [Env.bind, hnlr, hceB]
        have hbindU : (eB.bind (splitLabel i) fct.id) (splitLabel i) = some fct.id := by
          simp [Env.bind]
        have hcondTrue : ((Graph.authGraph store f).walk fct.id []).any
            (fun a => ((Graph.authGraph store f).walk cid pc.rolesRight).contains a) = true := by
          have hc' := hc
          simp only [allHold, holds, PathCondition.holds, hbindU, hbindC, Bool.and_true] at hc'
          exact hc'
        have hmemwalk : fct.id ∈ (Graph.authGraph store f).walk cid pc.rolesRight := by
          rw [List.any_eq_true] at hcondTrue
          obtain ⟨a, ha, hcontains⟩ := hcondTrue
          simp only [Graph.walk, List.mem_singleton] at ha
          subst ha
          simpa using hcontains
        have hne : pc.rolesRight ≠ [] := by intro h; rw [h] at hl; simp at hl
        obtain ⟨role0, rest0, hrr⟩ := List.exists_cons_of_ne_nil hne
        have hfctInStore : InStore store fct.id := by
          rw [hrr] at hmemwalk
          rcases hsafeC with hfid | hstoreid
          · subst hfid
            exact walk_from_f_sub_store hclosed hfnotin hfpred role0 rest0 fct.id hmemwalk
          · rw [(walk_authGraph_eq (f := f) hclosed (role0 :: rest0) hstoreid).1] at hmemwalk
            exact (walk_authGraph_eq (f := f) hclosed (role0 :: rest0) hstoreid).2 fct.id hmemwalk
        refine ⟨fct.id, ?_, hfctInStore⟩
        show e2 (splitLabel i) = some fct.id
        rw [evalMatches_frame he2' (splitLabel i) (by simp)]
        exact hbindU
      | true, none, _ => intro e2 he2 x hx; simp at hx
      | true, some _, false => intro e2 he2 x hx; simp at hx
      | false, _, _ => intro e2 he2 x hx; simp at hx
    | scope, hordScope, i, pos, .existential e ms, eB, hsafe, e2, he2, x, hx => by
      rcases hgenM : hoistMatches scope i (pos && e) ms with ⟨i1, headMs, ms'⟩
      have heq : (hoistCondition scope i pos (.existential e ms)).2.1 = headMs := by
        show (hoistCondition scope i pos (.existential e ms)).2.1 = _
        unfold hoistCondition; simp [hgenM]
      exact hoistMatches_head_binds_store hclosed hfnotin hfpred scope hordScope i (pos && e) ms eB hsafe e2
        (by rw [hgenM]; rw [heq] at he2; exact he2) x (by rw [hgenM]; rw [heq] at hx; exact hx)
end

section BoundaryHoist

variable {s : Specification} {g0 : Label} {store : Graph} {f : Fact} {env : Env}

/-- A rule whose tail is given the fact under authorization admits nobody:
`hoist`'s general form of `store_denies`. -/
theorem store_denies_hoist (hwf : WellFormed s) (hg : s.given = [g0]) (_hord : OrdinaryTypes s)
    (_hclosed : store.closed) (hfnotin : ¬ InStore store f.id)
    (_hfpred : ∀ p ∈ f.predecessors, InStore store p.2) (henv : env g0.name = some f.id)
    (h : tailReadsGiven (hoist s) g0.name = true) :
    (hoist s).evaluateStore store f env = [] :=
  store_denies_of hoist
    (given_notin_headMatchList_hoist hwf (by rw [hg]; simp)) hfnotin henv h

/-- A rule whose tail is not given the fact under authorization means, on the
store, exactly what the whole specification means on `authGraph store f`:
`hoist`'s general form of `store_correct`. -/
theorem store_correct_hoist (hwf : WellFormed s) (hg : s.given = [g0]) (hord : OrdinaryTypes s)
    (hclosed : store.closed) (hfnotin : ¬ InStore store f.id)
    (hfpred : ∀ p ∈ f.predecessors, InStore store p.2) (henv : env g0.name = some f.id)
    (h : tailReadsGiven (hoist s) g0.name = false) (r : List (Option FactId)) :
    r ∈ (hoist s).evaluateStore store f env ↔
      r ∈ s.evaluate (Graph.authGraph store f) env := by
  rw [← hoist_correct s hwf (Graph.authGraph store f) env r]
  rcases hspan : s.matchList.span matchIsDeterministic with ⟨before, rest⟩
  cases rest with
  | nil =>
    have hsplit_eq : hoist s = { head := s, tail := none } := by
      rw [hoist, hspan]
    rw [hsplit_eq]
    simp [Split.evaluateStore, Split.evaluate]
  | cons pivot after =>
    have hs : s.matchList = before ++ pivot :: after := by
      have h1 := span_loop_append matchIsDeterministic s.matchList []
      unfold List.span at hspan
      rw [hspan] at h1
      simpa using h1.symm
    have hsplit_eq : hoist s = hoistAt s before pivot after := by
      rw [hoist, hspan]
    rcases hgenM : hoistMatches (scopeAt s before) 0 true (pivot :: after) with ⟨n, hm, tailMatches⟩
    have htail_eq : (hoistAt s before pivot after).tail =
        some (Specification.mk (tailGivenAt s (before ++ hm) tailMatches) tailMatches s.projection) := by
      unfold hoistAt
      simp only [hgenM]
    have hhead_eq : (hoistAt s before pivot after).head =
        { given := s.given, matchList := before ++ hm,
          projection := .composite ((tailGivenAt s (before ++ hm) tailMatches).map
            fun l => { name := l.name, label := l.name }) } := by
      unfold hoistAt
      simp only [hgenM]
    let tailGiven := tailGivenAt s (before ++ hm) tailMatches
    rw [hsplit_eq] at h ⊢
    unfold tailReadsGiven at h
    rw [htail_eq] at h
    rw [List.any_eq_false] at h
    have hgn : ∀ l ∈ tailGiven, l.name ≠ g0.name := by
      intro l hl heq
      exact h l hl (by simp [heq])
    have hordBoth : OrdinaryTypesMatches before ∧ OrdinaryTypesMatches (pivot :: after) := by
      have h1 : OrdinaryTypesMatches s.matchList := hord
      rw [hs, ordinaryTypesMatches_append] at h1
      exact h1
    have hg0notin_before : g0.name ∉ before.map (·.unknown.name) := by
      have h1 := given_notin_headMatchList_hoist (s := s) hwf (g0 := g0) (by rw [hg]; simp)
      rw [hsplit_eq, hhead_eq] at h1
      simp only [List.map_append, List.mem_append] at h1
      intro hmem
      exact h1 (Or.inl hmem)
    have hordScope : ∀ x ∈ scopeAt s before, isReserved x = false := scopeAt_ordinary hwf hs
    have hheadStore : ∀ tuple ∈ evalMatches (Graph.authGraph store f) env (before ++ hm),
        ∀ l ∈ tailGiven, ∃ id, tuple l.name = some id ∧ InStore store id := by
      intro tuple htuple l hl
      have hlmem : l = g0 ∨ l ∈ (before ++ hm).map (·.unknown) := by
        have h1 := hl
        change l ∈ tailGivenAt s (before ++ hm) tailMatches at h1
        unfold tailGivenAt at h1
        simp only [List.mem_filter, List.mem_append, hg, List.mem_singleton] at h1
        exact h1.1
      have hlname : l.name ∈ before.map (·.unknown.name) ++ hm.map (·.unknown.name) := by
        rcases hlmem with rfl | hlmem
        · exact absurd rfl (hgn l hl)
        · simp only [List.map_append, List.mem_append] at hlmem ⊢
          rcases hlmem with hlmem | hlmem
          · obtain ⟨m, hm', hmn⟩ := List.mem_map.mp hlmem
            exact Or.inl (hmn ▸ List.mem_map_of_mem hm')
          · obtain ⟨m, hm', hmn⟩ := List.mem_map.mp hlmem
            exact Or.inr (hmn ▸ List.mem_map_of_mem hm')
      obtain ⟨eB, heB, htupleSm⟩ := mem_evalMatches_append.mp htuple
      have hsafe : ∀ y ∈ scopeAt s before, ∃ id, eB y = some id ∧ SafeId store f id :=
        safeAt_before hg hordBoth.1 henv hg0notin_before heB
      rw [List.mem_append] at hlname
      rcases hlname with hlname | hlname
      · have hlord : isReserved l.name = false := by
          obtain ⟨m, hm', hmn⟩ := List.mem_map.mp hlname
          exact hmn ▸ wellNamed_ordinary (by
            have h1 := hwf.wellNamed
            rw [hs, wellNamedMatches_append] at h1
            exact h1.1) m hm'
        have hsmres : l.name ∉ hm.map (·.unknown.name) := by
          intro hmem
          obtain ⟨m, hm', hmn⟩ := List.mem_map.mp hmem
          have := hoistMatches_reserved (scopeAt s before) 0 true (pivot :: after) m
            (by rw [hgenM]; exact hm')
          rw [hmn] at this
          rw [hlord] at this
          exact absurd this (by simp)
        have hframe : tuple l.name = eB l.name := evalMatches_frame htupleSm l.name hsmres
        obtain ⟨id, heq, hInStore⟩ := ordinary_binds_store before hordBoth.1 env eB heB l.name hlname
        exact ⟨id, hframe ▸ heq, hInStore⟩
      · exact hoistMatches_head_binds_store hclosed hfnotin hfpred (scopeAt s before) hordScope 0 true
          (pivot :: after) eB hsafe tuple (by rw [hgenM]; exact htupleSm) l.name (by rw [hgenM]; exact hlname)
    simp only [Split.evaluateStore, Split.evaluate, htail_eq, hhead_eq]
    have hordTailMatches : OrdinaryTypesMatches tailMatches := by
      have h1 := hoistMatches_ordinaryTypes (scopeAt s before) 0 true (pivot :: after) hordBoth.2
      rw [hgenM] at h1
      simpa using h1
    exact Iff.of_eq (congrArg (r ∈ ·) (flatMap_congr
      (tailGiven_pointwise hclosed hfnotin (before ++ hm) tailGiven tailMatches s.projection
        hordTailMatches hheadStore)))

end BoundaryHoist

end JinagaSpec
