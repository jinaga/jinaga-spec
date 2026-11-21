import JinagaSpec.Proofs.Cursor
import JinagaSpec.Proofs.Derivation

/-!
# Flat levels

What every feed algorithm here relies on: a level with every positive condition
joined into it (`flatten`), its scoping and its labels; a flat level agreeing
on a replica and the replicator's graph when its solutions are delivered
(`flat_agree`); and a feed that walks only to predecessors delivering only what
the replica holds (`dropped_settled`).

`feeds_cover`: a replica that holds the givens and every fact the feeds
deliver on the replicator's graph, with their predecessors, reads what the
replicator reads. The replica is `g`, and what of the replicator's graph it does
not hold is `B`: a fresh batch to it, because it holds every fact's
predecessors (`Fresh`, as for the stream).
-/
namespace JinagaSpec

/-! ## Flattening every positive condition -/

theorem flattenConditions_cons (c : Condition) (cs : List Condition) :
    flattenConditions (fun _ => true) (c :: cs) = match c with
      | .existential true ms => ((flattenConditions (fun _ => true) cs).1, flatten ms ++ (flattenConditions (fun _ => true) cs).2)
      | c => (c :: (flattenConditions (fun _ => true) cs).1, (flattenConditions (fun _ => true) cs).2) := by
  rw [flattenConditions]
  rcases flattenConditions (fun _ => true) cs with ⟨k, l⟩
  cases c with
  | path => rfl
  | existential e ms => cases e <;> rfl

/-- Every condition is a path condition or a negative one. -/
def FlatConditions (cs : List Condition) : Prop :=
  ∀ c ∈ cs, c.isPath = true ∨ ∃ ns, c = .existential false ns

def Flat (L : List Match) : Prop := ∀ m ∈ L, FlatConditions m.conditions

theorem Flat.append {a b : List Match} (ha : Flat a) (hb : Flat b) : Flat (a ++ b) :=
  fun m hm => (List.mem_append.mp hm).elim (ha m) (hb m)

mutual
  theorem flatten_flat : ∀ ms : List Match, Flat (flatten ms)
    | [] => by simp [flatten, flattenMatches, Flat]
    | .mk u cs :: rest => by
      rw [flatten, flattenMatches_cons]
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact (flattenConditions_flat cs).1
      · exact ((flattenConditions_flat cs).2.append (flatten_flat rest)) m hm

  theorem flattenConditions_flat : ∀ cs : List Condition,
      FlatConditions (flattenConditions (fun _ => true) cs).1 ∧ Flat (flattenConditions (fun _ => true) cs).2
    | [] => by simp [flattenConditions, FlatConditions, Flat]
    | c :: cs => by
      obtain ⟨hk, hl⟩ := flattenConditions_flat cs
      rw [flattenConditions_cons]
      cases c with
      | path pc =>
        refine ⟨fun d hd => ?_, hl⟩
        rcases List.mem_cons.mp hd with rfl | hd
        · exact Or.inl rfl
        · exact hk d hd
      | existential e ms =>
        cases e with
        | true => exact ⟨hk, (flatten_flat ms).append hl⟩
        | false =>
          refine ⟨fun d hd => ?_, hl⟩
          rcases List.mem_cons.mp hd with rfl | hd
          · exact Or.inr ⟨ms, rfl⟩
          · exact hk d hd
end

mutual
  theorem flatten_scoped : ∀ (ms : List Match) (S : List Name), ScopedMatches S ms → ScopedMatches S (flatten ms)
    | [], _, _ => by simp [flatten, flattenMatches, ScopedMatches]
    | .mk u cs :: rest, S, ⟨hcs, hrest⟩ => by
      rw [flatten, flattenMatches_cons]
      refine ⟨flattenConditions_keep_scoped cs hcs, scopedMatches_append.mpr ⟨flattenConditions_scoped cs u.name S hcs, ?_⟩⟩
      exact scopedMatches_mono _ _ _ (fun x hx => mem_scopeAfter.mpr (Or.inr hx)) (flatten_scoped rest _ hrest)

  theorem flattenConditions_scoped : ∀ (cs : List Condition) (u : Name) (S : List Name),
      ScopedConditions (u :: S) S cs → ScopedMatches (u :: S) (flattenConditions (fun _ => true) cs).2
    | [], _, _, _ => by simp [flattenConditions, ScopedMatches]
    | c :: cs, u, S, ⟨hc, hcs⟩ => by
      have ih := flattenConditions_scoped cs u S hcs
      rw [flattenConditions_cons]
      cases c with
      | path => exact ih
      | existential e ms =>
        cases e with
        | false => exact ih
        | true =>
          exact scopedMatches_append.mpr ⟨flatten_scoped ms _ hc,
            scopedMatches_mono _ _ _ (fun x hx => mem_scopeAfter.mpr (Or.inr hx)) ih⟩
end

/-- The labels the negative conditions of a level declare. -/
def negativeLabels (L : List Match) : List Name := (L.flatMap Match.negatives).flatMap declaredMatches

theorem negatives_mk (u : Label) (c : Condition) (cs : List Condition) :
    (Match.mk u (c :: cs)).negatives =
      (match c with | .existential false ms => [ms] | _ => []) ++ (Match.mk u cs).negatives := by
  cases c with
  | path => rfl
  | existential e ms => cases e <;> rfl

mutual
  /-- A flattened level's names, then the labels its negative conditions
  declare, are among the labels the level declares, as often. -/
  theorem flatten_declared : ∀ (ms : List Match) (x : Name),
      (names (flatten ms) ++ negativeLabels (flatten ms)).count x ≤ (declaredMatches ms).count x
    | [], _ => by simp [flatten, flattenMatches, names, negativeLabels, declaredMatches]
    | .mk u cs :: rest, x => by
      have h1 := flattenConditions_declared u cs x
      have h2 := flatten_declared rest x
      rw [flatten, flattenMatches_cons]
      simp only [flatten, declaredMatches, names, negativeLabels, List.map_cons, List.map_append, List.flatMap_cons,
        List.flatMap_append, List.count_append, List.count_cons] at h1 h2 ⊢
      simp only [Match.unknown_mk] at *
      by_cases hx : u.name = x <;> simp_all <;> omega

  theorem flattenConditions_declared (u : Label) : ∀ (cs : List Condition) (x : Name),
      (names (flattenConditions (fun _ => true) cs).2 ++ negativeLabels (flattenConditions (fun _ => true) cs).2 ++
        ((Match.mk u (flattenConditions (fun _ => true) cs).1).negatives).flatMap declaredMatches).count x ≤
        (declaredConditions cs).count x
    | [], _ => by simp [flattenConditions, names, negativeLabels, Match.negatives, declaredConditions]
    | c :: cs, x => by
      have ih := flattenConditions_declared u cs x
      rw [flattenConditions_cons]
      cases c with
      | path pc =>
        simp only [negatives_mk, declaredConditions] at ih ⊢
        simpa using ih
      | existential e ms =>
        cases e with
        | false =>
          simp only [negatives_mk, declaredConditions, List.flatMap_append, List.count_append,
            List.flatMap_cons, List.flatMap_nil, List.append_nil] at ih ⊢
          omega
        | true =>
          have hm := flatten_declared ms x
          simp only [declaredConditions, names, negativeLabels, List.map_append, List.flatMap_append,
            List.count_append] at ih hm ⊢
          omega
end

/-- The level declares each label once, and none in scope. -/
def Distinct (S : List Name) (ms : List Match) : Prop :=
  (declaredMatches ms).Nodup ∧ ∀ x ∈ declaredMatches ms, x ∉ S

theorem count_le_flatMap {α β : Type} [BEq β] [LawfulBEq β] (f : α → List β) (x : β) :
    ∀ {L : List α} {a : α}, a ∈ L → (f a).count x ≤ (L.flatMap f).count x
  | b :: L, a, h => by
    simp only [List.flatMap_cons, List.count_append]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := count_le_flatMap f x h; omega

theorem nodup_of_count_le_one : ∀ {l : List Name}, (∀ x, l.count x ≤ 1) → l.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    have ha := h a
    simp only [List.count_cons_self] at ha
    refine List.nodup_cons.mpr ⟨fun hm => by have := List.count_pos_iff.mpr hm; omega,
      nodup_of_count_le_one fun x => Nat.le_trans (List.count_le_count_cons ..) (h x)⟩

theorem nodup_of_count_le {l1 l2 : List Name} (h : ∀ x, l1.count x ≤ l2.count x) (hn : l2.Nodup) : l1.Nodup :=
  nodup_of_count_le_one fun x => Nat.le_trans (h x) (by rw [hn.count]; split <;> omega)

theorem mem_of_count_le {l1 l2 : List Name} (h : ∀ x, l1.count x ≤ l2.count x) {x : Name} (hx : x ∈ l1) : x ∈ l2 :=
  List.count_pos_iff.mp (Nat.lt_of_lt_of_le (List.count_pos_iff.mpr hx) (h x))

/-- What the flattened level needs of its names, and its negative conditions of theirs. -/
theorem Distinct.flat {S : List Name} {ms : List Match} (h : Distinct S ms) :
    (names (flatten ms)).Nodup ∧ (∀ x ∈ names (flatten ms), x ∉ S) ∧
      ∀ m ∈ flatten ms, ∀ ns ∈ m.negatives, ∀ S' : List Name,
        (∀ x ∈ S', x ∈ names (flatten ms) ∨ x ∈ S) → Distinct S' ns := by
  have hc := flatten_declared ms
  have hnd := nodup_of_count_le hc h.1
  refine ⟨(List.nodup_append.mp hnd).1, fun x hx => h.2 x (mem_of_count_le hc (List.mem_append_left _ hx)), ?_⟩
  intro m hm ns hns S' hS'
  have hsub : ∀ x, (declaredMatches ns).count x ≤ (negativeLabels (flatten ms)).count x := fun x =>
    count_le_flatMap declaredMatches x (List.mem_flatMap.mpr ⟨m, hm, hns⟩)
  refine ⟨nodup_of_count_le hsub (List.nodup_append.mp hnd).2.1, fun x hx hxS => ?_⟩
  have hneg := mem_of_count_le hsub hx
  rcases hS' x hxS with hxn | hxS
  · exact (List.nodup_append.mp hnd).2.2 x hxn x hneg rfl
  · exact h.2 x (mem_of_count_le hc (List.mem_append_right _ hneg)) hxS

/-! ## A flat level agrees -/

variable {g : Graph} {B : List Fact}

theorem allHold_filter_paths {G : Graph} {e : Env} {u : Name} :
    ∀ {cs : List Condition}, allHold G e u cs = true → allHold G e u (cs.filter (·.isPath)) = true
  | [], _ => rfl
  | c :: cs, h => by
    simp only [allHold, Bool.and_eq_true] at h
    cases hc : c.isPath <;> simp [hc, allHold, h.1, allHold_filter_paths h.2]

/-- A solution is a solution of the path conditions. -/
theorem evalMatches_paths {G : Graph} : ∀ {L : List Match} {e σ : Env},
    σ ∈ evalMatches G e L → σ ∈ evalMatches G e (L.map Match.paths)
  | [], _, _, h => h
  | .mk u cs :: L, e, σ, h => by
    obtain ⟨f, hf, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
    exact mem_evalMatches_cons.mpr ⟨f, hf, ht, allHold_filter_paths hc, evalMatches_paths hr⟩

theorem names_paths (L : List Match) : names (L.map Match.paths) = names L := by
  simp only [names, List.map_map]
  congr 1; funext m; cases m; rfl

theorem scopedConditions_mem {inner outer : List Name} :
    ∀ {cs : List Condition} {c : Condition}, ScopedConditions inner outer cs → c ∈ cs → ScopedCondition inner outer c
  | _ :: _, _, ⟨h, _⟩, .head _ => h
  | _ :: _, _, ⟨_, h⟩, .tail _ hc => scopedConditions_mem h hc

/-- The conditions of a flat match agree on both graphs at `e'`, given that the
negative ones agree at `τ`, which agrees with `e'` on the scope. -/
theorem allHold_flat (hf : Fresh g B) {u : Name} {S : List Name} {e' τ : Env} (he' : Settled B e')
    (hag : Agree (u :: S) e' τ) :
    ∀ {cs : List Condition}, FlatConditions cs → ScopedConditions (u :: S) S cs →
      (∀ ns, Condition.existential false ns ∈ cs →
        ((∃ σ, σ ∈ evalMatches g τ ns) ↔ (∃ σ, σ ∈ evalMatches (g ++ B) τ ns))) →
      allHold g e' u cs = allHold (g ++ B) e' u cs
  | [], _, _, _ => rfl
  | c :: cs, hfl, ⟨hc, hcs⟩, hneg => by
    have ih := allHold_flat hf he' hag (fun d hd => hfl d (List.mem_cons_of_mem _ hd)) hcs
      fun ns h => hneg ns (List.mem_cons_of_mem _ h)
    simp only [allHold, ih]
    congr 1
    rcases hfl c (List.mem_cons_self ..) with hp | ⟨ns, rfl⟩
    · cases c with
      | path pc => simp only [holds, pathHolds_fresh hf pc (he' u) (he' pc.labelRight)]
      | existential => simp [Condition.isPath] at hp
    · rw [holds_agree g _ u S e' τ hc hag, holds_agree (g ++ B) _ u S e' τ hc hag]
      have := hneg ns (List.mem_cons_self ..)
      simp only [holds]
      congr 2
      cases h1 : evalMatches g τ ns <;> cases h2 : evalMatches (g ++ B) τ ns <;> simp_all

/-- **A flat level agrees.** Its matches carry only path conditions and
negative ones. Every solution of its path conditions on the replicator's graph
binds facts the replica holds, and at each such solution each negative
condition's own level agrees, for any scope among the level's labels and the
labels around it. Then the level has the same solutions on both graphs. -/
theorem flat_agree (hf : Fresh g B) : ∀ (L : List Match) (S : List Name) (e : Env),
    Flat L → ScopedMatches S L → (names L).Nodup → (∀ x ∈ names L, x ∉ S) → Settled B e →
    (∀ τ ∈ evalMatches (g ++ B) e (L.map Match.paths), Settled B τ ∧
      ∀ m ∈ L, ∀ ns ∈ m.negatives, ∀ S' : List Name, (∀ x ∈ S', x ∈ names L ∨ x ∈ S) → ScopedMatches S' ns →
        ((∃ σ, σ ∈ evalMatches g τ ns) ↔ (∃ σ, σ ∈ evalMatches (g ++ B) τ ns))) →
    ∀ σ, σ ∈ evalMatches g e L ↔ σ ∈ evalMatches (g ++ B) e L
  | [], _, _, _, _, _, _, _, _, σ => Iff.rfl
  | .mk u cs :: L, S, e, hfl, ⟨hcs, hL⟩, hnd, hdis, he, hτ, σ => by
    have hnd' : u.name ∉ names L ∧ (names L).Nodup := by simpa [names] using hnd
    have hdis' : ∀ x ∈ names L, x ∉ u.name :: S := by
      intro x hx hxS
      rcases List.mem_cons.mp hxS with rfl | hxS
      · exact hnd'.1 hx
      · exact hdis x (by simp [names] at hx ⊢; exact Or.inr hx) hxS
    -- Through a candidate `f` whose path conditions hold, the rest of the level
    -- meets the same premises, and if the rest has a solution of its path
    -- conditions, the candidate's conditions agree.
    have step : ∀ f ∈ g ++ B, f.type = u.type → Outside B f.id →
        allHold (g ++ B) (e.bind u.name f.id) u.name (cs.filter (·.isPath)) = true →
        (∀ τ ∈ evalMatches (g ++ B) (e.bind u.name f.id) (L.map Match.paths), Settled B τ ∧
          ∀ m ∈ L, ∀ ns ∈ m.negatives, ∀ S' : List Name, (∀ x ∈ S', x ∈ names L ∨ x ∈ u.name :: S) →
            ScopedMatches S' ns → ((∃ σ, σ ∈ evalMatches g τ ns) ↔ (∃ σ, σ ∈ evalMatches (g ++ B) τ ns))) ∧
        (∀ τ ∈ evalMatches (g ++ B) (e.bind u.name f.id) (L.map Match.paths),
          allHold g (e.bind u.name f.id) u.name cs = allHold (g ++ B) (e.bind u.name f.id) u.name cs) := by
      intro f hfG ht hout hp
      have hlift : ∀ τ ∈ evalMatches (g ++ B) (e.bind u.name f.id) (L.map Match.paths),
          τ ∈ evalMatches (g ++ B) e ((Match.mk u cs :: L).map Match.paths) := fun τ hτ' =>
        mem_evalMatches_cons.mpr ⟨f, hfG, ht, hp, hτ'⟩
      have hscope : ∀ x, x ∈ names L ∨ x ∈ u.name :: S → x ∈ names (Match.mk u cs :: L) ∨ x ∈ S := by
        intro x hx
        simp only [names, List.map_cons, Match.unknown_mk, List.mem_cons] at hx ⊢
        rcases hx with hx | rfl | hx
        · exact Or.inl (Or.inr hx)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr hx
      refine ⟨fun τ hτ' => ⟨(hτ τ (hlift τ hτ')).1, fun m hm ns hns S' hS' =>
          (hτ τ (hlift τ hτ')).2 m (List.mem_cons_of_mem _ hm) ns hns S' fun x hx => hscope x (hS' x hx)⟩, ?_⟩
      intro τ hτ'
      have hag : Agree (u.name :: S) (e.bind u.name f.id) τ := fun x hx =>
        (evalMatches_frame hτ' x (show x ∉ names (L.map Match.paths) by
          rw [names_paths]; exact fun hm => hdis' x hm hx)).symm
      refine allHold_flat hf (he.bind hout) hag (hfl _ (List.mem_cons_self ..)) hcs fun ns hns => ?_
      exact (hτ τ (hlift τ hτ')).2 _ (List.mem_cons_self ..) ns (Match.mem_negatives.mpr hns) (u.name :: S)
        (fun x hx => hscope x (Or.inr hx))
        (scopedConditions_mem hcs hns)
    constructor
    · intro h
      obtain ⟨f, hfg, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
      have hout : Outside B f.id := fun b hb => hf.idNew f hfg b hb
      have hp : allHold (g ++ B) (e.bind u.name f.id) u.name (cs.filter (·.isPath)) = true := by
        rw [allHold_paths_fresh hf (he.bind hout) fun c hc => (List.mem_filter.mp hc).2]
        exact allHold_filter_paths hc
      obtain ⟨hrest, hagree⟩ := step f (List.mem_append_left _ hfg) ht hout hp
      have hτ' := evalMatches_paths_mono hf (pathsOnly_paths L) (he.bind hout) (evalMatches_paths hr)
      refine mem_evalMatches_cons.mpr ⟨f, List.mem_append_left _ hfg, ht, hagree σ hτ' ▸ hc, ?_⟩
      exact (flat_agree hf L _ _ (fun m hm => hfl m (List.mem_cons_of_mem _ hm)) hL hnd'.2 hdis' (he.bind hout)
        hrest σ).mp hr
    · intro h
      obtain ⟨f, hfG, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
      have hp := allHold_filter_paths hc
      have hτ' := evalMatches_paths hr
      have hset := (hτ σ (mem_evalMatches_cons.mpr ⟨f, hfG, ht, hp, hτ'⟩)).1
      have hout : Outside B f.id := hset u.name f.id (by rw [evalMatches_frame hτ' u.name (show u.name ∉ names (L.map Match.paths) by rw [names_paths]; exact hnd'.1)]; simp [Env.bind])
      have hfg : f ∈ g := (List.mem_append.mp hfG).resolve_right fun hb => hout f hb rfl
      obtain ⟨hrest, hagree⟩ := step f hfG ht hout hp
      refine mem_evalMatches_cons.mpr ⟨f, hfg, ht, (hagree σ hτ').symm ▸ hc, ?_⟩
      exact (flat_agree hf L _ _ (fun m hm => hfl m (List.mem_cons_of_mem _ hm)) hL hnd'.2 hdis' (he.bind hout)
        hrest σ).mpr hr

/-! ## Every feed is scoped and binds each label once -/

/-- A feed that a replicator can read from the givens `S`: its path conditions
name labels bound before them, and it binds each label once, none of them a
given. -/
def FeedScoped (S : List Name) (F : List Match) : Prop :=
  ScopedMatches S F ∧ (names F).Nodup ∧ ∀ x ∈ names F, x ∉ S

theorem scoped_paths : ∀ {S : List Name} {L : List Match}, ScopedMatches S L → ScopedMatches S (L.map Match.paths)
  | _, [], _ => trivial
  | S, .mk u cs :: L, ⟨hcs, hL⟩ => by
    refine ⟨?_, scoped_paths hL⟩
    clear hL
    induction cs with
    | nil => trivial
    | cons c cs ih =>
      cases hc : c.isPath
      · simp only [List.filter_cons, hc]; exact ih hcs.2
      · simp only [List.filter_cons, hc, ite_true]; exact ⟨hcs.1, ih hcs.2⟩

/-- A negative condition of a match of a scoped list is scoped after the whole list. -/
theorem scoped_negatives : ∀ {T : List Name} {L : List Match}, ScopedMatches T L →
    ∀ m ∈ L, ∀ ns ∈ m.negatives, ScopedMatches (scopeAfter T L) ns
  | _, [], _, _, h, _, _ => by simp at h
  | T, .mk u cs :: L, ⟨hcs, hL⟩, m, hm, ns, hns => by
    rcases List.mem_cons.mp hm with rfl | hm
    · have hsc := scopedConditions_mem hcs (Match.mem_negatives.mp hns)
      show ScopedMatches (scopeAfter (u.name :: T) L) ns
      exact scopedMatches_mono _ _ _ (fun x hx => mem_scopeAfter.mpr (Or.inr hx)) hsc
    · exact scoped_negatives hL m hm ns hns

/-! ## A dropped feed delivers what the replica holds -/

theorem walk_outside (hf : Fresh g B) : ∀ (rs : List Role) {start : FactId}, Outside B start →
    ∀ x ∈ (g ++ B).walk start rs, Outside B x := by
  intro rs start hs
  rw [walk_fresh hf rs hs]
  induction rs generalizing start with
  | nil => intro x hx; simp [Graph.walk] at hx; exact hx ▸ hs
  | cons role rs ih =>
    intro x hx
    simp only [Graph.walk, List.mem_flatMap] at hx
    obtain ⟨p, hp, hx⟩ := hx
    exact ih (step_outside hf hp) x hx

/-- A feed whose path conditions all walk from earlier labels to their
predecessors binds only facts reached from the facts it starts from. -/
theorem dropped_settled (hf : Fresh g B) : ∀ (F : List Match) (S : List Name) (e : Env),
    FeedScoped S F →
    (∀ m ∈ F, ∃ pc, Condition.path pc ∈ m.conditions ∧ pc.rolesLeft = []) → Settled B e →
    ∀ τ ∈ evalMatches (g ++ B) e F, Settled B τ
  | [], _, _, _, _, he, τ, h => by simp [evalMatches] at h; exact h ▸ he
  | .mk u cs :: F, S, e, ⟨⟨hcs, hF⟩, hnd, hdis⟩, hroot, he, τ, h => by
    have hnd' : u.name ∉ names F ∧ (names F).Nodup := by simpa [names] using hnd
    obtain ⟨f, -, -, hc, hr⟩ := mem_evalMatches_cons.mp h
    obtain ⟨pc, hpc, hleft⟩ := hroot _ (List.mem_cons_self ..)
    have hholds := (allHold_iff cs).mp hc _ hpc
    have hright : pc.labelRight ∈ S := scopedConditions_mem hcs hpc
    have hu : u.name ∉ S := hdis u.name (by simp [names])
    have hne : pc.labelRight ≠ u.name := fun h => hu (h ▸ hright)
    simp only [holds, PathCondition.holds, Env.bind, hne, ite_false, ite_true] at hholds
    split at hholds
    · rename_i a r ha hr'
      simp only [Option.some.injEq] at ha
      subst ha
      simp only [hleft, Graph.walk, List.any_cons, List.any_nil, Bool.or_false, List.contains_iff_mem] at hholds
      have hout := walk_outside hf pc.rolesRight (he _ r hr') f.id (by simpa using hholds)
      refine dropped_settled hf F (u.name :: S) _ ⟨hF, hnd'.2, fun x hx hxS => ?_⟩
        (fun m hm => hroot m (List.mem_cons_of_mem _ hm)) (he.bind hout) τ hr
      rcases List.mem_cons.mp hxS with rfl | hxS
      · exact hnd'.1 hx
      · exact hdis x (by simp [names] at hx ⊢; exact Or.inr hx) hxS
    · simp at hholds

/-- A match with a path condition. -/
def HasPath (m : Match) : Prop := ∃ c ∈ m.conditions, c.isPath = true

mutual
  theorem flatten_rooted : ∀ ms : List Match, RootedMatches ms →
      (∀ m ∈ flatten ms, HasPath m) ∧ ∀ m ∈ flatten ms, ∀ ns ∈ m.negatives, RootedMatches ns
    | [], _ => by simp [flatten, flattenMatches]
    | .mk u cs :: rest, h => by
      simp only [RootedMatches] at h
      obtain ⟨⟨c, hc, hp⟩, hcs, hrest⟩ := h
      obtain ⟨hkeep, hl1, hl2, hneg⟩ := flattenConditions_rooted cs hcs
      obtain ⟨hr1, hr2⟩ := flatten_rooted rest hrest
      rw [flatten, flattenMatches_cons]
      refine ⟨fun m hm => ?_, fun m hm ns hns => ?_⟩
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact ⟨c, hkeep c hc hp, hp⟩
        · rcases List.mem_append.mp hm with hm | hm
          all_goals first | exact hl1 m hm | exact hr1 m hm
      · rcases List.mem_cons.mp hm with rfl | hm
        · exact hneg _ (Match.mem_negatives.mp hns)
        · rcases List.mem_append.mp hm with hm | hm
          all_goals first | exact hl2 m hm ns hns | exact hr2 m hm ns hns

  theorem flattenConditions_rooted : ∀ cs : List Condition, RootedConditions cs →
      (∀ c ∈ cs, c.isPath = true → c ∈ (flattenConditions (fun _ => true) cs).1) ∧
      (∀ m ∈ (flattenConditions (fun _ => true) cs).2, HasPath m) ∧
      (∀ m ∈ (flattenConditions (fun _ => true) cs).2, ∀ ns ∈ m.negatives, RootedMatches ns) ∧
      (∀ ns, Condition.existential false ns ∈ (flattenConditions (fun _ => true) cs).1 → RootedMatches ns)
    | [], _ => by simp [flattenConditions]
    | c :: cs, h => by
      rw [flattenConditions_cons]
      cases c with
      | path pc =>
        obtain ⟨k, l1, l2, n⟩ := flattenConditions_rooted cs (by simpa [RootedConditions] using h)
        dsimp only
        refine ⟨fun d hd hp => ?_, l1, l2, fun ns hns => ?_⟩
        · rcases List.mem_cons.mp hd with rfl | hd
          all_goals first | exact List.mem_cons_self .. | exact List.mem_cons_of_mem _ (k d hd hp)
        · rcases List.mem_cons.mp hns with h | hns
          all_goals first | (cases h) | exact n ns hns
      | existential e ms =>
        simp only [RootedConditions] at h
        obtain ⟨hms, hcs⟩ := h
        obtain ⟨k, l1, l2, n⟩ := flattenConditions_rooted cs hcs
        cases e with
        | false =>
          dsimp only
          refine ⟨fun d hd hp => ?_, l1, l2, fun ns hns => ?_⟩
          · rcases List.mem_cons.mp hd with rfl | hd
            · simp [Condition.isPath] at hp
            · exact List.mem_cons_of_mem _ (k d hd hp)
          · rcases List.mem_cons.mp hns with h | hns
            · cases h; exact hms
            · exact n ns hns
        | true =>
          dsimp only
          obtain ⟨f1, f2⟩ := flatten_rooted ms hms
          refine ⟨fun d hd hp => ?_, fun m hm => ?_, fun m hm => ?_, n⟩
          · rcases List.mem_cons.mp hd with rfl | hd
            · simp [Condition.isPath] at hp
            · exact k d hd hp
          · rcases List.mem_append.mp hm with hm | hm
            all_goals first | exact f1 m hm | exact l1 m hm
          · rcases List.mem_append.mp hm with hm | hm
            all_goals first | exact f2 m hm | exact l2 m hm
end

mutual
  theorem wellNamed_declared : ∀ (S : List Name) (ms : List Match), WellNamedMatches S ms →
      ∀ x ∈ declaredMatches ms, x ∉ S
    | _, [], _, _, h => by simp [declaredMatches] at h
    | S, .mk u cs :: rest, ⟨hu, _, hcs, hrest⟩, x, hx => by
      simp only [declaredMatches, List.mem_cons, List.mem_append] at hx
      rcases hx with rfl | hx | hx
      · exact hu
      · exact fun h => wellNamed_declaredConditions _ cs hcs x hx (List.mem_cons_of_mem _ h)
      · exact fun h => wellNamed_declared _ rest hrest x hx (List.mem_cons_of_mem _ h)

  theorem wellNamed_declaredConditions : ∀ (S : List Name) (cs : List Condition), WellNamedConditions S cs →
      ∀ x ∈ declaredConditions cs, x ∉ S
    | _, [], _, _, h => by simp [declaredConditions] at h
    | S, .path _ :: cs, ⟨_, hcs⟩, x, hx => wellNamed_declaredConditions S cs hcs x (by simpa [declaredConditions] using hx)
    | S, .existential _ ms :: cs, ⟨hms, hcs⟩, x, hx => by
      simp only [declaredConditions, List.mem_append] at hx
      rcases hx with hx | hx
      all_goals first | exact wellNamed_declared S ms hms x hx | exact wellNamed_declaredConditions S cs hcs x hx
end

/-! ## Givens -/

theorem has_settled {env : Env} (henv : Settled B env) (l : Label) :
    (g ++ B).has env l = g.has env l := by
  unfold Graph.has
  split
  · rename_i id h; rw [factOf_append_outside (henv _ id h)]
  · rfl

end JinagaSpec
