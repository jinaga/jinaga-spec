import JinagaSpec.Exact
import JinagaSpec.Proofs.Stream

/-!
# Exact inverses: sound on the new graph, and complete

**Conjunction.** Two lists of matches over the same unknowns, each bound once,
read as one (`conj`) have exactly the solutions the two have in common
(`mem_evalMatches_conj`): each binds the same unknown to a fact of the same
type, and the finished solution says which fact, because nothing rebinds it.

**Sound.** A solution of an add inverse is then a solution of the
specification on the new graph, so its row is read there (`adds_sound`). A
solution of a remove inverse fails one existential condition at one top-level
match on the new graph. A solution of the specification with the same row
binds the same top-level unknowns, when the projection names them all
(`ProjectsUnknowns`), so it reads that condition from the same bindings, and
the condition holds for it: a contradiction (`removes_sound`).

**Complete.** The inverse that found a gained solution
(`inverses_complete`'s walk) has it as a solution, and so does the
specification, so the add inverse has it. A lost solution fails, on the new
graph, one condition of one top-level match. Path conditions do not change, so
it is an existential condition, and the remove test for it holds
(`changes_complete`).

Adding a row the set holds, or removing one it lacks, changes nothing, so
together these make the held set exact (`exact_correct`), with no claim about
the old graph.
-/
namespace JinagaSpec

/-! ## Conjunction -/

theorem names_eq_of_unknowns {ms1 ms2 : List Match} (h : ms1.map (·.unknown) = ms2.map (·.unknown)) :
    names ms1 = names ms2 := by
  simpa [names, Function.comp_def] using congrArg (List.map Label.name) h

theorem mem_evalMatches_conj {g : Graph} :
    ∀ {ms1 ms2 : List Match} {env e : Env}, ms1.map (·.unknown) = ms2.map (·.unknown) →
      (names ms1).Nodup →
      (e ∈ evalMatches g env (conj ms1 ms2) ↔ e ∈ evalMatches g env ms1 ∧ e ∈ evalMatches g env ms2)
  | [], [], _, _, _, _ => by simp [conj, evalMatches]
  | [], _ :: _, _, _, hu, _ | _ :: _, [], _, _, hu, _ => by simp at hu
  | .mk u cs1 :: r1, .mk u2 cs2 :: r2, env, e, hu, hnd => by
    simp only [List.map_cons, List.cons.injEq, Match.unknown_mk] at hu
    obtain ⟨rfl, hu⟩ := hu
    simp only [names, List.map_cons, List.nodup_cons, Match.unknown_mk] at hnd
    have hn2 : u.name ∉ names r2 := names_eq_of_unknowns hu ▸ hnd.1
    show e ∈ evalMatches g env (.mk u (cs1 ++ cs2) :: conj r1 r2) ↔ _
    simp only [mem_evalMatches_cons, mem_evalMatches_conj hu hnd.2, allHold_append, Bool.and_eq_true]
    constructor
    · rintro ⟨f, hf, ht, ⟨h1, h2⟩, he1, he2⟩
      exact ⟨⟨f, hf, ht, h1, he1⟩, f, hf, ht, h2, he2⟩
    · rintro ⟨⟨f, hf, ht, h1, he1⟩, f2, -, -, h2, he2⟩
      -- The finished solution says which fact the unknown is.
      have hid : f2.id = f.id := by
        have := (evalMatches_frame he2 _ hn2).symm.trans (evalMatches_frame he1 _ hnd.1)
        simpa [Env.bind] using this
      rw [hid] at h2 he2
      exact ⟨f, hf, ht, ⟨h1, h2⟩, he1, he2⟩

/-- A well-named list of matches binds each unknown once. -/
theorem WellNamedMatches.nodup : ∀ {ms : List Match} {A : List Name}, WellNamedMatches A ms → (names ms).Nodup
  | [], _, _ => List.nodup_nil
  | .mk _ _ :: _, _, ⟨_, _, _, h⟩ =>
    List.nodup_cons.mpr ⟨fun hx => wellNamed_names_notin h _ hx List.mem_cons_self, h.nodup⟩

/-- Every inverse keeps the original's unknowns, in order. -/
theorem touchMatches_unknowns {b : Bool} :
    ∀ {ms : List Match} {t : Label × List Match}, t ∈ touchMatches b ms →
      t.2.map (·.unknown) = ms.map (·.unknown)
  | [], _, h => by simp [touchMatches] at h
  | .mk u cs :: rest, t, h => by
    simp only [touchMatches, List.mem_append, List.mem_map] at h
    rcases h with (h | ⟨_, _, rfl⟩) | ⟨t', ht', rfl⟩
    · cases b <;> simp_all
    · cases b <;> simp [relaxMatches]
    · simp [touchMatches_unknowns ht']

theorem removeTests_unknowns :
    ∀ {ms t : List Match}, t ∈ removeTests ms → t.map (·.unknown) = ms.map (·.unknown)
  | [], _, h => by simp [removeTests] at h
  | .mk u cs :: rest, t, h => by
    simp only [removeTests, List.mem_append, List.mem_map] at h
    rcases h with ⟨_, _, rfl⟩ | ⟨t', ht', rfl⟩
    · simp
    · simp [removeTests_unknowns ht']

/-! ## Flipping -/

theorem holds_flip {G : Graph} {env : Env} {u : Name} {d : Condition} (hd : d.isPath = false) :
    holds G env u d.flip = !holds G env u d := by
  cases d with
  | path => simp [Condition.isPath] at hd
  | existential e => cases e <;> simp [Condition.flip, holds]

theorem mem_usedInConditions {c : Condition} :
    ∀ {cs : List Condition}, c ∈ cs → ∀ x ∈ usedInCondition c, x ∈ usedInConditions cs
  | _ :: _, .head _, _, hx => by simp [usedInConditions, hx]
  | _ :: _, .tail _ h, _, hx => by simp [usedInConditions, mem_usedInConditions h _ hx]

theorem usedInMatches_clear :
    ∀ ms : List Match, usedInMatches (ms.map fun m => .mk m.unknown []) = []
  | [] => rfl
  | _ :: ms => by simp [usedInMatches, usedInConditions, usedInMatches_clear ms]

/-- A remove test uses only labels the matches use. -/
theorem removeTests_used :
    ∀ {ms t : List Match}, t ∈ removeTests ms → ∀ x ∈ usedInMatches t, x ∈ usedInMatches ms
  | [], _, h => by simp [removeTests] at h
  | .mk u cs :: rest, t, h => by
    simp only [removeTests, List.mem_append, List.mem_map, List.mem_filter] at h
    rcases h with ⟨d, ⟨hd, hp⟩, rfl⟩ | ⟨t', ht', rfl⟩
    · intro x hx
      cases d with
      | path => simp [Condition.isPath] at hp
      | existential =>
        simp only [usedInMatches, usedInConditions, usedInMatches_clear, Condition.flip,
          List.append_nil] at hx
        exact List.mem_append_left _ (mem_usedInConditions hd x hx)
    · intro x hx
      simp only [usedInMatches, usedInConditions, List.nil_append] at hx
      exact List.mem_append_right _ (removeTests_used ht' x hx)

/-! ## Sound on the new graph -/

/-- A solution of the matches satisfies none of their remove tests, from the
same environment, if it binds the unknowns as the test's solution does. -/
theorem removeTests_fail {G : Graph} :
    ∀ {ms t : List Match} {env σ e : Env}, (names ms).Nodup → t ∈ removeTests ms →
      σ ∈ evalMatches G env ms → e ∈ evalMatches G env t → (∀ x ∈ names ms, σ x = e x) → False
  | [], _, _, _, _, _, h, _, _, _ => by simp [removeTests] at h
  | .mk u cs :: rest, t, env, σ, e, hnd, ht, hσ, he, hag => by
    simp only [names, List.map_cons, List.nodup_cons, Match.unknown_mk] at hnd
    obtain ⟨x, -, -, hc, hσ'⟩ := mem_evalMatches_cons.mp hσ
    have hxid : e u.name = some x.id := by
      rw [← hag u.name List.mem_cons_self, evalMatches_frame hσ' _ hnd.1]; simp [Env.bind]
    -- The test binds `u` to the same fact, so reads from the same environment.
    simp only [removeTests, List.mem_append, List.mem_map, List.mem_filter] at ht
    rcases ht with ⟨d, ⟨hd, hp⟩, rfl⟩ | ⟨t', ht', rfl⟩
    · obtain ⟨y, -, -, hy, he'⟩ := mem_evalMatches_cons.mp he
      have : y.id = x.id := by
        have := (evalMatches_frame he' u.name (by simpa [names] using hnd.1)).symm.trans hxid
        simpa [Env.bind] using this
      rw [this] at hy
      simp [allHold, holds_flip (by simpa using hp), (allHold_iff cs).mp hc d hd] at hy
    · obtain ⟨y, -, -, -, he'⟩ := mem_evalMatches_cons.mp he
      have : y.id = x.id := by
        have hn : u.name ∉ names t' := by rw [names_eq_of_unknowns (removeTests_unknowns ht')]; exact hnd.1
        have := (evalMatches_frame he' u.name hn).symm.trans hxid
        simpa [Env.bind] using this
      rw [this] at he'
      exact removeTests_fail hnd.2 ht' hσ' he' fun z hz => hag z (List.mem_cons_of_mem _ hz)

section
variable {s : Specification} {env : Env} {g : Graph} {B : List Fact}

/-- The projection names every top-level unknown. -/
def ProjectsUnknowns (s : Specification) : Prop := ∀ x ∈ names s.matchList, x ∈ s.projection.labels

theorem projectsUnknowns_iff : projectsUnknowns s = true ↔ ProjectsUnknowns s := by
  simp [projectsUnknowns, ProjectsUnknowns, names]

/-- A row of the add inverses: a solution of a gained-direction inverse with
the original's conditions re-attached. -/
theorem mem_addInverses {G : Graph} {P : Env} {r : Row} :
    r ∈ ((addInverses s).map reorderOrSelf).flatMap (·.evaluate G P) ↔
      ∃ t ∈ touchMatches true s.matchList,
        ∃ e ∈ evalMatches G P (conj t.2 s.matchList), s.projection.labels.map e = r := by
  simp only [addInverses, inversesFor, List.map_map, List.flatMap_map, List.mem_flatMap,
    Function.comp_def, reorderOrSelf_correct]
  simp [Specification.evaluate]

/-- A row of the remove inverses: a solution of a lost-direction inverse with
one remove test attached. -/
theorem mem_removeInverses {G : Graph} {P : Env} {r : Row} :
    r ∈ ((removeInverses s).map reorderOrSelf).flatMap (·.evaluate G P) ↔
      ∃ t ∈ touchMatches false s.matchList, ∃ tl ∈ removeTests s.matchList,
        ∃ e ∈ evalMatches G P (conj t.2 tl), s.projection.labels.map e = r := by
  simp only [removeInverses, inversesFor, List.flatMap_map, List.flatMap_assoc, List.mem_flatMap,
    reorderOrSelf_correct]
  simp [Specification.evaluate]

/-- In the stored case, a fact's changes are what its exact inverses read. -/
theorem factChanges_stored {f : Fact} (hgiv : ¬ s.given.any (env ·.name == some f.id) = true)
    (hpres : s.given.all (g.has env) = true) :
    factChanges s env g f =
      (((addInverses s).map reorderOrSelf).flatMap (·.evaluate g (pinEnv s env f)),
       ((removeInverses s).map reorderOrSelf).flatMap (·.evaluate g (pinEnv s env f))) := by
  simp [factChanges, hgiv, hpres]

/-- **Adds are sound.** Every row a batch's add inverses report is in the new
result. -/
theorem adds_sound (hwf : WellFormed s) {r : Row} (h : r ∈ (changes s env g B).1) :
    r ∈ s.read (g ++ B) env := by
  obtain ⟨f, -, hr⟩ := List.mem_flatMap.mp h
  unfold factChanges at hr
  split at hr
  · exact hr
  split at hr
  · rename_i hpres
    obtain ⟨t, ht, e, he, rfl⟩ := mem_addInverses.mp hr
    rw [mem_evalMatches_conj (touchMatches_unknowns ht)
      (names_eq_of_unknowns (touchMatches_unknowns ht) ▸ hwf.wellNamed.nodup)] at he
    simp only [Specification.read, hpres, ite_true]
    exact (evaluate_agree hwf (pinEnv_agree hwf env f) _).mp (List.mem_map.mpr ⟨e, he.2, rfl⟩)
  · simp at hr

/-- **Removes are sound**, when the projection names every top-level unknown.
Every row a batch's remove inverses report is absent from the new result. -/
theorem removes_sound (hwf : WellFormed s) (hpu : ProjectsUnknowns s) {r : Row}
    (h : r ∈ (changes s env g B).2) : r ∉ s.read (g ++ B) env := by
  obtain ⟨f, -, hr⟩ := List.mem_flatMap.mp h
  unfold factChanges at hr
  split at hr
  · simp at hr
  split at hr
  · rename_i hpres
    obtain ⟨t, ht, tl, htl, e, he, rfl⟩ := mem_removeInverses.mp hr
    rw [mem_evalMatches_conj ((touchMatches_unknowns ht).trans (removeTests_unknowns htl).symm)
      (names_eq_of_unknowns (touchMatches_unknowns ht) ▸ hwf.wellNamed.nodup)] at he
    simp only [Specification.read, hpres, ite_true]
    intro hread
    obtain ⟨σ, hσ, hσr⟩ := List.mem_map.mp ((evaluate_agree hwf (pinEnv_agree hwf env f) _).mpr hread)
    exact removeTests_fail hwf.wellNamed.nodup htl hσ he.2 fun x hx =>
      List.map_inj_left.mp hσr x (hpu x hx)
  · simp at hr

/-! ## Complete -/

/-- Matches with no conditions have every solution they had on a smaller graph. -/
theorem evalMatches_clear {g G : Graph} (hsub : ∀ x ∈ g, x ∈ G) :
    ∀ (ms : List Match) {env e : Env}, e ∈ evalMatches g env ms →
      e ∈ evalMatches G env (ms.map fun m => .mk m.unknown [])
  | [], _, _, h => h
  | .mk _ _ :: rest, _, _, h => by
    obtain ⟨x, hx, ht, -, hr⟩ := mem_evalMatches_cons.mp h
    exact mem_evalMatches_cons.mpr ⟨x, hsub x hx, ht, rfl, evalMatches_clear hsub rest hr⟩

/-- A solution the batch removes fails, on the new graph, an existential
condition of one of its matches, so satisfies one of the remove tests there. -/
theorem lost_test (hf : Fresh g B) :
    ∀ (ms : List Match) {env e3 : Env}, PinOnly B env → pinLabel ∉ usedInMatches ms →
      pinLabel ∉ declaredInMatches ms → e3 ∈ evalMatches g env ms → e3 ∉ evalMatches (g ++ B) env ms →
      ∃ t ∈ removeTests ms, e3 ∈ evalMatches (g ++ B) env t
  | [], _, _, _, _, _, h, hn => absurd (by simpa [evalMatches] using h) hn
  | .mk u cs :: rest, env, e3, hpin, hu, hd, h, hn => by
    simp only [usedInMatches, declaredInMatches, List.mem_append, List.mem_cons, not_or] at hu hd
    obtain ⟨x, hx, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
    have hx' : x ∈ g ++ B := List.mem_append_left _ hx
    have hpin' := hpin.bind u.name (hf.idNew x hx)
    cases hcg : allHold (g ++ B) (env.bind u.name x.id) u.name cs
    · -- A condition fails on the new graph. It held on the old one, so it is existential.
      obtain ⟨d, hdm, hdn⟩ : ∃ d ∈ cs, holds (g ++ B) (env.bind u.name x.id) u.name d = false := by
        simpa using mt (allHold_iff cs).mpr (by simp [hcg])
      have hp : d.isPath = false := by
        cases d with
        | existential => rfl
        | path pc =>
          have hr : pc.labelRight ≠ pinLabel := fun heq =>
            hu.1 (mem_usedInConditions hdm _ (by simp [usedInCondition, heq]))
          rw [holds_path_fresh hf hpin' (Ne.symm hd.1.1) pc hr, (allHold_iff cs).mp hc _ hdm] at hdn
          contradiction
      refine ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨d, List.mem_filter.mpr ⟨hdm, by simp [hp]⟩, rfl⟩),
        mem_evalMatches_cons.mpr ⟨x, hx', ht, ?_, evalMatches_clear (fun _ => List.mem_append_left _) rest hr⟩⟩
      simp [allHold, holds_flip hp, hdn]
    · obtain ⟨t, htm, he⟩ := lost_test hf rest hpin' hu.2 hd.2 hr
        fun h' => hn (mem_evalMatches_cons.mpr ⟨x, hx', ht, hcg, h'⟩)
      exact ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨t, htm, rfl⟩),
        mem_evalMatches_cons.mpr ⟨x, hx', ht, rfl, he⟩⟩

/-- A solution read with the pin unbound, once the pin is bound, is the
solution of other matches that agrees with it off the pin. -/
theorem mem_evalMatches_pin {G : Graph} {ms ms' : List Match} {env e3 e : Env} {id : FactId}
    (hu : pinLabel ∉ usedInMatches ms) (hn : pinLabel ∉ names ms) (hn' : pinLabel ∉ names ms')
    (h3 : e3 ∈ evalMatches G env ms) (he : e ∈ evalMatches G (env.bind pinLabel id) ms')
    (hag : AgreeOff e3 e) : e ∈ evalMatches G (env.bind pinLabel id) ms := by
  obtain ⟨e2, he2, hag2⟩ := evalMatches_agreeOff ms (AgreeOff.pin env id).symm hu h3
  have : e = e2 := funext fun y => by
    by_cases hy : y = pinLabel
    · subst hy; rw [evalMatches_frame he _ hn', evalMatches_frame he2 _ hn]
    · exact (hag y hy).symm.trans (hag2 y hy)
  exact this ▸ he2

/-- **The changes are complete.** For a well-formed specification and a fresh
batch, every row the batch adds is among its adds, and every row it removes
is among its removes. -/
theorem changes_complete (hwf : WellFormed s) (hf : Fresh g B) (r : Row) :
    (r ∉ s.read g env → r ∈ s.read (g ++ B) env → r ∈ (changes s env g B).1) ∧
    (r ∈ s.read g env → r ∉ s.read (g ++ B) env → r ∈ (changes s env g B).2) := by
  by_cases hgiv : ∃ f ∈ B, s.given.any (env ·.name == some f.id) = true
  · -- A given arrives in the batch: every row read now is added, and none was read before.
    obtain ⟨f, hfB, hg⟩ := hgiv
    exact ⟨fun _ h2 => List.mem_flatMap.mpr ⟨f, hfB, by simpa [factChanges, hg] using h2⟩,
      fun h1 => absurd h1 (by simp [read_given_arrives hf hfB hg])⟩
  simp only [not_exists, not_and] at hgiv
  cases hpres : s.given.all (g.has env)
  · simp [Specification.read, givens_stored_append (g := g) hgiv, hpres]
  have hpres' := (givens_stored_append (g := g) hgiv).trans hpres
  have hsame := fun G => evaluate_agree (G := G) hwf (Env.restrictTo_agree (s.given.map (·.name)) env).symm r
  simp only [Specification.read, hpres, hpres', ite_true, hsame]
  have hnd := hwf.wellNamed.nodup
  have hnp : pinLabel ∉ names s.matchList := fun h => hwf.not_pin (Or.inr h) rfl
  constructor
  · intro h1 h2
    obtain ⟨e3, he3, rfl⟩ := List.mem_map.mp h2
    obtain ⟨b, hb, t, ht, e, he, hag⟩ := gainedMatches hf s.matchList (pinOnly_restrict hgiv)
      hwf.pin_unused hwf.pin_undeclared he3 fun h => h1 (List.mem_map.mpr ⟨e3, h, rfl⟩)
    have hu := touchMatches_unknowns ht
    have he' := mem_evalMatches_pin hwf.pin_unused hnp (names_eq_of_unknowns hu ▸ hnp) he3 he hag
    refine List.mem_flatMap.mpr ⟨b, hb, ?_⟩
    rw [factChanges_stored (hgiv b hb) hpres']
    exact mem_addInverses.mpr ⟨t, ht, e, (mem_evalMatches_conj hu (names_eq_of_unknowns hu ▸ hnd)).mpr ⟨he, he'⟩,
      (hwf.project_agreeOff hag).symm⟩
  · intro h1 h2
    obtain ⟨e3, he3, rfl⟩ := List.mem_map.mp h1
    have hn3 : e3 ∉ evalMatches (g ++ B) _ s.matchList := fun h => h2 (List.mem_map.mpr ⟨e3, h, rfl⟩)
    obtain ⟨b, hb, t, ht, e, he, hag⟩ := lostMatches hf s.matchList (pinOnly_restrict hgiv)
      hwf.pin_unused hwf.pin_undeclared he3 hn3
    obtain ⟨tl, htl, hetl⟩ := lost_test hf s.matchList (pinOnly_restrict hgiv)
      hwf.pin_unused hwf.pin_undeclared he3 hn3
    have hu := touchMatches_unknowns ht
    have hul := removeTests_unknowns htl
    have he' := mem_evalMatches_pin (fun h => hwf.pin_unused (removeTests_used htl _ h))
      (names_eq_of_unknowns hul ▸ hnp) (names_eq_of_unknowns hu ▸ hnp) hetl he hag
    refine List.mem_flatMap.mpr ⟨b, hb, ?_⟩
    rw [factChanges_stored (hgiv b hb) hpres']
    exact mem_removeInverses.mpr ⟨t, ht, tl, htl, e,
      (mem_evalMatches_conj (hu.trans hul.symm) (names_eq_of_unknowns hu ▸ hnd)).mpr ⟨he, he'⟩,
      (hwf.project_agreeOff hag).symm⟩

/-! ## Exact -/

/-- **`exact_correct`.** Start from a held set that equals the result on `g`.
Apply a fresh batch's adds and removes: the held set is then exactly the
result on `g ++ B`, with no second read. -/
theorem exact_correct (hwf : WellFormed s) (hpu : ProjectsUnknowns s) (hf : Fresh g B)
    (held : List Row) (hheld : ∀ r, r ∈ held ↔ r ∈ s.read g env) (r : Row) :
    r ∈ applyChanges (changes s env g B).1 (changes s env g B).2 held ↔ r ∈ s.read (g ++ B) env := by
  have hc := changes_complete (env := env) hwf hf r
  have ha := adds_sound (env := env) (g := g) (B := B) (r := r) hwf
  have hr := removes_sound (env := env) (g := g) (B := B) (r := r) hwf hpu
  simp only [applyChanges, List.mem_append, List.mem_filter, hheld, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not]
  by_cases h1 : r ∈ s.read g env <;> by_cases h2 : r ∈ s.read (g ++ B) env <;> simp_all

end

/-- **An exact stream is its specification's result.** Start from a read of
the result, and after each batch arrives apply its adds and removes: the
stream then holds exactly the specification's results on the replica's graph,
provided each batch is fresh when it arrives and the projection names every
top-level unknown. -/
theorem exact_stream_correct (s : Specification) (hwf : WellFormed s) (hpu : ProjectsUnknowns s)
    (env : Env) :
    ∀ (bs : List (List Fact)) (g : Graph) (held : List Row),
      (∀ r, r ∈ held ↔ r ∈ s.read g env) →
      (∀ pre B post, bs = pre ++ B :: post → Fresh (g ++ pre.flatten) B) →
      ∀ r, r ∈ (bs.foldl (exactStep s env) (g, held)).2 ↔ r ∈ s.read (g ++ bs.flatten) env :=
  fun bs g held hheld hfresh => advance_correct (s.read · env) _ bs g held hheld
    fun pre B post h _ hheld => exact_correct hwf hpu (hfresh pre B post h) _ hheld

end JinagaSpec
