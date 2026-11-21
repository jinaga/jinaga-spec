import JinagaSpec.Proofs.Defer

/-!
# The feeds cover the specification

`feeds_cover`: a replica that holds the givens and every fact the feeds
deliver on the replicator's graph, with their predecessors, reads what the
replicator reads. The replica is `g`, and what of the replicator's graph it
does not hold is `B`: a fresh batch to it, since a replica saves each fact with
its predecessors (`Fresh`, as for the stream).

1. **Normal form** (`nf`). A level has a solution exactly when its path
   conditions, with every positive condition joined in, have one at which each
   of its negative conditions has none.
2. **Two semantic inductions.** (A) A context valid on the replicator, whose
   valid cancellers are all delivered, is valid on the replica. (B) A context
   invalid on the replicator, whose first failing condition's valid witnesses
   are delivered, is invalid on the replica. Neither mentions a feed.
3. **The walk delivers both.** Restoring through a cancelled witness delivers its
   canceller (`pd_walk`); the excluding feed at the first condition that fails
   delivers its witnesses (`evd_walk`).
-/
namespace JinagaSpec

/-! ## Negative conditions can be checked at the end of a flat level -/

theorem allHold_flat_iff {G : Graph} {e : Env} {u : Name} :
    ∀ {cs : List Condition}, FlatConditions cs →
      (allHold G e u cs = true ↔ allHold G e u (cs.filter (·.isPath)) = true ∧
        ∀ ns, Condition.existential false ns ∈ cs → evalMatches G e ns = [])
  | [], _ => by simp [allHold]
  | c :: cs, hfl => by
    have ih := allHold_flat_iff (u := u) (e := e) (G := G) (cs := cs) fun d hd => hfl d (List.mem_cons_of_mem _ hd)
    rcases hfl c (List.mem_cons_self ..) with hp | ⟨ns, rfl⟩
    · cases c with
      | path pc =>
        simp only [allHold, List.filter_cons, Condition.isPath, ite_true, Bool.and_eq_true, ih, List.mem_cons,
          reduceCtorEq, false_or]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      | existential => simp [Condition.isPath] at hp
    · simp only [allHold, List.filter_cons, Condition.isPath, Bool.false_eq_true, ite_false, Bool.and_eq_true, ih,
        List.mem_cons, Condition.existential.injEq, true_and]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h2, fun n hn => ?_⟩
        rcases hn with rfl | hn
        · simp only [holds] at h1; cases h : evalMatches G e n <;> simp_all
        · exact h3 n hn
      · rintro ⟨h2, h3⟩
        refine ⟨?_, h2, fun n hn => h3 n (Or.inr hn)⟩
        have := h3 ns (Or.inl rfl)
        simp [holds, this]

theorem negatives_cons (m : Match) (L : List Match) :
    (m :: L).flatMap Match.negatives = m.negatives ++ L.flatMap Match.negatives := rfl

/-- In a flat level, scoped and binding each label once, a solution is a
solution of the path conditions at which every negative condition has none. -/
theorem flat_end {G : Graph} : ∀ (L : List Match) (S : List Name) (e σ : Env),
    Flat L → ScopedMatches S L → (names L).Nodup → (∀ x ∈ names L, x ∉ S) →
    (σ ∈ evalMatches G e L ↔ σ ∈ evalMatches G e (L.map Match.paths) ∧
      ∀ ns ∈ L.flatMap Match.negatives, evalMatches G σ ns = [])
  | [], _, _, _, _, _, _, _ => by simp [evalMatches]
  | .mk u cs :: L, S, e, σ, hfl, ⟨hcs, hL⟩, hnd, hdis => by
    have hnd' : u.name ∉ names L ∧ (names L).Nodup := by simpa [names] using hnd
    have hdis' : ∀ x ∈ names L, x ∉ u.name :: S := by
      intro x hx hxS
      rcases List.mem_cons.mp hxS with rfl | hxS
      · exact hnd'.1 hx
      · exact hdis x (by simp [names] at hx ⊢; exact Or.inr hx) hxS
    have hflc : FlatConditions cs := hfl _ (List.mem_cons_self ..)
    have hflL : Flat L := fun m hm => hfl m (List.mem_cons_of_mem _ hm)
    -- A negative condition of this match reads the same where it is checked as at the end.
    have hneg : ∀ (f : Fact) (σ : Env), σ ∈ evalMatches G (e.bind u.name f.id) (L.map Match.paths) →
        ∀ ns ∈ (Match.mk u cs).negatives,
          (evalMatches G (e.bind u.name f.id) ns = [] ↔ evalMatches G σ ns = []) := by
      intro f σ hσ ns hns
      have hag : Agree (u.name :: S) (e.bind u.name f.id) σ := fun x hx =>
        (evalMatches_frame hσ x (show x ∉ names (L.map Match.paths) by
          rw [names_paths]; exact fun hm => hdis' x hm hx)).symm
      have hsc := scopedConditions_mem hcs (Match.mem_negatives.mp hns)
      have := holds_agree G (.existential false ns) u.name S _ σ hsc hag
      simp only [holds] at this
      cases h1 : evalMatches G (e.bind u.name f.id) ns <;> cases h2 : evalMatches G σ ns <;> simp_all
    constructor
    · intro h
      obtain ⟨f, hf, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
      obtain ⟨hp, hn'⟩ := (allHold_flat_iff hflc).mp hc
      have hn : ∀ ns ∈ (Match.mk u cs).negatives, evalMatches G (e.bind u.name f.id) ns = [] :=
        fun ns hns => hn' ns (Match.mem_negatives.mp hns)
      obtain ⟨hr1, hr2⟩ := (flat_end L _ _ σ hflL hL hnd'.2 hdis').mp hr
      refine ⟨mem_evalMatches_cons.mpr ⟨f, hf, ht, hp, hr1⟩, fun ns hns => ?_⟩
      rw [negatives_cons] at hns
      rcases List.mem_append.mp hns with hns | hns
      · exact (hneg f σ hr1 ns hns).mp (hn ns hns)
      · exact hr2 ns hns
    · rintro ⟨h, hn⟩
      obtain ⟨f, hf, ht, hp, hr⟩ := mem_evalMatches_cons.mp h
      refine mem_evalMatches_cons.mpr ⟨f, hf, ht, (allHold_flat_iff hflc).mpr ⟨hp, fun ns hns =>
        (hneg f σ hr ns (Match.mem_negatives.mpr hns)).mpr
          (hn ns (by rw [negatives_cons]; exact List.mem_append_left _ (Match.mem_negatives.mpr hns)))⟩, ?_⟩
      exact (flat_end L _ _ σ hflL hL hnd'.2 hdis').mpr ⟨hr, fun ns hns =>
        hn ns (by rw [negatives_cons]; exact List.mem_append_right _ hns)⟩

/-! ## Normal form -/

/-- Each negative condition of the level, joined, has no solution at `σ`. -/
def ValidL (G : Graph) (σ : Env) (ms : List Match) : Prop := ∀ ns ∈ negativesOf ms, evalMatches G σ ns = []

/-- **Normal form.** A level's solutions are, up to the labels of its own
matches, the solutions of its path conditions, positive conditions joined, at
which every negative condition has none. -/
theorem nf {G : Graph} {S : List Name} {ms : List Match} (hsc : ScopedMatches S ms) (hd : Distinct S ms) (e : Env) :
    (∀ σ ∈ evalMatches G e ms, ∃ σ' ∈ evalMatches G e (level ms), ValidL G σ' ms ∧ Agree (names ms) σ σ') ∧
    (∀ σ' ∈ evalMatches G e (level ms), ValidL G σ' ms → ∃ σ ∈ evalMatches G e ms, Agree (names ms) σ σ') := by
  obtain ⟨hnd, hdis, -⟩ := hd.flat
  have hfc := flatten_correct (G := G) (lift := fun _ => true) ms S e hsc hnd hdis
  have hfe := fun σ => flat_end (G := G) (flatten ms) S e σ (flatten_flat ms) (flatten_scoped ms S hsc) hnd hdis
  refine ⟨fun σ h => ?_, fun σ' h hv => ?_⟩
  · obtain ⟨σ', h', ag⟩ := hfc.1 σ h
    obtain ⟨hp, hn⟩ := (hfe σ').mp h'
    exact ⟨σ', hp, hn, ag⟩
  · obtain ⟨σ, hσ, ag⟩ := hfc.2 σ' ((hfe σ').mpr ⟨h, hv⟩)
    exact ⟨σ, hσ, ag⟩

theorem nf_empty {G : Graph} {S : List Name} {ms : List Match} (hsc : ScopedMatches S ms) (hd : Distinct S ms)
    (e : Env) : evalMatches G e ms = [] ↔ ∀ σ' ∈ evalMatches G e (level ms), ¬ ValidL G σ' ms := by
  constructor
  · intro h σ' hσ' hv
    obtain ⟨σ, hσ, -⟩ := (nf hsc hd e).2 σ' hσ' hv
    simp [h] at hσ
  · intro h
    refine List.eq_nil_iff_forall_not_mem.mpr fun σ hσ => ?_
    obtain ⟨σ', hσ', hv, -⟩ := (nf hsc hd e).1 σ hσ
    exact h σ' hσ' hv

/-! ## What must be delivered -/

/-- The labels `L` bind facts outside `B`. -/
def SettledOn (B : List Fact) (L : List Name) (σ : Env) : Prop := ∀ x ∈ L, ∀ id, σ x = some id → Outside B id

theorem negativesOf_lt {ms N N' : List Match} (h1 : N ∈ negativesOf ms) (h2 : N' ∈ negativesOf N) :
    sizeOf N' < sizeOf ms := Nat.lt_trans (sizeOf_negativesOf _ h2) (sizeOf_negativesOf _ h1)

/-- **Positive delivery.** For each negative condition of the level at `σ`, each
witness, and each valid fact of one of the witness's own negative conditions, a
canceller: its facts are delivered, and so, recursively, are its own. -/
def PD (G : Graph) (B : List Fact) (σ : Env) (ms : List Match) : Prop :=
  ∀ N ∈ negativesOf ms, ∀ x ∈ evalMatches G σ (level N), ∀ N' ∈ negativesOf N, ∀ y ∈ evalMatches G x (level N'),
    ValidL G y N' → SettledOn B (names (level N')) y ∧ PD G B y N'
termination_by sizeOf ms
decreasing_by exact negativesOf_lt ‹_› ‹_›

/-- **Evidence delivery.** At the first negative condition of the level that
fails at `σ`, each valid witness is delivered, and, at each solution of one of
its negative conditions' path conditions, so recursively is its evidence. -/
def EvD (G : Graph) (B : List Fact) (σ : Env) (ms : List Match) : Prop :=
  ∀ L1 N L2, negativesOf ms = L1 ++ N :: L2 → (∀ N0 ∈ L1, evalMatches G σ N0 = []) → evalMatches G σ N ≠ [] →
    ∀ x ∈ evalMatches G σ (level N), ValidL G x N →
      SettledOn B (names (level N)) x ∧ ∀ N' ∈ negativesOf N, ∀ y ∈ evalMatches G x (level N'), EvD G B y N'
termination_by sizeOf ms
decreasing_by
  have : N ∈ negativesOf ms := by rw [‹negativesOf ms = _›]; simp
  exact negativesOf_lt this ‹_›

/-! ## The two semantic inductions -/

section Semantic
variable {g : Graph} {B : List Fact}

/-- Solutions read on the replica bind only what it holds. -/
theorem settled_eval (hf : Fresh g B) : ∀ {L : List Match} {σ x : Env}, Settled B σ →
    x ∈ evalMatches g σ L → Settled B x
  | [], _, _, h, hx => by simp [evalMatches] at hx; exact hx ▸ h
  | .mk u cs :: L, σ, x, h, hx => by
    obtain ⟨f, hf', -, -, hr⟩ := mem_evalMatches_cons.mp hx
    exact settled_eval hf (h.bind fun b hb => hf.idNew f hf' b hb) hr

theorem settled_of_on {σ x : Env} {L : List Match} (hσ : Settled B σ) {G : Graph} (hx : x ∈ evalMatches G σ L)
    (hon : SettledOn B (names L) x) : Settled B x := by
  intro n id hn
  by_cases hm : n ∈ names L
  · exact hon n hm id hn
  · exact hσ n id (by rw [← evalMatches_frame hx n hm]; exact hn)

theorem distinct_negativesOf {S : List Name} {ms N : List Match} (hd : Distinct S ms) (hN : N ∈ negativesOf ms) :
    Distinct (S ++ names (level ms)) N := by
  obtain ⟨-, -, h⟩ := hd.flat
  obtain ⟨m, hm, hn⟩ := List.mem_flatMap.mp hN
  exact h m hm N hn _ fun x hx => by
    rw [List.mem_append, names_level] at hx; exact hx.symm

theorem nodup_level {S : List Name} {ms : List Match} (hd : Distinct S ms) : (names (level ms)).Nodup := by
  rw [names_level]; exact hd.flat.1

/-- **(A)** A context valid on the replicator, held by the replica, all of whose
valid cancellers are delivered, is valid on the replica. -/
theorem semA (hf : Fresh g B) : ∀ (ms : List Match) (S : List Name) (σ : Env), ScopedMatches S ms → Distinct S ms →
    Settled B σ → ValidL (g ++ B) σ ms → PD (g ++ B) B σ ms → ValidL g σ ms := by
  intro ms S σ hsc hd hσ hv hpd N hN
  have hscN := scoped_negativesOf hsc hN
  have hdN := distinct_negativesOf hd hN
  refine (nf_empty hscN hdN σ).mpr fun x hx hvx => ?_
  have hxG := evalMatches_paths_mono hf (pathsOnly_paths _) hσ hx
  have hxS := settled_eval hf hσ hx
  -- On the replicator the witness is cancelled: some condition of its level has a valid fact.
  obtain ⟨N', hN', hne⟩ : ∃ N' ∈ negativesOf N, evalMatches (g ++ B) x N' ≠ [] := by
    have := (nf_empty hscN hdN σ).mp (hv N hN) x hxG
    exact Classical.byContradiction fun hc => this fun N' hN' => Classical.byContradiction fun h => hc ⟨N', hN', h⟩
  have hscN' := scoped_negativesOf hscN hN'
  have hdN' := distinct_negativesOf hdN hN'
  obtain ⟨ρ, hρ⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨y, hy, hvy, -⟩ := (nf hscN' hdN' x).1 ρ hρ
  rw [PD] at hpd
  obtain ⟨hon, hpdy⟩ := hpd N hN x hxG N' hN' y hy hvy
  have hyS := settled_of_on hxS hy hon
  have hyg := evalMatches_paths_antitone hf (pathsOnly_paths _).shape (nodup_level hdN') hxS hy hyS
  have := semA hf N' _ y hscN' hdN' hyS hvy hpdy
  obtain ⟨ρ', hρ', -⟩ := (nf hscN' hdN' x).2 y hyg this
  have := hvx N' hN'
  simp [this] at hρ'
termination_by ms => sizeOf ms
decreasing_by exact negativesOf_lt ‹_› ‹_›

theorem first_failing {α : Type} (P : α → Prop) : ∀ (L : List α), ¬ (∀ a ∈ L, P a) →
    ∃ L1 a L2, L = L1 ++ a :: L2 ∧ (∀ b ∈ L1, P b) ∧ ¬ P a
  | [], h => absurd (fun _ h => by simp at h) h
  | a :: L, h => by
    by_cases ha : P a
    · have hL : ¬ ∀ c ∈ L, P c := fun hL => h fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ha
        · exact hL c hc
      obtain ⟨L1, b, L2, rfl, h1, h2⟩ := first_failing P L hL
      refine ⟨a :: L1, b, L2, rfl, fun c hc => ?_, h2⟩
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ha
      · exact h1 c hc
    · exact ⟨[], a, L, rfl, by simp, ha⟩

/-- **(B)** A context held by the replica and invalid on the replicator, whose
first failing condition's valid witnesses are delivered, is invalid on the
replica. -/
theorem semB (hf : Fresh g B) : ∀ (ms : List Match) (S : List Name) (σ : Env), ScopedMatches S ms → Distinct S ms →
    Settled B σ → ¬ ValidL (g ++ B) σ ms → EvD (g ++ B) B σ ms → ¬ ValidL g σ ms := by
  intro ms S σ hsc hd hσ hnv hevd hvg
  obtain ⟨L1, N, L2, hL, h1, hN⟩ := first_failing (fun N => evalMatches (g ++ B) σ N = []) _ hnv
  have hNm : N ∈ negativesOf ms := by rw [hL]; simp
  have hscN := scoped_negativesOf hsc hNm
  have hdN := distinct_negativesOf hd hNm
  obtain ⟨ρ, hρ⟩ := List.exists_mem_of_ne_nil _ hN
  obtain ⟨x, hx, hvx, -⟩ := (nf hscN hdN σ).1 ρ hρ
  rw [EvD] at hevd
  obtain ⟨hon, hev⟩ := hevd L1 N L2 hL h1 hN x hx hvx
  have hxS := settled_of_on hσ hx hon
  have hxg := evalMatches_paths_antitone hf (pathsOnly_paths _).shape (nodup_level hdN) hσ hx hxS
  -- The witness is valid on the replica too.
  have hvxg : ValidL g x N := by
    intro N' hN'
    have hscN' := scoped_negativesOf hscN hN'
    have hdN' := distinct_negativesOf hdN hN'
    refine (nf_empty hscN' hdN' x).mpr fun y hy hvy => ?_
    have hyG := evalMatches_paths_mono hf (pathsOnly_paths _) hxS hy
    have hyS := settled_eval hf hxS hy
    have hnvy := (nf_empty hscN' hdN' x).mp (hvx N' hN') y hyG
    exact semB hf N' _ y hscN' hdN' hyS hnvy (hev N' hN' y hyG) hvy
  obtain ⟨ρ', hρ', -⟩ := (nf hscN hdN σ).2 x hxg hvxg
  have := hvg N hNm
  simp [this] at hρ'
termination_by ms => sizeOf ms
decreasing_by exact negativesOf_lt ‹_› ‹_›

end Semantic

end JinagaSpec
