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

/-! ## Walking the feeds -/

section Walk
variable {G : Graph} {env : Env} (Out : List (List Match))

/-- Every feed the walk from `Q`, with `negs` to walk, produces is in `Out`. -/
def Reached (k : List Match → List (List Match)) (Q : List Match) (negs : List (List Match)) : Prop :=
  ∀ F ∈ negFeeds k Q negs, F ∈ Out

def ReachedL (k : List Match → List (List Match)) (P ms : List Match) : Prop :=
  ∀ F ∈ levelFeeds k P ms, F ∈ Out

variable {Out}

theorem ReachedL.unit {k : List Match → List (List Match)} {P : List Match} {m : Match} {rest : List Match}
    (h : ReachedL Out k P (m :: rest)) :
    Reached Out (fun Q => levelFeeds k Q rest) (P ++ level [m]) (negativesOf [m]) := by
  intro F hF; exact h F (by rw [levelFeeds]; exact hF)

theorem ReachedL.done {k : List Match → List (List Match)} {P : List Match} (h : ReachedL Out k P []) :
    ∀ F ∈ k P, F ∈ Out := fun F hF => h F (by rw [levelFeeds]; exact hF)

theorem Reached.done {k : List Match → List (List Match)} {Q : List Match} (h : Reached Out k Q []) :
    ∀ F ∈ k Q, F ∈ Out := fun F hF => h F (by rw [negFeeds]; exact hF)

theorem Reached.emit {k : List Match → List (List Match)} {Q N : List Match} {rest : List (List Match)}
    (h : Reached Out k Q (N :: rest)) : Q ++ level N ∈ Out := h _ (by rw [negFeeds]; exact List.mem_cons_self ..)

theorem Reached.filter {k : List Match → List (List Match)} {Q N : List Match} {rest : List (List Match)}
    (h : Reached Out k Q (N :: rest)) : Reached Out k (addLast (.existential false (level N)) Q) rest :=
  fun F hF => h F (by rw [negFeeds]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hF))

theorem Reached.restore {k : List Match → List (List Match)} {Q N N' : List Match} {rest : List (List Match)}
    (h : Reached Out k Q (N :: rest)) (hN' : N' ∈ negativesOf N) :
    ReachedL Out (fun Q' => negFeeds k Q' rest) (Q ++ level N) N' :=
  fun F hF => h F (by
    rw [negFeeds]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨N', hN'⟩, List.mem_attach .., hF⟩)))

end Walk

/-- A filter on the last match keeps each solution at which it holds. -/
theorem mem_addLast_of {G : Graph} {ns : List Match} :
    ∀ {Q : List Match} {e σ : Env}, σ ∈ evalMatches G e Q → evalMatches G σ ns = [] →
      σ ∈ evalMatches G e (addLast (.existential false ns) Q)
  | [], _, _, h, _ => by simpa [addLast] using h
  | [.mk u cs], e, σ, h, hn => by
    simp only [addLast, Match.addCondition]
    obtain ⟨f, hf, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
    simp only [evalMatches, List.mem_singleton] at hr
    subst hr
    refine mem_evalMatches_cons.mpr ⟨f, hf, ht, ?_, by simp [evalMatches]⟩
    rw [allHold_append]
    simp [hc, allHold, holds, hn]
  | m :: m' :: ms, e, σ, h, hn => by
    rw [show addLast (.existential false ns) (m :: m' :: ms) = m :: addLast (.existential false ns) (m' :: ms) from rfl]
    obtain ⟨u, cs⟩ := m
    obtain ⟨f, hf, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
    exact mem_evalMatches_cons.mpr ⟨f, hf, ht, hc, mem_addLast_of hr hn⟩

/-- The walk can pass a negative condition at `τ`: it has no witness, and the
feed is filtered by it, or a witness has a valid canceller, and the feed is
restored through it. -/
def Choosable (G : Graph) (τ : Env) (N : List Match) : Prop :=
  evalMatches G τ (level N) = [] ∨
    ∃ x ∈ evalMatches G τ (level N), ∃ N' ∈ negativesOf N, ∃ y ∈ evalMatches G x (level N'), ValidL G y N'

/-- A negative condition that holds can be passed. -/
theorem choosable_of_holds {G : Graph} {S : List Name} {N : List Match} (hsc : ScopedMatches S N) (hd : Distinct S N)
    {τ : Env} (h : evalMatches G τ N = []) : Choosable G τ N := by
  cases hx : evalMatches G τ (level N) with
  | nil => exact Or.inl hx
  | cons x _ =>
    have hxm : x ∈ evalMatches G τ (level N) := by rw [hx]; exact List.mem_cons_self ..
    have hnv := (nf_empty hsc hd τ).mp h x hxm
    obtain ⟨N', hN', hne⟩ : ∃ N' ∈ negativesOf N, evalMatches G x N' ≠ [] :=
      Classical.byContradiction fun hc => hnv fun N' hN' => Classical.byContradiction fun h => hc ⟨N', hN', h⟩
    have hsc' := scoped_negativesOf hsc hN'
    have hd' := distinct_negativesOf hd hN'
    obtain ⟨ρ, hρ⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨y, hy, hvy, -⟩ := (nf hsc' hd' x).1 ρ hρ
    exact Or.inr ⟨x, hxm, N', hN', y, hy, hvy⟩

/-! ## Moving along agreeing environments -/

theorem empty_agree {G : Graph} {S : List Name} {e e' : Env} {L : List Match} (hag : Agree S e e')
    (hsc : ScopedMatches S L) (h : evalMatches G e L = []) : evalMatches G e' L = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
    obtain ⟨x', hx', -⟩ := evalMatches_agree G L S e' e hsc hag.symm x hx
    simp [h] at hx'

theorem validL_agree {G : Graph} {S : List Name} {e e' : Env} {ms : List Match} (hag : Agree S e e')
    (hsc : ∀ N ∈ negativesOf ms, ScopedMatches S N) (h : ValidL G e ms) : ValidL G e' ms :=
  fun N hN => empty_agree hag (hsc N hN) (h N hN)

theorem choosable_agree {G : Graph} {S : List Name} {τ τ' : Env} {N : List Match} (hag : Agree S τ τ')
    (hsc : ScopedMatches S N) (h : Choosable G τ N) : Choosable G τ' N := by
  have hL := scoped_level hsc
  rcases h with h | ⟨x, hx, N', hN', y, hy, hvy⟩
  · exact Or.inl (empty_agree hag hL h)
  · obtain ⟨x', hx', ax⟩ := evalMatches_agree G _ S τ τ' hL hag x hx
    have hsc' := scoped_negativesOf hsc hN'
    obtain ⟨y', hy', ay⟩ := evalMatches_agree G _ (S ++ names (level N)) x x' (scoped_level hsc') ax y hy
    exact Or.inr ⟨x', hx', N', hN', y', hy', validL_agree ay (fun N'' hN'' => scoped_negativesOf hsc' hN'') hvy⟩

/-- A negative condition of a level being walked has the labels it needs. -/
theorem distinct_of_hygiene {G0 : List Name} {P ms N : List Match} (h : Hygiene G0 P [ms]) (hN : N ∈ negativesOf ms) :
    Distinct (G0 ++ names P ++ names (level ms)) N := by
  have hw : Within (names P ++ names (level ms) ++ declaredMatches N) (names P ++ [ms].flatMap declaredMatches) := by
    intro x; have := within_level ms x; have := within_negative hN x
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *; omega
  have hnd := nodup_within hw h.nodup
  refine ⟨(List.nodup_append.mp hnd).2.1, fun x hx hxS => ?_⟩
  rcases List.mem_append.mp hxS with hxS | hxS
  · rcases List.mem_append.mp hxS with hxS | hxS
    · exact h.ordinary x (mem_within hw (List.mem_append_right _ hx)) hxS
    · exact (List.nodup_append.mp hnd).2.2 x (List.mem_append_left _ hxS) x hx rfl
  · exact (List.nodup_append.mp hnd).2.2 x (List.mem_append_right _ hxS) x hx rfl

/-! ## The walk completes a context it can pass -/

section Complete
variable {G : Graph} {env : Env} {Out : List (List Match)}

/-- A partial feed handed on to `k`, with a tuple that goes on from `τ`. -/
structure Completion (G : Graph) (env : Env) (Out : List (List Match)) (k : List Match → List (List Match))
    (start : List Match) (bound : List Name) (τ : Env) (Q' : List Match) (τ' : Env) : Prop where
  reached : ∀ F ∈ k Q', F ∈ Out
  mem : τ' ∈ evalMatches G env Q'
  agree : Agree (names start) τ τ'
  grows : ∀ x ∈ names start, x ∈ names Q'
  within : Within (names Q') (names start ++ bound)

mutual
  theorem walk_level (G0 : List Name) (k : List Match → List (List Match)) :
      ∀ (P ms : List Match) (τP σ : Env), ReachedL Out k P ms → Hygiene G0 P [ms] → τP ∈ evalMatches G env P →
        σ ∈ evalMatches G τP (level ms) → (∀ N ∈ negativesOf ms, Choosable G σ N) →
        ∃ Q' τ', Completion G env Out k P (declaredMatches ms) τP Q' τ' ∧ Agree (names (level ms)) σ τ' ∧
          ∀ x ∈ names (level ms), x ∈ names Q'
    | P, [], τP, σ, hR, _, hτP, hσ, _ => by
      simp [level, flatten, flattenMatches, evalMatches] at hσ; subst σ
      exact ⟨P, τP, ⟨hR.done, hτP, fun _ _ => rfl, fun _ h => h, fun x => by simp⟩,
        fun x hx => by simp [level, flatten, flattenMatches, names] at hx, fun x hx => by
          simp [level, flatten, flattenMatches, names] at hx⟩
    | P, m :: rest, τP, σ, hR, h, hτP, hσ, hch => by
      have hu := hygiene_unit h
      rw [show m :: rest = [m] ++ rest from rfl, level_append] at hσ
      obtain ⟨σ1, hσ1, hσr⟩ := mem_evalMatches_append.mp hσ
      have hσ1P : σ1 ∈ evalMatches G env (P ++ level [m]) := mem_evalMatches_append.mpr ⟨τP, hτP, hσ1⟩
      have hwr : Within (names (P ++ level [m]) ++ names (level rest)) (names P ++ declaredMatches (m :: rest)) := by
        intro x; have := within_level [m] x; have := within_level rest x; have := declared_cons m rest x
        simp only [names_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *
        omega
      have hdisR := disjoint_of_nodup hwr (by simpa using h.nodup)
      have hdisU : ∀ x ∈ names (level [m]), x ∉ names P := by
        have : Within (names P ++ names (level [m])) (names P ++ declaredMatches (m :: rest)) := by
          intro x; have := hwr x; simp only [names_append, List.count_append] at *; omega
        exact disjoint_of_nodup this (by simpa using h.nodup)
      have hordU : ∀ x ∈ names (P ++ level [m]), x ∉ G0 := fun x hx =>
        hu.ordinary x (List.mem_append_left _ hx)
      -- σ and the unit's tuple agree on everything the unit's conditions name.
      have hagU : Agree (G0 ++ names (P ++ level [m])) σ σ1 := fun x hx =>
        evalMatches_frame hσr x fun hm => by
          rcases List.mem_append.mp hx with hx | hx
          · exact h.ordinary x (by
              have := mem_within hwr (List.mem_append_right _ hm)
              simpa using this) hx
          · exact hdisR x hm hx
      have hchU : ∀ N ∈ negativesOf [m], Choosable G σ1 N := fun N hN =>
        choosable_agree hagU (hu.inScope N hN) (hch N (by
          rw [show m :: rest = [m] ++ rest from rfl, negativesOf_append]; exact List.mem_append_left _ hN))
      obtain ⟨Q1, τ1, c1⟩ := walk_neg G0 _ _ _ _ hR.unit hu (by simp [level_ne_nil]) hσ1P hchU
      have h2 := hygiene_rest h c1.within c1.grows
      -- Move the rest of σ to the walk's tuple.
      have hscR : ScopedMatches (G0 ++ names (P ++ level [m])) (level rest) := by
        have := h.inScope _ (List.mem_singleton_self _)
        obtain ⟨u, cs⟩ := m
        refine scoped_level (scopedMatches_mono _ _ _ (fun x hx => ?_) this.2)
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_right _ (mem_names_level u cs))
        · rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append_left _ hx
          · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_left _ hx)
      have hag1 : Agree (G0 ++ names (P ++ level [m])) σ1 τ1 := fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact agree_outside hσ1P c1.mem hordU (fun y hy => h2.ordinary y (List.mem_append_left _ hy)) x hx
        · exact c1.agree x hx
      obtain ⟨σ', hσ', ag'⟩ := evalMatches_agree G _ _ σ1 τ1 hscR hag1 σ hσr
      -- The rest's negative conditions name only what comes before them and the rest's own labels.
      have hscRN : ∀ N ∈ negativesOf rest, ScopedMatches (G0 ++ names (P ++ level [m]) ++ names (level rest)) N := by
        intro N hN
        have := h.inScope _ (List.mem_singleton_self _)
        obtain ⟨u, cs⟩ := m
        refine scoped_negativesOf (scopedMatches_mono _ _ _ (fun x hx => ?_) this.2) hN
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_right _ (mem_names_level u cs))
        · rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append_left _ hx
          · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_left _ hx)
      have hchR : ∀ N ∈ negativesOf rest, Choosable G σ' N := fun N hN =>
        choosable_agree ag' (hscRN N hN) (hch N (by
          rw [show m :: rest = [m] ++ rest from rfl, negativesOf_append]; exact List.mem_append_right _ hN))
      have hR2 : ReachedL Out k Q1 rest := c1.reached
      obtain ⟨Q', τ', c2, ag2, gr2⟩ := walk_level G0 k Q1 rest τ1 σ' hR2 h2 c1.mem hσ' hchR
      refine ⟨Q', τ', ⟨c2.reached, c2.mem, fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
      · have hx1 : x ∈ names (P ++ level [m]) := by rw [names_append]; exact List.mem_append_left _ hx
        exact (evalMatches_frame hσ1 x fun hm => hdisU x hm hx).symm.trans
          ((c1.agree x hx1).trans (c2.agree x (c1.grows x hx1)))
      · exact c2.grows x (c1.grows x (by rw [names_append]; exact List.mem_append_left _ hx))
      · have := c2.within x; have := c1.within x; have := within_level [m] x; have := declared_cons m rest x
        simp only [names_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *
        omega
      · rw [show m :: rest = [m] ++ rest from rfl, level_append, names_append] at hx
        rcases List.mem_append.mp hx with hx | hx
        · have hx1 : x ∈ names (P ++ level [m]) := by rw [names_append]; exact List.mem_append_right _ hx
          rw [evalMatches_frame hσr x fun hm => hdisR x hm hx1]
          exact (c1.agree x hx1).trans (c2.agree x (c1.grows x hx1))
        · exact (ag' x (List.mem_append_right _ hx)).trans (ag2 x hx)
      · rw [show m :: rest = [m] ++ rest from rfl, level_append, names_append] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact c2.grows x (c1.grows x (by rw [names_append]; exact List.mem_append_right _ hx))
        · exact gr2 x hx
  termination_by _ ms => (sizeOf ms, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | (apply Prod.Lex.left
         have := maxSize_lt (b := sizeOf (m :: rest)) (by simp; omega) fun p hp => sizeOf_negativesOf_unit p hp
         simpa using this)
      | (apply Prod.Lex.left; omega)

  theorem walk_neg (G0 : List Name) (k : List Match → List (List Match)) :
      ∀ (Q : List Match) (negs : List (List Match)) (τ : Env), Reached Out k Q negs → Hygiene G0 Q negs → Q ≠ [] →
        τ ∈ evalMatches G env Q → (∀ N ∈ negs, Choosable G τ N) →
        ∃ Q' τ', Completion G env Out k Q (negs.flatMap declaredMatches) τ Q' τ'
    | Q, [], τ, hR, _, _, hτ, _ =>
      ⟨Q, τ, ⟨hR.done, hτ, fun _ _ => rfl, fun _ h => h, fun x => by simp⟩⟩
    | Q, N :: rest, τ, hR, h, hQ, hτ, hch => by
      have hwl : Within (names (Q ++ level N)) (names Q ++ (N :: rest).flatMap declaredMatches) := by
        intro x; have := within_level N x
        simp only [names_append, List.flatMap_cons, List.count_append] at *; omega
      have hdisL : ∀ x ∈ names (level N), x ∉ names Q := by
        rw [names_append] at hwl
        exact disjoint_of_nodup hwl h.nodup
      rcases hch N (List.mem_cons_self ..) with hn | ⟨x, hx, N', hN', y, hy, hvy⟩
      · -- Filtered.
        have hQf : addLast (.existential false (level N)) Q ≠ [] := fun he =>
          names_ne_nil hQ (by rw [← names_addLast (.existential false (level N)) Q, he]; rfl)
        obtain ⟨Q', τ', c⟩ := walk_neg G0 k _ rest τ hR.filter (hygiene_filter h) hQf (mem_addLast_of hτ hn)
          fun N hN => hch N (List.mem_cons_of_mem _ hN)
        refine ⟨Q', τ', ⟨c.reached, c.mem, fun x hx => c.agree x (by rwa [names_addLast]),
          fun x hx => c.grows x (by rwa [names_addLast]), fun x => ?_⟩⟩
        have := c.within x; rw [names_addLast] at this
        simp only [List.flatMap_cons, List.count_append] at *; omega
      · -- Restored, through a valid canceller of a witness.
        have hr := hygiene_restore h hN'
        have hxQ : x ∈ evalMatches G env (Q ++ level N) := mem_evalMatches_append.mpr ⟨τ, hτ, hx⟩
        have hscN' := hr.inScope N' (List.mem_singleton_self _)
        have hchN' : ∀ N'' ∈ negativesOf N', Choosable G y N'' := fun N'' hN'' =>
          choosable_of_holds (scoped_negativesOf hscN' hN'') (by
            have := distinct_of_hygiene hr hN''
            simpa [List.append_assoc] using this) (hvy N'' hN'')
        obtain ⟨Q'', τ'', c1, -, -⟩ := walk_level G0 _ _ N' x y (hR.restore hN') hr hxQ hy hchN'
        have hgQ : ∀ z ∈ names Q, z ∈ names Q'' := fun z hz =>
          c1.grows z (by rw [names_append]; exact List.mem_append_left _ hz)
        have hne : Q'' ≠ [] := ne_nil_of_names hQ hgQ
        have h2 := hygiene_after_restore h hN' c1.within hgQ
        have hagQ : Agree (G0 ++ names Q) τ τ'' := fun z hz => by
          rcases List.mem_append.mp hz with hz | hz
          · exact agree_outside hτ c1.mem (fun w hw => h.ordinary w (List.mem_append_left _ hw))
              (fun w hw => h2.ordinary w (List.mem_append_left _ hw)) z hz
          · exact (evalMatches_frame hx z fun hm => hdisL z hm hz).symm.trans
              (c1.agree z (by rw [names_append]; exact List.mem_append_left _ hz))
        obtain ⟨Q', τ', c⟩ := walk_neg G0 k Q'' rest τ'' c1.reached h2 hne c1.mem fun N2 hN2 =>
          choosable_agree hagQ (h.inScope N2 (List.mem_cons_of_mem _ hN2)) (hch N2 (List.mem_cons_of_mem _ hN2))
        refine ⟨Q', τ', ⟨c.reached, c.mem, fun z hz => (hagQ z (List.mem_append_right _ hz)).trans (c.agree z (hgQ z hz)),
          fun z hz => c.grows z (hgQ z hz), fun z => ?_⟩⟩
        have := c.within z; have := c1.within z; have := within_level N z; have := within_negative hN' z
        simp only [names_append, List.flatMap_cons, List.count_append] at *; omega
  termination_by _ negs => (maxSize negs, negs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact maxSize_lex _ _
      | exact Prod.Lex.left _ _ (Nat.lt_of_lt_of_le (sizeOf_negativesOf _ ‹_›) (le_maxSize (List.mem_cons_self ..)))
end

end Complete

/-! ## Delivery moves along agreeing environments -/

section Transfer
variable {G : Graph} {B : List Fact}

theorem settledOn_agree {L : List Name} {y y' : Env} (hag : Agree L y y') (h : SettledOn B L y) : SettledOn B L y' :=
  fun x hx id hid => h x hx id (by rw [hag x hx]; exact hid)

/-- Positive delivery at one negative condition, `PD`'s body. -/
def PDN (G : Graph) (B : List Fact) (σ : Env) (N : List Match) : Prop :=
  ∀ x ∈ evalMatches G σ (level N), ∀ N' ∈ negativesOf N, ∀ y ∈ evalMatches G x (level N'),
    ValidL G y N' → SettledOn B (names (level N')) y ∧ PD G B y N'

theorem pd_iff {σ : Env} {ms : List Match} : PD G B σ ms ↔ ∀ N ∈ negativesOf ms, PDN G B σ N := by
  rw [PD]; rfl

mutual
  theorem pdn_agree : ∀ (N : List Match) (T : List Name) (σ σ' : Env), ScopedMatches T N → Agree T σ σ' →
      PDN G B σ N → PDN G B σ' N
    | N, T, σ, σ', hsc, hag, h => by
      intro x' hx' N' hN' y' hy' hvy'
      have hL := scoped_level hsc
      obtain ⟨x, hx, ax⟩ := evalMatches_agree G _ T σ' σ hL hag.symm x' hx'
      have hsc' := scoped_negativesOf hsc hN'
      obtain ⟨y, hy, ay⟩ := evalMatches_agree G _ _ x' x (scoped_level hsc') ax y' hy'
      have hscN'' : ∀ N'' ∈ negativesOf N', ScopedMatches (T ++ names (level N) ++ names (level N')) N'' :=
        fun N'' hN'' => scoped_negativesOf hsc' hN''
      obtain ⟨hon, hpd⟩ := h x hx N' hN' y hy (validL_agree ay hscN'' hvy')
      refine ⟨settledOn_agree (fun z hz => (ay z (List.mem_append_right _ hz)).symm) hon, ?_⟩
      exact pd_agree N' _ y y' hscN'' (fun z hz => (ay z hz).symm) hpd
  termination_by N => (sizeOf N, 1)
  decreasing_by all_goals (simp_wf; exact Prod.Lex.left _ _ (sizeOf_negativesOf _ ‹_›))

  theorem pd_agree : ∀ (ms : List Match) (T : List Name) (σ σ' : Env), (∀ N ∈ negativesOf ms, ScopedMatches T N) →
      Agree T σ σ' → PD G B σ ms → PD G B σ' ms
    | ms, T, σ, σ', hsc, hag, h =>
      pd_iff.mpr fun N hN => pdn_agree N T σ σ' (hsc N hN) hag (pd_iff.mp h N hN)
  termination_by ms => (sizeOf ms, 2)
  decreasing_by all_goals (simp_wf; exact Prod.Lex.left _ _ (sizeOf_negativesOf _ ‹_›))
end

theorem evd_agree : ∀ (ms : List Match) (T : List Name) (σ σ' : Env), (∀ N ∈ negativesOf ms, ScopedMatches T N) →
    Agree T σ σ' → EvD G B σ ms → EvD G B σ' ms := by
  intro ms T σ σ' hsc hag h
  rw [EvD] at h ⊢
  intro L1 N L2 hL h1 hN x' hx' hvx'
  have hNm : N ∈ negativesOf ms := by rw [hL]; simp
  have hscN := hsc N hNm
  have h1' : ∀ N0 ∈ L1, evalMatches G σ N0 = [] := fun N0 hN0 =>
    empty_agree hag.symm (hsc N0 (by rw [hL]; simp [hN0])) (h1 N0 hN0)
  have hN' : evalMatches G σ N ≠ [] := fun he => hN (empty_agree hag hscN he)
  obtain ⟨x, hx, ax⟩ := evalMatches_agree G _ T σ' σ (scoped_level hscN) hag.symm x' hx'
  have hvx : ValidL G x N := validL_agree ax (fun N'' hN'' => scoped_negativesOf hscN hN'') hvx'
  obtain ⟨hon, hev⟩ := h L1 N L2 hL h1' hN' x hx hvx
  refine ⟨settledOn_agree (fun z hz => (ax z (List.mem_append_right _ hz)).symm) hon, fun N' hN'' y' hy' => ?_⟩
  have hsc' := scoped_negativesOf hscN hN''
  obtain ⟨y, hy, ay⟩ := evalMatches_agree G _ _ x' x (scoped_level hsc') ax y' hy'
  exact evd_agree N' _ y y' (fun N2 hN2 => scoped_negativesOf hsc' hN2) (fun z hz => (ay z hz).symm) (hev N' hN'' y hy)
termination_by ms => sizeOf ms
decreasing_by exact negativesOf_lt ‹_› ‹_›

end Transfer

/-! ## One step of the walk -/

theorem distinct_of_hygieneN {G0 : List Name} {Q : List Match} {negs : List (List Match)} {N : List Match}
    (h : Hygiene G0 Q negs) (hN : N ∈ negs) : Distinct (G0 ++ names Q) N := by
  have hw : Within (names Q ++ declaredMatches N) (names Q ++ negs.flatMap declaredMatches) :=
    Within.append_left _ fun x => count_le_flatMap declaredMatches x hN
  have hnd := nodup_within hw h.nodup
  refine ⟨(List.nodup_append.mp hnd).2.1, fun x hx hxS => ?_⟩
  rcases List.mem_append.mp hxS with hxS | hxS
  · exact h.ordinary x (mem_within hw (List.mem_append_right _ hx)) hxS
  · exact (List.nodup_append.mp hnd).2.2 x hxS x hx rfl

section Step
variable {G : Graph} {env : Env} {Out : List (List Match)}

/-- Passing the first pending negative condition, which can be passed. -/
theorem walk_step (G0 : List Name) {k : List Match → List (List Match)} {Q N : List Match}
    {rest : List (List Match)} {τ : Env} (hR : Reached Out k Q (N :: rest)) (h : Hygiene G0 Q (N :: rest))
    (hQ : Q ≠ []) (hτ : τ ∈ evalMatches G env Q) (hch : Choosable G τ N) :
    ∃ Q' τ', Reached Out k Q' rest ∧ Hygiene G0 Q' rest ∧ Q' ≠ [] ∧ τ' ∈ evalMatches G env Q' ∧
      Agree (G0 ++ names Q) τ τ' ∧ (∀ x ∈ names Q, x ∈ names Q') ∧
      Within (names Q' ++ rest.flatMap declaredMatches) (names Q ++ (N :: rest).flatMap declaredMatches) := by
  have hwl : Within (names (Q ++ level N)) (names Q ++ (N :: rest).flatMap declaredMatches) := by
    intro x; have := within_level N x
    simp only [names_append, List.flatMap_cons, List.count_append] at *; omega
  have hdisL : ∀ x ∈ names (level N), x ∉ names Q := by
    rw [names_append] at hwl
    exact disjoint_of_nodup hwl h.nodup
  rcases hch with hn | ⟨x, hx, N', hN', y, hy, hvy⟩
  · have hQf : addLast (.existential false (level N)) Q ≠ [] := fun he =>
      names_ne_nil hQ (by rw [← names_addLast (.existential false (level N)) Q, he]; rfl)
    refine ⟨_, τ, hR.filter, hygiene_filter h, hQf, mem_addLast_of hτ hn, fun _ _ => rfl,
      fun x hx => by rwa [names_addLast], fun x => ?_⟩
    rw [names_addLast]; simp only [List.flatMap_cons, List.count_append]; omega
  · have hr := hygiene_restore h hN'
    have hxQ : x ∈ evalMatches G env (Q ++ level N) := mem_evalMatches_append.mpr ⟨τ, hτ, hx⟩
    have hscN' := hr.inScope N' (List.mem_singleton_self _)
    have hchN' : ∀ N'' ∈ negativesOf N', Choosable G y N'' := fun N'' hN'' =>
      choosable_of_holds (scoped_negativesOf hscN' hN'') (by
        have := distinct_of_hygiene hr hN''
        simpa [List.append_assoc] using this) (hvy N'' hN'')
    obtain ⟨Q'', τ'', c1, -, -⟩ := walk_level (G := G) (env := env) (Out := Out) G0 _ _ N' x y (hR.restore hN') hr hxQ hy hchN'
    have hgQ : ∀ z ∈ names Q, z ∈ names Q'' := fun z hz =>
      c1.grows z (by rw [names_append]; exact List.mem_append_left _ hz)
    have h2 := hygiene_after_restore h hN' c1.within hgQ
    refine ⟨Q'', τ'', c1.reached, h2, ne_nil_of_names hQ hgQ, c1.mem, fun z hz => ?_, hgQ, fun z => ?_⟩
    · rcases List.mem_append.mp hz with hz | hz
      · exact agree_outside hτ c1.mem (fun w hw => h.ordinary w (List.mem_append_left _ hw))
          (fun w hw => h2.ordinary w (List.mem_append_left _ hw)) z hz
      · exact (evalMatches_frame hx z fun hm => hdisL z hm hz).symm.trans
          (c1.agree z (by rw [names_append]; exact List.mem_append_left _ hz))
    · have := c1.within z; have := within_level N z; have := within_negative hN' z
      simp only [names_append, List.flatMap_cons, List.count_append] at *; omega

end Step

/-! ## The walk delivers the evidence -/

section Evidence
variable {G : Graph} {B : List Fact} {env : Env} {Out : List (List Match)}

/-- Moving an evaluation of a level to an environment agreeing on its scope. -/
theorem level_agree' {S : List Name} {e e' : Env} {N : List Match} (hag : Agree S e e') (hsc : ScopedMatches S N)
    {x : Env} (hx : x ∈ evalMatches G e (level N)) :
    ∃ x' ∈ evalMatches G e' (level N), Agree (S ++ names (level N)) x x' :=
  evalMatches_agree G _ S e e' (scoped_level hsc) hag x hx

mutual
  theorem evd_level (G0 : List Name) (H : ∀ F ∈ Out, ∀ τ ∈ evalMatches G env F, Settled B τ)
      (k : List Match → List (List Match)) :
      ∀ (P ms : List Match) (τP σ : Env), ReachedL Out k P ms → Hygiene G0 P [ms] → τP ∈ evalMatches G env P →
        σ ∈ evalMatches G τP (level ms) → EvD G B σ ms
    | P, [], τP, σ, _, _, _, _ => by
      rw [EvD]; intro L1 N L2 hL; simp [negativesOf, flatten, flattenMatches] at hL
    | P, m :: rest, τP, σ, hR, h, hτP, hσ => by
      have hu := hygiene_unit h
      rw [show m :: rest = [m] ++ rest from rfl, level_append] at hσ
      obtain ⟨σ1, hσ1, hσr⟩ := mem_evalMatches_append.mp hσ
      have hσ1P : σ1 ∈ evalMatches G env (P ++ level [m]) := mem_evalMatches_append.mpr ⟨τP, hτP, hσ1⟩
      have hwr : Within (names (P ++ level [m]) ++ names (level rest)) (names P ++ declaredMatches (m :: rest)) := by
        intro x; have := within_level [m] x; have := within_level rest x; have := declared_cons m rest x
        simp only [names_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *
        omega
      have hdisR := disjoint_of_nodup hwr (by simpa using h.nodup)
      have hordU : ∀ x ∈ names (P ++ level [m]), x ∉ G0 := fun x hx => hu.ordinary x (List.mem_append_left _ hx)
      have hagU : Agree (G0 ++ names (P ++ level [m])) σ σ1 := fun x hx =>
        evalMatches_frame hσr x fun hm => by
          rcases List.mem_append.mp hx with hx | hx
          · exact h.ordinary x (by
              have := mem_within hwr (List.mem_append_right _ hm)
              simpa using this) hx
          · exact hdisR x hm hx
      have hscR : ScopedMatches (G0 ++ names (P ++ level [m])) (level rest) := by
        have := h.inScope _ (List.mem_singleton_self _)
        obtain ⟨u, cs⟩ := m
        refine scoped_level (scopedMatches_mono _ _ _ (fun x hx => ?_) this.2)
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_right _ (mem_names_level u cs))
        · rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append_left _ hx
          · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_left _ hx)
      have hscRN : ∀ N ∈ negativesOf rest, ScopedMatches (G0 ++ names (P ++ level [m]) ++ names (level rest)) N := by
        intro N hN
        have := h.inScope _ (List.mem_singleton_self _)
        obtain ⟨u, cs⟩ := m
        refine scoped_negativesOf (scopedMatches_mono _ _ _ (fun x hx => ?_) this.2) hN
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_right _ (mem_names_level u cs))
        · rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append_left _ hx
          · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_left _ hx)
      rw [EvD]
      intro L1 N L2 hL h1 hN x hx hvx
      rw [show m :: rest = [m] ++ rest from rfl, negativesOf_append] at hL
      -- Whether the first failing condition is the unit's, or comes after it.
      have hrest : ∀ a', L1 = negativesOf [m] ++ a' → negativesOf rest = a' ++ N :: L2 →
          SettledOn B (names (level N)) x ∧ ∀ N' ∈ negativesOf N, ∀ y ∈ evalMatches G x (level N'), EvD G B y N' := by
        intro a' hL1 hR'
        have hchU : ∀ N ∈ negativesOf [m], Choosable G σ1 N := fun n hn =>
          choosable_of_holds (hu.inScope n hn) (distinct_of_hygieneN hu hn)
            (empty_agree hagU (hu.inScope n hn) (h1 n (by rw [hL1]; exact List.mem_append_left _ hn)))
        obtain ⟨Q1, τ1, c1⟩ := walk_neg (G := G) (env := env) (Out := Out) G0 _ _ _ _ hR.unit hu
          (by simp [level_ne_nil]) hσ1P hchU
        have h2 := hygiene_rest h c1.within c1.grows
        have hag1 : Agree (G0 ++ names (P ++ level [m])) σ1 τ1 := fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact agree_outside hσ1P c1.mem hordU (fun y hy => h2.ordinary y (List.mem_append_left _ hy)) x hx
          · exact c1.agree x hx
        obtain ⟨σ', hσ', ag'⟩ := evalMatches_agree G _ _ σ1 τ1 hscR hag1 σ hσr
        have hev := evd_level G0 H k Q1 rest τ1 σ' c1.reached h2 c1.mem hσ'
        have hev' := evd_agree rest _ σ' σ hscRN (fun z hz => (ag' z hz).symm) hev
        rw [EvD] at hev'
        exact hev' a' N L2 hR' (fun n hn => h1 n (by rw [hL1]; exact List.mem_append_right _ hn)) hN x hx hvx
      rcases List.append_eq_append_iff.mp hL with ⟨a', hL1, hR'⟩ | ⟨c', hU, hc'⟩
      · exact hrest a' hL1 hR'
      · cases c' with
        | nil =>
          simp only [List.append_nil, List.nil_append] at hU hc'
          exact hrest [] (by simp [hU]) hc'.symm
        | cons n c'' =>
          simp only [List.cons_append, List.cons.injEq] at hc'
          obtain ⟨rfl, -⟩ := hc'
          have hscN := hu.inScope N (by rw [hU]; simp)
          obtain ⟨x1, hx1, ax⟩ := level_agree' hagU hscN hx
          have hvx1 : ValidL G x1 N := validL_agree ax (fun n hn => scoped_negativesOf hscN hn) hvx
          obtain ⟨hon, hev⟩ := evd_neg G0 H _ _ _ σ1 hR.unit hu (by simp [level_ne_nil]) hσ1P L1 N c'' hU
            (fun n hn => empty_agree hagU (hu.inScope n (by rw [hU]; simp [hn])) (h1 n hn))
            (fun he => hN (empty_agree hagU.symm hscN he)) x1 hx1 hvx1
          refine ⟨settledOn_agree (fun z hz => (ax z (List.mem_append_right _ hz)).symm) hon, fun N' hN' y hy => ?_⟩
          have hsc' := scoped_negativesOf hscN hN'
          obtain ⟨y1, hy1, ay⟩ := level_agree' ax hsc' hy
          exact evd_agree N' _ y1 y (fun n hn => scoped_negativesOf hsc' hn) (fun z hz => (ay z hz).symm)
            (hev N' hN' y1 hy1)
  termination_by _ ms => (sizeOf ms, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | (apply Prod.Lex.left
         have := maxSize_lt (b := sizeOf (m :: rest)) (by simp; omega) fun p hp => sizeOf_negativesOf_unit p hp
         simpa using this)
      | (apply Prod.Lex.left; omega)

  theorem evd_neg (G0 : List Name) (H : ∀ F ∈ Out, ∀ τ ∈ evalMatches G env F, Settled B τ)
      (k : List Match → List (List Match)) :
      ∀ (Q : List Match) (negs : List (List Match)) (τ : Env), Reached Out k Q negs → Hygiene G0 Q negs → Q ≠ [] →
        τ ∈ evalMatches G env Q → ∀ L1 N L2, negs = L1 ++ N :: L2 → (∀ N0 ∈ L1, evalMatches G τ N0 = []) →
        evalMatches G τ N ≠ [] → ∀ x ∈ evalMatches G τ (level N), ValidL G x N →
          SettledOn B (names (level N)) x ∧ ∀ N' ∈ negativesOf N, ∀ y ∈ evalMatches G x (level N'), EvD G B y N'
    | Q, negs, τ, hR, h, hQ, hτ, [], N, L2, hL, _, _, x, hx, _ => by
      rw [hL] at hR h
      have hxQ : x ∈ evalMatches G env (Q ++ level N) := mem_evalMatches_append.mpr ⟨τ, hτ, hx⟩
      refine ⟨fun z _ id hz => H _ hR.emit x hxQ z id hz, fun N' hN' y hy => ?_⟩
      exact evd_level G0 H _ _ N' x y (hR.restore hN') (hygiene_restore h hN') hxQ hy
    | Q, negs, τ, hR, h, hQ, hτ, N0 :: L1, N, L2, hL, h1, hN, x, hx, hvx => by
      rw [hL] at hR h
      have hd0 := distinct_of_hygieneN h (List.mem_cons_self ..)
      have hch := choosable_of_holds (h.inScope N0 (List.mem_cons_self ..)) hd0 (h1 N0 (List.mem_cons_self ..))
      obtain ⟨Q', τ', hR', h', hQ', hτ', ag, -, -⟩ := walk_step G0 hR h hQ hτ hch
      have hscIn : ∀ n ∈ L1 ++ N :: L2, ScopedMatches (G0 ++ names Q) n := fun n hn =>
        h.inScope n (List.mem_cons_of_mem _ hn)
      have hscN := hscIn N (by simp)
      obtain ⟨x', hx', ax⟩ := level_agree' ag hscN hx
      have hvx' : ValidL G x' N := validL_agree ax (fun n hn => scoped_negativesOf hscN hn) hvx
      obtain ⟨hon, hev⟩ := evd_neg G0 H k Q' (L1 ++ N :: L2) τ' hR' h' hQ' hτ' L1 N L2 rfl
        (fun n hn => empty_agree ag (hscIn n (by simp [hn])) (h1 n (List.mem_cons_of_mem _ hn)))
        (fun he => hN (empty_agree ag.symm hscN he)) x' hx' hvx'
      refine ⟨settledOn_agree (fun z hz => (ax z (List.mem_append_right _ hz)).symm) hon, fun N' hN' y hy => ?_⟩
      have hsc' := scoped_negativesOf hscN hN'
      obtain ⟨y', hy', ay⟩ := level_agree' ax hsc' hy
      exact evd_agree N' _ y' y (fun n hn => scoped_negativesOf hsc' hn) (fun z hz => (ay z hz).symm) (hev N' hN' y' hy')
  termination_by _ negs => (maxSize negs, negs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact maxSize_lex _ _
      | (rw [hL]; have := maxSize_lex N0 (L1 ++ N :: L2); simpa using this)
      | (rw [hL]
         exact Prod.Lex.left _ _ (Nat.lt_of_lt_of_le (sizeOf_negativesOf _ hN') (le_maxSize (by simp))))
end

end Evidence

/-! ## The walk delivers every valid canceller -/

section Positive
variable {G : Graph} {B : List Fact} {env : Env} {Out : List (List Match)}

/-- A continuation that lands: every partial handed to it, with a tuple agreeing
with `ρ` on `A`, and labels within the budget `T` together with `Dk`, the
labels the continuation still adds, has its tuple delivered. -/
def KDone (G : Graph) (B : List Fact) (env : Env) (Out : List (List Match)) (G0 T : List Name)
    (k : List Match → List (List Match)) (A : List Name) (ρ : Env) (Dk : List Name) : Prop :=
  ∀ Q' τ', (∀ F ∈ k Q', F ∈ Out) → τ' ∈ evalMatches G env Q' → Agree A ρ τ' →
    Within (names Q' ++ Dk) T → (∀ x ∈ A, x ∈ G0 ∨ x ∈ names Q') → Settled B τ'

/-- Settledness on a partial's own labels is settledness, from a settled `env`. -/
theorem settled_of_partial (henv : Settled B env) {Q : List Match} {τ τ' : Env}
    (hτ : τ ∈ evalMatches G env Q) (hag : Agree (names Q) τ τ') (h : Settled B τ') : Settled B τ := by
  intro x id hx
  by_cases hm : x ∈ names Q
  · exact h x id (by rw [← hag x hm]; exact hx)
  · exact henv x id (by rw [← evalMatches_frame hτ x hm]; exact hx)

theorem agree_A {A G0 : List Name} {Q : List Match} {ρ τ τ' : Env} (hA : ∀ x ∈ A, x ∈ G0 ∨ x ∈ names Q)
    (h1 : Agree A ρ τ) (h2 : Agree (G0 ++ names Q) τ τ') : Agree A ρ τ' := fun x hx =>
  (h1 x hx).trans (h2 x (List.mem_append.mpr (hA x hx)))

theorem hygiene_of_budget {G0 T D : List Name} (hT : T.Nodup) (hTo : ∀ x ∈ T, x ∉ G0) {Q : List Match}
    {negs : List (List Match)} (hw : Within (names Q ++ negs.flatMap declaredMatches ++ D) T)
    (hs : ∀ ns ∈ negs, ScopedMatches (G0 ++ names Q) ns) : Hygiene G0 Q negs := by
  have hw' : Within (names Q ++ negs.flatMap declaredMatches) T := fun x => by
    have := hw x; simp only [List.count_append] at *; omega
  exact ⟨nodup_within hw' hT, fun x hx => hTo x (mem_within hw' hx), hs⟩

theorem scoped_sub_A {A G0 : List Name} {Q : List Match} {ns : List Match} (hA : ∀ x ∈ A, x ∈ G0 ∨ x ∈ names Q)
    (h : ScopedMatches A ns) : ScopedMatches (G0 ++ names Q) ns :=
  scopedMatches_mono _ _ _ (fun x hx => List.mem_append.mpr (hA x hx)) h

mutual
  theorem pd_level (G0 T : List Name) (hT : T.Nodup) (hTo : ∀ x ∈ T, x ∉ G0)
      (H : ∀ F ∈ Out, ∀ τ ∈ evalMatches G env F, Settled B τ) (henv : Settled B env)
      (k : List Match → List (List Match)) (A : List Name) (ρ : Env) (Dk : List Name)
      (hk : KDone G B env Out G0 T k A ρ Dk) :
      ∀ (P ms : List Match) (τP σ : Env), ReachedL Out k P ms → Hygiene G0 P [ms] →
        Within (names P ++ declaredMatches ms ++ Dk) T → τP ∈ evalMatches G env P → Agree A ρ τP →
        (∀ x ∈ A, x ∈ G0 ∨ x ∈ names P) → σ ∈ evalMatches G τP (level ms) → ValidL G σ ms → PD G B σ ms
    | P, [], _, σ, _, _, _, _, _, _, _, _ => by
      rw [pd_iff]; intro N hN; simp [negativesOf, flatten, flattenMatches] at hN
    | P, m :: rest, τP, σ, hR, h, hw, hτP, agP, hAP, hσ, hv => by
      have hu := hygiene_unit h
      rw [show m :: rest = [m] ++ rest from rfl, level_append] at hσ
      obtain ⟨σ1, hσ1, hσr⟩ := mem_evalMatches_append.mp hσ
      have hσ1P : σ1 ∈ evalMatches G env (P ++ level [m]) := mem_evalMatches_append.mpr ⟨τP, hτP, hσ1⟩
      have hwr : Within (names (P ++ level [m]) ++ names (level rest)) (names P ++ declaredMatches (m :: rest)) := by
        intro x; have := within_level [m] x; have := within_level rest x; have := declared_cons m rest x
        simp only [names_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *
        omega
      have hdisR := disjoint_of_nodup hwr (by simpa using h.nodup)
      have hdisU : ∀ x ∈ names (level [m]), x ∉ names P := by
        have : Within (names P ++ names (level [m])) (names P ++ declaredMatches (m :: rest)) := by
          intro x; have := hwr x; simp only [names_append, List.count_append] at *; omega
        exact disjoint_of_nodup this (by simpa using h.nodup)
      have hordU : ∀ x ∈ names (P ++ level [m]), x ∉ G0 := fun x hx => hu.ordinary x (List.mem_append_left _ hx)
      have hagU : Agree (G0 ++ names (P ++ level [m])) σ σ1 := fun x hx =>
        evalMatches_frame hσr x fun hm => by
          rcases List.mem_append.mp hx with hx | hx
          · exact h.ordinary x (by
              have := mem_within hwr (List.mem_append_right _ hm)
              simpa using this) hx
          · exact hdisR x hm hx
      have hscR : ScopedMatches (G0 ++ names (P ++ level [m])) (level rest) := by
        have := h.inScope _ (List.mem_singleton_self _)
        obtain ⟨u, cs⟩ := m
        refine scoped_level (scopedMatches_mono _ _ _ (fun x hx => ?_) this.2)
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_right _ (mem_names_level u cs))
        · rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append_left _ hx
          · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_left _ hx)
      have hscRm : ScopedMatches (G0 ++ names (P ++ level [m])) rest := by
        have := h.inScope _ (List.mem_singleton_self _)
        obtain ⟨u, cs⟩ := m
        refine scopedMatches_mono _ _ _ (fun x hx => ?_) this.2
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_right _ (mem_names_level u cs))
        · rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append_left _ hx
          · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_left _ hx)
      have hscRN : ∀ N ∈ negativesOf rest, ScopedMatches (G0 ++ names (P ++ level [m]) ++ names (level rest)) N :=
        fun N hN => scoped_negativesOf hscRm hN
      have hnegs : negativesOf (m :: rest) = negativesOf [m] ++ negativesOf rest := by
        rw [show m :: rest = [m] ++ rest from rfl, negativesOf_append]
      have hvU : ∀ N ∈ negativesOf [m], evalMatches G σ1 N = [] := fun N hN =>
        empty_agree hagU (hu.inScope N hN) (hv N (by rw [hnegs]; exact List.mem_append_left _ hN))
      have hAU : ∀ x ∈ A, x ∈ G0 ∨ x ∈ names (P ++ level [m]) := fun x hx => by
        rcases hAP x hx with hg | hp
        · exact Or.inl hg
        · exact Or.inr (by rw [names_append]; exact List.mem_append_left _ hp)
      have agσ1 : Agree A ρ σ1 := fun x hx => (agP x hx).trans (by
        rcases hAP x hx with hg | hp
        · exact (evalMatches_frame hσ1 x fun hm => hu.ordinary x (List.mem_append_left _ (by
            rw [names_append]; exact List.mem_append_right _ hm)) hg).symm
        · exact (evalMatches_frame hσ1 x fun hm => hdisU x hm hp).symm)
      -- After the unit, the walk goes on through the rest of the level and hands on to `k`.
      have k1 : KDone G B env Out G0 T (fun Q => levelFeeds k Q rest) (G0 ++ names (P ++ level [m])) σ1
          (declaredMatches rest ++ Dk) := by
        intro Q3 τ3 hR3 hτ3 ag3 hw3 hA3
        have h3 : Hygiene G0 Q3 [rest] :=
          hygiene_of_budget (D := Dk) hT hTo (by simpa [List.append_assoc] using hw3)
            fun n hn => by simp at hn; subst hn; exact scoped_sub_A hA3 hscRm
        obtain ⟨σ3, hσ3, ag'⟩ := evalMatches_agree G _ _ σ1 τ3 hscR ag3 σ hσr
        have hch3 : ∀ N ∈ negativesOf rest, Choosable G σ3 N := fun N hN => by
          have hsc3 := scoped_negativesOf (h3.inScope rest (List.mem_singleton_self _)) hN
          exact choosable_of_holds hsc3 (by simpa [List.append_assoc] using distinct_of_hygiene h3 hN)
            (empty_agree ag' (hscRN N hN) (hv N (by rw [hnegs]; exact List.mem_append_right _ hN)))
        obtain ⟨Q4, τ4, c, -, -⟩ := walk_level (G := G) (env := env) (Out := Out) G0 k Q3 rest τ3 σ3 hR3 h3 hτ3 hσ3 hch3
        have hordQ4 : ∀ w ∈ names Q4, w ∉ G0 := fun w hw' => hTo w (mem_within (show Within (names Q4) T from
          fun z => by have := c.within z; have := hw3 z; simp only [List.count_append] at *; omega) hw')
        have ag34 : Agree (G0 ++ names Q3) τ3 τ4 := fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact agree_outside hτ3 c.mem (fun y hy => h3.ordinary y (List.mem_append_left _ hy)) hordQ4 x hx
          · exact c.agree x hx
        have hAQ3 : ∀ x ∈ A, x ∈ G0 ∨ x ∈ names Q3 := fun x hx => by
          rcases hAU x hx with hg | hq
          · exact Or.inl hg
          · rcases hA3 x (List.mem_append_right _ hq) with hg | h3'
            · exact Or.inl hg
            · exact Or.inr h3'
        have hs4 := hk Q4 τ4 c.reached c.mem
          (agree_A hAQ3 (fun x hx => (agσ1 x hx).trans (ag3 x (List.mem_append.mpr (hAU x hx)))) ag34)
          (fun z => by have := c.within z; have := hw3 z; simp only [List.count_append] at *; omega)
          (fun x hx => by
            rcases hAQ3 x hx with hg | hq
            · exact Or.inl hg
            · exact Or.inr (c.grows x hq))
        exact settled_of_partial henv hτ3 c.agree hs4
      have hwU : Within (names (P ++ level [m]) ++ (negativesOf [m]).flatMap declaredMatches ++
          (declaredMatches rest ++ Dk)) T := by
        intro z; have := hw z; have := within_level [m] z; have := declared_cons m rest z
        simp only [names_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *; omega
      rw [pd_iff]
      intro N hN
      rw [hnegs] at hN
      rcases List.mem_append.mp hN with hN | hN
      · -- A condition of the unit.
        have := pd_neg G0 T hT hTo H henv _ _ σ1 _ k1 _ _ σ1 hR.unit hu hwU (by simp [level_ne_nil]) hσ1P
          (fun _ _ => rfl) (fun x hx => List.mem_append.mp hx) hvU N hN
        exact pdn_agree N _ σ1 σ (hu.inScope N hN) hagU.symm this
      · -- A condition after the unit: pass the unit, then it is one of the rest.
        have hchU : ∀ N ∈ negativesOf [m], Choosable G σ1 N := fun n hn =>
          choosable_of_holds (hu.inScope n hn) (distinct_of_hygieneN hu hn) (hvU n hn)
        obtain ⟨Q1, τ1, c1⟩ := walk_neg (G := G) (env := env) (Out := Out) G0 _ _ _ _ hR.unit hu
          (by simp [level_ne_nil]) hσ1P hchU
        have h2 := hygiene_rest h c1.within c1.grows
        have hag1 : Agree (G0 ++ names (P ++ level [m])) σ1 τ1 := fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact agree_outside hσ1P c1.mem hordU (fun y hy => h2.ordinary y (List.mem_append_left _ hy)) x hx
          · exact c1.agree x hx
        obtain ⟨σ', hσ', ag'⟩ := evalMatches_agree G _ _ σ1 τ1 hscR hag1 σ hσr
        have hpd := pd_level G0 T hT hTo H henv k A ρ Dk hk Q1 rest τ1 σ' c1.reached h2
          (fun z => by
            have := c1.within z; have := hw z; have := within_level [m] z; have := declared_cons m rest z
            simp only [names_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *
            omega)
          c1.mem (agree_A hAU agσ1 hag1)
          (fun x hx => by
            rcases hAU x hx with hg | hq
            · exact Or.inl hg
            · exact Or.inr (c1.grows x hq))
          hσ' (validL_agree ag' hscRN fun N hN => hv N (by rw [hnegs]; exact List.mem_append_right _ hN))
        exact pdn_agree N _ σ' σ (hscRN N hN) (fun z hz => (ag' z hz).symm) (pd_iff.mp hpd N hN)
  termination_by _ ms => (sizeOf ms, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | (apply Prod.Lex.left
         have := maxSize_lt (b := sizeOf (m :: rest)) (by simp; omega) fun p hp => sizeOf_negativesOf_unit p hp
         simpa using this)
      | (apply Prod.Lex.left; omega)

  theorem pd_neg (G0 T : List Name) (hT : T.Nodup) (hTo : ∀ x ∈ T, x ∉ G0)
      (H : ∀ F ∈ Out, ∀ τ ∈ evalMatches G env F, Settled B τ) (henv : Settled B env)
      (k : List Match → List (List Match)) (A : List Name) (ρ : Env) (Dk : List Name)
      (hk : KDone G B env Out G0 T k A ρ Dk) :
      ∀ (Q : List Match) (negs : List (List Match)) (τ : Env), Reached Out k Q negs → Hygiene G0 Q negs →
        Within (names Q ++ negs.flatMap declaredMatches ++ Dk) T → Q ≠ [] → τ ∈ evalMatches G env Q →
        Agree A ρ τ → (∀ x ∈ A, x ∈ G0 ∨ x ∈ names Q) → (∀ N ∈ negs, evalMatches G τ N = []) →
        ∀ N ∈ negs, PDN G B τ N
    | Q, [], _, _, _, _, _, _, _, _, _, N, hN => by simp at hN
    | Q, N :: rest, τ, hR, h, hw, hQ, hτ, agτ, hAQ, hholds, N₀, hN₀ => by
      have hscRest : ∀ n ∈ rest, ScopedMatches (G0 ++ names Q) n := fun n hn => h.inScope n (List.mem_cons_of_mem _ hn)
      -- The continuation after this condition walks the rest, then hands on to `k`.
      have kc : KDone G B env Out G0 T (fun Q'' => negFeeds k Q'' rest) (G0 ++ names Q) τ
          (rest.flatMap declaredMatches ++ Dk) := by
        intro Q3 τ3 hR3 hτ3 ag3 hw3 hA3
        have h3 : Hygiene G0 Q3 rest :=
          hygiene_of_budget (D := Dk) hT hTo (by simpa [List.append_assoc] using hw3)
            fun n hn => scoped_sub_A hA3 (hscRest n hn)
        have hQ3 : Q3 ≠ [] := by
          intro he; subst he
          obtain ⟨m0, hm0⟩ := List.exists_mem_of_ne_nil _ (names_ne_nil hQ)
          rcases hA3 m0 (List.mem_append_right _ hm0) with hg | hm
          · exact h.ordinary m0 (List.mem_append_left _ hm0) hg
          · simp [names] at hm
        have hch3 : ∀ n ∈ rest, Choosable G τ3 n := fun n hn =>
          choosable_of_holds (h3.inScope n hn) (distinct_of_hygieneN h3 hn)
            (empty_agree ag3 (hscRest n hn) (hholds n (List.mem_cons_of_mem _ hn)))
        obtain ⟨Q4, τ4, c⟩ := walk_neg (G := G) (env := env) (Out := Out) G0 k Q3 rest τ3 hR3 h3 hQ3 hτ3 hch3
        have ag34 : Agree (G0 ++ names Q3) τ3 τ4 := fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact agree_outside hτ3 c.mem (fun y hy => h3.ordinary y (List.mem_append_left _ hy))
              (fun y hy => hTo y (mem_within (show Within (names Q4) T from fun z => by
                have := c.within z; have := hw3 z; simp only [List.count_append] at *; omega) hy)) x hx
          · exact c.agree x hx
        have hAQ3 : ∀ x ∈ A, x ∈ G0 ∨ x ∈ names Q3 := fun x hx => by
          rcases hAQ x hx with hg | hq
          · exact Or.inl hg
          · rcases hA3 x (List.mem_append_right _ hq) with hg | h3'
            · exact Or.inl hg
            · exact Or.inr h3'
        have hs4 := hk Q4 τ4 c.reached c.mem
          (agree_A hAQ3 (fun x hx => (agτ x hx).trans (ag3 x (List.mem_append.mpr (hAQ x hx)))) ag34)
          (fun z => by have := c.within z; have := hw3 z; simp only [List.count_append] at *; omega)
          (fun x hx => by
            rcases hAQ3 x hx with hg | hq
            · exact Or.inl hg
            · exact Or.inr (c.grows x hq))
        exact settled_of_partial henv hτ3 c.agree hs4
      have hwl : Within (names (Q ++ level N)) (names Q ++ (N :: rest).flatMap declaredMatches) := by
        intro x; have := within_level N x
        simp only [names_append, List.flatMap_cons, List.count_append] at *; omega
      have hdisL : ∀ x ∈ names (level N), x ∉ names Q := by
        rw [names_append] at hwl
        exact disjoint_of_nodup hwl h.nodup
      rcases List.mem_cons.mp hN₀ with h0 | hN₀
      · -- At this condition: each valid canceller of each witness is delivered.
        subst N₀
        intro x hx N' hN' y hy hvy
        have hr := hygiene_restore h hN'
        have hxQ : x ∈ evalMatches G env (Q ++ level N) := mem_evalMatches_append.mpr ⟨τ, hτ, hx⟩
        have hscN' := hr.inScope N' (List.mem_singleton_self _)
        have hchN' : ∀ N'' ∈ negativesOf N', Choosable G y N'' := fun N'' hN'' =>
          choosable_of_holds (scoped_negativesOf hscN' hN'') (by
            have := distinct_of_hygiene hr hN''
            simpa [List.append_assoc] using this) (hvy N'' hN'')
        have agx : Agree (G0 ++ names Q) τ x := fun z hz => by
          rcases List.mem_append.mp hz with hz | hz
          · exact (evalMatches_frame hx z fun hm => h.ordinary z (by
              have := mem_within hwl (by rw [names_append]; exact List.mem_append_right _ hm)
              simpa using this) hz).symm
          · exact (evalMatches_frame hx z fun hm => hdisL z hm hz).symm
        have hwr : Within (names (Q ++ level N) ++ declaredMatches N' ++ (rest.flatMap declaredMatches ++ Dk)) T := by
          intro z; have := hw z; have := within_level N z; have := within_negative hN' z
          simp only [names_append, List.flatMap_cons, List.count_append] at *; omega
        have hAx : ∀ z ∈ G0 ++ names Q, z ∈ G0 ∨ z ∈ names (Q ++ level N) := fun z hz => by
          rcases List.mem_append.mp hz with hz | hz
          · exact Or.inl hz
          · exact Or.inr (by rw [names_append]; exact List.mem_append_left _ hz)
        obtain ⟨Q'', τ'', c1, ag1, -⟩ := walk_level (G := G) (env := env) (Out := Out) G0 _ _ N' x y
          (hR.restore hN') hr hxQ hy hchN'
        have hordQ'' : ∀ w ∈ names Q'', w ∉ G0 := fun w hw => hTo w (mem_within (show Within (names Q'') T from
          fun z => by have := c1.within z; have := hwr z; simp only [List.count_append] at *; omega) hw)
        have agτ'' : Agree (G0 ++ names Q) τ τ'' := fun z hz => by
          rcases List.mem_append.mp hz with hz | hz
          · exact agree_outside hτ c1.mem (fun w hw => h.ordinary w (List.mem_append_left _ hw)) hordQ'' z hz
          · exact (agx z (List.mem_append_right _ hz)).trans
              (c1.agree z (by rw [names_append]; exact List.mem_append_left _ hz))
        have hs'' := kc Q'' τ'' c1.reached c1.mem agτ''
          (fun z => by have := c1.within z; have := hwr z; simp only [List.count_append] at *; omega)
          (fun z hz => by
            rcases hAx z hz with hg | hq
            · exact Or.inl hg
            · exact Or.inr (c1.grows z hq))
        refine ⟨fun z hz id hzid => hs'' z id (by rw [← ag1 z hz]; exact hzid), ?_⟩
        exact pd_level G0 T hT hTo H henv _ (G0 ++ names Q) τ (rest.flatMap declaredMatches ++ Dk) kc
          (Q ++ level N) N' x y (hR.restore hN') hr hwr hxQ agx hAx hy hvy
      · -- After it: pass it, then the condition is one of the rest.
        have hd0 := distinct_of_hygieneN h (List.mem_cons_self ..)
        have hch := choosable_of_holds (h.inScope N (List.mem_cons_self ..)) hd0 (hholds N (List.mem_cons_self ..))
        obtain ⟨Q', τ', hR', h', hQ', hτ', ag, gr, wi⟩ := walk_step G0 hR h hQ hτ hch
        have := pd_neg G0 T hT hTo H henv k A ρ Dk hk Q' rest τ' hR' h'
          (fun z => by have := wi z; have := hw z; simp only [List.flatMap_cons, List.count_append] at *; omega)
          hQ' hτ' (agree_A hAQ agτ ag)
          (fun z hz => by
            rcases hAQ z hz with hg | hq
            · exact Or.inl hg
            · exact Or.inr (gr z hq))
          (fun n hn => empty_agree ag (hscRest n hn) (hholds n (List.mem_cons_of_mem _ hn))) N₀ hN₀
        exact pdn_agree N₀ (G0 ++ names Q) τ' τ (hscRest N₀ hN₀) ag.symm this
  termination_by _ negs => (maxSize negs, negs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact maxSize_lex _ _
      | exact Prod.Lex.left _ _ (Nat.lt_of_lt_of_le (sizeOf_negativesOf _ ‹_›) (le_maxSize (List.mem_cons_self ..)))
end

end Positive

end JinagaSpec
