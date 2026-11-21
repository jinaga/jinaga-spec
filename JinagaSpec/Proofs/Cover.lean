import JinagaSpec.Proofs.Defer
import JinagaSpec.Proofs.Cursor

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

theorem distinct_of_hygieneN {G0 : List Name} {Q : List Match} {negs : List (List Match)} {N : List Match}
    (h : Hygiene G0 Q negs) (hN : N ∈ negs) : Distinct (G0 ++ names Q) N := by
  have hw : Within (names Q ++ declaredMatches N) (names Q ++ negs.flatMap declaredMatches) :=
    Within.append_left _ fun x => count_le_flatMap declaredMatches x hN
  have hnd := nodup_within hw h.nodup
  refine ⟨(List.nodup_append.mp hnd).2.1, fun x hx hxS => ?_⟩
  rcases List.mem_append.mp hxS with hxS | hxS
  · exact h.ordinary x (mem_within hw (List.mem_append_right _ hx)) hxS
  · exact (List.nodup_append.mp hnd).2.2 x hxS x hx rfl

/-! ## The walk completes a context it can pass -/

section Complete
variable {G : Graph} {env : Env} {Out : List (List Match)}

/-- The rest of a level is scoped after its first unit. -/
theorem scoped_rest {G0 : List Name} {P : List Match} {m : Match} {rest : List Match}
    (h : Hygiene G0 P [m :: rest]) : ScopedMatches (G0 ++ names (P ++ level [m])) rest := by
  have := h.inScope _ (List.mem_singleton_self _)
  obtain ⟨u, cs⟩ := m
  refine scopedMatches_mono _ _ _ (fun x hx => ?_) this.2
  rw [names_append]
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_append_right _ (List.mem_append_right _ (mem_names_level u cs))
  · rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ hx
    · exact List.mem_append_right _ (List.mem_append_left _ hx)

theorem negativesOf_cons (m : Match) (rest : List Match) :
    negativesOf (m :: rest) = negativesOf [m] ++ negativesOf rest := negativesOf_append [m] rest

/-- A tuple of a level, split at its first unit: the unit's tuple agrees with it
on everything the unit's conditions name. -/
theorem unit_split {G : Graph} {env : Env} {G0 : List Name} {P : List Match} {m : Match} {rest : List Match}
    {τP σ : Env} (h : Hygiene G0 P [m :: rest]) (hτP : τP ∈ evalMatches G env P)
    (hσ : σ ∈ evalMatches G τP (level (m :: rest))) :
    ∃ σ1, σ1 ∈ evalMatches G τP (level [m]) ∧ σ1 ∈ evalMatches G env (P ++ level [m]) ∧
      σ ∈ evalMatches G σ1 (level rest) ∧ Agree (G0 ++ names (P ++ level [m])) σ σ1 ∧
      (∀ x ∈ names (level [m]), x ∉ names P) ∧ ∀ x ∈ names (level rest), x ∉ names (P ++ level [m]) := by
  rw [show m :: rest = [m] ++ rest from rfl, level_append] at hσ
  obtain ⟨σ1, hσ1, hσr⟩ := mem_evalMatches_append.mp hσ
  have hwr : Within (names (P ++ level [m]) ++ names (level rest)) (names P ++ declaredMatches (m :: rest)) := by
    intro x; have := within_level [m] x; have := within_level rest x; have := declared_cons m rest x
    simp only [names_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *
    omega
  have hnd : (names P ++ declaredMatches (m :: rest)).Nodup := by simpa using h.nodup
  have hdisR := disjoint_of_nodup hwr hnd
  refine ⟨σ1, hσ1, mem_evalMatches_append.mpr ⟨τP, hτP, hσ1⟩, hσr, fun x hx => evalMatches_frame hσr x fun hm => ?_,
    disjoint_of_nodup (show Within (names P ++ names (level [m])) _ from fun x => by
      have := hwr x; simp only [names_append, List.count_append] at *; omega) hnd, hdisR⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact h.ordinary x (by simpa using mem_within hwr (List.mem_append_right _ hm)) hx
  · exact hdisR x hm hx

/-- A partial feed handed on to `k`, with a tuple that goes on from `τ`. -/
structure Completion (G : Graph) (env : Env) (Out : List (List Match)) (k : List Match → List (List Match))
    (start : List Match) (bound : List Name) (τ : Env) (Q' : List Match) (τ' : Env) : Prop where
  reached : ∀ F ∈ k Q', F ∈ Out
  mem : τ' ∈ evalMatches G env Q'
  agree : Agree (names start) τ τ'
  grows : ∀ x ∈ names start, x ∈ names Q'
  within : Within (names Q') (names start ++ bound)

/-- After the walk passes a level's first unit, the rest of the level's tuple
goes on from where it lands. -/
theorem after_unit {G : Graph} {env : Env} {Out : List (List Match)} {G0 : List Name}
    {k : List Match → List (List Match)} {P : List Match} {m : Match} {rest : List Match} {σ σ1 τ1 : Env}
    {Q1 : List Match} (h : Hygiene G0 P [m :: rest]) (hσ1P : σ1 ∈ evalMatches G env (P ++ level [m]))
    (hσr : σ ∈ evalMatches G σ1 (level rest))
    (c1 : Completion G env Out k (P ++ level [m]) ((negativesOf [m]).flatMap declaredMatches) σ1 Q1 τ1) :
    Hygiene G0 Q1 [rest] ∧ Agree (G0 ++ names (P ++ level [m])) σ1 τ1 ∧
      ∃ σ' ∈ evalMatches G τ1 (level rest), Agree (G0 ++ names (P ++ level [m]) ++ names (level rest)) σ σ' := by
  have h2 := hygiene_rest h c1.within c1.grows
  have hag1 : Agree (G0 ++ names (P ++ level [m])) σ1 τ1 := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact agree_outside hσ1P c1.mem (fun y hy => (hygiene_unit h).ordinary y (List.mem_append_left _ hy))
        (fun y hy => h2.ordinary y (List.mem_append_left _ hy)) x hx
    · exact c1.agree x hx
  exact ⟨h2, hag1, evalMatches_agree G _ _ σ1 τ1 (scoped_level (scoped_rest h)) hag1 σ hσr⟩

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
      obtain ⟨σ1, hσ1, hσ1P, hσr, hagU, hdisU, hdisR⟩ := unit_split h hτP hσ
      have hchU : ∀ N ∈ negativesOf [m], Choosable G σ1 N := fun N hN =>
        choosable_agree hagU (hu.inScope N hN) (hch N (by rw [negativesOf_cons]; exact List.mem_append_left _ hN))
      obtain ⟨Q1, τ1, c1⟩ := walk_neg G0 _ _ _ _ hR.unit hu (by simp [level_ne_nil]) hσ1P hchU
      obtain ⟨h2, -, σ', hσ', ag'⟩ := after_unit h hσ1P hσr c1
      have hchR : ∀ N ∈ negativesOf rest, Choosable G σ' N := fun N hN =>
        choosable_agree ag' (scoped_negativesOf (scoped_rest h) hN)
          (hch N (by rw [negativesOf_cons]; exact List.mem_append_right _ hN))
      obtain ⟨Q', τ', c2, ag2, gr2⟩ := walk_level G0 k Q1 rest τ1 σ' c1.reached h2 c1.mem hσ' hchR
      have hlev : ∀ {x}, x ∈ names (level (m :: rest)) → x ∈ names (level [m]) ∨ x ∈ names (level rest) := fun hx => by
        rwa [show m :: rest = [m] ++ rest from rfl, level_append, names_append, List.mem_append] at hx
      have hmid : ∀ x ∈ names (level [m]), x ∈ names (P ++ level [m]) := fun x hx => by
        rw [names_append]; exact List.mem_append_right _ hx
      refine ⟨Q', τ', ⟨c2.reached, c2.mem, fun x hx => ?_, fun x hx => ?_, fun x => ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
      · have hx1 : x ∈ names (P ++ level [m]) := by rw [names_append]; exact List.mem_append_left _ hx
        exact (evalMatches_frame hσ1 x fun hm => hdisU x hm hx).symm.trans
          ((c1.agree x hx1).trans (c2.agree x (c1.grows x hx1)))
      · exact c2.grows x (c1.grows x (by rw [names_append]; exact List.mem_append_left _ hx))
      · have := c2.within x; have := c1.within x; have := within_level [m] x; have := declared_cons m rest x
        simp only [names_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *
        omega
      · rcases hlev hx with hx | hx
        · rw [evalMatches_frame hσr x fun hm => hdisR x hm (hmid x hx)]
          exact (c1.agree x (hmid x hx)).trans (c2.agree x (c1.grows x (hmid x hx)))
        · exact (ag' x (List.mem_append_right _ hx)).trans (ag2 x hx)
      · rcases hlev hx with hx | hx
        · exact c2.grows x (c1.grows x (hmid x hx))
        · exact gr2 x hx
  termination_by _ ms => (sizeOf ms, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | (apply Prod.Lex.left
         have := maxSize_lt (b := sizeOf (m :: rest)) (by simp; omega) fun p hp => sizeOf_negativesOf_unit p hp
         simpa using this)
      | (apply Prod.Lex.left; omega)

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
      obtain ⟨Q'', τ'', c1, -, -⟩ := walk_level G0 _ _ N' x y (hR.restore hN') hr hxQ hy hchN'
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
  termination_by (maxSize (N :: rest), 0)
  decreasing_by
    all_goals simp_wf
    exact Prod.Lex.left _ _ (Nat.lt_of_lt_of_le (sizeOf_negativesOf _ ‹_›) (le_maxSize (List.mem_cons_self ..)))

  theorem walk_neg (G0 : List Name) (k : List Match → List (List Match)) :
      ∀ (Q : List Match) (negs : List (List Match)) (τ : Env), Reached Out k Q negs → Hygiene G0 Q negs → Q ≠ [] →
        τ ∈ evalMatches G env Q → (∀ N ∈ negs, Choosable G τ N) →
        ∃ Q' τ', Completion G env Out k Q (negs.flatMap declaredMatches) τ Q' τ'
    | Q, [], τ, hR, _, _, hτ, _ =>
      ⟨Q, τ, ⟨hR.done, hτ, fun _ _ => rfl, fun _ h => h, fun x => by simp⟩⟩
    | Q, N :: rest, τ, hR, h, hQ, hτ, hch => by
      obtain ⟨Q1, τ1, hR1, h1, hQ1, hτ1, ag1, gr1, wi1⟩ := walk_step G0 hR h hQ hτ (hch N (List.mem_cons_self ..))
      obtain ⟨Q', τ', c⟩ := walk_neg G0 k Q1 rest τ1 hR1 h1 hQ1 hτ1 fun N2 hN2 =>
        choosable_agree ag1 (h.inScope N2 (List.mem_cons_of_mem _ hN2)) (hch N2 (List.mem_cons_of_mem _ hN2))
      refine ⟨Q', τ', ⟨c.reached, c.mem, fun z hz => (ag1 z (List.mem_append_right _ hz)).trans (c.agree z (gr1 z hz)),
        fun z hz => c.grows z (gr1 z hz), fun z => ?_⟩⟩
      have := c.within z; have := wi1 z; simp only [List.count_append] at *; omega
  termination_by _ negs => (maxSize negs, negs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact maxSize_lex _ _
      | (apply Prod.Lex.right; omega)
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
      obtain ⟨σ1, -, hσ1P, hσr, hagU, -, -⟩ := unit_split h hτP hσ
      rw [EvD]
      intro L1 N L2 hL h1 hN x hx hvx
      rw [negativesOf_cons] at hL
      have hafter : ∀ a', L1 = negativesOf [m] ++ a' → negativesOf rest = a' ++ N :: L2 →
          SettledOn B (names (level N)) x ∧ ∀ N' ∈ negativesOf N, ∀ y ∈ evalMatches G x (level N'), EvD G B y N' := by
        -- The first failing condition comes after the unit, all of whose conditions hold.
        intro a' hL1 hR'
        have hchU : ∀ N ∈ negativesOf [m], Choosable G σ1 N := fun n hn =>
          choosable_of_holds (hu.inScope n hn) (distinct_of_hygieneN hu hn)
            (empty_agree hagU (hu.inScope n hn) (h1 n (by rw [hL1]; exact List.mem_append_left _ hn)))
        obtain ⟨Q1, τ1, c1⟩ := walk_neg (G := G) (env := env) (Out := Out) G0 _ _ _ _ hR.unit hu
          (by simp [level_ne_nil]) hσ1P hchU
        obtain ⟨h2, -, σ', hσ', ag'⟩ := after_unit h hσ1P hσr c1
        have hev := evd_agree rest _ σ' σ (fun n hn => scoped_negativesOf (scoped_rest h) hn)
          (fun z hz => (ag' z hz).symm) (evd_level G0 H k Q1 rest τ1 σ' c1.reached h2 c1.mem hσ')
        rw [EvD] at hev
        exact hev a' N L2 hR' (fun n hn => h1 n (by rw [hL1]; exact List.mem_append_right _ hn)) hN x hx hvx
      rcases List.append_eq_append_iff.mp hL with ⟨a', hL1, hR'⟩ | ⟨c', hU, hc'⟩
      · exact hafter a' hL1 hR'
      cases c' with
      | nil => simp only [List.append_nil, List.nil_append] at hU hc'; exact hafter [] (by simp [hU]) hc'.symm
      | cons n c'' =>
        simp only [List.cons_append, List.cons.injEq] at hc'
        obtain ⟨rfl, -⟩ := hc'
        have hscN := hu.inScope N (by rw [hU]; simp)
        obtain ⟨x1, hx1, ax⟩ := level_agree' hagU hscN hx
        obtain ⟨hon, hev⟩ := evd_neg G0 H _ _ _ σ1 hR.unit hu (by simp [level_ne_nil]) hσ1P L1 N c'' hU
          (fun n hn => empty_agree hagU (hu.inScope n (by rw [hU]; simp [hn])) (h1 n hn))
          (fun he => hN (empty_agree hagU.symm hscN he)) x1 hx1
          (validL_agree ax (fun n hn => scoped_negativesOf hscN hn) hvx)
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

/-- Where the walk of a pending stretch hands on to a landing continuation, its
tuple was delivered. -/
theorem kdone_land {G0 T : List Name} (hTo : ∀ x ∈ T, x ∉ G0)
    {k : List Match → List (List Match)} {A : List Name} {ρ : Env} {Dk : List Name}
    (hk : KDone G B env Out G0 T k A ρ Dk) {Q3 Q4 : List Match} {bound : List Name} {τ3 τ4 : Env}
    (c : Completion G env Out k Q3 bound τ3 Q4 τ4) (hτ3 : τ3 ∈ evalMatches G env Q3)
    (hw : Within (names Q3 ++ bound ++ Dk) T) (ag : Agree A ρ τ3) (hA : ∀ x ∈ A, x ∈ G0 ∨ x ∈ names Q3) :
    Settled B τ4 := by
  have hw4 : Within (names Q4 ++ Dk) T := fun z => by
    have := c.within z; have := hw z; simp only [List.count_append] at *; omega
  have ag34 : Agree (G0 ++ names Q3) τ3 τ4 := fun x hx => by
    rcases List.mem_append.mp hx with hx | hx
    · exact agree_outside hτ3 c.mem (fun y hy => hTo y (mem_within hw (by simp [hy])))
        (fun y hy => hTo y (mem_within hw4 (List.mem_append_left _ hy))) x hx
    · exact c.agree x hx
  exact hk _ _ c.reached c.mem (agree_A hA ag ag34) hw4 fun x hx => (hA x hx).imp id (c.grows x)

theorem kdone_neg {G0 T : List Name} (hT : T.Nodup) (hTo : ∀ x ∈ T, x ∉ G0) (henv : Settled B env)
    {k : List Match → List (List Match)} {A : List Name} {ρ : Env} {Dk : List Name}
    (hk : KDone G B env Out G0 T k A ρ Dk) {Q : List Match} {rest : List (List Match)} {τ : Env}
    (hQ : Q ≠ []) (hord : ∀ x ∈ names Q, x ∉ G0) (hsc : ∀ n ∈ rest, ScopedMatches (G0 ++ names Q) n)
    (hholds : ∀ n ∈ rest, evalMatches G τ n = []) (ag : Agree A ρ τ) (hA : ∀ x ∈ A, x ∈ G0 ∨ x ∈ names Q) :
    KDone G B env Out G0 T (fun Q' => negFeeds k Q' rest) (G0 ++ names Q) τ (rest.flatMap declaredMatches ++ Dk) := by
  intro Q3 τ3 hR3 hτ3 ag3 hw3 hA3
  have h3 : Hygiene G0 Q3 rest := hygiene_of_budget (D := Dk) hT hTo (by simpa [List.append_assoc] using hw3)
    fun n hn => scoped_sub_A hA3 (hsc n hn)
  have hQ3 : Q3 ≠ [] := by
    rintro rfl
    obtain ⟨m0, hm0⟩ := List.exists_mem_of_ne_nil _ (names_ne_nil hQ)
    rcases hA3 m0 (List.mem_append_right _ hm0) with hg | hm
    · exact hord m0 hm0 hg
    · simp [names] at hm
  obtain ⟨Q4, τ4, c⟩ := walk_neg (G := G) (env := env) (Out := Out) G0 k Q3 rest τ3 hR3 h3 hQ3 hτ3 fun n hn =>
    choosable_of_holds (h3.inScope n hn) (distinct_of_hygieneN h3 hn) (empty_agree ag3 (hsc n hn) (hholds n hn))
  exact settled_of_partial henv hτ3 c.agree <| kdone_land hTo hk c hτ3 (by simpa [List.append_assoc] using hw3)
    (agree_A hA ag ag3) fun x hx => (hA x hx).elim Or.inl fun hq => hA3 x (List.mem_append_right _ hq)

theorem kdone_level {G0 T : List Name} (hT : T.Nodup) (hTo : ∀ x ∈ T, x ∉ G0) (henv : Settled B env)
    {k : List Match → List (List Match)} {A : List Name} {ρ : Env} {Dk : List Name}
    (hk : KDone G B env Out G0 T k A ρ Dk) {P1 rest : List Match} {σ1 σ : Env}
    (hsc : ScopedMatches (G0 ++ names P1) rest) (hσr : σ ∈ evalMatches G σ1 (level rest))
    (hv : ∀ N ∈ negativesOf rest, evalMatches G σ N = []) (ag : Agree A ρ σ1) (hA : ∀ x ∈ A, x ∈ G0 ∨ x ∈ names P1) :
    KDone G B env Out G0 T (fun Q => levelFeeds k Q rest) (G0 ++ names P1) σ1 (declaredMatches rest ++ Dk) := by
  intro Q3 τ3 hR3 hτ3 ag3 hw3 hA3
  have h3 : Hygiene G0 Q3 [rest] := hygiene_of_budget (D := Dk) hT hTo (by simpa [List.append_assoc] using hw3)
    fun n hn => by simp at hn; subst hn; exact scoped_sub_A hA3 hsc
  obtain ⟨σ3, hσ3, ag'⟩ := evalMatches_agree G _ _ σ1 τ3 (scoped_level hsc) ag3 σ hσr
  obtain ⟨Q4, τ4, c, -, -⟩ := walk_level (G := G) (env := env) (Out := Out) G0 k Q3 rest τ3 σ3 hR3 h3 hτ3 hσ3
    fun N hN => choosable_of_holds (scoped_negativesOf (h3.inScope rest (List.mem_singleton_self _)) hN)
      (by simpa [List.append_assoc] using distinct_of_hygiene h3 hN)
      (empty_agree ag' (scoped_negativesOf hsc hN) (hv N hN))
  exact settled_of_partial henv hτ3 c.agree <| kdone_land hTo hk c hτ3 (by simpa [List.append_assoc] using hw3)
    (agree_A hA ag ag3) fun x hx => (hA x hx).elim Or.inl fun hq => hA3 x (List.mem_append_right _ hq)

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
      obtain ⟨σ1, hσ1, hσ1P, hσr, hagU, hdisU, -⟩ := unit_split h hτP hσ
      have hscRN : ∀ N ∈ negativesOf rest, ScopedMatches (G0 ++ names (P ++ level [m]) ++ names (level rest)) N :=
        fun N hN => scoped_negativesOf (scoped_rest h) hN
      have hvR : ∀ N ∈ negativesOf rest, evalMatches G σ N = [] := fun N hN =>
        hv N (by rw [negativesOf_cons]; exact List.mem_append_right _ hN)
      have hvU : ∀ N ∈ negativesOf [m], evalMatches G σ1 N = [] := fun N hN =>
        empty_agree hagU (hu.inScope N hN) (hv N (by rw [negativesOf_cons]; exact List.mem_append_left _ hN))
      have hAU : ∀ x ∈ A, x ∈ G0 ∨ x ∈ names (P ++ level [m]) := fun x hx =>
        (hAP x hx).imp id fun hp => by rw [names_append]; exact List.mem_append_left _ hp
      have agσ1 : Agree A ρ σ1 := fun x hx => (agP x hx).trans (evalMatches_frame hσ1 x fun hm =>
        (hAP x hx).elim (hu.ordinary x (by rw [names_append]; exact List.mem_append_left _ (List.mem_append_right _ hm)))
          (hdisU x hm)).symm
      have hwU : Within (names (P ++ level [m]) ++ (negativesOf [m]).flatMap declaredMatches ++
          (declaredMatches rest ++ Dk)) T := by
        intro z; have := hw z; have := within_level [m] z; have := declared_cons m rest z
        simp only [names_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *; omega
      rw [pd_iff]
      intro N hN
      rw [negativesOf_cons] at hN
      rcases List.mem_append.mp hN with hN | hN
      · -- A condition of the unit; after it, the walk goes on through the rest and hands on to `k`.
        have := pd_neg G0 T hT hTo H henv _ _ σ1 _ (kdone_level hT hTo henv hk (scoped_rest h) hσr hvR agσ1 hAU)
          _ _ σ1 hR.unit hu hwU (by simp [level_ne_nil]) hσ1P (fun _ _ => rfl) (fun x hx => List.mem_append.mp hx)
          hvU N hN
        exact pdn_agree N _ σ1 σ (hu.inScope N hN) hagU.symm this
      · -- A condition after the unit: pass the unit, then it is one of the rest.
        obtain ⟨Q1, τ1, c1⟩ := walk_neg (G := G) (env := env) (Out := Out) G0 _ _ _ _ hR.unit hu
          (by simp [level_ne_nil]) hσ1P fun n hn =>
            choosable_of_holds (hu.inScope n hn) (distinct_of_hygieneN hu hn) (hvU n hn)
        obtain ⟨h2, hag1, σ', hσ', ag'⟩ := after_unit h hσ1P hσr c1
        have hpd := pd_level G0 T hT hTo H henv k A ρ Dk hk Q1 rest τ1 σ' c1.reached h2
          (fun z => by
            have := c1.within z; have := hw z; have := within_level [m] z; have := declared_cons m rest z
            simp only [names_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *
            omega)
          c1.mem (agree_A hAU agσ1 hag1) (fun x hx => (hAU x hx).imp id (c1.grows x))
          hσ' (validL_agree ag' hscRN hvR)
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
      have kc := kdone_neg hT hTo henv hk hQ (fun x hx => h.ordinary x (List.mem_append_left _ hx)) hscRest
        (fun n hn => hholds n (List.mem_cons_of_mem _ hn)) agτ hAQ
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
        have hAx : ∀ z ∈ G0 ++ names Q, z ∈ G0 ∨ z ∈ names (Q ++ level N) := fun z hz =>
          (List.mem_append.mp hz).imp id fun hz => by rw [names_append]; exact List.mem_append_left _ hz
        obtain ⟨Q'', τ'', c1, ag1, -⟩ := walk_level (G := G) (env := env) (Out := Out) G0 _ _ N' x y
          (hR.restore hN') hr hxQ hy hchN'
        have hs'' := kdone_land hTo kc c1 hxQ (by simpa [List.append_assoc] using hwr) agx hAx
        refine ⟨fun z hz id hzid => hs'' z id (by rw [← ag1 z hz]; exact hzid), ?_⟩
        exact pd_level G0 T hT hTo H henv _ (G0 ++ names Q) τ (rest.flatMap declaredMatches ++ Dk) kc
          (Q ++ level N) N' x y (hR.restore hN') hr hwr hxQ agx hAx hy hvy
      · -- After it: pass it, then the condition is one of the rest.
        have hd0 := distinct_of_hygieneN h (List.mem_cons_self ..)
        have hch := choosable_of_holds (h.inScope N (List.mem_cons_self ..)) hd0 (hholds N (List.mem_cons_self ..))
        obtain ⟨Q', τ', hR', h', hQ', hτ', ag, gr, wi⟩ := walk_step G0 hR h hQ hτ hch
        have := pd_neg G0 T hT hTo H henv k A ρ Dk hk Q' rest τ' hR' h'
          (fun z => by have := wi z; have := hw z; simp only [List.flatMap_cons, List.count_append] at *; omega)
          hQ' hτ' (agree_A hAQ agτ ag) (fun z hz => (hAQ z hz).imp id (gr z))
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

/-! ## Every feed is scoped and rooted -/

/-- A feed's path conditions name only givens and labels bound before them, and
each of its matches has one. -/
def Rooted (G0 : List Name) (Q : List Match) : Prop :=
  ScopedMatches G0 (Q.map Match.paths) ∧ ∀ m ∈ Q, HasPath m

theorem paths_paths (m : Match) : m.paths.paths = m.paths := by
  cases m; simp [Match.paths, List.filter_filter]

theorem negativesOf_rooted {N : List Match} (hr : RootedMatches N) : ∀ ns ∈ negativesOf N, RootedMatches ns := by
  intro ns hns
  obtain ⟨m, hm, hn⟩ := List.mem_flatMap.mp hns
  exact (flatten_rooted N hr).2 m hm ns hn

theorem Rooted.append {G0 : List Name} {Q N : List Match} (h : Rooted G0 Q) (hsc : ScopedMatches (G0 ++ names Q) N)
    (hr : RootedMatches N) : Rooted G0 (Q ++ level N) := by
  refine ⟨?_, fun m hm => ?_⟩
  · rw [List.map_append, scopedMatches_append]
    refine ⟨h.1, ?_⟩
    rw [show (level N).map Match.paths = level N by simp [level, List.map_map, Function.comp_def, paths_paths]]
    refine scopedMatches_mono _ _ _ (fun x hx => ?_) (scoped_level hsc)
    rw [mem_scopeAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr hx
    · exact Or.inl (by rw [← names, names_paths]; exact hx)
  · rcases List.mem_append.mp hm with hm | hm
    · exact h.2 m hm
    · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
      obtain ⟨c, hc, hp⟩ := (flatten_rooted N hr).1 m0 hm0
      obtain ⟨u, cs⟩ := m0
      exact ⟨c, List.mem_filter.mpr ⟨hc, hp⟩, hp⟩

theorem paths_addLast {c : Condition} (hc : c.isPath = false) :
    ∀ Q : List Match, (addLast c Q).map Match.paths = Q.map Match.paths
  | [] => rfl
  | [.mk u cs] => by simp [addLast, Match.addCondition, Match.paths, List.filter_append, hc]
  | m :: m' :: ms => by
    rw [show addLast c (m :: m' :: ms) = m :: addLast c (m' :: ms) from rfl, List.map_cons, paths_addLast hc (m' :: ms)]
    rfl

theorem hasPath_addLast (c : Condition) : ∀ Q : List Match, (∀ m ∈ Q, HasPath m) → ∀ m ∈ addLast c Q, HasPath m
  | [], _ => by simp [addLast]
  | [.mk u cs], h => by
    intro m hm
    simp [addLast, Match.addCondition] at hm; subst hm
    obtain ⟨c', hc', hp⟩ := h _ (List.mem_singleton_self _)
    exact ⟨c', List.mem_append_left _ hc', hp⟩
  | m :: m' :: ms, h => by
    rw [show addLast c (m :: m' :: ms) = m :: addLast c (m' :: ms) from rfl]
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h x (List.mem_cons_self ..)
    · exact hasPath_addLast c (m' :: ms) (fun y hy => h y (List.mem_cons_of_mem _ hy)) x hx

theorem Rooted.addLast {G0 : List Name} {Q ns : List Match} (h : Rooted G0 Q) :
    Rooted G0 (JinagaSpec.addLast (.existential false ns) Q) :=
  ⟨by rw [paths_addLast rfl]; exact h.1, hasPath_addLast _ Q h.2⟩

theorem scoped_sub {S S' : List Name} {ms : List Match} (h : ScopedMatches S ms) (hs : ∀ x ∈ S, x ∈ S') :
    ScopedMatches S' ms := scopedMatches_mono _ _ _ hs h

mutual
  theorem levelFeeds_rooted (G0 : List Name) (k : List Match → List (List Match)) :
      ∀ (P ms : List Match), Rooted G0 P → ScopedMatches (G0 ++ names P) ms → RootedMatches ms →
        (∀ Q, Rooted G0 Q → (∀ x ∈ names (P ++ level ms), x ∈ names Q) → ∀ F ∈ k Q, Rooted G0 F) →
        ∀ F ∈ levelFeeds k P ms, Rooted G0 F
    | P, [], hP, _, _, hk, F, hF => by
      rw [levelFeeds] at hF; exact hk P hP (fun x hx => by simpa [level, flatten, flattenMatches] using hx) F hF
    | P, .mk u cs :: rest, hP, ⟨hcs, hrest⟩, hr, hk, F, hF => by
      rw [RootedMatches] at hr
      obtain ⟨hu, hrc, hrr⟩ := hr
      rw [levelFeeds] at hF
      have hsc1 : ScopedMatches (G0 ++ names P) [.mk u cs] := ⟨hcs, trivial⟩
      have hr1 : RootedMatches [.mk u cs] := by rw [RootedMatches]; exact ⟨hu, hrc, by rw [RootedMatches]; trivial⟩
      refine negFeeds_rooted G0 _ _ _ (hP.append hsc1 hr1)
        (fun ns hns => ⟨by simpa [names_append, List.append_assoc] using scoped_negativesOf hsc1 hns,
          negativesOf_rooted hr1 ns hns⟩) (fun Q hQ hg F hF => ?_) F hF
      refine levelFeeds_rooted G0 k Q rest hQ (scoped_sub hrest fun x hx => ?_) hrr (fun Q' hQ' hg' => hk Q' hQ' ?_) F hF
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_append_right _ (hg _ (by rw [names_append]; exact List.mem_append_right _ (mem_names_level u cs)))
        · rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append_left _ hx
          · exact List.mem_append_right _ (hg _ (by rw [names_append]; exact List.mem_append_left _ hx))
      · intro x hx
        rw [show Match.mk u cs :: rest = [.mk u cs] ++ rest from rfl, level_append, ← List.append_assoc,
          names_append, List.mem_append] at hx
        rcases hx with hx | hx
        · exact hg' x (by rw [names_append]; exact List.mem_append_left _ (hg x hx))
        · exact hg' x (by rw [names_append]; exact List.mem_append_right _ hx)
  termination_by _ ms => (sizeOf ms, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | (apply Prod.Lex.left
         have := maxSize_lt (b := sizeOf (Match.mk u cs :: rest)) (by simp; omega)
           fun p hp => sizeOf_negativesOf_unit p hp
         simpa using this)
      | (apply Prod.Lex.left; omega)

  theorem negFeeds_rooted (G0 : List Name) (k : List Match → List (List Match)) :
      ∀ (Q : List Match) (negs : List (List Match)), Rooted G0 Q →
        (∀ ns ∈ negs, ScopedMatches (G0 ++ names Q) ns ∧ RootedMatches ns) →
        (∀ Q', Rooted G0 Q' → (∀ x ∈ names Q, x ∈ names Q') → ∀ F ∈ k Q', Rooted G0 F) →
        ∀ F ∈ negFeeds k Q negs, Rooted G0 F
    | Q, [], hQ, _, hk, F, hF => by rw [negFeeds] at hF; exact hk Q hQ (fun _ h => h) F hF
    | Q, ns :: rest, hQ, hn, hk, F, hF => by
      rw [negFeeds] at hF
      have hns := hn ns (List.mem_cons_self ..)
      have hrest : ∀ n ∈ rest, ScopedMatches (G0 ++ names Q) n ∧ RootedMatches n :=
        fun n h => hn n (List.mem_cons_of_mem _ h)
      have hQl := hQ.append hns.1 hns.2
      rcases List.mem_cons.mp hF with rfl | hF
      · exact hQl
      rcases List.mem_append.mp hF with hF | hF
      · exact negFeeds_rooted G0 k _ rest hQ.addLast (by rw [names_addLast]; exact hrest)
          (fun Q' hQ' hg => hk Q' hQ' fun x hx => hg x (by rw [names_addLast]; exact hx)) F hF
      · obtain ⟨⟨ns', hns'⟩, -, hF⟩ := List.mem_flatMap.mp hF
        refine levelFeeds_rooted G0 _ _ ns' hQl
          (by simpa [names_append, List.append_assoc] using scoped_negativesOf hns.1 hns')
          (negativesOf_rooted hns.2 ns' hns') (fun Q' hQ' hg F hF => ?_) F hF
        have hgQ : ∀ x ∈ names Q, x ∈ names Q' := fun x hx =>
          hg x (by simp only [names_append, List.mem_append]; exact Or.inl (Or.inl hx))
        exact negFeeds_rooted G0 k Q' rest hQ'
          (fun n h => ⟨scoped_sub (hrest n h).1 fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact List.mem_append_left _ hx
            · exact List.mem_append_right _ (hgQ x hx), (hrest n h).2⟩)
          (fun Q'' hQ'' hg'' => hk Q'' hQ'' fun x hx => hg'' x (hgQ x hx)) F hF
  termination_by _ negs => (maxSize negs, negs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact maxSize_lex _ _
      | exact Prod.Lex.left _ _ (Nat.lt_of_lt_of_le (sizeOf_negativesOf _ ‹_›) (le_maxSize (List.mem_cons_self ..)))
end

/-! ## The feeds cover the specification -/

section Top
variable {g : Graph} {B : List Fact}

theorem hygiene_top {s : Specification} (hwf : WellFormed s) (hd : DistinctLabels s) :
    Hygiene (s.given.map (·.name)) [] [s.matchList] :=
  ⟨by simpa [names, DistinctLabels] using hd,
   fun x hx => wellNamed_declared _ _ hwf.wellNamed x (by simpa [names] using hx),
   fun n hn => by simp at hn; subst hn; simpa [names] using hwf.inScope⟩

/-- A feed binds each label the specification declares at most once. -/
theorem levelFeeds_within {s : Specification} (hwf : WellFormed s) (hd : DistinctLabels s) :
    ∀ F ∈ levelFeeds (fun P => [P]) [] s.matchList, Within (names F) (declaredMatches s.matchList) := by
  intro F hF
  rcases levelFeeds_split (G := []) (env := fun _ => none) _ _ [] s.matchList (hygiene_top hwf hd) F hF with
    ⟨Q', hQ', hF⟩ | ⟨hw, -⟩
  · simp at hF; subst hF; simpa [names] using hQ'.within
  · simpa [names] using hw

/-- Every feed binds each of its labels once, none of them a given: what
`feed_grow` needs, with `buildFeeds_feedShape`, to page it by bookmark. -/
theorem buildFeeds_nodup {s : Specification} (hwf : WellFormed s) (hd : DistinctLabels s) :
    ∀ f ∈ buildFeeds s, (names f.matchList).Nodup := by
  intro f hf
  obtain ⟨hf, -⟩ := List.mem_filter.mp hf
  obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hf
  exact nodup_within (levelFeeds_within hwf hd F hF) hd

/-- Every tuple of every feed of the walk binds facts the replica holds: a feed
that is kept delivered them, and one that is dropped walks only to
predecessors of what it starts from. -/
theorem feeds_settled {s : Specification} (hwf : WellFormed s) (hd : DistinctLabels s)
    (hr : RootedMatches s.matchList) (hf : Fresh g B) {env : Env} (henv : Settled B env)
    (hdel : ∀ id ∈ delivered s (g ++ B) env, Outside B id) :
    ∀ F ∈ levelFeeds (fun P => [P]) [] s.matchList, ∀ τ ∈ evalMatches (g ++ B) env F, Settled B τ := by
  intro F hF τ hτ
  let G0 := s.given.map (·.name)
  by_cases ht : traversesSuccessors { given := usedGivens s.given F, matchList := F, projection := .composite [] } = true
  · have hkept : ({ given := usedGivens s.given F, matchList := F, projection := .composite [] } : Specification) ∈
        buildFeeds s := List.mem_filter.mpr ⟨List.mem_map.mpr ⟨F, hF, rfl⟩, ht⟩
    intro n id hn
    by_cases hm : n ∈ names F
    · exact hdel id (List.mem_flatMap.mpr ⟨_, hkept, List.mem_flatten.mpr
        ⟨_, List.mem_map.mpr ⟨τ, hτ, rfl⟩, List.mem_filterMap.mpr ⟨n, hm, hn⟩⟩⟩)
    · exact henv n id (by rw [← evalMatches_frame hτ n hm]; exact hn)
  · have hroot := levelFeeds_rooted G0 _ [] s.matchList ⟨trivial, by simp⟩ (by simpa [names] using hwf.inScope) hr
      (fun Q hQ _ F hF => by simp at hF; exact hF ▸ hQ) F hF
    have hw := levelFeeds_within hwf hd F hF
    have hnd := nodup_within hw hd
    refine dropped_settled hf (F.map Match.paths) G0 env
      ⟨hroot.1, by rw [names_paths]; exact hnd, fun x hx => wellNamed_declared _ _ hwf.wellNamed x
        (mem_within hw (by rwa [names_paths] at hx))⟩ (fun m hm => ?_) henv τ (evalMatches_paths hτ)
    obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
    obtain ⟨c, hc, hp⟩ := hroot.2 m0 hm0
    cases c with
    | path pc =>
      refine ⟨pc, ?_, ?_⟩
      · obtain ⟨u, cs⟩ := m0; exact List.mem_filter.mpr ⟨hc, rfl⟩
      · simp only [traversesSuccessors, List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at ht
        simpa using ht m0 hm0 (.path pc) hc
    | existential => simp [Condition.isPath] at hp

/-- **The feeds cover the specification.** A replica `g` that holds the givens
and every fact the feeds deliver on the replicator's graph `g ++ B`, where `B`
is what of that graph the replica does not hold, reads what the replicator
reads.

`B` is fresh to `g` because a replica saves each fact with its predecessors.
The specification declares each label once (`DistinctLabels`), so that joining
a positive condition into its level binds nothing twice, and every match has a
path condition (`RootedMatches`), so that a feed walking only to predecessors
reaches nothing the replica does not hold. -/
theorem feeds_cover {s : Specification} (hwf : WellFormed s) (hd : DistinctLabels s)
    (hr : RootedMatches s.matchList) (hf : Fresh g B) {env : Env} (henv : Settled B env)
    (hgiv : ∀ l ∈ s.given, g.has env l = true) (hdel : ∀ id ∈ delivered s (g ++ B) env, Outside B id) :
    ∀ r, r ∈ s.read g env ↔ r ∈ s.read (g ++ B) env := by
  let G0 := s.given.map (·.name)
  let ms := s.matchList
  have hall := feeds_settled hwf hd hr hf henv hdel
  have hsc : ScopedMatches G0 ms := hwf.inScope
  have hdis : ∀ x ∈ declaredMatches ms, x ∉ G0 := wellNamed_declared _ _ hwf.wellNamed
  have hdist : Distinct G0 ms := ⟨hd, hdis⟩
  have hyg := hygiene_top hwf hd
  have hR : ReachedL (levelFeeds (fun P => [P]) [] ms) (fun P => [P]) [] ms := fun _ h => h
  have hε : env ∈ evalMatches (g ++ B) env [] := by simp [evalMatches]
  -- A valid solution of the level's path conditions on the replicator is delivered.
  have hset : ∀ σ' ∈ evalMatches (g ++ B) env (level ms), ValidL (g ++ B) σ' ms → Settled B σ' := by
    intro σ' hσ' hv
    obtain ⟨Q', τ', c, ag, -⟩ := walk_level (G := g ++ B) (env := env) G0 _ [] ms env σ' hR hyg hε hσ'
      fun N hN => choosable_of_holds (scoped_negativesOf hsc hN)
        (by simpa [names] using distinct_of_hygiene hyg hN) (hv N hN)
    have hτ' := hall Q' (c.reached Q' (List.mem_singleton_self _)) τ' c.mem
    exact settled_of_on henv hσ' fun x hx id h => hτ' x id (by rw [← ag x hx]; exact h)
  have hpd : ∀ σ' ∈ evalMatches (g ++ B) env (level ms), ValidL (g ++ B) σ' ms → PD (g ++ B) B σ' ms :=
    fun σ' hσ' hv => pd_level G0 (declaredMatches ms) hd hdis hall henv (fun P => [P]) [] env []
      (fun Q' τ' hR' hτ' _ _ _ => hall Q' (hR' Q' (List.mem_singleton_self _)) τ' hτ')
      [] ms env σ' hR hyg (by simpa [names] using Within.refl (declaredMatches ms)) hε
      (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil) hσ' hv
  -- The two sides have solutions agreeing on the unknowns.
  have hagree : (∀ σ ∈ evalMatches g env ms, ∃ σ0 ∈ evalMatches (g ++ B) env ms, Agree (names ms) σ σ0) ∧
      (∀ σ ∈ evalMatches (g ++ B) env ms, ∃ σ0 ∈ evalMatches g env ms, Agree (names ms) σ0 σ) := by
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
    · obtain ⟨σ', hσ', hv, ag⟩ := (nf (G := g) hsc hdist env).1 σ hσ
      have hS := settled_eval hf henv hσ'
      have hσ'G := evalMatches_paths_mono hf (pathsOnly_paths _) henv hσ'
      have hvG : ValidL (g ++ B) σ' ms := Classical.byContradiction fun hn =>
        semB hf ms G0 σ' hsc hdist hS hn (evd_level G0 hall _ [] ms env σ' hR hyg hε hσ'G) hv
      obtain ⟨σ0, hσ0, ag0⟩ := (nf (G := g ++ B) hsc hdist env).2 σ' hσ'G hvG
      exact ⟨σ0, hσ0, fun x hx => (ag x hx).trans (ag0 x hx).symm⟩
    · obtain ⟨σ', hσ', hv, ag⟩ := (nf (G := g ++ B) hsc hdist env).1 σ hσ
      have hS := hset σ' hσ' hv
      have hσ'g := evalMatches_paths_antitone hf (pathsOnly_paths _).shape (nodup_level hdist) henv hσ' hS
      have hvg := semA hf ms G0 σ' hsc hdist hS hv (hpd σ' hσ' hv)
      obtain ⟨σ0, hσ0, ag0⟩ := (nf (G := g) hsc hdist env).2 σ' hσ'g hvg
      exact ⟨σ0, hσ0, fun x hx => (ag0 x hx).trans (ag x hx).symm⟩
  -- The givens are held on both graphs, so both read the specification.
  have hgivG : ∀ l ∈ s.given, (g ++ B).has env l = true := fun l hl => (has_settled henv l).symm ▸ hgiv l hl
  intro r
  simp only [Specification.read, List.all_eq_true.mpr hgiv, List.all_eq_true.mpr hgivG, ite_true,
    Specification.evaluate, List.mem_map]
  -- Solutions that agree on the unknowns project the same row: the projection
  -- names only givens and unknowns, and neither side rebinds a given.
  have hrow : ∀ σ σ', σ ∈ evalMatches g env ms → σ' ∈ evalMatches (g ++ B) env ms →
      Agree (names ms) σ σ' → s.projection.labels.map σ = s.projection.labels.map σ' := by
    intro σ σ' hσ hσ' hag
    refine List.map_congr_left fun l hl => ?_
    by_cases hn : l ∈ names ms
    · exact hag l hn
    · rw [evalMatches_frame hσ l hn, evalMatches_frame hσ' l hn]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨σ', hσ', hag⟩ := hagree.1 σ hσ
    exact ⟨σ', hσ', (hrow σ σ' hσ hσ' hag).symm⟩
  · rintro ⟨σ', hσ', rfl⟩
    obtain ⟨σ, hσ, hag⟩ := hagree.2 σ' hσ'
    exact ⟨σ, hσ, hrow σ σ' hσ hσ' hag⟩

/-- **Eventual consistency.** A replica that has paged every feed of `s` until a
page came back empty, and holds what the pages delivered with its
predecessors, reads what the replicator reads.

The replica is `g`; what of the replicator's graph it does not hold is `B`.
`caught_start`, `caught_page` and `feed_grow` keep each feed `Caught` from the
first page to the last while the replicator's graph grows; this theorem takes
the last step, from `caught_sync` and `feeds_cover`. -/
theorem feed_converges {s : Specification} (hwf : WellFormed s) (hd : DistinctLabels s)
    (hr : RootedMatches s.matchList) (hf : Fresh g B) {env : Env} (henv : Settled B env)
    (hgiv : ∀ l ∈ s.given, g.has env l = true)
    (bookmark : Specification → List Nat) (D : List FactId)
    (hcaught : ∀ f ∈ buildFeeds s, Caught (f.tuples (g ++ B) env) (bookmark f) D)
    (hsync : ∀ f ∈ buildFeeds s, IsPage (f.tuples (g ++ B) env) [] (bookmark f))
    (hheld : ∀ id ∈ D, Outside B id) :
    ∀ r, r ∈ s.read g env ↔ r ∈ s.read (g ++ B) env :=
  feeds_cover hwf hd hr hf henv hgiv fun id hid => by
    obtain ⟨f, hf, hid⟩ := List.mem_flatMap.mp hid
    obtain ⟨t, ht, hid⟩ := List.mem_flatten.mp hid
    exact hheld id (caught_sync (hcaught f hf) (hsync f hf) t ht id hid)

end Top

end JinagaSpec
