import JinagaSpec.Proofs.Cover

/-!
# Child specifications

A child specification is a specification: one with the same givens, whose
matches are its parent's followed by its own (`Specification.descendants`). The
feeds of a specification are the flat feeds of its descendants
(`mem_buildFeeds`): `projectionFeeds` hands each positive feed on to the
children's matches, which is what walking the parent's matches and then the
child's does. So every requirement of a specification with child
specifications follows from the same requirement of its descendants, which
have none:

* `buildFeeds_feedShape` and `buildFeeds_nodup` (append-only);
* `feeds_defer` (deferral), which applies to each descendant, and so to an
  entity a child specification matches, since the feeds of a descendant are
  among the specification's (`buildFeeds_descendant`);
* `feeds_cover` (consistency): a replica reads the replicator's results, child
  specifications' included, at every depth, because the flat feeds give it the
  replicator's solutions of each descendant's matches (`flatFeeds_cover`), and
  those determine the nested results (`reads_congr`);
* `feed_converges`.
-/
namespace JinagaSpec

/-! ## The feeds of a specification are the flat feeds of its descendants -/

mutual
  /-- A walk whose continuation hands each partial to any of the continuations
  `k' i` makes the feeds of any of the walks with `k' i`. Excluding feeds do not
  depend on the continuation, so `I` must not be empty. -/
  theorem levelFeeds_mem_iff {ι : Type} (I : List ι) (hI : I ≠ []) :
      ∀ (k : List Match → List (List Match)) (k' : ι → List Match → List (List Match)),
        (∀ Q F, F ∈ k Q ↔ ∃ i ∈ I, F ∈ k' i Q) →
        ∀ (P ms F : List Match), F ∈ levelFeeds k P ms ↔ ∃ i ∈ I, F ∈ levelFeeds (k' i) P ms
    | k, k', hk, P, [], F => by simp only [levelFeeds]; exact hk P F
    | k, k', hk, P, m :: rest, F => by
      simp only [levelFeeds]
      exact negFeeds_mem_iff I hI _ (fun i Q => levelFeeds (k' i) Q rest)
        (fun Q F => levelFeeds_mem_iff I hI k k' hk Q rest F) _ _ F
  termination_by _ _ _ _ ms => (sizeOf ms, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | (apply Prod.Lex.left
         have := maxSize_lt (b := sizeOf (m :: rest)) (by simp; omega) fun p hp => sizeOf_negativesOf_unit p hp
         simpa using this)
      | (apply Prod.Lex.left; omega)

  theorem negFeeds_mem_iff {ι : Type} (I : List ι) (hI : I ≠ []) :
      ∀ (k : List Match → List (List Match)) (k' : ι → List Match → List (List Match)),
        (∀ Q F, F ∈ k Q ↔ ∃ i ∈ I, F ∈ k' i Q) →
        ∀ (Q : List Match) (negs : List (List Match)) (F : List Match),
          F ∈ negFeeds k Q negs ↔ ∃ i ∈ I, F ∈ negFeeds (k' i) Q negs
    | k, k', hk, Q, [], F => by simp only [negFeeds]; exact hk Q F
    | k, k', hk, Q, ns :: rest, F => by
      have hl : ∀ ns' ∈ negativesOf ns, (F ∈ levelFeeds (fun Q' => negFeeds k Q' rest) (Q ++ level ns) ns' ↔
          ∃ i ∈ I, F ∈ levelFeeds (fun Q' => negFeeds (k' i) Q' rest) (Q ++ level ns) ns') := fun ns' _ =>
        levelFeeds_mem_iff I hI _ _ (fun Q' F => negFeeds_mem_iff I hI k k' hk Q' rest F) _ ns' F
      have hn := negFeeds_mem_iff I hI k k' hk (addLast (.existential false (level ns)) Q) rest F
      obtain ⟨i0, hi0⟩ := List.exists_mem_of_ne_nil I hI
      simp only [negFeeds, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_attach, true_and,
        Subtype.exists, hn]
      constructor
      · rintro (h | ⟨i, hi, h⟩ | ⟨ns', hns', h⟩)
        · exact ⟨i0, hi0, Or.inl h⟩
        · exact ⟨i, hi, Or.inr (Or.inl h)⟩
        · obtain ⟨i, hi, h⟩ := (hl ns' hns').mp h
          exact ⟨i, hi, Or.inr (Or.inr ⟨ns', hns', h⟩)⟩
      · rintro ⟨i, hi, h | h | ⟨ns', hns', h⟩⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨i, hi, h⟩)
        · exact Or.inr (Or.inr ⟨ns', hns', (hl ns' hns').mpr ⟨i, hi, h⟩⟩)
  termination_by _ _ _ _ negs => (maxSize negs, negs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact maxSize_lex _ _
      | exact Prod.Lex.left _ _ (Nat.lt_of_lt_of_le (sizeOf_negativesOf _ ‹_›) (le_maxSize (List.mem_cons_self ..)))
end

theorem mem_paths {p : Projection} {x : List Match × Projection} :
    x ∈ p.paths ↔ x = ([], p) ∨ ∃ c ∈ p.children, ∃ y ∈ c.2.paths, x = (c.1 ++ y.1, y.2) := by
  rw [Projection.paths]
  simp only [List.mem_cons, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists, List.mem_map]
  constructor
  · rintro (h | ⟨c, hc, y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, y, hy, rfl⟩
  · rintro (h | ⟨c, hc, y, hy, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, y, hy, rfl⟩

theorem paths_ne_nil (p : Projection) : p.paths ≠ [] := by
  rw [Projection.paths]; exact List.cons_ne_nil _ _

/-- Going on to a projection's feeds is going on through the matches of any of
its paths. -/
theorem mem_projectionFeeds : ∀ (p : Projection) (Q F : List Match),
    F ∈ projectionFeeds p Q ↔ ∃ x ∈ p.paths, F ∈ levelFeeds (fun P => [P]) Q x.1
  | p, Q, F => by
    have hc : ∀ c ∈ p.children, (F ∈ levelFeeds (projectionFeeds c.2) Q c.1 ↔
        ∃ y ∈ c.2.paths, F ∈ levelFeeds (fun P => [P]) Q (c.1 ++ y.1)) := fun c _ => by
      rw [levelFeeds_mem_iff c.2.paths (paths_ne_nil _) _ (fun y Q' => levelFeeds (fun P => [P]) Q' y.1)
        (fun Q' F => mem_projectionFeeds c.2 Q' F)]
      simp only [levelFeeds_append]
    rw [projectionFeeds]
    simp only [List.mem_cons, List.mem_flatMap, List.mem_attach, true_and, Subtype.exists]
    constructor
    · rintro (rfl | ⟨c, hc', h⟩)
      · exact ⟨_, mem_paths.mpr (Or.inl rfl), by simp [levelFeeds]⟩
      · obtain ⟨y, hy, h⟩ := (hc c hc').mp h
        exact ⟨_, mem_paths.mpr (Or.inr ⟨c, hc', y, hy, rfl⟩), h⟩
    · rintro ⟨x, hx, h⟩
      rcases mem_paths.mp hx with rfl | ⟨c, hc', y, hy, rfl⟩
      · simp [levelFeeds] at h; exact Or.inl h
      · exact Or.inr ⟨c, hc', (hc c hc').mpr ⟨y, hy, h⟩⟩
termination_by p => sizeOf p
decreasing_by exact Projection.sizeOf_children ‹_›

theorem mem_feedsOf {s : Specification} {Fs : List (List Match)} {α : Type} {X : List α}
    {G : α → List (List Match)} (h : ∀ F, F ∈ Fs ↔ ∃ x ∈ X, F ∈ G x) (f : Specification) :
    f ∈ feedsOf s Fs ↔ ∃ x ∈ X, f ∈ feedsOf s (G x) := by
  simp only [feedsOf, List.mem_filter, List.mem_map, h]
  constructor
  · rintro ⟨⟨F, ⟨x, hx, hF⟩, rfl⟩, ht⟩; exact ⟨x, hx, ⟨F, hF, rfl⟩, ht⟩
  · rintro ⟨x, hx, ⟨F, hF, rfl⟩, ht⟩; exact ⟨⟨F, ⟨x, hx, hF⟩, rfl⟩, ht⟩

/-- **The feeds of a specification are the flat feeds of its descendants.** -/
theorem mem_buildFeeds {s : Specification} {f : Specification} :
    f ∈ buildFeeds s ↔ ∃ d ∈ s.descendants, f ∈ flatFeeds d := by
  have hF : ∀ F, F ∈ levelFeeds (projectionFeeds s.projection) [] s.matchList ↔
      ∃ x ∈ s.projection.paths, F ∈ levelFeeds (fun P => [P]) [] (s.matchList ++ x.1) := fun F => by
    rw [levelFeeds_mem_iff _ (paths_ne_nil _) _ _ (mem_projectionFeeds _) [] s.matchList F]
    simp only [levelFeeds_append]
  rw [buildFeeds, mem_feedsOf hF]
  simp only [Specification.descendants, List.mem_map]
  constructor
  · rintro ⟨x, hx, h⟩; exact ⟨_, ⟨x, hx, rfl⟩, h⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, h⟩; exact ⟨x, hx, h⟩

/-! ## Descendants -/

theorem paths_trans : ∀ (p : Projection) {x y : List Match × Projection}, x ∈ p.paths → y ∈ x.2.paths →
    (x.1 ++ y.1, y.2) ∈ p.paths
  | p, x, y, hx, hy => by
    rcases mem_paths.mp hx with rfl | ⟨c, hc, z, hz, rfl⟩
    · simpa using hy
    · exact mem_paths.mpr (Or.inr ⟨c, hc, _, paths_trans c.2 hz hy, by simp⟩)
termination_by p => sizeOf p
decreasing_by exact Projection.sizeOf_children ‹_›

/-- A descendant of a descendant is a descendant. -/
theorem descendants_trans {s d d' : Specification} (hd : d ∈ s.descendants) (hd' : d' ∈ d.descendants) :
    d' ∈ s.descendants := by
  simp only [Specification.descendants, List.mem_map] at hd hd' ⊢
  obtain ⟨x, hx, rfl⟩ := hd
  obtain ⟨y, hy, rfl⟩ := hd'
  exact ⟨_, paths_trans _ hx hy, by simp⟩

/-- The feeds of a descendant are feeds of the specification. -/
theorem buildFeeds_descendant {s d : Specification} (hd : d ∈ s.descendants) :
    ∀ f ∈ buildFeeds d, f ∈ buildFeeds s := fun f hf => by
  obtain ⟨d', hd', hf⟩ := mem_buildFeeds.mp hf
  exact mem_buildFeeds.mpr ⟨d', descendants_trans hd hd', hf⟩

/-- A descendant's matches go on from the specification's. -/
theorem descendants_prefix {s d : Specification} (hd : d ∈ s.descendants) :
    d.given = s.given ∧ ∃ X, d.matchList = s.matchList ++ X := by
  simp only [Specification.descendants, List.mem_map] at hd
  obtain ⟨x, -, rfl⟩ := hd
  exact ⟨rfl, x.1, rfl⟩

/-! ## The requirements -/

/-- **Append-only.** Every feed has one level of negative condition, over
matches with only path conditions. -/
theorem buildFeeds_feedShape (s : Specification) : ∀ f ∈ buildFeeds s, FeedShape f.matchList := fun f hf => by
  obtain ⟨d, -, hf⟩ := mem_buildFeeds.mp hf
  exact flatFeeds_feedShape d f hf

/-- Every feed binds each of its labels once, none of them a given: what
`feed_grow` needs, with `buildFeeds_feedShape`, to page it by bookmark. -/
theorem buildFeeds_nodup {s : Specification} (hwf : ∀ d ∈ s.descendants, WellFormed d)
    (hd : ∀ d ∈ s.descendants, DistinctLabels d) : ∀ f ∈ buildFeeds s, (names f.matchList).Nodup := fun f hf => by
  obtain ⟨d, hdd, hf⟩ := mem_buildFeeds.mp hf
  exact flatFeeds_nodup (hwf d hdd) (hd d hdd) f hf

/-- **Deferral.** A feed that carries any of the details of a top-level match
`m`, the matches after it or any child specification's, does so only for
tuples at which each of `m`'s negative conditions, with its positive conditions
joined, is either not witnessed, or has a witness with a fact of one of its own
negative conditions.

So a new client is not sent the details of an entity excluded by a fact that
nothing has tried to cancel: the names of a deleted menu item, while no restore
of its delete exists. A child specification is a specification, a descendant,
whose feeds are among these (`buildFeeds_descendant`), so this holds of an
entity a child specification matches too. Exactness is not possible:
`restore-revoked-and-unrevoked` (`FeedCases.lean`) is an entity still excluded
whose details a feed must carry, because telling it apart needs a nested
negative condition. -/
theorem feeds_defer {s : Specification} (hwf : ∀ d ∈ s.descendants, WellFormed d)
    (hd : ∀ d ∈ s.descendants, DistinctLabels d)
    {a b : List Match} {m : Match} (hs : s.matchList = a ++ m :: b) (G : Graph) (env : Env) :
    ∀ f ∈ buildFeeds s, (∃ y ∈ names (flatten b), y ∈ names f.matchList) →
      ∀ τ ∈ evalMatches G env f.matchList, ∀ ns ∈ negativesOf [m], Passes G τ ns := by
  intro f hf ⟨y, hyb, hyf⟩
  obtain ⟨d, hdd, hf⟩ := mem_buildFeeds.mp hf
  obtain ⟨-, X, hX⟩ := descendants_prefix hdd
  exact flatFeeds_defer (hwf d hdd) (hd d hdd) (a := a) (m := m) (b := b ++ X) (by rw [hX, hs]; simp) G env f hf
    ⟨y, by rw [flatten_append, names_append]; exact List.mem_append_left _ hyb, hyf⟩

/-! ## Consistency -/

/-- A solution of `ms` that a solution of `X` goes on from, binding nothing of
`ms` again, is determined by it. -/
theorem prefix_unique {G1 G2 : Graph} {env σ1 σ2 τ : Env} {ms X : List Match}
    (h1 : σ1 ∈ evalMatches G1 env ms) (h2 : σ2 ∈ evalMatches G2 env ms)
    (hτ1 : τ ∈ evalMatches G1 σ1 X) (hτ2 : τ ∈ evalMatches G2 σ2 X) (hdis : ∀ x ∈ names ms, x ∉ names X) :
    σ1 = σ2 := funext fun x => by
  by_cases hx : x ∈ names ms
  · rw [← evalMatches_frame hτ1 x (hdis x hx), ← evalMatches_frame hτ2 x (hdis x hx)]
  · rw [evalMatches_frame h1 x hx, evalMatches_frame h2 x hx]

/-- Two graphs with the same solutions of `ms ++ X` from `env` have the same
solutions of `X` from any solution of `ms` they share. -/
theorem prefix_iff {G1 G2 : Graph} {env σ : Env} {ms X : List Match}
    (h1 : σ ∈ evalMatches G1 env ms) (h2 : σ ∈ evalMatches G2 env ms) (hdis : ∀ x ∈ names ms, x ∉ names X)
    (h : ∀ τ, τ ∈ evalMatches G1 env (ms ++ X) ↔ τ ∈ evalMatches G2 env (ms ++ X)) :
    ∀ τ, τ ∈ evalMatches G1 σ X ↔ τ ∈ evalMatches G2 σ X := by
  have go : ∀ {G G' : Graph}, σ ∈ evalMatches G env ms → σ ∈ evalMatches G' env ms →
      (∀ τ, τ ∈ evalMatches G env (ms ++ X) → τ ∈ evalMatches G' env (ms ++ X)) →
      ∀ τ, τ ∈ evalMatches G σ X → τ ∈ evalMatches G' σ X := fun hG hG' h τ hτ => by
    obtain ⟨σ', hσ', hτ'⟩ := mem_evalMatches_append.mp (h τ (mem_evalMatches_append.mpr ⟨σ, hG, hτ⟩))
    exact prefix_unique hG hσ' hτ hτ' hdis ▸ hτ'
  exact fun τ => ⟨go h1 h2 (fun τ => (h τ).mp) τ, go h2 h1 (fun τ => (h τ).mpr) τ⟩

theorem names_sub_declared : ∀ {ms : List Match} {x : Name}, x ∈ names ms → x ∈ declaredMatches ms
  | .mk u cs :: rest, x, h => by
    simp only [names, List.map_cons, List.mem_cons, Match.unknown_mk] at h
    simp only [declaredMatches, List.mem_cons, List.mem_append]
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (names_sub_declared (ms := rest) h))

/-- **Nested results are determined by the solutions along each path.** Two
graphs that have the same solutions of the matches along every path to a child
specification read the same results, at every depth. -/
theorem reads_congr {g g' : Graph} : ∀ (p : Projection) (ms : List Match) (env : Env),
    (∀ x ∈ p.paths, (declaredMatches (ms ++ x.1)).Nodup) →
    (∀ x ∈ p.paths, ∀ σ, σ ∈ evalMatches g env (ms ++ x.1) ↔ σ ∈ evalMatches g' env (ms ++ x.1)) →
    ∀ r, p.Reads g ms env r ↔ p.Reads g' ms env r
  | p, ms, env, hd, he, .mk row cs => by
    have he0 : ∀ σ, σ ∈ evalMatches g env ms ↔ σ ∈ evalMatches g' env ms := by
      simpa using he _ (mem_paths.mpr (Or.inl rfl))
    -- A child's paths are paths of `p`, through the child.
    have hchild : ∀ c ∈ p.children, ∀ y ∈ c.2.paths, (c.1 ++ y.1, y.2) ∈ p.paths := fun c hc y hy =>
      mem_paths.mpr (Or.inr ⟨c, hc, y, hy, rfl⟩)
    have hih : ∀ σ ∈ evalMatches g env ms, ∀ c ∈ p.children, ∀ r,
        c.2.Reads g c.1 σ r ↔ c.2.Reads g' c.1 σ r := fun σ hσ c hc =>
      reads_congr c.2 c.1 σ
        (fun y hy => by
          have := hd _ (hchild c hc y hy)
          rw [declared_append] at this
          exact (List.nodup_append.mp this).2.1)
        (fun y hy => by
          have hnd := hd _ (hchild c hc y hy)
          rw [declared_append] at hnd
          exact prefix_iff hσ ((he0 σ).mp hσ)
            (fun x hx hx' => (List.nodup_append.mp hnd).2.2 x (names_sub_declared hx) x
              (names_sub_declared hx') rfl)
            (by simpa only [List.append_assoc] using he _ (hchild c hc y hy)))
    rw [Projection.Reads, Projection.Reads]
    constructor
    · rintro ⟨σ, hσ, hrow, hlen, hch⟩
      refine ⟨σ, (he0 σ).mp hσ, hrow, hlen, fun x hx r => (hch x hx r).trans (hih σ hσ _ x.1.2 r)⟩
    · rintro ⟨σ, hσ, hrow, hlen, hch⟩
      have hσ' := (he0 σ).mpr hσ
      refine ⟨σ, hσ', hrow, hlen, fun x hx r => (hch x hx r).trans (hih σ hσ' _ x.1.2 r).symm⟩
termination_by p => sizeOf p
decreasing_by exact Projection.sizeOf_children ‹_›

section Top
variable {g : Graph} {B : List Fact}

/-- **The feeds cover the specification.** A replica `g` that holds the givens
and every fact the feeds deliver on the replicator's graph `g ++ B`, where `B`
is what of that graph the replica does not hold, reads what the replicator
reads, the results of its child specifications included, at every depth.

`B` is fresh to `g` because a replica saves each fact with its predecessors.
Each descendant declares each label once (`DistinctLabels`), so that joining a
positive condition into its level binds nothing twice, and every match has a
path condition (`RootedMatches`), so that a feed walking only to predecessors
reaches nothing the replica does not hold. -/
theorem feeds_cover {s : Specification} (hwf : ∀ d ∈ s.descendants, WellFormed d)
    (hd : ∀ d ∈ s.descendants, DistinctLabels d) (hr : ∀ d ∈ s.descendants, RootedMatches d.matchList)
    (hf : Fresh g B) {env : Env} (henv : Settled B env)
    (hgiv : ∀ l ∈ s.given, g.has env l = true) (hdel : ∀ id ∈ delivered s (g ++ B) env, Outside B id) :
    ∀ r, s.Reads g env r ↔ s.Reads (g ++ B) env r := by
  have hpath : ∀ x ∈ s.projection.paths,
      ({ given := s.given, matchList := s.matchList ++ x.1, projection := x.2 } : Specification) ∈ s.descendants :=
    fun x hx => List.mem_map_of_mem hx
  have hgivG : ∀ l ∈ s.given, (g ++ B).has env l = true := fun l hl => (has_settled henv l).symm ▸ hgiv l hl
  intro r
  simp only [Specification.Reads, List.all_eq_true.mpr hgiv, List.all_eq_true.mpr hgivG, true_and]
  exact reads_congr _ _ _ (fun x hx => hd _ (hpath x hx)) (fun x hx =>
    flatFeeds_cover (hwf _ (hpath x hx)) (hd _ (hpath x hx)) (hr _ (hpath x hx)) hf henv fun f hf id hid =>
      hdel id (List.mem_flatMap.mpr ⟨f, mem_buildFeeds.mpr ⟨_, hpath x hx, hf⟩, hid⟩)) r

/-- **Eventual consistency.** A replica that has paged every feed of `s` until a
page came back empty, and holds what the pages delivered with its
predecessors, reads what the replicator reads.

The replica is `g`; what of the replicator's graph it does not hold is `B`.
`caught_start`, `caught_page` and `feed_grow` keep each feed `Caught` from the
first page to the last while the replicator's graph grows; this theorem takes
the last step, from `caught_sync` and `feeds_cover`. -/
theorem feed_converges {s : Specification} (hwf : ∀ d ∈ s.descendants, WellFormed d)
    (hd : ∀ d ∈ s.descendants, DistinctLabels d) (hr : ∀ d ∈ s.descendants, RootedMatches d.matchList)
    (hf : Fresh g B) {env : Env} (henv : Settled B env)
    (hgiv : ∀ l ∈ s.given, g.has env l = true)
    (bookmark : Specification → List Nat) (D : List FactId)
    (hcaught : ∀ f ∈ buildFeeds s, Caught (f.tuples (g ++ B) env) (bookmark f) D)
    (hsync : ∀ f ∈ buildFeeds s, IsPage (f.tuples (g ++ B) env) [] (bookmark f))
    (hheld : ∀ id ∈ D, Outside B id) :
    ∀ r, s.Reads g env r ↔ s.Reads (g ++ B) env r :=
  feeds_cover hwf hd hr hf henv hgiv fun id hid => by
    obtain ⟨f, hf, hid⟩ := List.mem_flatMap.mp hid
    obtain ⟨t, ht, hid⟩ := List.mem_flatten.mp hid
    exact hheld id (caught_sync (hcaught f hf) (hsync f hf) t ht id hid)

end Top

end JinagaSpec
