import JinagaSpec.Proofs.Cascade.MapProps

/-!
# Cascade: aggregates

`aggregate_correct`: forwarding each event, then emitting one change per
affected parent whose aggregate changed, keeps the output equal to the
denotation. A move changes two parents; any other child event changes one.
Nothing else changes an aggregate, because only the children at level `c` with
a given parent contribute to it.
-/
namespace JinagaSpec.Cascade

variable {c : Level} {contributes : Props → Bool} {g : List Props → Option Val}

/-! ## A tree's list order does not change an aggregate -/

theorem perm_sum_int {l₁ l₂ : List Int} (h : l₁.Perm l₂) : l₁.sum = l₂.sum := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [ih]
  | swap x y l => simp only [List.sum_cons]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem nodup_of_keys {T : Tree} (h : (T.map (·.1)).Nodup) : T.Nodup :=
  List.Pairwise.of_map (·.1) (fun _ _ hne heq => hne (heq ▸ rfl)) h

theorem perm_of_equiv {T U : Tree} (hT : T.WF) (hU : U.WF) (h : T.Equiv U) : T.Perm U := by
  rw [List.perm_ext_iff_of_nodup (nodup_of_keys hT.nodup) (nodup_of_keys hU.nodup)]
  rintro ⟨id, n⟩
  constructor
  · intro hm; exact mem_of_get ((h id).symm.trans (get_of_mem hT.nodup hm))
  · intro hm; exact mem_of_get ((h id).trans (get_of_mem hU.nodup hm))

/-- An aggregate reads only which children contribute. -/
theorem aggregate_eq_of_eq {T U : Tree} {k : Key}
    (h : contributors c contributes T k = contributors c contributes U k) :
    aggregate c contributes g T k = aggregate c contributes g U k := by
  unfold aggregate; rw [h]

/-- An aggregate whose `g` ignores the order of its values ignores the order of
the tree. -/
theorem aggregate_eq_of_perm (hg : ∀ l₁ l₂ : List Props, l₁.Perm l₂ → g l₁ = g l₂) {T U : Tree} {k : Key}
    (h : (contributors c contributes T k).Perm (contributors c contributes U k)) :
    aggregate c contributes g T k = aggregate c contributes g U k := by
  unfold aggregate
  cases hT : contributors c contributes T k <;> cases hU : contributors c contributes U k
  · rfl
  · rw [hT, hU] at h; exact absurd h.symm.eq_nil (by simp)
  · rw [hT, hU] at h; exact absurd h.eq_nil (by simp)
  · rw [hT, hU] at h; exact hg _ _ (h.map _)

theorem aggregate_denotation (c : Level) (q : String) (contributes : Props → Bool)
    (g : List Props → Option Val) (hg : ∀ l₁ l₂ : List Props, l₁.Perm l₂ → g l₁ = g l₂) :
    Denotation (aggregate.F c q contributes g) := by
  refine ⟨fun _ hT => mapProps_wf hT, fun T U hT hU h id => ?_⟩
  simp only [aggregate.F, get_mapProps, h id]
  congr 1; funext n; unfold mapNode; split
  · dsimp only; rw [aggregate_eq_of_perm hg ((perm_of_equiv hT hU h).filter _)]
  · rfl

/-! ## The aggregates ignore order -/

theorem sumBy_perm (w : Props → Int) : ∀ l₁ l₂ : List Props, l₁.Perm l₂ → sumBy w l₁ = sumBy w l₂ :=
  fun _ _ h => by simp only [sumBy, Option.some.injEq]; exact perm_sum_int (h.map _)

theorem minStep_comm (x y : Val) (a : Option Val) : minStep x (minStep y a) = minStep y (minStep x a) := by
  cases a with
  | none => simp only [minStep, Option.some.injEq]; exact Int.min_comm x y
  | some a =>
    simp only [minStep, Option.some.injEq]
    rw [← Int.min_assoc, Int.min_comm x y, Int.min_assoc]

theorem optMin_perm : ∀ {l₁ l₂ : List Val}, l₁.Perm l₂ → optMin l₁ = optMin l₂ := by
  intro l₁ l₂ h
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [optMin, List.foldr_cons] at ih ⊢; rw [ih]
  | swap x y l => simp only [optMin, List.foldr_cons]; exact minStep_comm y x _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem maxStep_comm (x y : Val) (a : Option Val) : maxStep x (maxStep y a) = maxStep y (maxStep x a) := by
  cases a with
  | none => simp only [maxStep, Option.some.injEq]; exact Int.max_comm x y
  | some a =>
    simp only [maxStep, Option.some.injEq]
    rw [← Int.max_assoc, Int.max_comm x y, Int.max_assoc]

theorem optMax_perm : ∀ {l₁ l₂ : List Val}, l₁.Perm l₂ → optMax l₁ = optMax l₂ := by
  intro l₁ l₂ h
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [optMax, List.foldr_cons] at ih ⊢; rw [ih]
  | swap x y l => simp only [optMax, List.foldr_cons]; exact maxStep_comm y x _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem minOf_perm (p : String) : ∀ l₁ l₂ : List Props, l₁.Perm l₂ → minOf p l₁ = minOf p l₂ :=
  fun _ _ h => optMin_perm (h.filterMap _)

theorem maxOf_perm (p : String) : ∀ l₁ l₂ : List Props, l₁.Perm l₂ → maxOf p l₁ = maxOf p l₂ :=
  fun _ _ h => optMax_perm (h.filterMap _)

theorem averageOf_perm (p : String) :
    ∀ l₁ l₂ : List Props, l₁.Perm l₂ → averageOf p l₁ = averageOf p l₂ := by
  intro l₁ l₂ h
  have hv := h.filterMap (· p)
  unfold averageOf
  cases h1 : l₁.filterMap (· p) <;> cases h2 : l₂.filterMap (· p)
  · rfl
  · rw [h1, h2] at hv; exact absurd hv.symm.eq_nil (by simp)
  · rw [h1, h2] at hv; exact absurd hv.eq_nil (by simp)
  · rw [h1, h2] at hv
    simp only [Option.some.injEq]
    rw [perm_sum_int hv, hv.length_eq]

/-! ## Which events leave an aggregate alone -/

theorem filter_map_irrel {α : Type} (p : α → Bool) (g : α → α) (L : List α)
    (h : ∀ e ∈ L, g e ≠ e → p (g e) = false ∧ p e = false) :
    (L.map g).filter p = L.filter p := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [List.map_cons, List.filter_cons]
    rw [ih fun e' he' => h e' (List.mem_cons_of_mem _ he')]
    by_cases hg : g e = e
    · rw [hg]
    · obtain ⟨h1, h2⟩ := h e (List.mem_cons_self) hg; simp [h1, h2]

theorem filter_filter_irrel {α : Type} (p q : α → Bool) (L : List α)
    (h : ∀ e ∈ L, q e = false → p e = false) :
    (L.filter q).filter p = L.filter p := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    have ih' := ih fun e' he' => h e' (List.mem_cons_of_mem _ he')
    by_cases hq : q e = true
    · simp [List.filter_cons, hq, ih']
    · have hp := h e List.mem_cons_self (by simpa using hq)
      simp [hq, hp, ih']

/-- The contributors to parent `k` are unchanged by an event on node `y`
that contributes to `k` neither before nor after. -/
theorem contributors_update {T : Tree} (hwf : T.WF) (y : Id) (f : Node → Node) (k : Key)
    (hy : ∀ n, T.get y = some n →
      ¬(y.1 = c ∧ n.parent = some k ∧ contributes n.props = true) ∧
      ¬(y.1 = c ∧ (f n).parent = some k ∧ contributes (f n).props = true)) :
    contributors c contributes (T.update y f) k = contributors c contributes T k := by
  unfold contributors Tree.update
  apply filter_map_irrel
  intro e he hne
  by_cases hey : e.1 = y
  · obtain ⟨h1, h2⟩ := hy e.2 (hey ▸ get_of_mem hwf.nodup he)
    simp only [beq_iff_eq, hey, ↓reduceIte, decide_eq_false_iff_not]
    exact ⟨h2, h1⟩
  · simp [hey] at hne

theorem contributors_filter {T : Tree} (hwf : T.WF) (y : Id) (k : Key)
    (hy : ∀ n, T.get y = some n → ¬(y.1 = c ∧ n.parent = some k ∧ contributes n.props = true)) :
    contributors c contributes (T.filter (·.1 != y)) k = contributors c contributes T k := by
  unfold contributors
  apply filter_filter_irrel
  rintro ⟨id, n⟩ he hq
  simp only [bne_eq_false_iff_eq] at hq
  subst hq
  simpa [decide_eq_false_iff_not] using hy n (get_of_mem hwf.nodup he)

/-! ## Changing the aggregates of some parents -/

/-- The aggregate changes the step emits for parents `K`. -/
def touches (P : Level) (q : String) (v₁ v₂ : Key → Option Val) (K : List Key) : List Event :=
  K.flatMap fun k => if v₁ k = v₂ k then [] else [.modified P k q (v₁ k) (v₂ k)]

theorem touches_cons (P : Level) (q : String) (v₁ v₂ : Key → Option Val) (j : Key)
    (K : List Key) : touches P q v₁ v₂ (j :: K) =
      (if v₁ j = v₂ j then [] else [.modified P j q (v₁ j) (v₂ j)]) ++ touches P q v₁ v₂ K := by
  simp [touches, List.flatMap_cons]

theorem touches_congr (P : Level) (q : String) {v₁ v₁' : Key → Option Val} (v₂ : Key → Option Val)
    (K : List Key) (h : ∀ k ∈ K, v₁ k = v₁' k) : touches P q v₁ v₂ K = touches P q v₁' v₂ K := by
  induction K with
  | nil => rfl
  | cons j K ih =>
    simp only [touches, List.flatMap_cons] at ih ⊢
    rw [h j List.mem_cons_self, ih fun k hk => h k (List.mem_cons_of_mem _ hk)]

/-- **`touchAll`.** Emitting a change for each parent in `K` whose value
changed takes the output from values `v₁` to values `v₂`, provided `K` lists
every parent whose value changed, each once, and each exists. -/
theorem touchAll {P : Level} {q : String} {T' : Tree} :
    ∀ (K : List Key) (v₁ v₂ : Key → Option Val) (U : Tree), K.Nodup →
      (∀ k, k ∉ K → v₁ k = v₂ k) → (∀ k ∈ K, (T'.get (P, k)).isSome) →
      U.Equiv (T'.mapProps P fun k ps => ps.set q (v₁ k)) →
      ∃ V, U.applyAll (touches P q v₁ v₂ K) = some V ∧
        V.Equiv (T'.mapProps P fun k ps => ps.set q (v₂ k)) := by
  intro K
  induction K with
  | nil =>
    intro v₁ v₂ U _ hv _ hU
    have : v₁ = v₂ := funext fun k => hv k (by simp)
    subst this; exact ⟨U, rfl, hU⟩
  | cons j K ih =>
    intro v₁ v₂ U hnd hv hex hU
    obtain ⟨hj, hnd⟩ := List.nodup_cons.mp hnd
    let v₁' : Key → Option Val := fun k => if k = j then v₂ j else v₁ k
    have htail : touches P q v₁ v₂ K = touches P q v₁' v₂ K :=
      touches_congr P q v₂ K fun k hk => by
        have : k ≠ j := fun h => hj (h ▸ hk)
        simp [v₁', this]
    have hv' : ∀ k, k ∉ K → v₁' k = v₂ k := by
      intro k hk; by_cases h : k = j
      · simp [v₁', h]
      · simp only [v₁', h, ↓reduceIte]; exact hv k (by simp [h, hk])
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (hex j List.mem_cons_self)
    have hUj : U.get (P, j) = some (mapNode P (fun k ps => ps.set q (v₁ k)) (P, j) n) := by
      rw [hU, get_mapProps, hn]; rfl
    by_cases hsame : v₁ j = v₂ j
    · have hU' : U.Equiv (T'.mapProps P fun k ps => ps.set q (v₁' k)) := by
        have : v₁' = v₁ := funext fun k => by by_cases h : k = j <;> simp [v₁', h, hsame]
        rwa [this]
      obtain ⟨V, hV, hVe⟩ := ih v₁' v₂ U hnd hv' (fun k hk => hex k (List.mem_cons_of_mem _ hk)) hU'
      refine ⟨V, ?_, hVe⟩
      rw [touches_cons, ite_eq_left hsame, List.nil_append, htail]; exact hV
    · have happ : U.apply (.modified P j q (v₁ j) (v₂ j)) = some (U.update (P, j)
          fun n => { n with props := n.props.set q (v₂ j) }) :=
        apply_modified.mpr ⟨_, hUj, by simp [mapNode, Props.set], hsame, rfl⟩
      have hU1 : (U.update (P, j) fun n => { n with props := n.props.set q (v₂ j) }).Equiv
          (T'.mapProps P fun k ps => ps.set q (v₁' k)) := by
        intro id
        rw [get_update, get_mapProps]
        split
        · rename_i h; subst h; rw [hUj, hn]; simp [mapNode, v₁', Props.set_set_self]
        · rw [hU, get_mapProps]
          congr 1; funext m; unfold mapNode; split
          · rename_i hl; obtain ⟨l, k⟩ := id; simp only at hl; subst hl
            have : k ≠ j := fun h => by subst h; simp_all
            simp [v₁', this]
          · rfl
      obtain ⟨V, hV, hVe⟩ := ih v₁' v₂ _ hnd hv' (fun k hk => hex k (List.mem_cons_of_mem _ hk)) hU1
      refine ⟨V, ?_, hVe⟩
      rw [touches_cons, ite_eq_right hsame, List.singleton_append, Tree.applyAll, happ, Option.bind_some,
        htail]
      exact hV

/-! ## The step -/

theorem dropLast_ne {c : Level} (hc : c ≠ []) : c.dropLast ≠ c := fun h => by
  have := congrArg List.length h
  simp only [List.length_dropLast] at this
  have : c.length ≠ 0 := by simpa using hc
  omega

/-- Forward one event, then change the aggregates of parents `K`. -/
theorem aggregate_finish {q : String} {T T' U : Tree} (e' : Event) (K : List Key)
    (hU : (aggregate.F c q contributes g T).apply e' = some U)
    (hUe : U.Equiv (T'.mapProps c.dropLast fun k ps => ps.set q (aggregate c contributes g T k)))
    (hnd : K.Nodup)
    (hchg : ∀ k, k ∉ K → aggregate c contributes g T k = aggregate c contributes g T' k)
    (hex : ∀ k ∈ K, (T'.get (c.dropLast, k)).isSome) :
    ∃ V, (aggregate.F c q contributes g T).applyAll
        (e' :: touches c.dropLast q (aggregate c contributes g T) (aggregate c contributes g T') K)
        = some V ∧ V.Equiv (aggregate.F c q contributes g T') := by
  simp only [Tree.applyAll, hU, Option.bind_some]
  exact touchAll K _ _ U hnd hchg hex hUe

/-- A child's parent exists. -/
theorem parent_exists {T : Tree} (hwf : T.WF) {l : Level} {k j : Key} {n : Node}
    (hn : T.get (l, k) = some n) (hp : n.parent = some j) : (T.get (l.dropLast, j)).isSome := by
  have := hwf.parents _ _ hn
  rw [hp] at this
  simp only [Tree.parentOk, Bool.and_eq_true] at this
  exact this.2

/-- **`aggregate_correct`.** -/
theorem aggregate_correct (c : Level) (hc : c ≠ []) (q : String) (contributes : Props → Bool)
    (g : List Props → Option Val) :
    Correct (aggregateStep c q contributes g) (aggregate.F c q contributes g) := by
  intro T e T' hwf he
  have hP := dropLast_ne hc
  simp only [aggregateStep, he]
  cases e with
  | added l k p ps =>
    obtain ⟨hn, hpok, rfl⟩ := apply_added.mp he
    have hsame : ∀ j, (l ≠ c ∨ p ≠ some j) →
        aggregate c contributes g (((l, k), ⟨p, ps⟩) :: T) j = aggregate c contributes g T j := by
      intro j hj
      refine (aggregate_eq_of_eq ?_).symm
      simp only [contributors, List.filter_cons]
      rcases hj with hj | hj <;> simp [hj]
    by_cases hl : l = c.dropLast
    · subst hl
      have hagg : aggregate c contributes g (((c.dropLast, k), ⟨p, ps⟩) :: T) =
          aggregate c contributes g T := funext fun j => hsame j (Or.inl hP)
      simp only [↓reduceIte, applyAll_single, aggregate.F, hagg]
      exact mapProps_added (φ := fun k ps => ps.set q (aggregate c contributes g T k)) he
    · simp only [hl, ↓reduceIte]
      obtain ⟨U, hU, hUe⟩ := mapProps_forward (s := c.dropLast)
        (φ := fun k ps => ps.set q (aggregate c contributes g T k))
        hwf he (by simp [Event.propsLevel, hl])
      let K := if l = c then p.toList else []
      have hK : (if l = c then p.toList.flatMap fun j =>
          if aggregate c contributes g T j = aggregate c contributes g (((l, k), ⟨p, ps⟩) :: T) j
          then [] else [.modified c.dropLast j q (aggregate c contributes g T j)
            (aggregate c contributes g (((l, k), ⟨p, ps⟩) :: T) j)] else []) =
          touches c.dropLast q (aggregate c contributes g T)
            (aggregate c contributes g (((l, k), ⟨p, ps⟩) :: T)) K := by
        by_cases hlc : l = c
        · simp only [K, hlc, ↓reduceIte, touches]
        · simp only [K, hlc, ↓reduceIte, touches, List.flatMap_nil]
      rw [hK]
      refine aggregate_finish _ K hU hUe ?_ ?_ ?_
      · by_cases hlc : l = c <;> cases p <;> simp [K, hlc]
      · intro j hj
        refine (hsame j ?_).symm
        by_cases hlc : l = c
        · exact Or.inr fun h => hj (by simp [K, hlc, h])
        · exact Or.inl hlc
      · intro j hj
        by_cases hlc : l = c
        · subst hlc
          have hpj : p = some j := by cases p <;> simp_all [K]
          subst hpj
          simp only [Tree.parentOk, Bool.and_eq_true] at hpok
          rw [get_cons]; split <;> simp_all
        · simp [K, hlc] at hj
  | removed l k =>
    obtain ⟨hs, hch, rfl⟩ := apply_removed.mp he
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨U, hU, hUe⟩ := mapProps_forward (s := c.dropLast)
      (φ := fun k ps => ps.set q (aggregate c contributes g T k)) hwf he (by simp [Event.propsLevel])
    let K := if l = c then n.parent.toList else []
    have hK : (if l = c then ((T.get (c, k)).bind (·.parent)).toList.flatMap fun j =>
        if aggregate c contributes g T j = aggregate c contributes g (T.filter (·.1 != (l, k))) j
        then [] else [.modified c.dropLast j q (aggregate c contributes g T j)
          (aggregate c contributes g (T.filter (·.1 != (l, k))) j)] else []) =
        touches c.dropLast q (aggregate c contributes g T)
          (aggregate c contributes g (T.filter (·.1 != (l, k)))) K := by
      by_cases hlc : l = c
      · subst hlc; simp [K, hn, touches]
      · simp [K, hlc, touches]
    dsimp only
    rw [hK]
    refine aggregate_finish _ K hU hUe ?_ ?_ ?_
    · by_cases hlc : l = c <;> cases hp : n.parent <;> simp [K, hlc, hp]
    · intro j hj
      apply aggregate_eq_of_eq
      refine (contributors_filter hwf _ j fun m hm => ?_).symm
      rw [hn] at hm; cases hm
      rintro ⟨hlc, hpar, -⟩
      simp only at hlc
      exact hj (by simp [K, hlc, hpar])
    · intro j hj
      by_cases hlc : l = c
      · subst hlc
        have hpar : n.parent = some j := by
          cases hp : n.parent <;> simp_all [K]
        have hne : (l.dropLast, j) ≠ (l, k) := fun h => hP (Prod.mk.inj h).1
        simp only [get_filter, hne, ↓reduceIte]
        exact parent_exists hwf hn hpar
      · simp [K, hlc] at hj
  | modified l k p old new =>
    obtain ⟨n, hn, h1, h2, rfl⟩ := apply_modified.mp he
    let f : Node → Node := fun n => { n with props := n.props.set p new }
    have hsame : ∀ j, (l ≠ c ∨ n.parent ≠ some j) →
        aggregate c contributes g (T.update (l, k) f) j = aggregate c contributes g T j := by
      intro j hj
      apply aggregate_eq_of_eq
      refine contributors_update hwf _ f j fun m hm => ?_
      rw [hn] at hm; cases hm
      rcases hj with hj | hj <;> simp [f, hj]
    by_cases hq : l = c.dropLast ∧ p = q
    · obtain ⟨rfl, rfl⟩ := hq
      have hagg : aggregate c contributes g (T.update (c.dropLast, k) f) =
          aggregate c contributes g T := funext fun j => hsame j (Or.inl hP)
      simp only [and_self, ↓reduceIte, aggregate.F]
      refine ⟨_, rfl, ?_⟩
      rw [hagg]
      exact mapProps_hidden (φ := fun k ps => ps.set p (aggregate c contributes g T k)) he
        fun ps => Props.set_set_self _ _ _ _
    · simp only [hq, ↓reduceIte]
      have hfwd : ∃ U, (aggregate.F c q contributes g T).apply (.modified l k p old new) = some U ∧
          U.Equiv ((T.update (l, k) f).mapProps c.dropLast
            fun k ps => ps.set q (aggregate c contributes g T k)) := by
        by_cases hl : l = c.dropLast
        · subst hl
          have hpq : p ≠ q := fun h => hq ⟨rfl, h⟩
          exact mapProps_modified he (fun ps => by simp [Props.set, hpq])
            (fun ps => Props.set_comm _ hpq _ _)
        · exact mapProps_forward (s := c.dropLast) hwf he (by simp [Event.propsLevel, hl])
      obtain ⟨U, hU, hUe⟩ := hfwd
      let K := if l = c then n.parent.toList else []
      have hK : (if l = c then ((T.get (c, k)).bind (·.parent)).toList.flatMap fun j =>
          if aggregate c contributes g T j = aggregate c contributes g (T.update (l, k) f) j
          then [] else [.modified c.dropLast j q (aggregate c contributes g T j)
            (aggregate c contributes g (T.update (l, k) f) j)] else []) =
          touches c.dropLast q (aggregate c contributes g T)
            (aggregate c contributes g (T.update (l, k) f)) K := by
        by_cases hlc : l = c
        · subst hlc; simp [K, hn, touches]
        · simp [K, hlc, touches]
      rw [hK]
      refine aggregate_finish _ K hU hUe ?_ ?_ ?_
      · by_cases hlc : l = c <;> cases hp : n.parent <;> simp [K, hlc, hp]
      · intro j hj
        refine (hsame j ?_).symm
        by_cases hlc : l = c
        · exact Or.inr fun h => hj (by simp [K, hlc, h])
        · exact Or.inl hlc
      · intro j hj
        by_cases hlc : l = c
        · subst hlc
          have hpar : n.parent = some j := by cases hp : n.parent <;> simp_all [K]
          rw [isSome_get_update]; exact parent_exists hwf hn hpar
        · simp [K, hlc] at hj
  | placed l k a b =>
    obtain ⟨n, hn, h1, h2, h3, rfl⟩ := apply_placed.mp he
    let f : Node → Node := fun n => { n with parent := some b }
    obtain ⟨U, hU, hUe⟩ := mapProps_forward (s := c.dropLast)
      (φ := fun k ps => ps.set q (aggregate c contributes g T k)) hwf he (by simp [Event.propsLevel])
    let K := if l = c then [a, b] else []
    have hK : (if l = c then
        (if aggregate c contributes g T a = aggregate c contributes g (T.update (l, k) f) a then []
          else [.modified c.dropLast a q (aggregate c contributes g T a)
            (aggregate c contributes g (T.update (l, k) f) a)]) ++
        (if aggregate c contributes g T b = aggregate c contributes g (T.update (l, k) f) b then []
          else [.modified c.dropLast b q (aggregate c contributes g T b)
            (aggregate c contributes g (T.update (l, k) f) b)]) else []) =
        touches c.dropLast q (aggregate c contributes g T)
          (aggregate c contributes g (T.update (l, k) f)) K := by
      by_cases hlc : l = c
      · simp [K, hlc, touches]
      · simp [K, hlc, touches]
    dsimp only
    rw [hK]
    refine aggregate_finish _ K hU hUe ?_ ?_ ?_
    · by_cases hlc : l = c <;> simp [K, hlc, h2]
    · intro j hj
      apply aggregate_eq_of_eq
      refine (contributors_update hwf _ f j fun m hm => ?_).symm
      rw [hn] at hm; cases hm
      by_cases hlc : l = c
      · have hja : a ≠ j := fun h => hj (by simp [K, hlc, h])
        have hjb : b ≠ j := fun h => hj (by simp [K, hlc, h])
        simp [f, h1, hja, hjb]
      · simp [hlc]
    · intro j hj
      by_cases hlc : l = c
      · subst hlc
        rw [isSome_get_update]
        simp only [K, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact parent_exists hwf hn h1
        · simp only [Tree.parentOk, Bool.and_eq_true] at h3; exact h3.2
      · simp [K, hlc] at hj

/-! ## `min`, `max` and `average` -/

/-- **`min_correct`.** `min(p)` over the children at `c`: the least defined `p`. -/
theorem min_correct (c : Level) (hc : c ≠ []) (q p : String) :
    Correct (aggregateStep c q (fun _ => true) (minOf p)) (aggregate.F c q (fun _ => true) (minOf p)) :=
  aggregate_correct c hc q _ _

theorem min_denotation (c : Level) (q p : String) :
    Denotation (aggregate.F c q (fun _ => true) (minOf p)) :=
  aggregate_denotation c q _ _ (minOf_perm p)

/-- **`max_correct`.** -/
theorem max_correct (c : Level) (hc : c ≠ []) (q p : String) :
    Correct (aggregateStep c q (fun _ => true) (maxOf p)) (aggregate.F c q (fun _ => true) (maxOf p)) :=
  aggregate_correct c hc q _ _

theorem max_denotation (c : Level) (q p : String) :
    Denotation (aggregate.F c q (fun _ => true) (maxOf p)) :=
  aggregate_denotation c q _ _ (maxOf_perm p)

/-- **`average_correct`.** -/
theorem average_correct (c : Level) (hc : c ≠ []) (q p : String) :
    Correct (aggregateStep c q (fun _ => true) (averageOf p)) (aggregate.F c q (fun _ => true) (averageOf p)) :=
  aggregate_correct c hc q _ _

theorem average_denotation (c : Level) (q p : String) :
    Denotation (aggregate.F c q (fun _ => true) (averageOf p)) :=
  aggregate_denotation c q _ _ (averageOf_perm p)

end JinagaSpec.Cascade
