import JinagaSpec.Proofs.Flat

/-!
# Deferral

`feeds_defer`: a feed that carries an entity's details, the top-level matches
after it, does so only where each of the entity's negative conditions is either
unwitnessed or has a witness with a cancelling fact. So a new client is not
sent the details of an entity that something excludes and nothing has tried to
cancel: a deleted menu item's names, while no restore exists.
-/
namespace JinagaSpec

/-! ## Structure -/

theorem flatten_append : ∀ (a b : List Match), flatten (a ++ b) = flatten a ++ flatten b
  | [], _ => by simp [flatten, flattenMatches]
  | .mk u cs :: a, b => by
    simp only [flatten, List.cons_append, flattenMatches_cons, List.append_assoc]
    rw [show flattenMatches (fun _ => true) (a ++ b) = flatten (a ++ b) from rfl, flatten_append a b]

theorem flatten_cons (m : Match) (ms : List Match) : flatten (m :: ms) = flatten [m] ++ flatten ms :=
  flatten_append [m] ms

theorem level_append (a b : List Match) : level (a ++ b) = level a ++ level b := by
  simp [level, flatten_append]

theorem negativesOf_append (a b : List Match) : negativesOf (a ++ b) = negativesOf a ++ negativesOf b := by
  simp [negativesOf, flatten_append]

theorem names_level (ms : List Match) : names (level ms) = names (flatten ms) := names_paths _

theorem levelFeeds_append (k : List Match → List (List Match)) :
    ∀ (P a b : List Match), levelFeeds k P (a ++ b) = levelFeeds (fun Q => levelFeeds k Q b) P a
  | P, [], b => by simp [levelFeeds]
  | P, m :: a, b => by
    rw [List.cons_append, levelFeeds, levelFeeds]
    congr 1
    funext Q
    exact levelFeeds_append k Q a b

theorem names_addLast (c : Condition) : ∀ Q : List Match, names (addLast c Q) = names Q
  | [] => rfl
  | [.mk u cs] => rfl
  | m :: m' :: ms => by
    rw [show addLast c (m :: m' :: ms) = m :: addLast c (m' :: ms) from rfl]
    simp only [names, List.map_cons] at *
    have := names_addLast c (m' :: ms)
    simp only [names] at this
    rw [this]; simp

/-- A filter on the last match keeps the solutions at which it holds. -/
theorem mem_addLast {G : Graph} {ns : List Match} :
    ∀ {Q : List Match} {e σ : Env}, Q ≠ [] → σ ∈ evalMatches G e (addLast (.existential false ns) Q) →
      σ ∈ evalMatches G e Q ∧ evalMatches G σ ns = []
  | [], _, _, hQ, _ => absurd rfl hQ
  | [.mk u cs], e, σ, _, h => by
    simp only [addLast, Match.addCondition] at h
    obtain ⟨f, hf, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
    simp only [evalMatches, List.mem_singleton] at hr
    subst hr
    rw [allHold_append] at hc
    simp only [Bool.and_eq_true, allHold, holds, Bool.and_true] at hc
    refine ⟨mem_evalMatches_cons.mpr ⟨f, hf, ht, hc.1, by simp [evalMatches]⟩, ?_⟩
    cases h2 : evalMatches G (e.bind u.name f.id) ns <;> simp_all
  | m :: m' :: ms, e, σ, _, h => by
    rw [show addLast (.existential false ns) (m :: m' :: ms) = m :: addLast (.existential false ns) (m' :: ms) from rfl] at h
    obtain ⟨u, cs⟩ := m
    obtain ⟨f, hf, ht, hc, hr⟩ := mem_evalMatches_cons.mp h
    obtain ⟨h1, h2⟩ := mem_addLast (List.cons_ne_nil _ _) hr
    exact ⟨mem_evalMatches_cons.mpr ⟨f, hf, ht, hc, h1⟩, h2⟩

/-! ## What a feed that goes on shows -/

/-- The negative condition `ns` is not witnessed at `σ`, or one of its
witnesses has a fact of one of its own negative conditions: something has
tried to cancel it. -/
def Passes (G : Graph) (σ : Env) (ns : List Match) : Prop :=
  evalMatches G σ (level ns) = [] ∨
    ∃ x ∈ evalMatches G σ (level ns), ∃ ns' ∈ negativesOf ns, ∃ y, y ∈ evalMatches G x (level ns')

variable {G : Graph} {env : Env}

/-- Every tuple of `F` goes on from a tuple of `Q`, agreeing on `Q`'s labels. -/
def Ext (G : Graph) (env : Env) (Q F : List Match) : Prop :=
  ∀ τ ∈ evalMatches G env F, ∃ σ ∈ evalMatches G env Q, Agree (names Q) σ τ

theorem Ext.refl (Q : List Match) : Ext G env Q Q := fun τ h => ⟨τ, h, fun _ _ => rfl⟩

theorem Ext.trans {A B C : List Match} (hab : Ext G env A B) (hbc : Ext G env B C)
    (hsub : ∀ x ∈ names A, x ∈ names B) : Ext G env A C := fun τ h =>
  let ⟨σB, hB, aB⟩ := hbc τ h
  let ⟨σA, hA, aA⟩ := hab σB hB
  ⟨σA, hA, fun x hx => (aA x hx).trans (aB x (hsub x hx))⟩

theorem Ext.append {A X : List Match} (hdis : ∀ x ∈ names X, x ∉ names A) : Ext G env A (A ++ X) := by
  intro τ h
  obtain ⟨σ, hσ, hτ⟩ := mem_evalMatches_append.mp h
  exact ⟨σ, hσ, fun x hx => (evalMatches_frame hτ x fun hm => hdis x hm hx).symm⟩

theorem Ext.addLast {Q : List Match} (hQ : Q ≠ []) (ns : List Match) :
    Ext G env Q (addLast (.existential false ns) Q) := fun τ h =>
  ⟨τ, (mem_addLast hQ h).1, fun _ _ => rfl⟩

/-- The labels of `L`, counted, are among those of `M`. -/
def Within (L M : List Name) : Prop := ∀ x, L.count x ≤ M.count x

/-- A partial feed handed on from `start`, through `pre`, walking `negs`: it
only grows, binds nothing but `start`'s labels and `bound`, extends `pre`, and
at each negative condition walked, where it was walked, passes it. -/
structure Handed (G : Graph) (env : Env) (start pre : List Match) (negs : List (List Match)) (bound : List Name)
    (Q' : List Match) : Prop where
  grows : ∀ x ∈ names pre, x ∈ names Q'
  within : Within (names Q') (names start ++ bound)
  ext : Ext G env pre Q'
  passes : ∀ τ ∈ evalMatches G env Q', ∀ ns ∈ negs, ∃ σ, Passes G σ ns ∧ Agree (names pre) σ τ ∧
    ∀ x, x ∉ names Q' → σ x = env x

/-! ## Evaluating a suffix after either of two agreeing tuples -/

/-- Solutions from `env` bind nothing outside the feed's labels: in particular,
not the givens. -/
theorem agree_outside {G0 : List Name} {Q Q' : List Match} {σ σ' : Env}
    (hσ : σ ∈ evalMatches G env Q) (hσ' : σ' ∈ evalMatches G env Q')
    (h1 : ∀ x ∈ names Q, x ∉ G0) (h2 : ∀ x ∈ names Q', x ∉ G0) : Agree G0 σ σ' := fun x hx =>
  (evalMatches_frame hσ x fun hm => h1 x hm hx).trans (evalMatches_frame hσ' x fun hm => h2 x hm hx).symm

/-- A feed that goes on from a partial `B`, which goes on from `A`, by a suffix
`X` that names only the givens and `A`'s labels, goes on from `A` by `X`. -/
theorem Ext.suffix {G0 : List Name} {A B X : List Match} (hab : Ext G env A B)
    (hsc : ScopedMatches (G0 ++ names A) X) (hgA : ∀ x ∈ names A, x ∉ G0) (hgB : ∀ x ∈ names B, x ∉ G0)
    (hdisA : ∀ x ∈ names X, x ∉ names A) :
    Ext G env (A ++ X) (B ++ X) := by
  intro τ h
  obtain ⟨σB, hB, hτ⟩ := mem_evalMatches_append.mp h
  obtain ⟨σA, hA, aA⟩ := hab σB hB
  have hag : Agree (G0 ++ names A) σB σA := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact agree_outside hB hA hgB hgA x hx
    · exact (aA x hx).symm
  obtain ⟨τA, hτA, aτ⟩ := evalMatches_agree G X _ σB σA hsc hag τ hτ
  refine ⟨τA, mem_evalMatches_append.mpr ⟨σA, hA, hτA⟩, fun x hx => ?_⟩
  rw [names_append] at hx
  rcases List.mem_append.mp hx with hx | hx
  · rw [evalMatches_frame hτA x fun hm => hdisA x hm hx, evalMatches_frame hτ x fun hm => hdisA x hm hx]
    exact aA x hx
  · exact (aτ x (List.mem_append_right _ hx)).symm

/-! ## Every feed is local to a level, or goes on from what it hands on -/

theorem Within.trans {a b c : List Name} (h1 : Within a b) (h2 : Within b c) : Within a c :=
  fun x => Nat.le_trans (h1 x) (h2 x)

theorem Within.refl (a : List Name) : Within a a := fun _ => Nat.le_refl _

theorem Within.append {a b c d : List Name} (h1 : Within a b) (h2 : Within c d) : Within (a ++ c) (b ++ d) :=
  fun x => by simp only [List.count_append]; exact Nat.add_le_add (h1 x) (h2 x)

theorem Within.append_left (a : List Name) {c d : List Name} (h : Within c d) : Within (a ++ c) (a ++ d) :=
  (Within.refl a).append h

/-- A level's labels, then those of its negative conditions, are among those it declares. -/
theorem within_level (ms : List Match) :
    Within (names (level ms) ++ (negativesOf ms).flatMap declaredMatches) (declaredMatches ms) := by
  intro x
  have := flatten_declared ms x
  simpa [names_level, negativeLabels, negativesOf] using this

theorem within_negative {ms ns : List Match} (h : ns ∈ negativesOf ms) :
    Within (declaredMatches ns) ((negativesOf ms).flatMap declaredMatches) :=
  fun x => count_le_flatMap declaredMatches x h

/-- What the walk of a partial feed and its pending negative conditions needs:
their labels distinct, none a given, and each condition scoped in the givens
and the partial's labels. -/
structure Hygiene (G0 : List Name) (Q : List Match) (negs : List (List Match)) : Prop where
  nodup : (names Q ++ negs.flatMap declaredMatches).Nodup
  ordinary : ∀ x ∈ names Q ++ negs.flatMap declaredMatches, x ∉ G0
  inScope : ∀ ns ∈ negs, ScopedMatches (G0 ++ names Q) ns

/-- A partial feed handed on from `P` by the walk of the level `ms`. -/
structure HandedL (G : Graph) (env : Env) (P ms : List Match) (Q' : List Match) : Prop where
  grows : ∀ x ∈ names (P ++ level ms), x ∈ names Q'
  within : Within (names Q') (names P ++ declaredMatches ms)
  ext : Ext G env (P ++ level ms) Q'
  passes : ∀ τ ∈ evalMatches G env Q', ∀ a m b, ms = a ++ m :: b → ∀ ns ∈ negativesOf [m],
    ∃ σ, Passes G σ ns ∧ Agree (names (P ++ level (a ++ [m]))) σ τ ∧ ∀ x, x ∉ names Q' → σ x = env x

theorem names_ne_nil {Q : List Match} (h : Q ≠ []) : names Q ≠ [] := by
  cases Q with
  | nil => exact absurd rfl h
  | cons => simp [names]

theorem ne_nil_of_names {Q Q' : List Match} (hQ : Q ≠ []) (hg : ∀ x ∈ names Q, x ∈ names Q') : Q' ≠ [] := by
  intro h; subst h
  cases Q with
  | nil => exact hQ rfl
  | cons m _ => exact absurd (hg m.unknown.name (by simp [names])) (by simp [names])

theorem declared_cons (m : Match) (rest : List Match) :
    Within (declaredMatches [m] ++ declaredMatches rest) (declaredMatches (m :: rest)) := by
  intro x; obtain ⟨u, cs⟩ := m; simp [declaredMatches, List.count_append, List.count_cons]

theorem level_ne_nil (m : Match) : level [m] ≠ [] := by
  obtain ⟨u, cs⟩ := m
  simp [level, flatten, flattenMatches_cons]

/-- Restricting an agreement to fewer labels. -/
theorem Agree.sub {S T : List Name} {e1 e2 : Env} (h : Agree T e1 e2) (hs : ∀ x ∈ S, x ∈ T) : Agree S e1 e2 :=
  fun x hx => h x (hs x hx)

/-! ## Hygiene along the walk -/

theorem nodup_within {a b : List Name} (h : Within a b) (hb : b.Nodup) : a.Nodup := nodup_of_count_le h hb

theorem mem_within {a b : List Name} (h : Within a b) {x : Name} (hx : x ∈ a) : x ∈ b := mem_of_count_le h hx

theorem Hygiene.within {G0 : List Name} {Q Q' : List Match} {negs negs' : List (List Match)}
    (h : Hygiene G0 Q negs) (hw : Within (names Q' ++ negs'.flatMap declaredMatches) (names Q ++ negs.flatMap declaredMatches))
    (hs : ∀ ns ∈ negs', ScopedMatches (G0 ++ names Q') ns) : Hygiene G0 Q' negs' :=
  ⟨nodup_within hw h.nodup, fun x hx => h.ordinary x (mem_within hw hx), hs⟩

theorem scoped_level {S : List Name} {ms : List Match} (h : ScopedMatches S ms) : ScopedMatches S (level ms) :=
  scoped_paths (flatten_scoped ms S h)

/-- A negative condition of a scoped level is scoped after the level. -/
theorem scoped_negativesOf {S : List Name} {ms ns : List Match} (h : ScopedMatches S ms) (hns : ns ∈ negativesOf ms) :
    ScopedMatches (S ++ names (level ms)) ns := by
  obtain ⟨x, hx, hn⟩ := List.mem_flatMap.mp hns
  refine scopedMatches_mono _ _ _ (fun y hy => ?_) (scoped_negatives (flatten_scoped ms S h) x hx ns hn)
  rw [mem_scopeAfter] at hy
  rw [List.mem_append, names_level]
  exact hy.symm

theorem hygiene_unit {G0 : List Name} {P : List Match} {m : Match} {rest : List Match}
    (h : Hygiene G0 P [m :: rest]) : Hygiene G0 (P ++ level [m]) (negativesOf [m]) := by
  refine h.within ?_ fun ns hns => ?_
  · have h1 := within_level [m]
    have h2 := declared_cons m rest
    intro x
    have := h1 x; have := h2 x
    simp only [names_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *
    omega
  · have hsc : ScopedMatches (G0 ++ names P) [m] := by
      have := h.inScope _ (List.mem_singleton_self _)
      obtain ⟨u, cs⟩ := m
      exact ⟨this.1, trivial⟩
    have := scoped_negativesOf hsc hns
    simpa [names_append, List.append_assoc] using this

theorem mem_names_level (u : Label) (cs : List Condition) : u.name ∈ names (level [.mk u cs]) := by
  rw [names_level, flatten, flattenMatches_cons]; simp [names]

theorem hygiene_rest {G0 : List Name} {P Q1 : List Match} {m : Match} {rest : List Match}
    (h : Hygiene G0 P [m :: rest]) (hw : Within (names Q1) (names (P ++ level [m]) ++ (negativesOf [m]).flatMap declaredMatches))
    (hg : ∀ x ∈ names (P ++ level [m]), x ∈ names Q1) : Hygiene G0 Q1 [rest] := by
  refine h.within ?_ fun ns hns => ?_
  · have h1 := within_level [m]
    have h2 := declared_cons m rest
    intro x
    have := h1 x; have := h2 x; have := hw x
    simp only [names_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *
    omega
  · simp only [List.mem_singleton] at hns; subst hns
    obtain ⟨u, cs⟩ := m
    have hsc : ScopedMatches (u.name :: (G0 ++ names P)) ns := (h.inScope _ (List.mem_singleton_self _)).2
    refine scopedMatches_mono _ _ _ (fun x hx => ?_) hsc
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_append_right _ (hg _ (by rw [names_append]; exact List.mem_append_right _ (mem_names_level u cs)))
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (hg x (by rw [names_append]; exact List.mem_append_left _ hx))

theorem hygiene_filter {G0 : List Name} {Q : List Match} {ns : List Match} {rest : List (List Match)}
    (h : Hygiene G0 Q (ns :: rest)) : Hygiene G0 (addLast (.existential false (level ns)) Q) rest := by
  refine h.within ?_ fun ns' hns' => ?_
  · intro x; rw [names_addLast]; simp only [List.flatMap_cons, List.count_append]; omega
  · rw [names_addLast]; exact h.inScope ns' (List.mem_cons_of_mem _ hns')

theorem hygiene_restore {G0 : List Name} {Q : List Match} {ns ns' : List Match} {rest : List (List Match)}
    (h : Hygiene G0 Q (ns :: rest)) (hns' : ns' ∈ negativesOf ns) : Hygiene G0 (Q ++ level ns) [ns'] := by
  refine h.within ?_ fun n hn => ?_
  · have h1 := within_level ns
    have h2 := within_negative hns'
    intro x
    have := h1 x; have := h2 x
    simp only [names_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.count_append] at *
    omega
  · simp only [List.mem_singleton] at hn; subst hn
    have := scoped_negativesOf (h.inScope ns (List.mem_cons_self ..)) hns'
    simpa [names_append, List.append_assoc] using this

theorem hygiene_after_restore {G0 : List Name} {Q Q'' : List Match} {ns ns' : List Match} {rest : List (List Match)}
    (h : Hygiene G0 Q (ns :: rest)) (hns' : ns' ∈ negativesOf ns)
    (hw : Within (names Q'') (names (Q ++ level ns) ++ declaredMatches ns'))
    (hg : ∀ x ∈ names Q, x ∈ names Q'') : Hygiene G0 Q'' rest := by
  refine h.within ?_ fun n hn => ?_
  · have h1 := within_level ns
    have h2 := within_negative hns'
    intro x
    have := h1 x; have := h2 x; have := hw x
    simp only [names_append, List.flatMap_cons, List.count_append] at *
    omega
  · exact scopedMatches_mono _ _ _ (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (hg x hx)) (h.inScope n (List.mem_cons_of_mem _ hn))

/-! ## The walk -/

theorem Ext.decompose {A X : List Match} {τ : Env} (h : τ ∈ evalMatches G env (A ++ X))
    (hdis : ∀ x ∈ names X, x ∉ names A) :
    ∃ σ ∈ evalMatches G env A, τ ∈ evalMatches G σ X ∧ Agree (names A) σ τ := by
  obtain ⟨σ, hσ, hτ⟩ := mem_evalMatches_append.mp h
  exact ⟨σ, hσ, hτ, fun x hx => (evalMatches_frame hτ x fun hm => hdis x hm hx).symm⟩

/-- The labels of `X` are not those of `A`, when both are among distinct labels. -/
theorem disjoint_of_nodup {A X : List Name} {B : List Name} (hw : Within (A ++ X) B) (hb : B.Nodup) :
    ∀ x ∈ X, x ∉ A := fun x hx hA =>
  (List.nodup_append.mp (nodup_within hw hb)).2.2 x hA x hx rfl

mutual
  theorem levelFeeds_split (G0 : List Name) (k : List Match → List (List Match)) :
      ∀ (P ms : List Match), Hygiene G0 P [ms] → ∀ F ∈ levelFeeds k P ms,
        (∃ Q', HandedL G env P ms Q' ∧ F ∈ k Q') ∨
          (Within (names F) (names P ++ declaredMatches ms) ∧ Ext G env P F)
    | P, [], _, F, hF => by
      rw [levelFeeds] at hF
      refine Or.inl ⟨P, ⟨fun x hx => by simpa [level, flatten, flattenMatches] using hx,
        fun x => by simp, by simpa [level, flatten, flattenMatches] using Ext.refl (G := G) (env := env) P,
        fun τ _ a m b hab => by cases a <;> simp at hab⟩, hF⟩
    | P, m :: rest, h, F, hF => by
      rw [levelFeeds] at hF
      have h1 := hygiene_unit h
      have hwu : Within (names (P ++ level [m]) ++ (negativesOf [m]).flatMap declaredMatches)
          (names P ++ declaredMatches (m :: rest)) := by
        intro x; have := within_level [m] x; have := declared_cons m rest x
        simp only [names_append, List.count_append] at *
        omega
      have hdisU : ∀ x ∈ names (level [m]), x ∉ names P := by
        have : Within (names P ++ names (level [m])) (names (P ++ level [m]) ++ (negativesOf [m]).flatMap declaredMatches) := by
          intro x; simp only [names_append, List.count_append]; omega
        exact disjoint_of_nodup (this.trans hwu) (by simpa using h.nodup)
      have eU : Ext G env P (P ++ level [m]) := Ext.append hdisU
      rcases negFeeds_split G0 _ _ _ (by simp [level_ne_nil]) h1 F hF with ⟨Q1, hQ1, hF⟩ | ⟨hloc, hext⟩
      · have h2 := hygiene_rest h hQ1.within hQ1.grows
        have eQ1 : Ext G env P Q1 := eU.trans hQ1.ext fun x hx => by rw [names_append]; exact List.mem_append_left _ hx
        rcases levelFeeds_split G0 k Q1 rest h2 F hF with ⟨Q', hQ', hF⟩ | ⟨hloc, hext⟩
        · refine Or.inl ⟨Q', ?_, hF⟩
          -- The level's later units name only the givens and what comes before.
          have hsc : ScopedMatches (G0 ++ names (P ++ level [m])) (level rest) := by
            have := h.inScope _ (List.mem_singleton_self _)
            obtain ⟨u, cs⟩ := m
            refine scoped_level (scopedMatches_mono _ _ _ (fun x hx => ?_) this.2)
            rcases List.mem_cons.mp hx with rfl | hx
            · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_right _ (mem_names_level u cs))
            · rcases List.mem_append.mp hx with hx | hx
              · exact List.mem_append_left _ hx
              · exact List.mem_append_right _ (by rw [names_append]; exact List.mem_append_left _ hx)
          have hwr : Within (names (P ++ level [m]) ++ names (level rest)) (names P ++ declaredMatches (m :: rest)) := by
            intro x; have := within_level [m] x; have := within_level rest x; have := declared_cons m rest x
            simp only [names_append, List.count_append] at *
            omega
          have hdis := disjoint_of_nodup hwr (by simpa using h.nodup)
          have hdisQ1 : ∀ x ∈ names (level rest), x ∉ names Q1 := by
            have : Within (names Q1 ++ names (level rest)) (names Q1 ++ declaredMatches rest) := by
              intro x; have := within_level rest x
              simp only [List.count_append] at *; omega
            exact disjoint_of_nodup this (by simpa using h2.nodup)
          have hgA : ∀ x ∈ names (P ++ level [m]), x ∉ G0 := fun x hx => h1.ordinary x (List.mem_append_left _ hx)
          have hgB : ∀ x ∈ names Q1, x ∉ G0 := fun x hx => h2.ordinary x (List.mem_append_left _ hx)
          have es := Ext.suffix hQ1.ext hsc hgA hgB hdis
          have hlevel : P ++ level (m :: rest) = (P ++ level [m]) ++ level rest := by
            rw [show m :: rest = [m] ++ rest from rfl, level_append, List.append_assoc]
          have hQ1Q' : ∀ x ∈ names Q1, x ∈ names Q' := fun x hx =>
            hQ'.grows x (by rw [names_append]; exact List.mem_append_left _ hx)
          refine ⟨fun x hx => ?_, ?_, ?_, ?_⟩
          · rw [hlevel, names_append] at hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hQ1Q' x (hQ1.grows x hx)
            · exact hQ'.grows x (by rw [names_append]; exact List.mem_append_right _ hx)
          · intro x; have := hQ'.within x; have := hQ1.within x; have := within_level [m] x
            have := declared_cons m rest x
            simp only [names_append, List.count_append] at *
            omega
          · rw [hlevel]
            refine es.trans hQ'.ext fun x hx => ?_
            rw [names_append] at hx ⊢
            rcases List.mem_append.mp hx with hx | hx
            · exact List.mem_append_left _ (hQ1.grows x hx)
            · exact List.mem_append_right _ hx
          · intro τ hτ a m' b hab ns hns
            cases a with
            | nil =>
              simp only [List.nil_append, List.cons.injEq] at hab
              obtain ⟨rfl, rfl⟩ := hab
              obtain ⟨ρ, hρ, aρ⟩ := hQ'.ext τ hτ
              obtain ⟨τ1, hτ1, -, a1⟩ := Ext.decompose hρ hdisQ1
              obtain ⟨σ, hp, aσ, oσ⟩ := hQ1.passes τ1 hτ1 ns hns
              refine ⟨σ, hp, fun x hx => ?_, fun x hx => oσ x fun hm => hx (hQ1Q' x hm)⟩
              simp only [List.nil_append] at hx
              exact (aσ x hx).trans ((a1 x (hQ1.grows x hx)).trans
                (aρ x (by rw [names_append]; exact List.mem_append_left _ (hQ1.grows x hx))))
            | cons a0 a' =>
              simp only [List.cons_append, List.cons.injEq] at hab
              obtain ⟨h1, h2⟩ := hab
              subst h1; subst h2
              obtain ⟨σ, hp, aσ, oσ⟩ := hQ'.passes τ hτ a' m' b rfl ns hns
              refine ⟨σ, hp, fun x hx => aσ x ?_, oσ⟩
              rw [show ∀ (y : Match) (l : List Match), y :: l ++ [m'] = [y] ++ (l ++ [m']) from fun _ _ => rfl,
                level_append, ← List.append_assoc, names_append] at hx
              rw [names_append]
              rcases List.mem_append.mp hx with hx | hx
              · exact List.mem_append_left _ (hQ1.grows x hx)
              · exact List.mem_append_right _ hx
        · refine Or.inr ⟨fun x => ?_, eQ1.trans hext fun x hx => hQ1.grows x (by
            rw [names_append]; exact List.mem_append_left _ hx)⟩
          have := hloc x; have := hQ1.within x; have := within_level [m] x; have := declared_cons m rest x
          simp only [names_append, List.count_append] at *
          omega
      · exact Or.inr ⟨hloc.trans hwu, eU.trans hext fun x hx => by rw [names_append]; exact List.mem_append_left _ hx⟩
  termination_by _ ms => (sizeOf ms, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | (apply Prod.Lex.left
         have := maxSize_lt (b := sizeOf (m :: rest)) (by simp; omega) fun p hp => sizeOf_negativesOf_unit p hp
         simpa using this)
      | (apply Prod.Lex.left; omega)

  theorem negFeeds_split (G0 : List Name) (k : List Match → List (List Match)) :
      ∀ (Q : List Match) (negs : List (List Match)), Q ≠ [] → Hygiene G0 Q negs → ∀ F ∈ negFeeds k Q negs,
        (∃ Q', Handed G env Q Q negs (negs.flatMap declaredMatches) Q' ∧ F ∈ k Q') ∨
          (Within (names F) (names Q ++ negs.flatMap declaredMatches) ∧ Ext G env Q F)
    | Q, [], _, _, F, hF => by
      rw [negFeeds] at hF
      exact Or.inl ⟨Q, ⟨fun _ hx => hx, fun x => by simp, Ext.refl Q, fun _ _ ns hns => by simp at hns⟩, hF⟩
    | Q, ns :: rest, hQ, h, F, hF => by
      rw [negFeeds] at hF
      have hwl : Within (names (Q ++ level ns)) (names Q ++ (ns :: rest).flatMap declaredMatches) := by
        intro x; have := within_level ns x
        simp only [names_append, List.flatMap_cons, List.count_append] at *; omega
      have hdisL : ∀ x ∈ names (level ns), x ∉ names Q := by
        rw [names_append] at hwl
        exact disjoint_of_nodup hwl h.nodup
      rcases List.mem_cons.mp hF with rfl | hF
      · exact Or.inr ⟨hwl, Ext.append hdisL⟩
      rcases List.mem_append.mp hF with hF | hF
      · -- Filtered.
        have hQf : addLast (.existential false (level ns)) Q ≠ [] := fun he =>
          names_ne_nil hQ (by rw [← names_addLast (.existential false (level ns)) Q, he]; rfl)
        have eF : Ext G env Q (addLast (.existential false (level ns)) Q) := Ext.addLast hQ (level ns)
        rcases negFeeds_split G0 k _ rest hQf (hygiene_filter h) F hF with ⟨Q', hQ', hF⟩ | ⟨hloc, hext⟩
        · refine Or.inl ⟨Q', ⟨fun x hx => hQ'.grows x (by rwa [names_addLast]), fun x => ?_,
            eF.trans hQ'.ext (fun x hx => by rwa [names_addLast]), ?_⟩, hF⟩
          · have := hQ'.within x; rw [names_addLast] at this
            simp only [List.flatMap_cons, List.count_append] at *; omega
          · intro τ hτ n hn
            rcases List.mem_cons.mp hn with hn | hn
            · rw [hn]
              obtain ⟨σ, hσ, aσ⟩ := hQ'.ext τ hτ
              refine ⟨σ, Or.inl (mem_addLast hQ hσ).2, fun x hx => aσ x (by rwa [names_addLast]),
                fun x hx => evalMatches_frame hσ x fun hm => hx (hQ'.grows x hm)⟩
            · obtain ⟨σ, hp, aσ, oσ⟩ := hQ'.passes τ hτ n hn
              exact ⟨σ, hp, fun x hx => aσ x (by rwa [names_addLast]), oσ⟩
        · refine Or.inr ⟨fun x => ?_, eF.trans hext fun x hx => by rwa [names_addLast]⟩
          have := hloc x; rw [names_addLast] at this
          simp only [List.flatMap_cons, List.count_append] at *; omega
      · -- Restored, through a negative condition of the condition's level.
        obtain ⟨⟨ns', hns'⟩, -, hF⟩ := List.mem_flatMap.mp hF
        have hr := hygiene_restore h hns'
        have hwr : Within (names (Q ++ level ns) ++ declaredMatches ns') (names Q ++ (ns :: rest).flatMap declaredMatches) := by
          intro x; have := within_level ns x; have := within_negative hns' x
          simp only [names_append, List.flatMap_cons, List.count_append] at *; omega
        have eL : Ext G env Q (Q ++ level ns) := Ext.append hdisL
        have hQQL : ∀ x ∈ names Q, x ∈ names (Q ++ level ns) := fun x hx => by
          rw [names_append]; exact List.mem_append_left _ hx
        rcases levelFeeds_split G0 _ _ ns' hr F hF with ⟨Q'', hQ'', hF⟩ | ⟨hloc, hext⟩
        · have hgQ : ∀ x ∈ names Q, x ∈ names Q'' := fun x hx =>
            hQ''.grows x (by rw [names_append]; exact List.mem_append_left _ (hQQL x hx))
          have hne : Q'' ≠ [] := ne_nil_of_names hQ hgQ
          have hdisL' : ∀ x ∈ names (level ns'), x ∉ names (Q ++ level ns) := by
            have : Within (names (Q ++ level ns) ++ names (level ns')) (names (Q ++ level ns) ++ declaredMatches ns') := by
              intro x; have := within_level ns' x
              simp only [names_append, List.count_append] at *; omega
            exact disjoint_of_nodup (this.trans hwr) h.nodup
          have e0 : Ext G env Q ((Q ++ level ns) ++ level ns') := eL.trans (Ext.append hdisL') hQQL
          have eQ'' : Ext G env Q Q'' := e0.trans hQ''.ext fun x hx => by
            rw [names_append]; exact List.mem_append_left _ (hQQL x hx)
          rcases negFeeds_split G0 k Q'' rest hne (hygiene_after_restore h hns' hQ''.within hgQ) F hF with
            ⟨Q', hQ', hF⟩ | ⟨hloc, hext⟩
          · refine Or.inl ⟨Q', ⟨fun x hx => hQ'.grows x (hgQ x hx), fun x => ?_, eQ''.trans hQ'.ext hgQ, ?_⟩, hF⟩
            · have := hQ'.within x; have := hQ''.within x; have := within_level ns x
              have := within_negative hns' x
              simp only [names_append, List.flatMap_cons, List.count_append] at *; omega
            · intro τ hτ n hn
              rcases List.mem_cons.mp hn with hn | hn
              · rw [hn]
                obtain ⟨σ'', hσ'', a''⟩ := hQ'.ext τ hτ
                obtain ⟨ρ, hρ, aρ⟩ := hQ''.ext σ'' hσ''
                obtain ⟨x, hx, hρx, ax⟩ := Ext.decompose hρ hdisL'
                obtain ⟨σ, hσ, hxσ, aσ⟩ := Ext.decompose hx hdisL
                refine ⟨σ, Or.inr ⟨x, hxσ, ns', hns', ρ, hρx⟩, fun y hy => ?_,
                  fun y hy => evalMatches_frame hσ y fun hm => hy (hQ'.grows y (hgQ y hm))⟩
                have hyQL : y ∈ names (Q ++ level ns) := hQQL y hy
                exact (aσ y hy).trans ((ax y hyQL).trans ((aρ y (by rw [names_append]; exact List.mem_append_left _ hyQL)).trans
                  (a'' y (hgQ y hy))))
              · obtain ⟨σ, hp, aσ, oσ⟩ := hQ'.passes τ hτ n hn
                exact ⟨σ, hp, fun y hy => aσ y (hgQ y hy), oσ⟩
          · refine Or.inr ⟨fun x => ?_, eQ''.trans hext hgQ⟩
            have := hloc x; have := hQ''.within x; have := within_level ns x; have := within_negative hns' x
            simp only [names_append, List.flatMap_cons, List.count_append] at *; omega
        · exact Or.inr ⟨hloc.trans hwr, eL.trans hext hQQL⟩
  termination_by _ negs => (maxSize negs, negs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | exact maxSize_lex _ _
      | exact Prod.Lex.left _ _ (Nat.lt_of_lt_of_le (sizeOf_negativesOf _ ‹_›) (le_maxSize (List.mem_cons_self ..)))
end

/-! ## Deferral -/

/-- Whether a negative condition is unwitnessed, or has a witness something
tries to cancel, depends only on the labels it is scoped in. -/
theorem passes_agree {S : List Name} {σ τ : Env} {ns : List Match} (hag : Agree S σ τ)
    (hsc : ScopedMatches S ns) (h : Passes G σ ns) : Passes G τ ns := by
  have hL := scoped_level hsc
  rcases h with h | ⟨x, hx, ns', hns', y, hy⟩
  · refine Or.inl (List.eq_nil_iff_forall_not_mem.mpr fun x hx => ?_)
    obtain ⟨x', hx', -⟩ := evalMatches_agree G _ S τ σ hL hag.symm x hx
    simp [h] at hx'
  · obtain ⟨x', hx', ax⟩ := evalMatches_agree G _ S σ τ hL hag x hx
    have hsc' := scoped_level (scoped_negativesOf hsc hns')
    obtain ⟨y', hy', -⟩ := evalMatches_agree G _ (S ++ names (level ns)) x x' hsc' ax y hy
    exact Or.inr ⟨x', hx', ns', hns', y', hy'⟩

theorem declared_append (a b : List Match) :
    declaredMatches (a ++ b) = declaredMatches a ++ declaredMatches b := by
  induction a with
  | nil => simp [declaredMatches]
  | cons m a ih => obtain ⟨u, cs⟩ := m; simp [declaredMatches, ih]

/-- **Deferral.** A feed that carries any of the details of a top-level match
`m`, the matches after it, does so only for tuples at which each of `m`'s
negative conditions, with its positive conditions joined, is either not
witnessed, or has a witness with a fact of one of its own negative conditions.

So a new client is not sent the details of an entity excluded by a fact that
nothing has tried to cancel: the names of a deleted menu item, while no restore
of its delete exists. Exactness is not possible: `restore-revoked-and-unrevoked`
(`FeedCases.lean`) is an entity still excluded whose details a feed must carry,
because telling it apart needs a nested negative condition. -/
theorem feeds_defer {s : Specification} (hwf : WellFormed s) (hd : DistinctLabels s)
    {a b : List Match} {m : Match} (hs : s.matchList = a ++ m :: b) (G : Graph) (env : Env) :
    ∀ f ∈ buildFeeds s, (∃ y ∈ names (flatten b), y ∈ names f.matchList) →
      ∀ τ ∈ evalMatches G env f.matchList, ∀ ns ∈ negativesOf [m], Passes G τ ns := by
  intro f hf ⟨y, hyb, hyf⟩ τ hτ ns hns
  obtain ⟨hf, -⟩ := List.mem_filter.mp hf
  obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hf
  simp only at hyf hτ
  let G0 := s.given.map (·.name)
  let A := a ++ [m]
  have hs' : s.matchList = A ++ b := by rw [hs]; simp [A]
  have hdecl : (declaredMatches A ++ declaredMatches b).Nodup := by
    have := hd; rw [DistinctLabels, hs', declared_append A b] at this; exact this
  have hord : ∀ x ∈ declaredMatches A ++ declaredMatches b, x ∉ G0 := by
    intro x hx; rw [← declared_append, ← hs'] at hx; exact wellNamed_declared _ _ hwf.wellNamed x hx
  have hsc : ScopedMatches G0 (A ++ b) := by rw [← hs']; exact hwf.inScope
  obtain ⟨hscA, hscB⟩ := scopedMatches_append.mp hsc
  have hyD : y ∈ declaredMatches b := mem_of_count_le (fun x => flatten_declared b x) (List.mem_append_left _ hyb)
  rw [hs', levelFeeds_append] at hF
  have hyg : Hygiene G0 [] [A] :=
    ⟨by simpa [names] using (List.nodup_append.mp hdecl).1,
     fun x hx => hord x (List.mem_append_left _ (by simpa [names] using hx)),
     fun n hn => by simp at hn; subst hn; simpa [names] using hscA⟩
  rcases levelFeeds_split (G := G) (env := env) G0 _ [] A hyg F hF with ⟨Q', hQ', hF⟩ | ⟨hloc, -⟩
  · -- The feed goes on from a partial that walked `m`'s negative conditions.
    have hwQ : Within (names Q' ++ declaredMatches b) (declaredMatches A ++ declaredMatches b) := by
      intro x; have := hQ'.within x; simp only [names, List.map_nil, List.nil_append, List.count_append] at *; omega
    have hgrowA : ∀ x ∈ names (level A), x ∈ names Q' := fun x hx => hQ'.grows x (by simpa using hx)
    have hyg2 : Hygiene G0 Q' [b] :=
      ⟨by simpa using nodup_within hwQ hdecl, fun x hx => hord x (mem_within hwQ (by simpa using hx)),
       fun n hn => by
        simp at hn; subst hn
        refine scopedMatches_mono _ _ _ (fun x hx => ?_) hscB
        rw [mem_scopeAfter] at hx
        rcases hx with hx | hx
        · exact List.mem_append_right _ (hgrowA x (by rw [names_level]; exact mem_names_flatten hx))
        · exact List.mem_append_left _ hx⟩
    -- Every feed that goes on from `Q'` extends it, and binds no given.
    have hFQ : Ext G env Q' F ∧ ∀ x ∈ names F, x ∉ G0 := by
      have hordF : Within (names F) (names Q' ++ declaredMatches b) → ∀ x ∈ names F, x ∉ G0 := fun hw x hx =>
        hyg2.ordinary x (by simpa using mem_within hw hx)
      rcases levelFeeds_split (G := G) (env := env) G0 _ Q' b hyg2 F hF with ⟨Q'', hQ'', hF⟩ | ⟨hw, hext⟩
      · simp at hF; subst hF
        have hdisB : ∀ x ∈ names (level b), x ∉ names Q' := by
          have : Within (names Q' ++ names (level b)) (names Q' ++ declaredMatches b) := by
            intro x; have := within_level b x; simp only [List.count_append] at *; omega
          exact disjoint_of_nodup this (by simpa using hyg2.nodup)
        exact ⟨(Ext.append hdisB).trans hQ''.ext fun x hx => by rw [names_append]; exact List.mem_append_left _ hx,
          hordF hQ''.within⟩
      · exact ⟨hext, hordF hw⟩
    obtain ⟨σ', hσ', aσ'⟩ := hFQ.1 τ hτ
    obtain ⟨σ, hp, aσ, oσ⟩ := hQ'.passes σ' hσ' a m [] rfl ns hns
    -- The condition names only the givens and the labels through `m`.
    have hscN : ScopedMatches (G0 ++ names (level A)) ns :=
      scoped_negativesOf hscA (by rw [negativesOf_append]; exact List.mem_append_right _ hns)
    have hQ'g : ∀ x ∈ names Q', x ∉ G0 := fun x hx => hyg2.ordinary x (List.mem_append_left _ hx)
    refine passes_agree (fun x hx => ?_) hscN hp
    rcases List.mem_append.mp hx with hx | hx
    · rw [oσ x fun h => hQ'g x h hx, evalMatches_frame hτ x fun h => hFQ.2 x h hx]
    · exact (aσ x (by simpa using hx)).trans (aσ' x (hgrowA x hx))
  · -- A local feed binds only the labels through `m`, not those after it.
    have := mem_within hloc hyf
    simp only [names, List.map_nil, List.nil_append] at this
    exact absurd rfl ((List.nodup_append.mp hdecl).2.2 y this y hyD)

end JinagaSpec
