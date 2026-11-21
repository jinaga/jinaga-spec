import JinagaSpec.Split

/-!
# Well-formed specifications

The hypotheses the split theorem needs, stated as the parser and validator
guarantee them:

* every label a path condition names is in scope (`ScopedMatches`), and
* a match never re-declares a label that is already in scope, and never
  declares a label reserved for the split (`WellNamedMatches`).
  `SpecificationParser.parseMatch` rejects the first with "The name ... has
  already been used".

Scope is lexical. A match sees the givens, the matches before it, and, inside
its own existential conditions, its own unknown.
-/
namespace JinagaSpec

/-- Two environments bind every label in `S` to the same fact. -/
def Agree (S : List Name) (e1 e2 : Env) : Prop := ∀ x ∈ S, e1 x = e2 x

theorem Agree.symm {S : List Name} {e1 e2 : Env} (h : Agree S e1 e2) : Agree S e2 e1 :=
  fun x hx => (h x hx).symm

theorem Agree.mono {S S' : List Name} {e1 e2 : Env} (h : Agree S e1 e2)
    (hsub : ∀ x ∈ S', x ∈ S) : Agree S' e1 e2 :=
  fun x hx => h x (hsub x hx)

/-- Binding the same fact to the same label keeps two environments in
agreement, and extends the agreement to that label. -/
theorem Agree.bind {S : List Name} {e1 e2 : Env} (h : Agree S e1 e2) (n : Name) (f : FactId) :
    Agree (n :: S) (e1.bind n f) (e2.bind n f) := by
  intro x hx
  by_cases hxn : x = n
  · simp [Env.bind, hxn]
  · have hxS : x ∈ S := by
      rcases List.mem_cons.mp hx with h' | h'
      · exact absurd h' hxn
      · exact h'
    simp [Env.bind, hxn, h x hxS]

theorem Env.restrictTo_agree (names : List Name) (e : Env) : Agree names (e.restrictTo names) e := by
  intro x hx
  simp [Env.restrictTo, hx]

/-- Equal projections of two environments that agree on the projected labels. -/
theorem Agree.map {S : List Name} {e1 e2 : Env} (h : Agree S e1 e2) : S.map e1 = S.map e2 :=
  List.map_congr_left fun x hx => h x hx

/-! ## Scope -/

mutual
  /-- Every path condition names a label in scope. A match adds its unknown to
  the scope of the matches after it, and of its own existential conditions. -/
  def ScopedMatches : List Name → List Match → Prop
    | _, [] => True
    | scope, .mk u cs :: rest =>
      ScopedConditions (u.name :: scope) scope cs ∧ ScopedMatches (u.name :: scope) rest

  /-- `inner` is the scope of existential conditions, `outer` of path
  conditions. -/
  def ScopedConditions (inner outer : List Name) : List Condition → Prop
    | [] => True
    | c :: cs => ScopedCondition inner outer c ∧ ScopedConditions inner outer cs

  def ScopedCondition (inner outer : List Name) : Condition → Prop
    | .path c => c.labelRight ∈ outer
    | .existential _ ms => ScopedMatches inner ms
end

mutual
  /-- Every match declares a new label, not one already in scope, and an ordinary
  one, not reserved for the split. -/
  def WellNamedMatches : List Name → List Match → Prop
    | _, [] => True
    | scope, .mk u cs :: rest =>
      u.name ∉ scope ∧ isReserved u.name = false ∧
        WellNamedConditions (u.name :: scope) cs ∧ WellNamedMatches (u.name :: scope) rest

  def WellNamedConditions (inner : List Name) : List Condition → Prop
    | [] => True
    | c :: cs => WellNamedCondition inner c ∧ WellNamedConditions inner cs

  def WellNamedCondition (inner : List Name) : Condition → Prop
    | .path _ => True
    | .existential _ ms => WellNamedMatches inner ms
end

/-- The scope after the matches: the unknown of each is added. -/
def scopeAfter : List Name → List Match → List Name
  | scope, [] => scope
  | scope, m :: ms => scopeAfter (m.unknown.name :: scope) ms

theorem mem_scopeAfter {scope : List Name} {ms : List Match} {x : Name} :
    x ∈ scopeAfter scope ms ↔ x ∈ ms.map (·.unknown.name) ∨ x ∈ scope := by
  induction ms generalizing scope with
  | nil => simp [scopeAfter]
  | cons m ms ih =>
    simp only [scopeAfter, ih, List.map_cons, List.mem_cons]
    grind

/-- The scope at a pivot: the givens and the unknowns of the matches before it. -/
def scopeAt (s : Specification) (before : List Match) : List Name :=
  scopeAfter (s.given.map (·.name)) before

/-- What the parser and validator guarantee about a specification, and what
the split theorem assumes. -/
structure WellFormed (s : Specification) : Prop where
  givensOrdinary : ∀ g ∈ s.given, isReserved g.name = false
  inScope : ScopedMatches (s.given.map (·.name)) s.matchList
  wellNamed : WellNamedMatches (s.given.map (·.name)) s.matchList
  projected : ∀ x ∈ s.projection.labels,
    x ∈ s.given.map (·.name) ∨ x ∈ s.matchList.map (·.unknown.name)

/-! ## Scope is monotone in the allowed names -/

mutual
  theorem scopedMatches_mono :
      ∀ (ms : List Match) (A B : List Name), (∀ x ∈ A, x ∈ B) → ScopedMatches A ms → ScopedMatches B ms
    | [], _, _, _, _ => trivial
    | .mk u cs :: rest, A, B, hsub, h => by
      obtain ⟨h1, h2⟩ : ScopedConditions (u.name :: A) A cs ∧ ScopedMatches (u.name :: A) rest := h
      have hsub' : ∀ x ∈ u.name :: A, x ∈ u.name :: B := by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (hsub x hx)
      exact ⟨scopedConditions_mono cs (u.name :: A) (u.name :: B) A B hsub' hsub h1,
        scopedMatches_mono rest (u.name :: A) (u.name :: B) hsub' h2⟩

  theorem scopedConditions_mono :
      ∀ (cs : List Condition) (inner1 inner2 outer1 outer2 : List Name),
        (∀ x ∈ inner1, x ∈ inner2) → (∀ x ∈ outer1, x ∈ outer2) →
        ScopedConditions inner1 outer1 cs → ScopedConditions inner2 outer2 cs
    | [], _, _, _, _, _, _, _ => trivial
    | c :: cs, inner1, inner2, outer1, outer2, hi, ho, h => by
      obtain ⟨h1, h2⟩ : ScopedCondition inner1 outer1 c ∧ ScopedConditions inner1 outer1 cs := h
      exact ⟨scopedCondition_mono c inner1 inner2 outer1 outer2 hi ho h1,
        scopedConditions_mono cs inner1 inner2 outer1 outer2 hi ho h2⟩

  theorem scopedCondition_mono :
      ∀ (c : Condition) (inner1 inner2 outer1 outer2 : List Name),
        (∀ x ∈ inner1, x ∈ inner2) → (∀ x ∈ outer1, x ∈ outer2) →
        ScopedCondition inner1 outer1 c → ScopedCondition inner2 outer2 c
    | .path _, _, _, _, _, _, ho, h => ho _ h
    | .existential _ ms, inner1, inner2, _, _, hi, _, h => scopedMatches_mono ms inner1 inner2 hi h
end

end JinagaSpec
