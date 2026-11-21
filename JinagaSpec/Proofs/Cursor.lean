import JinagaSpec.Cursor
import JinagaSpec.Proofs.Feeds

/-!
# Paging a feed by bookmark loses nothing

* `caught_start`: a replica with no bookmark has caught up on nothing it needs.
* `caught_page`: delivering a page and moving the bookmark to its end keeps it
  caught up. Two tuples at one position hold the same facts, so a page that
  ends between them loses nothing.
* `caught_grow`: facts arriving at the replicator keep it caught up, provided
  their ids are larger (`IdsIncrease`) and a tuple of new facts was a tuple
  before; `feed_grow` is the case of a feed, from `feed_antitone`.
* `caught_sync`: an empty page means every tuple's facts are delivered.
* `Caught.mono`: delivering more keeps it caught up, so a replica that saves a
  page's facts before its bookmark is caught up at every point between.
-/
namespace JinagaSpec

private def descending : Nat → Nat → Bool := fun a b => decide (b ≤ a)

theorem position_perm (t : List FactId) : (position t).Perm t := List.mergeSort_perm t _

theorem mem_position {t : List FactId} {id : FactId} : id ∈ position t ↔ id ∈ t := (position_perm t).mem_iff

/-- The first of a position is its largest id. -/
theorem le_head_position {t : List FactId} {h : Nat} {rest : List Nat} (hp : position t = h :: rest)
    {id : FactId} (hid : id ∈ t) : id ≤ h := by
  have hs := List.pairwise_mergeSort (le := descending) (fun a b c h1 h2 => by simp [descending] at *; omega)
    (fun a b => by simp [descending]; omega) t
  rw [show t.mergeSort descending = position t from rfl, hp] at hs
  rcases List.mem_cons.mp (hp ▸ mem_position.mpr hid) with rfl | hmem
  · exact Nat.le_refl _
  · simpa [descending] using List.rel_of_pairwise_cons hs hmem

theorem position_eq_nil {t : List FactId} (h : position t ≤ []) : t = [] := by
  cases hp : position t with
  | nil => exact List.Perm.eq_nil ((position_perm t).symm.trans (hp ▸ List.Perm.refl _))
  | cons a r => rw [hp] at h; exact absurd (List.Lex.nil) (List.not_lt.mpr h)

theorem Caught.mono {T : List (List FactId)} {b : List Nat} {D D' : List FactId} (h : Caught T b D)
    (hD : ∀ id ∈ D, id ∈ D') : Caught T b D' :=
  fun t ht hb id hid => hD id (h t ht hb id hid)

theorem caught_start (T : List (List FactId)) (D : List FactId) : Caught T [] D :=
  fun t _ hb id hid => by simp [position_eq_nil hb] at hid

theorem nextBookmark_cases (b : List Nat) :
    ∀ P : List (List FactId), nextBookmark b P = b ∨ ∃ p ∈ P, nextBookmark b P = position p
  | [] => Or.inl rfl
  | t :: P => by
    simp only [nextBookmark, List.foldl_cons]
    rcases nextBookmark_cases (if position t ≤ b then b else position t) P with h | ⟨p, hp, h⟩
    · simp only [nextBookmark] at h
      rw [h]; split
      · exact Or.inl rfl
      · exact Or.inr ⟨t, List.mem_cons_self .., rfl⟩
    · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, h⟩

theorem nextBookmark_le {x : List Nat} :
    ∀ {b : List Nat} {P : List (List FactId)}, b ≤ x → (∀ p ∈ P, position p ≤ x) → nextBookmark b P ≤ x
  | _, [], hb, _ => hb
  | b, t :: P, hb, hP => by
    simp only [nextBookmark, List.foldl_cons]
    exact nextBookmark_le (by split <;> simp_all) fun p hp => hP p (List.mem_cons_of_mem _ hp)

theorem caught_page {T P : List (List FactId)} {b : List Nat} {D : List FactId} (hc : Caught T b D)
    (hp : IsPage T P b) : Caught T (nextBookmark b P) (D ++ P.flatten) := by
  intro t ht hb' id hid
  by_cases hb : position t ≤ b
  · exact List.mem_append_left _ (hc t ht hb id hid)
  have hlt : b < position t := List.not_le.mp hb
  by_cases htP : t ∈ P
  · exact List.mem_append_right _ (List.mem_flatten.mpr ⟨t, htP, hid⟩)
  have hle := nextBookmark_le (List.le_of_lt hlt) (hp.noGap t ht hlt htP)
  have heq : nextBookmark b P = position t := List.le_antisymm hle hb'
  rcases nextBookmark_cases b P with h | ⟨p, hpP, h⟩
  · exact absurd (h ▸ heq ▸ hlt) (List.lt_irrefl _)
  · have hperm : t.Perm p := (position_perm t).symm.trans ((heq.symm.trans h) ▸ position_perm p)
    exact List.mem_append_right _ (List.mem_flatten.mpr ⟨p, hpP, hperm.mem_iff.mp hid⟩)

theorem caught_sync {T : List (List FactId)} {b : List Nat} {D : List FactId} (hc : Caught T b D)
    (hp : IsPage T [] b) : ∀ t ∈ T, ∀ id ∈ t, id ∈ D := by
  intro t ht
  by_cases hb : position t ≤ b
  · exact hc t ht hb
  · exact absurd rfl (hp.progress ⟨t, ht, List.not_le.mp hb⟩)

/-- The bookmark names only facts of `g`. -/
def Graph.Bounds (g : Graph) (b : List Nat) : Prop := ∀ id ∈ b, ∃ x ∈ g, x.id = id

theorem bounds_page {g : Graph} {T P : List (List FactId)} {b : List Nat} (hb : g.Bounds b)
    (hT : ∀ t ∈ T, g.Bounds t) (hp : IsPage T P b) : g.Bounds (nextBookmark b P) := by
  rcases nextBookmark_cases b P with h | ⟨p, hpP, h⟩
  · rw [h]; exact hb
  · rw [h]; exact fun id hid => hT p (hp.beyond p hpP).1 id (mem_position.mp hid)

theorem Graph.Bounds.append {g : Graph} {b : List Nat} (h : g.Bounds b) (B : List Fact) : (g ++ B).Bounds b :=
  fun id hid => let ⟨x, hx, he⟩ := h id hid; ⟨x, List.mem_append_left _ hx, he⟩

theorem caught_grow {g : Graph} {B : List Fact} {T T' : List (List FactId)} {b : List Nat} {D : List FactId}
    (hc : Caught T b D) (hb : g.Bounds b) (hinc : IdsIncrease g B)
    (hold : ∀ t ∈ T', (∀ id ∈ t, Outside B id) → t ∈ T) : Caught T' b D := by
  intro t ht hle id hid
  refine hc t (hold t ht fun i hi y hy heq => ?_) hle id hid
  subst heq
  cases hbp : b with
  | nil => rw [hbp] at hle; simp [position_eq_nil hle] at hi
  | cons h1 rest =>
    obtain ⟨x, hx, hxid⟩ := hb h1 (by simp [hbp])
    cases hpt : position t with
    | nil => simp [← mem_position, hpt] at hi
    | cons h0 r =>
      have : b < position t := by
        rw [hbp, hpt]; exact List.Lex.rel (hxid ▸ Nat.lt_of_lt_of_le (hinc x hx y hy) (le_head_position hpt hi))
      exact absurd this (List.not_lt.mpr hle)

/-- Facts arriving at the replicator keep a replica that pages a feed caught up,
provided their ids are larger than every id it has seen. -/
theorem feed_grow {g : Graph} {B : List Fact} (hf : Fresh g B) (hinc : IdsIncrease g B)
    {f : Specification} (hs : PathsOnly f.matchList) (hnd : (names f.matchList).Nodup)
    {env : Env} (henv : Settled B env) {b : List Nat} {D : List FactId}
    (hc : Caught (f.tuples g env) b D) (hb : g.Bounds b) : Caught (f.tuples (g ++ B) env) b D :=
  caught_grow hc hb hinc fun _ ht hout => feed_antitone hf hs hnd henv ht hout

end JinagaSpec
