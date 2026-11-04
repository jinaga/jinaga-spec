/-!
# Cascade: canonical finite maps

A finite map is a list of entries kept sorted by key, with no key repeated. Two
such maps with the same lookups are the same list (`CMap.ext`), so a map's
equality is its list's: decidable, structural, and blind to the order entries
were inserted in.

Keys are ordered through an injective encoding into lists of integers
(`Encode`), compared lexicographically, which is a strict total order.
-/
namespace JinagaSpec.Cascade

/-- An injective encoding into lists of integers. -/
class Encode (α : Type) where
  enc : α → List Int
  enc_inj : ∀ {a b : α}, enc a = enc b → a = b

namespace Encode

variable {α : Type} [Encode α]

/-- The order of the encodings. -/
def lt (a b : α) : Prop := enc a < enc b

instance (a b : α) : Decidable (lt a b) := inferInstanceAs (Decidable (enc a < enc b))

theorem lt_irrefl (a : α) : ¬ lt a a := List.lt_irrefl (enc a)

theorem lt_trans {a b c : α} (h₁ : lt a b) (h₂ : lt b c) : lt a c := List.lt_trans h₁ h₂

theorem lt_asymm {a b : α} (h : lt a b) : ¬ lt b a := fun h' => lt_irrefl a (lt_trans h h')

theorem lt_total {a b : α} (h : a ≠ b) : lt a b ∨ lt b a := by
  rcases List.le_total (enc a) (enc b) with h' | h'
  · rcases List.le_iff_lt_or_eq.mp h' with h' | h'
    · exact Or.inl h'
    · exact absurd (enc_inj h') h
  · rcases List.le_iff_lt_or_eq.mp h' with h' | h'
    · exact Or.inr h'
    · exact absurd (enc_inj h'.symm) h

/-- Equality, decided through the encoding. -/
def decEq (a b : α) : Decidable (a = b) :=
  if h : enc a = enc b then isTrue (enc_inj h) else isFalse fun e => h (e ▸ rfl)

end Encode

/-- A finite map from `α` to `β`: its entries, sorted by key with no key repeated. -/
structure CMap (α β : Type) [Encode α] where
  entries : List (α × β)
  sorted : (entries.map (·.1)).Pairwise Encode.lt

namespace CMap

variable {α β : Type} [Encode α] [DecidableEq α]

/-- The value of key `k`. -/
def get (m : CMap α β) (k : α) : Option β := (m.entries.find? (·.1 = k)).map (·.2)

def empty : CMap α β := ⟨[], List.Pairwise.nil⟩

/-! ## Lookup in a sorted list -/

/-- The value of key `k` in a list of entries. -/
def lookup (k : α) (l : List (α × β)) : Option β := (l.find? (·.1 = k)).map (·.2)

omit [Encode α] in
theorem lookup_nil (k : α) : lookup k ([] : List (α × β)) = none := rfl

omit [Encode α] in
theorem lookup_cons (k k' : α) (v : β) (l : List (α × β)) :
    lookup k ((k', v) :: l) = if k' = k then some v else lookup k l := by
  by_cases h : k' = k <;> simp [lookup, h]

omit [Encode α] in
theorem lookup_cons_self (k : α) (v : β) (l : List (α × β)) : lookup k ((k, v) :: l) = some v := by
  simp [lookup_cons]

omit [Encode α] in
theorem lookup_cons_ne {k k' : α} (h : k' ≠ k) (v : β) (l : List (α × β)) :
    lookup k ((k', v) :: l) = lookup k l := by
  simp [lookup_cons, h]

/-- A key less than every key of a sorted list is not in it. -/
theorem lookup_below {k : α} {l : List (α × β)} (h : ∀ e ∈ l, Encode.lt k e.1) : lookup k l = none := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨k', v⟩ := e
    have hk : k' ≠ k := fun he => Encode.lt_irrefl k (he ▸ h _ (List.mem_cons_self ..))
    rw [lookup_cons_ne hk]
    exact ih fun e he => h e (List.mem_cons_of_mem _ he)

omit [DecidableEq α] in
theorem sorted_cons {k : α} {v : β} {l : List (α × β)} :
    (((k, v) :: l).map (·.1)).Pairwise Encode.lt ↔
      (∀ e ∈ l, Encode.lt k e.1) ∧ (l.map (·.1)).Pairwise Encode.lt := by
  simp [List.pairwise_cons]

/-- **`ext_entries`.** Two sorted lists with the same lookups are equal. -/
theorem ext_entries : ∀ {l₁ l₂ : List (α × β)},
    (l₁.map (·.1)).Pairwise Encode.lt → (l₂.map (·.1)).Pairwise Encode.lt →
    (∀ k, lookup k l₁ = lookup k l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], (k, v) :: l₂, _, _, h => by
    have := h k; rw [lookup_nil, lookup_cons_self] at this; cases this
  | (k, v) :: l₁, [], _, _, h => by
    have := h k; rw [lookup_nil, lookup_cons_self] at this; cases this
  | (k₁, v₁) :: l₁, (k₂, v₂) :: l₂, h₁, h₂, h => by
    rw [sorted_cons] at h₁ h₂
    -- The least keys are the same: otherwise the lesser is missing from the other list.
    have hk : k₁ = k₂ := by
      apply Classical.byContradiction
      intro hne
      rcases Encode.lt_total hne with hlt | hlt
      · have := h k₁
        rw [lookup_cons_self, lookup_cons_ne (fun e => hne e.symm),
          lookup_below fun e he => Encode.lt_trans hlt (h₂.1 e he)] at this
        cases this
      · have := h k₂
        rw [lookup_cons_ne hne, lookup_cons_self,
          lookup_below fun e he => Encode.lt_trans hlt (h₁.1 e he)] at this
        cases this
    subst hk
    have hv : v₁ = v₂ := by
      have := h k₁
      rw [lookup_cons_self, lookup_cons_self] at this
      exact Option.some.inj this
    subst hv
    have ht : l₁ = l₂ := ext_entries h₁.2 h₂.2 fun k => by
      by_cases hk : k₁ = k
      · subst hk
        rw [lookup_below h₁.1, lookup_below h₂.1]
      · have := h k
        rwa [lookup_cons_ne hk, lookup_cons_ne hk] at this
    rw [ht]

/-- **`CMap.ext`.** Maps with the same lookups are equal. -/
theorem ext {m₁ m₂ : CMap α β} (h : ∀ k, m₁.get k = m₂.get k) : m₁ = m₂ := by
  obtain ⟨l₁, s₁⟩ := m₁
  obtain ⟨l₂, s₂⟩ := m₂
  have : l₁ = l₂ := ext_entries s₁ s₂ h
  subst this
  rfl

/-! ## Setting a key -/

/-- Put `(k, v)` in its place in a sorted list, replacing `k`'s entry if there is one. -/
def insertEntry (k : α) (v : β) : List (α × β) → List (α × β)
  | [] => [(k, v)]
  | (k', v') :: l =>
    if Encode.lt k k' then (k, v) :: (k', v') :: l
    else if k = k' then (k, v) :: l
    else (k', v') :: insertEntry k v l

/-- Remove `k`'s entry. -/
def eraseEntry (k : α) (l : List (α × β)) : List (α × β) := l.filter fun e => e.1 ≠ k

theorem mem_insertEntry {k : α} {v : β} {e : α × β} :
    ∀ {l : List (α × β)}, e ∈ insertEntry k v l → e = (k, v) ∨ e ∈ l
  | [], h => by simp [insertEntry] at h; exact Or.inl h
  | (k', v') :: l, h => by
    unfold insertEntry at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · split at h
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (h ▸ List.mem_cons_self ..)
        · rcases mem_insertEntry h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

theorem sorted_insertEntry (k : α) (v : β) :
    ∀ {l : List (α × β)}, (l.map (·.1)).Pairwise Encode.lt →
      ((insertEntry k v l).map (·.1)).Pairwise Encode.lt
  | [], _ => by simp [insertEntry]
  | (k', v') :: l, h => by
    rw [sorted_cons] at h
    unfold insertEntry
    split
    · rename_i hlt
      rw [sorted_cons, sorted_cons]
      refine ⟨fun e he => ?_, h⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact hlt
      · exact Encode.lt_trans hlt (h.1 e he)
    · split
      · rename_i _ heq
        subst heq
        rw [sorted_cons]
        exact h
      · rename_i hlt hne
        rw [sorted_cons]
        refine ⟨fun e he => ?_, sorted_insertEntry k v h.2⟩
        rcases mem_insertEntry he with rfl | he
        · rcases Encode.lt_total hne with h' | h'
          · exact absurd h' hlt
          · exact h'
        · exact h.1 e he

theorem lookup_insertEntry (k k' : α) (v : β) :
    ∀ (l : List (α × β)), lookup k' (insertEntry k v l) = if k = k' then some v else lookup k' l
  | [] => by simp [insertEntry, lookup_cons, lookup_nil]
  | (k₀, v₀) :: l => by
    unfold insertEntry
    split
    · rw [lookup_cons]
    · split
      · rename_i _ heq
        subst heq
        rw [lookup_cons, lookup_cons]
        by_cases hk : k = k' <;> simp [hk]
      · rename_i _ hne
        rw [lookup_cons, lookup_cons, lookup_insertEntry k k' v l]
        by_cases hk : k = k'
        · subst hk; simp [Ne.symm hne]
        · by_cases hk0 : k₀ = k' <;> simp [hk, hk0]

theorem sorted_eraseEntry (k : α) {l : List (α × β)} (h : (l.map (·.1)).Pairwise Encode.lt) :
    ((eraseEntry k l).map (·.1)).Pairwise Encode.lt := by
  unfold eraseEntry
  rw [List.pairwise_map] at h ⊢
  exact h.sublist List.filter_sublist

omit [Encode α] in
theorem lookup_eraseEntry (k k' : α) (l : List (α × β)) :
    lookup k' (eraseEntry k l) = if k = k' then none else lookup k' l := by
  induction l with
  | nil => simp [eraseEntry, lookup_nil]
  | cons e l ih =>
    obtain ⟨k₀, v₀⟩ := e
    by_cases h0 : k₀ = k
    · subst h0
      have : eraseEntry k₀ ((k₀, v₀) :: l) = eraseEntry k₀ l := by simp [eraseEntry]
      rw [this, ih, lookup_cons]
      by_cases hk : k₀ = k' <;> simp [hk]
    · have : eraseEntry k ((k₀, v₀) :: l) = (k₀, v₀) :: eraseEntry k l := by simp [eraseEntry, h0]
      rw [this, lookup_cons, ih, lookup_cons]
      by_cases hk : k = k'
      · subst hk; simp [h0]
      · simp [hk]

/-- Set key `k` to `v`, or remove it when `v` is `none`. -/
def set (m : CMap α β) (k : α) : Option β → CMap α β
  | some v => ⟨insertEntry k v m.entries, sorted_insertEntry k v m.sorted⟩
  | none => ⟨eraseEntry k m.entries, sorted_eraseEntry k m.sorted⟩

@[simp] theorem get_set (m : CMap α β) (k k' : α) (v : Option β) :
    (m.set k v).get k' = if k' = k then v else m.get k' := by
  cases v with
  | some v =>
    show lookup k' (insertEntry k v m.entries) = _
    rw [lookup_insertEntry k k' v _]
    by_cases h : k' = k
    · subst h; simp
    · simp [h, Ne.symm h]; rfl
  | none =>
    show lookup k' (eraseEntry k m.entries) = _
    rw [lookup_eraseEntry]
    by_cases h : k' = k
    · subst h; simp
    · simp [h, Ne.symm h]; rfl

@[simp] theorem get_empty (k : α) : (empty : CMap α β).get k = none := rfl

/-- The map that takes each key in `ks` to `f` of it. -/
def ofFn (ks : List α) (f : α → Option β) : CMap α β :=
  ks.foldr (fun k m => m.set k (f k)) empty

theorem get_ofFn (ks : List α) (f : α → Option β) (k : α) :
    (ofFn ks f).get k = if k ∈ ks then f k else none := by
  induction ks with
  | nil => simp [ofFn]
  | cons k₀ ks ih =>
    simp only [ofFn, List.foldr_cons] at ih ⊢
    rw [get_set, ih]
    by_cases h : k = k₀
    · subst h; simp
    · simp [h]

/-- The keys of a map. -/
def keys (m : CMap α β) : List α := m.entries.map (·.1)

theorem get_isSome_iff_mem_keys (m : CMap α β) (k : α) : (m.get k).isSome ↔ k ∈ m.keys := by
  obtain ⟨l, hl⟩ := m
  show (lookup k l).isSome ↔ k ∈ l.map (·.1)
  clear hl
  induction l with
  | nil => simp [lookup_nil]
  | cons e l ih =>
    obtain ⟨k₀, v₀⟩ := e
    rw [lookup_cons]
    by_cases h : k₀ = k
    · subst h; simp
    · simp only [h, ↓reduceIte, List.map_cons, List.mem_cons]
      rw [ih]
      constructor
      · exact Or.inr
      · rintro (h' | h')
        · exact absurd h'.symm h
        · exact h'

omit [DecidableEq α] in
theorem entries_inj {m₁ m₂ : CMap α β} (h : m₁.entries = m₂.entries) : m₁ = m₂ := by
  cases m₁; cases m₂; cases h; rfl

instance [DecidableEq β] : DecidableEq (CMap α β) := fun m₁ m₂ =>
  if h : m₁.entries = m₂.entries then isTrue (entries_inj h) else isFalse fun e => h (e ▸ rfl)

/-- A map is the map of its keys to its values. -/
theorem eq_ofFn (m : CMap α β) : m = ofFn m.keys m.get :=
  ext fun k => by
    rw [get_ofFn]
    by_cases h : k ∈ m.keys
    · simp [h]
    · have hn : m.get k = none := by
        cases hg : m.get k with
        | none => rfl
        | some _ => exact absurd ((get_isSome_iff_mem_keys m k).mp (by simp [hg])) h
      simp [h, hn]

end CMap

end JinagaSpec.Cascade
