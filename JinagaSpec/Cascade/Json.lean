import JinagaSpec.Cascade.CMap

/-!
# Cascade: JSON values

A value is finite, as it is in the TypeScript: an integer, a string, a list, or a
map from values to values. A map is stored as a sorted list of entries with no
key repeated, so equal maps are equal lists (`CMap`); `Json.map` holds that list,
and the model builds maps only through `CMap`.

The encoding into lists of integers writes each value's tag and length before
its parts, so no encoding is a proper prefix of another (`enc_prefix`), and the
encoding is injective. It orders values, and decides their equality.
-/
namespace JinagaSpec.Cascade

inductive Json where
  | int (n : Int)
  | str (s : String)
  | list (items : List Json)
  | map (entries : List (Json × Json))

mutual
/-- The encoding: a tag, a length where there is one, then the parts. -/
def Json.enc : Json → List Int
  | .int n => [0, n]
  | .str s => 1 :: s.toList.length :: s.toList.map fun c => (c.toNat : Int)
  | .list vs => 2 :: vs.length :: Json.encList vs
  | .map es => 3 :: es.length :: Json.encEntries es

def Json.encList : List Json → List Int
  | [] => []
  | v :: vs => v.enc ++ Json.encList vs

def Json.encEntries : List (Json × Json) → List Int
  | [] => []
  | (k, v) :: es => k.enc ++ (v.enc ++ Json.encEntries es)
end

theorem chars_inj {a b : List Char} (h : a.map (fun c => (c.toNat : Int)) = b.map fun c => (c.toNat : Int)) :
    a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons _ _ => simp at h
  | cons c a ih => cases b with
    | nil => simp at h
    | cons d b =>
      simp only [List.map_cons, List.cons.injEq] at h
      have hc : c = d := Char.toNat_inj.mp (by exact_mod_cast h.1)
      rw [hc, ih h.2]

mutual
/-- No encoding is a proper prefix of another. -/
theorem Json.enc_prefix : ∀ (a b : Json) (r s : List Int), a.enc ++ r = b.enc ++ s → a = b ∧ r = s
  | .int n, .int m, r, s, h => by
    simp only [Json.enc, List.cons_append, List.nil_append, List.cons.injEq] at h
    exact ⟨by rw [h.2.1], h.2.2⟩
  | .str x, .str y, r, s, h => by
    simp only [Json.enc, List.cons_append, List.cons.injEq] at h
    obtain ⟨-, hl, h⟩ := h
    have hl : x.toList.length = y.toList.length := by exact_mod_cast hl
    obtain ⟨hc, hr⟩ := List.append_inj h (by simpa using hl)
    exact ⟨by rw [String.ext (chars_inj hc)], hr⟩
  | .list xs, .list ys, r, s, h => by
    simp only [Json.enc, List.cons_append, List.cons.injEq] at h
    obtain ⟨-, hl, h⟩ := h
    have hl : xs.length = ys.length := by exact_mod_cast hl
    obtain ⟨he, hr⟩ := Json.encList_prefix xs ys r s hl h
    exact ⟨by rw [he], hr⟩
  | .map xs, .map ys, r, s, h => by
    simp only [Json.enc, List.cons_append, List.cons.injEq] at h
    obtain ⟨-, hl, h⟩ := h
    have hl : xs.length = ys.length := by exact_mod_cast hl
    obtain ⟨he, hr⟩ := Json.encEntries_prefix xs ys r s hl h
    exact ⟨by rw [he], hr⟩
  | .int _, .str _, _, _, h | .int _, .list _, _, _, h | .int _, .map _, _, _, h
  | .str _, .int _, _, _, h | .str _, .list _, _, _, h | .str _, .map _, _, _, h
  | .list _, .int _, _, _, h | .list _, .str _, _, _, h | .list _, .map _, _, _, h
  | .map _, .int _, _, _, h | .map _, .str _, _, _, h | .map _, .list _, _, _, h => by
    simp [Json.enc] at h

theorem Json.encList_prefix : ∀ (xs ys : List Json) (r s : List Int), xs.length = ys.length →
    Json.encList xs ++ r = Json.encList ys ++ s → xs = ys ∧ r = s
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | x :: xs, y :: ys, r, s, hl, h => by
    simp only [Json.encList, List.append_assoc] at h
    obtain ⟨hxy, h⟩ := Json.enc_prefix x y _ _ h
    obtain ⟨hs, hr⟩ := Json.encList_prefix xs ys r s (by simpa using hl) h
    exact ⟨by rw [hxy, hs], hr⟩
  | [], _ :: _, _, _, hl, _ | _ :: _, [], _, _, hl, _ => by simp at hl

theorem Json.encEntries_prefix : ∀ (xs ys : List (Json × Json)) (r s : List Int), xs.length = ys.length →
    Json.encEntries xs ++ r = Json.encEntries ys ++ s → xs = ys ∧ r = s
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | (k, v) :: xs, (k', v') :: ys, r, s, hl, h => by
    simp only [Json.encEntries, List.append_assoc] at h
    obtain ⟨hk, h⟩ := Json.enc_prefix k k' _ _ h
    obtain ⟨hv, h⟩ := Json.enc_prefix v v' _ _ h
    obtain ⟨hs, hr⟩ := Json.encEntries_prefix xs ys r s (by simpa using hl) h
    exact ⟨by rw [hk, hv, hs], hr⟩
  | [], _ :: _, _, _, hl, _ | _ :: _, [], _, _, hl, _ => by simp at hl
end

theorem Json.enc_inj {a b : Json} (h : a.enc = b.enc) : a = b :=
  (Json.enc_prefix a b [] [] (by simp [h])).1

instance : Encode Json := ⟨Json.enc, Json.enc_inj⟩

instance : DecidableEq Json := Encode.decEq

instance : Encode String :=
  ⟨fun s => s.toList.map fun c => (c.toNat : Int), fun h => String.ext (chars_inj h)⟩

/-- A map as a value. -/
def Json.ofMap (m : CMap Json Json) : Json := .map m.entries

theorem Json.ofMap_inj {m₁ m₂ : CMap Json Json} (h : Json.ofMap m₁ = Json.ofMap m₂) : m₁ = m₂ :=
  CMap.entries_inj (Json.map.inj h)

/-! ## Canonical values -/

mutual
/-- Every map in a value, at every depth, is sorted by key with no key repeated.
`Json.map` can hold any list, so this is a condition, not a guarantee: the
model's own values are built through `CMap`, and a caller's values are assumed
canonical. Two canonical values that hold the same JSON are the same value. -/
def Json.Canonical : Json → Prop
  | .int _ => True
  | .str _ => True
  | .list vs => Json.CanonicalList vs
  | .map es => (es.map (·.1)).Pairwise Encode.lt ∧ Json.CanonicalEntries es

def Json.CanonicalList : List Json → Prop
  | [] => True
  | v :: vs => v.Canonical ∧ Json.CanonicalList vs

def Json.CanonicalEntries : List (Json × Json) → Prop
  | [] => True
  | (k, v) :: es => k.Canonical ∧ v.Canonical ∧ Json.CanonicalEntries es
end

/-! ## Examples, checked by evaluation -/

/-- A map does not remember the order its entries were set in. -/
example :
    Json.ofMap ((CMap.empty.set (.str "a") (some (.int 1))).set (.str "b") (some (.int 2))) =
      Json.ofMap ((CMap.empty.set (.str "b") (some (.int 2))).set (.str "a") (some (.int 1))) := by
  decide

/-- Values of different kinds differ. -/
example : Json.int 1 ≠ Json.str "1" := by decide

end JinagaSpec.Cascade
