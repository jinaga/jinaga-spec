import JinagaSpec.Proofs.Children
import JinagaSpec.Proofs.Maintain
import JinagaSpec.Proofs.WellFormedCheck
import JinagaSpec.FeedCases
import JinagaSpec.Proofs.Rename

/-!
# No feeds defer a contested exclusion exactly

`feeds_defer` withholds an entity's details while no witness of its exclusion
has a cancelling fact. It does not withhold them while every witness stands.
This file proves that no feeds can: any feeds meeting consistency and
append-only deliver the name of an event that is excluded, its one delete
standing (`exact_deferral_impossible`).

The specification is `contested` (`FeedCases.lean`): an event's names, unless
its delete stands; a delete stands unless restored, a restore unless revoked,
a revoke unless unrevoked. The graphs (`graph N U`) have one event, one
delete, one restore, `N` revokes of the restore, and an unrevoke of each
revoke in `U`, then the event's name.

* With every revoke unrevoked, the restore stands, the delete is cancelled,
  and the event's name is a result. Consistency forces some feed's tuple to
  deliver the name: a replica missing it would read nothing.
* Take away the last unrevoke, the one with the largest id, and the restore is
  revoked, the delete stands, and the event is excluded. Exact deferral would
  withhold the name. But the unrevoke arrives as a batch with a larger id than
  any the graph holds, so append-only says the tuple was there before it
  arrived, unless it binds that unrevoke.
* Ids mean nothing to a specification (`tuples_rename`), and swapping two
  revokes with their unrevokes keeps the graph. So any unrevoke can be the
  last, and the tuple binds every one of the `N`. A tuple binds one fact per
  match, and `N` is more than any feed has.

The requirements are stated for any list of feeds, as `feeds_cover`'s and
`feed_antitone`'s conclusions (`Consistent`, `AppendOnly`), the latter for
the batches paging meets (`IdsIncrease`). A feed may be any specification,
with any nesting of conditions. What it delivers is the facts its matches
bind, at the specification's givens (`Specification.tuples`); a feed's
projection, and any child specification in it, deliver nothing. `buildFeeds`
meets both requirements (`buildFeeds_consistent`, `buildFeeds_appendOnly`), on
`contested` too (`contested_feasible`), so it is deferral that cannot be made
exact.
-/
namespace JinagaSpec

/-! ## The requirements, for any feeds -/

/-- **Consistency**, for the feeds `Fs` of `s`: `feeds_cover`'s conclusion. A
replica that holds the givens and every fact the feeds deliver reads what the
replicator reads. -/
def Consistent (s : Specification) (Fs : List Specification) : Prop :=
  ∀ (g : Graph) (B : List Fact) (env : Env), Fresh g B → Settled B env → (∀ l ∈ s.given, g.has env l = true) →
    (∀ id ∈ deliver Fs (g ++ B) env, Outside B id) → ∀ r, s.Reads g env r ↔ s.Reads (g ++ B) env r

/-- **Append-only**, for a feed: `feed_antitone`'s conclusion, for the batches
paging by bookmark meets (`caught_grow`), whose ids are larger than the graph's.
A tuple found after such a batch, none of whose facts is in the batch, was
found before, so a tuple never appears behind a bookmark. -/
def AppendOnly (f : Specification) : Prop :=
  ∀ (g : Graph) (B : List Fact) (env : Env), Fresh g B → IdsIncrease g B → Settled B env →
    ∀ t ∈ f.tuples (g ++ B) env, (∀ id ∈ t, Outside B id) → t ∈ f.tuples g env

theorem buildFeeds_consistent {s : Specification} (hwf : ∀ d ∈ s.descendants, WellFormed d)
    (hd : ∀ d ∈ s.descendants, DistinctLabels d) (hr : ∀ d ∈ s.descendants, RootedMatches d.matchList) :
    Consistent s (buildFeeds s) :=
  fun _ _ _ hf henv hgiv hdel => feeds_cover hwf hd hr hf henv hgiv hdel

theorem buildFeeds_appendOnly {s : Specification} (hwf : ∀ d ∈ s.descendants, WellFormed d)
    (hd : ∀ d ∈ s.descendants, DistinctLabels d) : ∀ f ∈ buildFeeds s, AppendOnly f :=
  fun f hf _ _ _ hfr _ henv _ ht hout =>
    feed_antitone hfr (buildFeeds_feedShape s f hf) (buildFeeds_nodup hwf hd f hf) henv ht hout

/-! ## Evaluating one role -/

/-- A path condition of one role, `u->ρ = r`, where `u` and `r` are bound to
facts `f` and `f'` of the graph, `f'` of the role's type: `f` names `f'` by the
role. -/
theorem holds_role {g : Graph} (hu : g.IdsUnique) {env : Env} {u r : Name} {ρ : Role} {f f' : Fact}
    (hf : f ∈ g) (hf' : f' ∈ g) (hu' : env u = some f.id) (hr : env r = some f'.id)
    (ht : f'.type = ρ.predecessorType) :
    PathCondition.holds g env u { rolesLeft := [ρ], labelRight := r, rolesRight := [] } = true ↔
      (ρ.name, f'.id) ∈ f.predecessors := by
  simp [PathCondition.holds, hu', hr, Graph.walk, Graph.step, factOf_of_mem hu hf]
  exact ⟨fun ⟨_, _, h, rfl, _, rfl⟩ => h, fun h => ⟨_, _, h, rfl, by simp [factOf_of_mem hu hf', ht], rfl⟩⟩

open Build in
/-- A match `u: t [u->ρ = r, rest]`, where `r` is bound to `f'`, has a solution
exactly when some fact of type `t` names `f'` by `ρ` and meets `rest`. -/
theorem exists_unknown {g : Graph} (hu : g.IdsUnique) {env : Env} {u t r : Name} {ρ : Role}
    {rest : List Condition} {f' : Fact} (hf' : f' ∈ g) (hr : env r = some f'.id)
    (ht : f'.type = ρ.predecessorType) (hne : r ≠ u) :
    (∃ σ, σ ∈ evalMatches g env [unknown u t (path [ρ] r :: rest)]) ↔
      ∃ f ∈ g, f.type = t ∧ (ρ.name, f'.id) ∈ f.predecessors ∧ allHold g (env.bind u f.id) u rest = true := by
  have hp : ∀ f ∈ g, (holds g (env.bind u f.id) u (path [ρ] r) = true ↔ (ρ.name, f'.id) ∈ f.predecessors) :=
    fun f hf => holds_role hu hf hf' (by simp [Env.bind]) (by simp [Env.bind, hne, hr]) ht
  simp only [unknown, mem_evalMatches_cons]
  simp only [evalMatches, List.mem_singleton, allHold, Bool.and_eq_true]
  exact ⟨fun ⟨_, f, hf, ht', h, _⟩ => ⟨f, hf, ht', (hp f hf).mp h.1, h.2⟩,
    fun ⟨f, hf, ht', h, hr⟩ => ⟨_, f, hf, ht', ⟨(hp f hf).mpr h, hr⟩, rfl⟩⟩

theorem tuples_congr {g g' : Graph} (hmem : ∀ x, x ∈ g ↔ x ∈ g') (hu : g.IdsUnique) (f : Specification)
    (env : Env) (t : List FactId) : t ∈ f.tuples g env ↔ t ∈ f.tuples g' env := by
  simp only [Specification.tuples, List.mem_map, evalMatches_congr hmem (factOf_congr hmem hu)]

/-! ## The graphs -/

namespace Contested
open Build

def tenant : Fact := ⟨0, "Tenant", []⟩
def event : Fact := ⟨1, "Event", [("tenant", 0)]⟩
def delete : Fact := ⟨2, "Delete", [("event", 1)]⟩
def restore : Fact := ⟨3, "Restore", [("delete", 2)]⟩
def name : Fact := ⟨4, "Name", [("event", 1)]⟩
def revoke (i : Nat) : Fact := ⟨2 * i + 5, "Revoke", [("restore", 3)]⟩
def unrevoke (i : Nat) : Fact := ⟨2 * i + 6, "Unrevoke", [("revoke", 2 * i + 5)]⟩

/-- An event, its delete, a restore of the delete, `N` revokes of the restore,
and an unrevoke of each revoke in `U`. The event's name comes after. -/
def graph (N : Nat) (U : List Nat) : Graph :=
  [tenant, event, delete, restore] ++ (List.range N).map revoke ++ U.map unrevoke

attribute [local simp] tenant event delete restore name revoke unrevoke role

/-- The tenant is the given. -/
def env0 : Env := Env.bind (fun _ => none) "t" 0

/-- The levels of `contested`, innermost first. -/
def zs : List Match := [unknown "z" "Unrevoke" [path [role "revoke" "Revoke"] "v"]]
def vs : List Match := [unknown "v" "Revoke" [path [role "restore" "Restore"] "x", notExists zs]]
def xs : List Match := [unknown "x" "Restore" [path [role "delete" "Delete"] "d", notExists vs]]
def ds : List Match := [unknown "d" "Delete" [path [role "event" "Event"] "e", notExists xs]]

theorem contested_matchList : contested.matchList =
    unknown "e" "Event" [path [role "tenant" "Tenant"] "t", notExists ds] ::
      [unknown "n" "Name" [path [role "event" "Event"] "e"]] := rfl

variable {N : Nat} {U : List Nat} {T : List Fact}

theorem mem_graph {f : Fact} : f ∈ graph N U ++ T ↔ f = tenant ∨ f = event ∨ f = delete ∨ f = restore ∨
    (∃ i < N, f = revoke i) ∨ (∃ j ∈ U, f = unrevoke j) ∨ f ∈ T := by
  simp [graph, eq_comm]

/-- Every fact of the graph, its name included. -/
theorem cases_graph (hT : ∀ f ∈ T, f = name) {f : Fact} (hf : f ∈ graph N U ++ T) :
    f = tenant ∨ f = event ∨ f = delete ∨ f = restore ∨ f = name ∨
      (∃ i < N, f = revoke i) ∨ (∃ j ∈ U, f = unrevoke j) := by
  rcases mem_graph.mp hf with h | h | h | h | h | h | h <;>
    first | simp only [h, true_or, or_true] | simp only [hT f h, true_or, or_true]

theorem idsUnique (hT : ∀ f ∈ T, f = name) : (graph N U ++ T).IdsUnique := by
  intro a ha b hb h
  rcases cases_graph hT ha with rfl | rfl | rfl | rfl | rfl | ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩ <;>
  rcases cases_graph hT hb with rfl | rfl | rfl | rfl | rfl | ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩ <;>
  simp at h ⊢ <;> omega

theorem revoke_mem {i : Nat} (hi : i < N) : revoke i ∈ graph N U ++ T :=
  mem_graph.mpr (.inr (.inr (.inr (.inr (.inl ⟨i, hi, rfl⟩)))))

theorem unrevoke_mem {j : Nat} (hj : j ∈ U) : unrevoke j ∈ graph N U ++ T :=
  mem_graph.mpr (.inr (.inr (.inr (.inr (.inr (.inl ⟨j, hj, rfl⟩))))))

theorem base_mem {f : Fact} (hf : f ∈ [tenant, event, delete, restore]) : f ∈ graph N U ++ T :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hf))

/-- A revoke is cancelled when it is unrevoked. -/
theorem zs_iff (hT : ∀ f ∈ T, f = name) {env : Env} {i : Nat} (hi : i < N) (hv : env "v" = some (revoke i).id) :
    (∃ σ, σ ∈ evalMatches (graph N U ++ T) env zs) ↔ i ∈ U := by
  rw [zs, exists_unknown (idsUnique hT) (revoke_mem hi) hv rfl (by decide)]
  constructor
  · rintro ⟨f, hf, ht, hp, -⟩
    rcases cases_graph hT hf with rfl | rfl | rfl | rfl | rfl | ⟨j, -, rfl⟩ | ⟨j, hj, rfl⟩ <;>
      simp at ht hp
    exact (show i = j by omega) ▸ hj
  · exact fun h => ⟨unrevoke i, unrevoke_mem h, rfl, by simp, rfl⟩

/-- A restore is revoked when one of its revokes is not unrevoked. -/
theorem vs_iff (hT : ∀ f ∈ T, f = name) {env : Env} (hx : env "x" = some restore.id) :
    (∃ σ, σ ∈ evalMatches (graph N U ++ T) env vs) ↔ ∃ i < N, i ∉ U := by
  rw [vs, exists_unknown (idsUnique hT) (base_mem (by simp)) hx rfl (by decide)]
  constructor
  · rintro ⟨f, hf, ht, hp, h⟩
    rcases cases_graph hT hf with rfl | rfl | rfl | rfl | rfl | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ <;>
      simp at ht hp
    simp only [allHold, Bool.and_true, notExists, holds_notExists] at h
    exact ⟨i, hi, fun hu => let ⟨σ, hσ⟩ := (zs_iff hT hi (by simp [Env.bind])).mpr hu; h σ hσ⟩
  · rintro ⟨i, hi, hu⟩
    refine ⟨revoke i, revoke_mem hi, rfl, by simp, ?_⟩
    simp only [allHold, Bool.and_true, notExists, holds_notExists]
    exact fun σ hσ => hu ((zs_iff hT hi (by simp [Env.bind])).mp ⟨σ, hσ⟩)

/-- The delete is restored when every revoke is unrevoked. -/
theorem xs_iff (hT : ∀ f ∈ T, f = name) {env : Env} (hd : env "d" = some delete.id) :
    (∃ σ, σ ∈ evalMatches (graph N U ++ T) env xs) ↔ ∀ i < N, i ∈ U := by
  rw [xs, exists_unknown (idsUnique hT) (base_mem (by simp)) hd rfl (by decide)]
  have hv := vs_iff hT (N := N) (U := U) (env := env.bind "x" restore.id) (by simp [Env.bind])
  simp only [allHold, Bool.and_true, notExists, holds_notExists]
  constructor
  · rintro ⟨f, hf, ht, hp, h⟩
    rcases cases_graph hT hf with rfl | rfl | rfl | rfl | rfl | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ <;>
      simp at ht hp
    exact fun i hi => Classical.byContradiction fun hu => let ⟨σ, hσ⟩ := hv.mpr ⟨i, hi, hu⟩; h σ hσ
  · intro hu
    refine ⟨restore, base_mem (by simp), rfl, by simp, fun σ hσ => ?_⟩
    obtain ⟨i, hi, hi'⟩ := hv.mp ⟨σ, hσ⟩
    exact hi' (hu i hi)

/-- The event is excluded when the delete is not restored. -/
theorem ds_iff (hT : ∀ f ∈ T, f = name) {env : Env} (he : env "e" = some event.id) :
    (∃ σ, σ ∈ evalMatches (graph N U ++ T) env ds) ↔ ∃ i < N, i ∉ U := by
  rw [ds, exists_unknown (idsUnique hT) (base_mem (by simp)) he rfl (by decide)]
  have hx := xs_iff hT (N := N) (U := U) (env := env.bind "d" delete.id) (by simp [Env.bind])
  simp only [allHold, Bool.and_true, notExists, holds_notExists]
  constructor
  · rintro ⟨f, hf, ht, hp, h⟩
    rcases cases_graph hT hf with rfl | rfl | rfl | rfl | rfl | ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩ <;>
      simp at ht hp
    refine Classical.byContradiction fun hn => ?_
    obtain ⟨σ, hσ⟩ := hx.mpr fun i hi => Classical.byContradiction fun hu => hn ⟨i, hi, hu⟩
    exact h σ hσ
  · rintro ⟨i, hi, hu⟩
    exact ⟨delete, base_mem (by simp), rfl, by simp, fun σ hσ => hu ((hx.mp ⟨σ, hσ⟩) i hi)⟩

/-- The event and its name are a solution exactly when every revoke is
unrevoked and the name is held. -/
theorem mem_contested (hT : ∀ f ∈ T, f = name) {σ : Env} :
    σ ∈ evalMatches (graph N U ++ T) env0 contested.matchList ↔
      (∀ i < N, i ∈ U) ∧ name ∈ T ∧ σ = (env0.bind "e" event.id).bind "n" name.id := by
  have hu := idsUnique (N := N) (U := U) hT
  have hd := ds_iff hT (N := N) (U := U) (env := env0.bind "e" event.id) (by simp [Env.bind])
  rw [contested_matchList]
  simp only [unknown, mem_evalMatches_cons]
  simp only [evalMatches, List.mem_singleton, allHold, Bool.and_true, Bool.and_eq_true, notExists,
    holds_notExists]
  constructor
  · rintro ⟨f, hf, ht, ⟨-, hneg⟩, f2, hf2, ht2, -, rfl⟩
    rcases cases_graph hT hf with rfl | rfl | rfl | rfl | rfl | ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩ <;> simp at ht
    rcases mem_graph.mp hf2 with rfl | rfl | rfl | rfl | ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩ | hn <;> try simp at ht2
    obtain rfl := hT _ hn
    refine ⟨fun i hi => Classical.byContradiction fun hu' => ?_, hn, rfl⟩
    obtain ⟨σ, hσ⟩ := hd.mpr ⟨i, hi, hu'⟩
    exact hneg σ hσ
  · rintro ⟨hall, hn, rfl⟩
    refine ⟨event, base_mem (f := event) (by simp), rfl, ⟨?_, fun σ hσ => ?_⟩, name, List.mem_append_right _ hn, rfl, ?_, rfl⟩
    · simp only [path, holds]
      refine (holds_role (f := event) (f' := tenant) hu (base_mem (by simp)) (base_mem (by simp))
        ?_ ?_ ?_).mpr ?_ <;> simp [env0, Env.bind]
    · obtain ⟨i, hi, hu'⟩ := hd.mp ⟨σ, hσ⟩
      exact hu' (hall i hi)
    · simp only [path, holds]
      refine (holds_role (f := name) (f' := event) hu (List.mem_append_right _ hn) (base_mem (by simp))
        ?_ ?_ ?_).mpr ?_ <;> simp [Env.bind]

theorem given_held (hT : ∀ f ∈ T, f = name) : ∀ l ∈ contested.given, (graph N U ++ T).has env0 l = true := by
  have ht := factOf_of_mem (idsUnique (N := N) (U := U) hT) (base_mem (f := tenant) (by simp))
  simp at ht
  simp [contested, spec, givens, Graph.has, env0, Env.bind, ht]

/-- A replica reads the event's name exactly when every revoke is unrevoked
and it holds the name. -/
theorem reads_contested (hT : ∀ f ∈ T, f = name) (r : Result) :
    contested.Reads (graph N U ++ T) env0 r ↔ (∀ i < N, i ∈ U) ∧ name ∈ T ∧ r = .mk [some name.id] [] := by
  obtain ⟨row, cs⟩ := r
  have hg : contested.given.all ((graph N U ++ T).has env0) = true := List.all_eq_true.mpr (given_held hT)
  rw [Specification.Reads, show contested.projection = fact "n" from rfl, Projection.Reads]
  simp only [hg, true_and, mem_contested hT]
  simp [fact, Projection.children, Projection.labels, Projection.ReadsAt]
  exact ⟨fun ⟨_, ⟨hu, hn, rfl⟩, hr, hc⟩ => ⟨hu, hn, by simpa [Env.bind] using hr, hc⟩,
    fun ⟨hu, hn, hr, hc⟩ => ⟨_, ⟨hu, hn, rfl⟩, by simpa [Env.bind] using hr, hc⟩⟩

theorem fresh_name : Fresh (graph N U) [name] where
  idNew x hx b hb := by
    rw [List.mem_singleton.mp hb]
    rcases (mem_graph (T := [])).mp (List.mem_append_left _ hx) with
      rfl | rfl | rfl | rfl | ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩ | h <;> simp_all <;> omega
  unreferenced x hx p hp b hb := by
    rw [List.mem_singleton.mp hb]
    rcases (mem_graph (T := [])).mp (List.mem_append_left _ hx) with
      rfl | rfl | rfl | rfl | ⟨i, -, rfl⟩ | ⟨j, -, rfl⟩ | h <;> simp_all <;> omega

theorem fresh_unrevoke (hT : ∀ f ∈ T, f = name) {i : Nat} (hi : i ∉ U) : Fresh (graph N U ++ T) [unrevoke i] where
  idNew x hx b hb := by
    rw [List.mem_singleton.mp hb]
    rcases cases_graph hT hx with rfl | rfl | rfl | rfl | rfl | ⟨k, -, rfl⟩ | ⟨j, hj, rfl⟩ <;> simp <;> try omega
    exact fun h => hi ((show i = j by omega) ▸ hj)
  unreferenced x hx p hp b hb := by
    rw [List.mem_singleton.mp hb]
    rcases cases_graph hT hx with rfl | rfl | rfl | rfl | rfl | ⟨k, -, rfl⟩ | ⟨j, -, rfl⟩ <;> simp_all <;> omega

theorem settled {B : List Fact} (hB : ∀ b ∈ B, b.id ≠ 0) : Settled B env0 := by
  intro n id h b hb
  simp only [env0, Env.bind] at h
  split at h
  · cases h; exact (hB b hb).symm
  · cases h

/-- The last unrevoke has the largest id. -/
theorem increase_last (m : Nat) :
    IdsIncrease (graph (m + 1) ((List.range (m + 1)).erase m) ++ [name]) [unrevoke m] := by
  intro x hx y hy
  rw [List.mem_singleton.mp hy]
  rcases cases_graph (by simp) hx with rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | ⟨j, hj, rfl⟩ <;> simp
  · omega
  · have := List.nodup_range.mem_erase_iff.mp hj; simp at this; omega

/-! ## Any unrevoke can come last

The ids of a graph do not matter to a specification (`tuples_rename`), so
swapping two revokes, with their unrevokes, gives a graph of the same facts and
the same tuples, renamed. -/

/-- Swap the indices `i` and `m`. -/
def swap (i m k : Nat) : Nat := if k = i then m else if k = m then i else k

/-- Swap the ids of revokes `i` and `m`, and of their unrevokes. -/
def swapIds (i m : Nat) (id : FactId) : FactId :=
  if id < 5 then id else 2 * swap i m ((id - 5) / 2) + 5 + (id - 5) % 2

theorem swap_swap (i m k : Nat) : swap i m (swap i m k) = k := by
  unfold swap; by_cases h1 : k = i <;> by_cases h2 : k = m <;> simp [h1, h2] <;> omega

theorem swap_lt {i m k : Nat} (hi : i < N) (hm : m < N) (hk : k < N) : swap i m k < N := by
  unfold swap; split <;> (try split) <;> omega

theorem swapIds_swapIds (i m id : Nat) : swapIds i m (swapIds i m id) = id := by
  unfold swapIds
  by_cases h : id < 5
  · simp [h]
  · obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 2 ∧ id = 2 * k + 5 + r := ⟨(id - 5) / 2, (id - 5) % 2, by omega, by omega⟩
    rw [ite_eq_right h, show (2 * k + 5 + r - 5) / 2 = k by omega, show (2 * k + 5 + r - 5) % 2 = r by omega,
      ite_eq_right (show ¬ 2 * swap i m k + 5 + r < 5 by omega), show (2 * swap i m k + 5 + r - 5) / 2 = swap i m k by omega,
      show (2 * swap i m k + 5 + r - 5) % 2 = r by omega, swap_swap]

theorem swapIds_inj (i m : Nat) : ∀ a b, swapIds i m a = swapIds i m b → a = b := fun a b h => by
  rw [← swapIds_swapIds i m a, h, swapIds_swapIds]

theorem swapIds_small {i m id : Nat} (h : id < 5) : swapIds i m id = id := by simp [swapIds, h]

theorem swapIds_revoke (i m k : Nat) : swapIds i m (2 * k + 5) = 2 * swap i m k + 5 := by
  unfold swapIds
  rw [ite_eq_right (show ¬ 2 * k + 5 < 5 by omega), show (2 * k + 5 - 5) / 2 = k by omega,
    show (2 * k + 5 - 5) % 2 = 0 by omega]

theorem swapIds_unrevoke (i m k : Nat) : swapIds i m (2 * k + 6) = 2 * swap i m k + 6 := by
  unfold swapIds
  rw [ite_eq_right (show ¬ 2 * k + 6 < 5 by omega), show (2 * k + 6 - 5) / 2 = k by omega,
    show (2 * k + 6 - 5) % 2 = 1 by omega]

theorem env0_rename (i m : Nat) : env0.rename (swapIds i m) = env0 := by
  funext n; simp only [Env.rename, env0, Env.bind]; split <;> simp [swapIds_small]

/-- Swapping two revokes keeps the graph with every revoke unrevoked. -/
theorem rename_full {i m : Nat} (hi : i < N) (hm : m < N) (x : Fact) :
    x ∈ graph N (List.range N) ++ [name] ↔ x ∈ (graph N (List.range N) ++ [name]).rename (swapIds i m) := by
  have hT : ∀ f ∈ [name], f = name := by simp
  -- The graph is closed under the swap, which is its own inverse.
  have hclosed : ∀ y ∈ graph N (List.range N) ++ [name], y.rename (swapIds i m) ∈ graph N (List.range N) ++ [name] := by
    intro y hy
    rcases cases_graph hT hy with rfl | rfl | rfl | rfl | rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    all_goals simp only [Fact.rename, tenant, event, delete, restore, name, revoke, unrevoke, List.map,
      swapIds_small (by decide : 0 < 5), swapIds_small (by decide : 1 < 5), swapIds_small (by decide : 2 < 5),
      swapIds_small (by decide : 3 < 5), swapIds_small (by decide : 4 < 5), swapIds_revoke, swapIds_unrevoke]
    · exact base_mem (f := tenant) (by simp)
    · exact base_mem (f := event) (by simp)
    · exact base_mem (f := delete) (by simp)
    · exact base_mem (f := restore) (by simp)
    · exact List.mem_append_right _ (by simp)
    · exact revoke_mem (swap_lt hi hm hk)
    · exact unrevoke_mem (List.mem_range.mpr (swap_lt hi hm (List.mem_range.mp hk)))
  have hinv : ∀ y : Fact, (y.rename (swapIds i m)).rename (swapIds i m) = y := fun ⟨id, t, ps⟩ => by
    simp [Fact.rename, swapIds_swapIds, List.map_map, Function.comp_def]
  simp only [Graph.rename, List.mem_map]
  exact ⟨fun h => ⟨_, hclosed x h, hinv x⟩, fun ⟨y, hy, h⟩ => h ▸ hclosed y hy⟩

end Contested

theorem contested_descendants : contested.descendants = [contested] := by
  rw [Specification.descendants, Projection.paths]; rfl

/-- `buildFeeds` is consistent and append-only on `contested`, so the
requirements `exact_deferral_impossible` assumes can be met. -/
theorem contested_feasible :
    Consistent contested (buildFeeds contested) ∧ ∀ f ∈ buildFeeds contested, AppendOnly f := by
  have hwf := (isWellFormedDeep_iff contested).mp (by decide +kernel)
  have hd : ∀ d ∈ contested.descendants, DistinctLabels d := by
    rw [contested_descendants]; simp only [List.mem_singleton, forall_eq]; unfold DistinctLabels; decide +kernel
  refine ⟨buildFeeds_consistent hwf hd ?_, buildFeeds_appendOnly hwf hd⟩
  rw [contested_descendants]
  simp [contested, Build.spec, Build.unknown, Build.path, Build.notExists, RootedMatches, RootedConditions,
    Condition.isPath]

open Contested in
/-- **Exact deferral is impossible** (R4). Any feeds of `contested` that are
consistent and append-only deliver the name of an event that is excluded: on a
graph of the event, its one delete, a restore of the delete, `N` revokes of the
restore and an unrevoke of each revoke in `U`, where some revoke is not
unrevoked. The delete stands, so the event reads no result, and yet the feeds
deliver its name.

So `feeds_defer` cannot be strengthened to "withheld while every witness
stands", for any feeds, let alone to "withheld while excluded". With `N = 2`
the graph is `restore-revoked-and-unrevoked`'s, up to ids. -/
theorem exact_deferral_impossible (Fs : List Specification) (hc : Consistent contested Fs)
    (ha : ∀ f ∈ Fs, AppendOnly f) :
    ∃ N U, (∃ i < N, i ∉ U) ∧ (∀ r, ¬ contested.Reads (graph N U ++ [name]) env0 r) ∧
      name.id ∈ deliver Fs (graph N U ++ [name]) env0 := by
  -- More unrevokes than the feeds have matches.
  let m := (Fs.flatMap (·.matchList)).length
  let N := m + 1
  have hT : ∀ f ∈ [name], f = name := by simp
  have hfull : name.id ∈ deliver Fs (graph N (List.range N) ++ [name]) env0 := by
    refine Classical.byContradiction fun hn => ?_
    have h := hc (graph N (List.range N)) [name] env0 fresh_name (settled (by simp [name]))
      (by simpa using given_held (N := N) (U := List.range N) (T := []) (by simp))
      (fun id hid b hb => by rw [List.mem_singleton.mp hb]; exact fun h => hn (h ▸ hid)) (.mk [some name.id] [])
    have h0 := reads_contested (N := N) (U := List.range N) (T := []) (by simp) (.mk [some name.id] [])
    rw [List.append_nil] at h0
    rw [reads_contested hT] at h
    simp at h0 h
    exact h0 h
  obtain ⟨f, hf, t, ht, hnt⟩ := mem_deliver.mp hfull
  -- The graph without the last unrevoke: the event is excluded.
  have hU : m ∉ (List.range N).erase m := fun h => (List.nodup_range.mem_erase_iff.mp h).1 rfl
  by_cases hd : name.id ∈ deliver Fs (graph N ((List.range N).erase m) ++ [name]) env0
  · exact ⟨N, _, ⟨m, by omega, hU⟩, fun r hr => hU (((reads_contested hT r).mp hr).1 m (by omega)), hd⟩
  exfalso
  have hperm : ((List.range N).map unrevoke).Perm (((List.range N).erase m).map unrevoke ++ [unrevoke m]) :=
    ((List.perm_cons_erase (List.mem_range.mpr (by omega))).map _).trans (List.perm_append_singleton _ _).symm
  have hmem : ∀ x, x ∈ graph N (List.range N) ++ [name] ↔
      x ∈ graph N ((List.range N).erase m) ++ [name] ++ [unrevoke m] := fun x => by
    simp only [graph, List.mem_append, hperm.mem_iff]
    simp only [or_assoc, or_comm]
  -- Every unrevoke `i`, swapped with the last, is one the tuple binds.
  have hz : ∀ i < N, (unrevoke i).id ∈ t := by
    intro i hi
    refine Classical.byContradiction fun hz => hd ?_
    have hr := tuples_rename (swapIds_inj i m) f (graph N (List.range N) ++ [name]) env0
    rw [env0_rename] at hr
    have ht1 : t.map (swapIds i m) ∈ f.tuples (graph N ((List.range N).erase m) ++ [name] ++ [unrevoke m]) env0 :=
      (tuples_congr hmem (idsUnique hT) f env0 _).mp ((tuples_congr (rename_full hi (by omega)) (idsUnique hT) f env0 _).mpr
        (hr ▸ List.mem_map_of_mem ht))
    have hout : ∀ id ∈ t.map (swapIds i m), Outside [unrevoke m] id := by
      intro id hid b hb heq
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hid
      rw [List.mem_singleton.mp hb] at heq
      have : a = (unrevoke i).id := by
        rw [← swapIds_swapIds i m a, heq]; simp [unrevoke, swapIds_unrevoke, swap]; split <;> omega
      exact hz (this ▸ ha')
    exact mem_deliver.mpr ⟨f, hf, _, ha f hf _ [unrevoke m] env0 (fresh_unrevoke hT hU) (increase_last m)
      (settled (by simp [unrevoke])) _ ht1 hout, List.mem_map.mpr ⟨_, hnt, swapIds_small (by simp [name])⟩⟩
  have hN := List.Nodup.length_le_of_subset (l₁ := (List.range N).map fun i => (unrevoke i).id)
    (List.Pairwise.map _ (fun a b hab h => hab (by simp [unrevoke] at h; omega)) List.nodup_range)
    (fun x hx => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact hz i (List.mem_range.mp hi))
  have := length_tuple ht
  have := length_le_flatMap (·.matchList) hf
  simp at hN
  omega

end JinagaSpec
