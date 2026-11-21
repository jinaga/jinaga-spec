import JinagaSpec.Proofs.Children
import JinagaSpec.Proofs.Maintain
import JinagaSpec.Proofs.WellFormedCheck
import JinagaSpec.FeedCases

/-!
# No feeds defer a contested exclusion exactly

`feeds_defer` withholds an entity's details while no witness of its exclusion
has a cancelling fact. It does not withhold them while every witness stands.
This file proves that no feeds can: any feeds at all, meeting consistency and
append-only, deliver the details of an entity that is excluded, with its one
witness standing (`exact_deferral_impossible`).

The specification is `contested` (`FeedCases.lean`): an event's names, unless
its delete stands; a delete stands unless restored, a restore unless revoked,
a revoke unless unrevoked. The graphs have one event, one delete, one restore,
`N` revokes of the restore, and an unrevoke of each revoke in `U`.

* With every revoke unrevoked, the restore stands, the delete is cancelled,
  and the event's name is a result. Consistency forces some feed to deliver
  the name: a replica missing it would read nothing.
* Take away any one unrevoke `i`, and the restore is revoked, the delete
  stands, and the event is excluded. Exact deferral would withhold the name.
  But the unrevoke arrives as a fresh batch, so append-only says the tuple
  delivering the name on the full graph was a tuple before it arrived, unless
  it binds the unrevoke.
* So the tuple binds every one of the `N` unrevokes. A feed's tuple binds one
  fact per match, and `N` is more than any feed has.

The requirements are stated for any list of feeds, as `feeds_cover`'s and
`feed_antitone`'s conclusions (`Consistent`, `AppendOnly`). A feed may be any
specification, with any nesting of conditions: the argument counts only the
facts a tuple binds. `buildFeeds` meets both (`buildFeeds_consistent`,
`buildFeeds_appendOnly`), on `contested` too (`contested_feasible`), so it is
deferral that cannot be made exact.
-/
namespace JinagaSpec

/-! ## The requirements, for any feeds -/

/-- **Consistency**, for the feeds `Fs` of `s`: `feeds_cover`'s conclusion. A
replica that holds the givens and every fact the feeds deliver reads what the
replicator reads. -/
def Consistent (s : Specification) (Fs : List Specification) : Prop :=
  ∀ (g : Graph) (B : List Fact) (env : Env), Fresh g B → Settled B env → (∀ l ∈ s.given, g.has env l = true) →
    (∀ id ∈ deliver Fs (g ++ B) env, Outside B id) → ∀ r, s.Reads g env r ↔ s.Reads (g ++ B) env r

/-- **Append-only**, for a feed: `feed_antitone`'s conclusion. A tuple found
after a fresh batch, none of whose facts is in the batch, was found before, so
a tuple never appears behind a bookmark. -/
def AppendOnly (f : Specification) : Prop :=
  ∀ (g : Graph) (B : List Fact) (env : Env), Fresh g B → Settled B env →
    ∀ t ∈ f.tuples (g ++ B) env, (∀ id ∈ t, Outside B id) → t ∈ f.tuples g env

theorem buildFeeds_consistent {s : Specification} (hwf : ∀ d ∈ s.descendants, WellFormed d)
    (hd : ∀ d ∈ s.descendants, DistinctLabels d) (hr : ∀ d ∈ s.descendants, RootedMatches d.matchList) :
    Consistent s (buildFeeds s) :=
  fun _ _ _ hf henv hgiv hdel => feeds_cover hwf hd hr hf henv hgiv hdel

theorem buildFeeds_appendOnly {s : Specification} (hwf : ∀ d ∈ s.descendants, WellFormed d)
    (hd : ∀ d ∈ s.descendants, DistinctLabels d) : ∀ f ∈ buildFeeds s, AppendOnly f :=
  fun f hf _ _ _ hfr henv _ ht hout =>
    feed_antitone hfr (buildFeeds_feedShape s f hf) (buildFeeds_nodup hwf hd f hf) henv ht hout

/-! ## Evaluating one role -/

theorem factOf_of_mem {g : Graph} (hu : g.IdsUnique) {f : Fact} (hf : f ∈ g) : g.factOf f.id = some f := by
  unfold Graph.factOf
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome (p := fun x : Fact => x.id == f.id) |>.mpr ⟨f, hf, beq_self_eq_true _⟩)
  rw [ha, hu a (List.mem_of_find?_eq_some ha) f hf (by simpa using List.find?_some ha)]

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

theorem mem_deliver {Fs : List Specification} {G : Graph} {env : Env} {id : FactId} :
    id ∈ deliver Fs G env ↔ ∃ f ∈ Fs, ∃ t ∈ f.tuples G env, id ∈ t := by
  simp [deliver, List.mem_flatMap, List.mem_flatten]

/-- A tuple binds one fact for each match. -/
theorem length_tuple {f : Specification} {G : Graph} {env : Env} {t : List FactId} (h : t ∈ f.tuples G env) :
    t.length ≤ f.matchList.length := by
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp h
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

theorem length_le_flatMap {α β : Type} (g : α → List β) : ∀ {l : List α} {a : α}, a ∈ l → (g a).length ≤ (l.flatMap g).length
  | b :: l, a, h => by
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := length_le_flatMap g h; omega

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
  rcases mem_graph.mp hf with h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hT f h)))))

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
  simp [fact, Projection.children, Projection.labels]
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
consistent and append-only deliver, on some graph, the name of an event that
is excluded, whose one delete stands.

So `feeds_defer` cannot be strengthened to "withheld while every witness
stands", for any feeds, let alone to "withheld while excluded". The graph is
`restore-revoked-and-unrevoked`'s, with more revokes than the feeds have
matches. -/
theorem exact_deferral_impossible (Fs : List Specification) (hc : Consistent contested Fs)
    (ha : ∀ f ∈ Fs, AppendOnly f) :
    ∃ G : Graph, (∀ r, ¬ contested.Reads G env0 r) ∧ (G.filter (·.type == "Delete")).length = 1 ∧
      name.id ∈ deliver Fs G env0 := by
  let N := (Fs.flatMap (·.matchList)).length + 1
  have hfull : name.id ∈ deliver Fs (graph N (List.range N) ++ [name]) env0 := by
    refine Classical.byContradiction fun hn => ?_
    have h := hc (graph N (List.range N)) [name] env0 fresh_name (settled (by simp [name]))
      (by simpa using given_held (N := N) (U := List.range N) (T := []) (by simp))
      (fun id hid b hb => by rw [List.mem_singleton.mp hb]; exact fun h => hn (h ▸ hid)) (.mk [some name.id] [])
    have h0 := reads_contested (N := N) (U := List.range N) (T := []) (by simp) (.mk [some name.id] [])
    rw [List.append_nil] at h0
    rw [reads_contested (by simp)] at h
    simp at h0 h
    exact h0 h
  obtain ⟨f, hf, t, ht, hnt⟩ := mem_deliver.mp hfull
  refine Classical.byContradiction fun hno => ?_
  have hT : ∀ f ∈ [name], f = name := by simp
  have hz : ∀ i < N, (unrevoke i).id ∈ t := by
    intro i hi
    refine Classical.byContradiction fun hz => hno ?_
    have hU : i ∉ (List.range N).erase i := fun h => (List.nodup_range.mem_erase_iff.mp h).1 rfl
    have hmem : ∀ x, x ∈ graph N (List.range N) ++ [name] ↔
        x ∈ graph N ((List.range N).erase i) ++ [name] ++ [unrevoke i] := by
      intro x
      simp only [graph, List.mem_append, List.mem_map, List.mem_singleton, List.nodup_range.mem_erase_iff,
        List.mem_range]
      by_cases hx : x = unrevoke i
      · subst hx; simp only [or_true, iff_true]; exact Or.inl (Or.inr ⟨i, hi, rfl⟩)
      · simp only [hx, or_false]
        constructor
        · rintro ((h | ⟨a, ha, rfl⟩) | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr ⟨a, ⟨fun h => hx (h ▸ rfl), ha⟩, rfl⟩)
          · exact Or.inr h
        · rintro ((h | ⟨a, ⟨-, ha⟩, rfl⟩) | h)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr ⟨a, ha, rfl⟩)
          · exact Or.inr h
    have ht' := ha f hf _ [unrevoke i] env0 (fresh_unrevoke hT hU) (settled (by simp [unrevoke]))
      t ((tuples_congr hmem (idsUnique hT) f env0 t).mp ht)
      (fun id hid b hb => by rw [List.mem_singleton.mp hb]; exact fun h => hz (h ▸ hid))
    refine ⟨_, fun r hr => hU (((reads_contested hT r).mp hr).1 i hi), ?_, mem_deliver.mpr ⟨f, hf, t, ht', hnt⟩⟩
    simp [graph, List.filter_append, List.filter_map, Function.comp_def, tenant, event, delete, restore, name,
      revoke, unrevoke]
  have hN := List.Nodup.length_le_of_subset (l₁ := (List.range N).map fun i => (unrevoke i).id)
    (List.Pairwise.map _ (fun a b hab h => hab (by simp [unrevoke] at h; omega)) List.nodup_range)
    (fun x hx => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact hz i (List.mem_range.mp hi))
  have := length_tuple ht
  have := length_le_flatMap (·.matchList) hf
  simp at hN
  omega

end JinagaSpec
