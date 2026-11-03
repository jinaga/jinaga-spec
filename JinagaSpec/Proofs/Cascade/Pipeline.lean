import JinagaSpec.Proofs.Cascade.GroupBy
import JinagaSpec.Proofs.Cascade.Filter

/-!
# Cascade: a whole pipeline

The pipeline that reproduced jinaga/jinaga-cascade-core#29 without `enrich`:
group rows by item and total them, put each item in a tier by its total, then
total each tier. An item moves to another tier when its total crosses the
threshold, so its tier is a grouping value that changes.

```
createPipeline()
  .groupBy(['item'], 'items').sum('items', 'v', 'total')
  .defineProperty('tier', r => r.total > 50 ? 'hi' : 'lo', ['total'])
  .groupBy(['tier'], 'groups').sum('groups', 'total', 'tierTotal')
```

`tiers_correct` follows from the steps' theorems by `andThen_correct`, with no
reasoning about the pipeline itself. `tiers_order_independent` is the property
the issue's tests check by permutation.
-/
namespace JinagaSpec.Cascade

/-- An item's tier, from its total. -/
def tierOf (ps : Props) : Option Val :=
  if (ps "total").getD 0 > 50 then some 1 else some 0

def sumOf (p : String) : Props → Int := fun ps => (ps p).getD 0

def tiersF : Tree → Tree :=
  aggregate.F ["groups"] "tierTotal" (fun _ => true) (sumOf "total") ∘
  groupBy.F ["tier"] "groups" ∘
  defineProperty.F [] "tier" tierOf ∘
  aggregate.F ["items"] "total" (fun _ => true) (sumOf "v") ∘
  groupBy.F ["item"] "items"

def tiers : Step :=
  ((((groupBy ["item"] "items").andThen
    (aggregateStep ["items"] "total" (fun _ => true) (sumOf "v")) (groupBy.F ["item"] "items")).andThen
    (defineProperty [] "tier" tierOf ["total"])
      (aggregate.F ["items"] "total" (fun _ => true) (sumOf "v") ∘ groupBy.F ["item"] "items")).andThen
    (groupBy ["tier"] "groups")
      (defineProperty.F [] "tier" tierOf ∘ aggregate.F ["items"] "total" (fun _ => true) (sumOf "v") ∘
        groupBy.F ["item"] "items")).andThen
    (aggregateStep ["groups"] "tierTotal" (fun _ => true) (sumOf "total"))
      (groupBy.F ["tier"] "groups" ∘ defineProperty.F [] "tier" tierOf ∘
        aggregate.F ["items"] "total" (fun _ => true) (sumOf "v") ∘ groupBy.F ["item"] "items")

theorem tiers_denotation : Denotation tiersF :=
  (((groupBy_denotation _ _).comp (aggregate_denotation _ _ _ _)).comp
    (defineProperty_denotation _ _ _)).comp (groupBy_denotation _ _) |>.comp
    (aggregate_denotation _ _ _ _)

/-- **`tiers_correct`.** The whole pipeline is correct. -/
theorem tiers_correct : Correct tiers tiersF := by
  have hdef : ∀ ps p v, p ∉ ["total"] → tierOf (ps.set p v) = tierOf ps := by
    intro ps p v hp
    have : p ≠ "total" := by simpa using hp
    simp [tierOf, Props.set, Ne.symm this]
  exact andThen_correct
    (andThen_correct
      (andThen_correct
        (andThen_correct (groupBy_correct _ _) (groupBy_denotation _ _)
          (aggregate_correct _ (by simp) _ _ _) (aggregate_denotation _ _ _ _))
        ((groupBy_denotation _ _).comp (aggregate_denotation _ _ _ _))
        (defineProperty_correct _ _ _ _ (by decide) hdef) (defineProperty_denotation _ _ _))
      (((groupBy_denotation _ _).comp (aggregate_denotation _ _ _ _)).comp
        (defineProperty_denotation _ _ _))
      (groupBy_correct _ _) (groupBy_denotation _ _))
    ((((groupBy_denotation _ _).comp (aggregate_denotation _ _ _ _)).comp
      (defineProperty_denotation _ _ _)).comp (groupBy_denotation _ _))
    (aggregate_correct _ (by simp) _ _ _) (aggregate_denotation _ _ _ _)

/-- **`tiers_order_independent`.** Rows that arrive in any order produce the same
tiers and totals. -/
theorem tiers_order_independent {T T₁ T₂ : Tree} {es₁ es₂ : List Event} (hT : T.WF)
    (h₁ : T.applyAll es₁ = some T₁) (h₂ : T.applyAll es₂ = some T₂) (h : T₁.Equiv T₂) :
    ∃ U₁ U₂, (tiersF T).applyAll (run tiers T es₁) = some U₁ ∧
      (tiersF T).applyAll (run tiers T es₂) = some U₂ ∧ U₁.Equiv U₂ :=
  order_independent tiers_correct tiers_denotation hT h₁ h₂ h

end JinagaSpec.Cascade
