import E8ScheduledHypergraphCorrectness
import Mathlib.Algebra.BigOperators.Ring.List

/-!
Weighted-derivation interpretation of the once-for-all scheduled interpreter.
Lists retain deduction occurrences and multiplicities. Each child contributes
its full derivation-choice list; their Cartesian product forms all combinations.
In an exact semiring the resulting sum equals the finite recurrence expansion.
A topologically indexed provider therefore has a single parametric chart/sum
correctness theorem, including the observer-frame interface. This does not
assert that derivation multiplicities equal RNA structure multiplicities or
that floating operations refine exact semiring arithmetic.
-/
namespace E8ScheduledDerivationSum
open E8ScheduledObserverFrame E8ScheduledHypergraphCorrectness

variable {Item Deduction Value : Type*} [Semiring Value] [DecidableEq Value]
    (children : Deduction → List Item) (semantic : SemanticView Item Deduction Value)

private theorem sum_flatMap (items : List Item) (f : Item → List Value) :
    (items.flatMap f).sum = (items.map (fun item => (f item).sum)).sum := by
  induction items with
  | nil => simp
  | cons item items ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

/-- Cartesian products of child derivation weights; no deduplication. -/
def childProducts : List (List Value) → List Value
  | [] => [1]
  | first :: pending => first.flatMap (fun value => (childProducts pending).map (fun rest => value * rest))

theorem childProducts_sum (childLists : List (List Value)) :
    (childProducts childLists).sum = (childLists.map List.sum).prod := by
  induction childLists with
  | nil => simp [childProducts]
  | cons first pending ih =>
    rw [childProducts, sum_flatMap]
    have hmap : (first.map (fun value => ((childProducts pending).map (fun rest => value * rest)).sum)).sum =
        (first.map (fun value => value * (childProducts pending).sum)).sum := by
      congr 1
      apply List.map_congr_left
      intro value _
      simpa using List.sum_map_mul_left (childProducts pending) id value
    rw [hmap]
    have hmul : (first.map (fun value => value * (childProducts pending).sum)).sum =
        first.sum * (childProducts pending).sum := by
      simpa using List.sum_map_mul_right first id (childProducts pending).sum
    rw [hmul, ih]
    rfl

private theorem ordered_fold_product (items : List Item) (chart : Item → Value) (initial : Value) :
    items.foldl (fun total item => total * chart item) initial = initial * (items.map chart).prod := by
  induction items generalizing initial with
  | nil => simp
  | cons item items ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih]
    exact mul_assoc _ _ _

theorem orderedContribution_as_product (chart : Item → Value) (d : Deduction) :
    orderedContribution children semantic chart d =
      semantic.localWeight d * ((children d).map chart).prod :=
  ordered_fold_product (children d) chart (semantic.localWeight d)

def effectiveContribution (chart : Item → Value) (d : Deduction) : Value :=
  if semantic.allowed d then
    if semantic.localWeight d = 0 then 0 else orderedContribution children semantic chart d
  else 0

theorem pureScan_as_sum (chart : Item → Value) (pending : List Deduction) (initial : Value) :
    pureScan children semantic chart pending initial =
      initial + (pending.map (effectiveContribution children semantic chart)).sum := by
  induction pending generalizing initial with
  | nil => simp [pureScan]
  | cons d pending ih =>
    by_cases ha : semantic.allowed d = true
    · by_cases hz : semantic.localWeight d = 0
      · simpa [pureScan, List.foldl_cons, effectiveContribution, ha, hz] using ih initial
      · simpa only [pureScan, List.foldl_cons, List.map_cons, List.sum_cons, effectiveContribution,
          ha, hz, if_true, if_false, add_assoc] using
          ih (initial + orderedContribution children semantic chart d)
    · have haf : semantic.allowed d = false := Bool.eq_false_iff.mpr ha
      simpa [pureScan, List.foldl_cons, effectiveContribution, haf] using ih initial

def derivationWeights : ℕ → Item → List Value
  | 0, _ => []
  | depth + 1, parent =>
    (semantic.provider parent).flatMap fun d =>
      if semantic.allowed d then
        if semantic.localWeight d = 0 then [] else
          (childProducts ((children d).map (derivationWeights depth))).map
            (fun rest => semantic.localWeight d * rest)
      else []

theorem derivation_sum_matches_expansion (depth : ℕ) (parent : Item) :
    (derivationWeights children semantic depth parent).sum = finiteExpansion children semantic depth parent := by
  induction depth generalizing parent with
  | zero => rfl
  | succ depth ih =>
    rw [derivationWeights, sum_flatMap]
    change _ = pureScan children semantic (finiteExpansion children semantic depth)
      (semantic.provider parent) 0
    rw [pureScan_as_sum, zero_add]
    congr 1
    apply List.map_congr_left
    intro d _
    by_cases ha : semantic.allowed d = true
    · by_cases hz : semantic.localWeight d = 0
      · simp [effectiveContribution, ha, hz]
      · simp only [effectiveContribution, ha, hz, if_true, if_false]
        rw [orderedContribution_as_product]
        have hmul : ((childProducts ((children d).map (derivationWeights children semantic depth))).map
            (fun rest => semantic.localWeight d * rest)).sum =
            semantic.localWeight d * (childProducts ((children d).map (derivationWeights children semantic depth))).sum := by
          simpa using List.sum_map_mul_left
            (childProducts ((children d).map (derivationWeights children semantic depth))) id (semantic.localWeight d)
        rw [hmul, childProducts_sum, List.map_map]
        congr 1
        congr 1
        apply List.map_congr_left
        intro child _
        exact ih child
    · have haf : semantic.allowed d = false := Bool.eq_false_iff.mpr ha
      simp [effectiveContribution, haf]

section Indexed
variable {n : ℕ} (children : Deduction → List (Fin n))
    (semantic : SemanticView (Fin n) Deduction Value)

theorem scheduled_chart_derivation_sum (hearlier : EarlierChildren children semantic) (parent : Fin n) :
    pureRun children semantic (List.finRange n) (fun _ => 0) parent =
      (derivationWeights children semantic n parent).sum := by
  rw [scheduled_chart_eq_complete_expansion children semantic hearlier,
    derivation_sum_matches_expansion children semantic n parent]

variable {Aux : Type*} (view : Aux → SemanticView (Fin n) Deduction Value)
    (observe : Aux → CandidateEvent (Fin n) Deduction Value → Aux)

theorem observed_scheduled_derivation_sum (hframe : ObserverFrame view observe) (aux : Aux)
    (hearlier : EarlierChildren children (view aux)) (parent : Fin n) :
    (sourceRun children view observe (List.finRange n) aux (fun _ => 0)).2 parent =
      (derivationWeights children (view aux) n parent).sum := by
  rw [observed_scheduled_chart_correct children view observe hframe aux hearlier,
    derivation_sum_matches_expansion children (view aux) n parent]

end Indexed
end E8ScheduledDerivationSum
#print axioms E8ScheduledDerivationSum.childProducts_sum
#print axioms E8ScheduledDerivationSum.orderedContribution_as_product
#print axioms E8ScheduledDerivationSum.pureScan_as_sum
#print axioms E8ScheduledDerivationSum.derivation_sum_matches_expansion
#print axioms E8ScheduledDerivationSum.scheduled_chart_derivation_sum
#print axioms E8ScheduledDerivationSum.observed_scheduled_derivation_sum
