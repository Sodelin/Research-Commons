import SourceLabelledForest
import G5FairSelectorMoments
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Actual finite original-site fair coin law and pair selector moments

Contributor: dot, 2026-10-02. The finite law uses the already constructed
source-forest product weights on original coin sites, including current-live
token sites for an independent pulse. Marginalizing all other original sites
gives an exact fair two-coordinate law when the retained sites are distinct.
This is an unconditional law, with no no-merger posterior refitting. A whole
continuous source trace, component-route compiler and safe-past disjointness
remain separate source obligations.
-/
namespace GProgram.G5.OriginalCoinLaw
open GProgram.SourceForest
open GProgram.G5.QuartetKernel
open scoped BigOperators ENNReal NNReal
variable {Site α : Type*} [Fintype Site] [DecidableEq Site]

@[simp] theorem bitWeight_fair (b : Bool) : bitWeight (1 / 2) b = (1 / 2 : ℚ) := by
  cases b <;> norm_num [bitWeight]

/-- Actual joint mass under the original finite product-weight source law. -/
noncomputable def jointBitMass (u v : Site) (a b : Bool) : ℚ := by
  classical
  exact ∑ coin : Site → Bool, independentWeight (1 / 2) coin *
    if coin u = a ∧ coin v = b then 1 else 0

/-- Distinct actual source coin sites have fair independent marginals after
all other site coins are summed out. -/
theorem jointBitMass_eq_quarter {u v : Site} (hne : u ≠ v) (a b : Bool) :
    jointBitMass u v a b = 1 / 4 := by
  classical
  let wanted : Site → Bool := fun s => if s = u then a else b
  have hc : jointBitMass u v a b = coinCylinderMass (1 / 2) {u,v} wanted := by
    simp only [jointBitMass, coinCylinderMass]
    apply Finset.sum_congr rfl
    intro coin hcoin
    simp [wanted, hne, hne.symm]
  rw [hc, coinCylinderMass_eq_retained_product]
  rw [Finset.prod_pair hne]
  simp only [bitWeight_fair]
  norm_num

/-- Every two-coordinate readout is the actual four equally weighted selector
readouts, not a chosen marginal probability interface. -/
theorem fair_two_site_expectation {u v : Site} (hne : u ≠ v)
    (readout : Bool → Bool → ℚ) :
    (∑ coin : Site → Bool, independentWeight (1 / 2) coin *
      readout (coin u) (coin v)) =
      (readout false false + readout false true +
        readout true false + readout true true) / 4 := by
  classical
  have hp : ∀ coin : Site → Bool,
      independentWeight (1 / 2) coin * readout (coin u) (coin v) =
        (independentWeight (1 / 2) coin *
          (if coin u = false ∧ coin v = false then 1 else 0)) * readout false false +
        (independentWeight (1 / 2) coin *
          (if coin u = false ∧ coin v = true then 1 else 0)) * readout false true +
        (independentWeight (1 / 2) coin *
          (if coin u = true ∧ coin v = false then 1 else 0)) * readout true false +
        (independentWeight (1 / 2) coin *
          (if coin u = true ∧ coin v = true then 1 else 0)) * readout true true := by
    intro coin
    cases hu : coin u <;> cases hv : coin v <;> simp [hu,hv]
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul]
  change jointBitMass u v false false * readout false false +
      jointBitMass u v false true * readout false true +
      jointBitMass u v true false * readout true false +
      jointBitMass u v true true * readout true true = _
  simp_rw [jointBitMass_eq_quarter hne]
  ring

/-- Standard selector indexing of the two actual source bit values. -/
def binaryPositions (position : Bool → α) : Fin 2 → α :=
  fun i => if i = 0 then position false else position true

/-- Actual unconditional original-site co-occupancy mass equals the raw
selector pair count divided by four. -/
theorem fair_source_meeting_weight [DecidableEq α] {u v : Site} (hne : u ≠ v)
    (p q : Bool → α) :
    (∑ coin : Site → Bool, independentWeight (1 / 2) coin *
      (if p (coin u) = q (coin v) then 1 else 0)) =
      (pairCount (binaryPositions p) (binaryPositions q) : ℚ) / 4 := by
  rw [fair_two_site_expectation hne (fun a b => if p a = q b then 1 else 0)]
  simp only [pairCount, binaryPositions]
  norm_num

#print axioms jointBitMass_eq_quarter
#print axioms fair_two_site_expectation
#print axioms fair_source_meeting_weight
end GProgram.G5.OriginalCoinLaw
