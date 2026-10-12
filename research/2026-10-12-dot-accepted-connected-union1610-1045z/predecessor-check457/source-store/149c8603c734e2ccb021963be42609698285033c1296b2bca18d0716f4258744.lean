import G4IndependentRoutingBridge
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ENNReal.BigOperators

/-!
# All-finite-root first-merger clock bridge

Dedicated Sol6.1 source-model contribution. One independent unit-rate
exponential clock is drawn for every unordered pair of current LIVE roots.
No first merger during an arm means every pair clock exceeds its duration.
This product-measure event is proved to have the choose(n,2) survival law.
Later merger/reset dynamics and graph-to-full-process interpretation remain
separate; this theorem does not assert a recognition cutoff.
-/

namespace GProgram.G4.PairClocks

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

abbrev LivePair (n : Nat) := { s : Finset (Fin n) // s.card = 2 }

theorem livePair_card (n : Nat) : Fintype.card (LivePair n) = n.choose 2 := by
  simp [LivePair,Fintype.card_finset_len]

local instance unitClock_probability : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)

noncomputable def pairClockMeasure (n : Nat) : Measure (LivePair n → ℝ) :=
  Measure.pi (fun _ : LivePair n => expMeasure (1 : ℝ))

def noFirstMergeEvent (n : Nat) (duration : ℝ) : Set (LivePair n → ℝ) :=
  Set.univ.pi (fun _ => Set.Ioi duration)

theorem noFirstMergeEvent_iff {n : Nat} {duration : ℝ} (clock : LivePair n → ℝ) :
    clock ∈ noFirstMergeEvent n duration ↔ ∀ pair, duration < clock pair := by
  simp [noFirstMergeEvent,Set.mem_pi]

theorem unitClock_tail_real {duration : ℝ} (ht : 0 ≤ duration) :
    (expMeasure (1 : ℝ)).real (Set.Ioi duration) = Real.exp (-duration) := by
  rw [← Set.compl_Iic,probReal_compl_eq_one_sub measurableSet_Iic,
    ← cdf_eq_real,cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1),if_pos ht]
  simp

theorem all_root_no_first_merge {duration : ℝ} (n : Nat) (ht : 0 ≤ duration) :
    (pairClockMeasure n (noFirstMergeEvent n duration)).toReal =
      (Real.exp (-duration))^(n.choose 2) := by
  rw [pairClockMeasure,noFirstMergeEvent,Measure.pi_pi,ENNReal.toReal_prod]
  change (∏ _ : LivePair n, (expMeasure (1 : ℝ)).real (Set.Ioi duration)) = _
  simp only [unitClock_tail_real ht,Finset.prod_const,Finset.card_univ,livePair_card]

theorem product_clock_eq_holding_model {duration : ℝ} (n : Nat) (ht : 0 ≤ duration) :
    (pairClockMeasure n (noFirstMergeEvent n duration)).toReal =
      GProgram.G4.IndependentRouting.firstHoldingKernel n duration := by
  rw [all_root_no_first_merge n ht,
    GProgram.G4.IndependentRouting.firstHoldingKernel_eq_power ht]

/-- Private independent arms use an actual product measure, not an assumed
product-of-probabilities conclusion. This remains a first-merger primitive. -/
theorem private_arms_no_first_merge {t0 t1 : ℝ} (k0 k1 : Nat)
    (ht0 : 0 ≤ t0) (ht1 : 0 ≤ t1) :
    (((pairClockMeasure k0).prod (pairClockMeasure k1))
      (noFirstMergeEvent k0 t0 ×ˢ noFirstMergeEvent k1 t1)).toReal =
      GProgram.G4.IndependentRouting.firstHoldingKernel k0 t0 *
      GProgram.G4.IndependentRouting.firstHoldingKernel k1 t1 := by
  letI : IsProbabilityMeasure (pairClockMeasure k0) := by
    unfold pairClockMeasure
    infer_instance
  letI : IsProbabilityMeasure (pairClockMeasure k1) := by
    unfold pairClockMeasure
    infer_instance
  have hh := Measure.prod_prod (μ := pairClockMeasure k0) (ν := pairClockMeasure k1)
    (noFirstMergeEvent k0 t0) (noFirstMergeEvent k1 t1)
  rw [hh,ENNReal.toReal_mul,
    product_clock_eq_holding_model k0 ht0,product_clock_eq_holding_model k1 ht1]

#print axioms private_arms_no_first_merge
#print axioms livePair_card
#print axioms all_root_no_first_merge
#print axioms product_clock_eq_holding_model

end GProgram.G4.PairClocks
