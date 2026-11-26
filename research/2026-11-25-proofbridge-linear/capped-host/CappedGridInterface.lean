import CappedGridCross
import CappedHostIntervals

namespace ResearchCommons.CappedGridInterface
open ResearchCommons.CappedHostIntervals ResearchCommons.CappedGridCross

/-- The finite grid obstruction given a certified assignment of bag intervals
to crosses. The actual graph-to-interval assignment remains a separate input. -/
theorem noSmallBagCover (side : Nat) (bag : Nat → List (Nat × Nat))
    (a : BagInterval) (rest : List BagInterval)
    (width : ∀ b, (bag b).length < side)
    (overlap : ∀ b ∈ a :: rest, ∀ c ∈ a :: rest,
      ∃ i : Nat, b.lo ≤ i ∧ i ≤ b.hi ∧ c.lo ≤ i ∧ i ≤ c.hi)
    (indexedCross : ∀ i j, i < side → j < side →
      ∃ I ∈ a :: rest,
        ∀ t, I.lo ≤ t → t ≤ I.hi → ∃ p ∈ bag t, p.1 = i ∨ p.2 = j) :
    False := by
  obtain ⟨t, ht⟩ := commonBag a rest overlap
  have hits (i j : Nat) (hi : i < side) (hj : j < side) :
      ∃ p ∈ bag t, p.1 = i ∨ p.2 = j := by
    obtain ⟨I, hI, hcross⟩ := indexedCross i j hi hj
    exact hcross t (ht I hI).1 (ht I hI).2
  exact Nat.not_lt_of_ge (crossHittingLowerBound side (bag t) hits) (width t)

end ResearchCommons.CappedGridInterface
#print axioms ResearchCommons.CappedGridInterface.noSmallBagCover
