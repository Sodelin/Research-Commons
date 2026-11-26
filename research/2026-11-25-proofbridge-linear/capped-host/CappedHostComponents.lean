import CappedHostIntervals
import SamuelAlexanderResearch.InfiniteConservation

open PopulationCounting InfiniteConservation ResearchCommons.CappedHostIntervals

/-- Reuse the existing crossing bound in the natural-order model. -/
theorem cappedCrossingReuse {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) :
    crossingCount p n ≤ k * fullRootCount p :=
  crossing_upper p n

/-- Omitting the overlap hypothesis would be unsound. -/
theorem cannotDropOverlap :
    ¬ (∃ n : Nat, ∀ b ∈ [BagInterval.mk 0 0, BagInterval.mk 1 1],
      b.lo ≤ n ∧ n ≤ b.hi) := by
  intro h
  obtain ⟨n, hn⟩ := h
  have a := hn (BagInterval.mk 0 0) (by simp)
  have b := hn (BagInterval.mk 1 1) (by simp)
  change 0 ≤ n ∧ n ≤ 0 at a
  change 1 ≤ n ∧ n ≤ 1 at b
  omega

#print axioms cappedCrossingReuse
#print axioms cannotDropOverlap
