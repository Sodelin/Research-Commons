import CappedActualBags
open PopulationCounting ResearchCommons.CappedActualBags
example {k : Nat} (p : InfiniteLabeledPopulation k k) (cut : Nat) :
    (bagVertices p cut).length ≤ k * fullRootCount p + 1 :=
  bag_width p cut
example {k d : Nat} (p : InfiniteLabeledPopulation k d) (u : Nat) :
    ∃ last, u ≤ last ∧ ∀ t, u ∈ bagVertices p t ↔ u ≤ t ∧ t ≤ last :=
  vertex_bag_interval p u
