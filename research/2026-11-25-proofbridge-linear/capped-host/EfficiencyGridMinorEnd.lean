import CappedMinorBranchCross
import EfficiencyBranchWidth

namespace ResearchCommons.EfficiencyGridMinorEnd
open PopulationCounting ResearchCommons.CappedConnectedBags
open ResearchCommons.CappedMinorBranchCross ResearchCommons.EfficiencyBranchWidth

/-- Finite disjoint connected branch models of the square grid cannot
exceed the actual balanced host's root budget. -/
theorem no_large_grid_minor {k : Nat} (p : InfiniteLabeledPopulation k k)
    (n : Nat) (large : k * fullRootCount p + 1 < n) (B : Nat → Nat → List Nat)
    (conn : ∀ r c, r < n → c < n → Connected (Adj p) (B r c))
    (row : ∀ r c, r < n → c+1 < n → Linking (Adj p) (B r c) (B r (c+1)))
    (col : ∀ r c, r+1 < n → c < n → Linking (Adj p) (B r c) (B (r+1) c))
    (inhab : ∀ r c, r < n → c < n → ∃ z, z ∈ B r c)
    (disjoint : ∀ a b c d : Fin n, ∀ v,
      v ∈ B a.val b.val → v ∈ B c.val d.val → a = c ∧ b = d) : False :=
  no_large_branch_model_of_raw_hits p large B disjoint
    (common_branch_cross_cut p n (by omega) B conn row col inhab)

end ResearchCommons.EfficiencyGridMinorEnd
#print axioms ResearchCommons.EfficiencyGridMinorEnd.no_large_grid_minor
