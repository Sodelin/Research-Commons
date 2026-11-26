import GridMinorObstruction
import EfficiencyGridMinorEnd

namespace ResearchCommons.GridMinorRouteParity
open PopulationCounting CappedConnectedBags CappedMinorBranchCross

/-- Display a single contract consumed by both independently checked endpoints. -/
def Contract {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) : Prop :=
  k * fullRootCount p + 1 < n →
  ∀ B : Nat → Nat → List Nat,
    (∀ i j, i < n → j < n → ∃ u, u ∈ B i j) →
    (∀ i j, i < n → j < n → Connected (Adj p) (B i j)) →
    (∀ i j, i < n → j+1 < n → Linking (Adj p) (B i j) (B i (j+1))) →
    (∀ i j, i+1 < n → j < n → Linking (Adj p) (B i j) (B (i+1) j)) →
    (∀ x y : Nat × Nat, x.1 < n ∧ x.2 < n → y.1 < n ∧ y.2 < n →
      ∀ u, u ∈ B x.1 x.2 → u ∈ B y.1 y.2 → x = y) → False

theorem reuse {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) : Contract p n :=
  GridMinorObstruction.no_large_grid_minor p n

theorem direct {k : Nat} (p : InfiniteLabeledPopulation k k) (n : Nat) : Contract p n := by
  intro large B inhab conn row col disjoint
  exact EfficiencyGridMinorEnd.no_large_grid_minor p n large B conn row col inhab
    (fun a b c d v hv hw => by
      have e := disjoint (a.val,b.val) (c.val,d.val) ⟨a.isLt,b.isLt⟩ ⟨c.isLt,d.isLt⟩ v hv hw
      exact ⟨Fin.ext (congrArg Prod.fst e),Fin.ext (congrArg Prod.snd e)⟩)

#print axioms reuse
#print axioms direct
end ResearchCommons.GridMinorRouteParity
