import CappedMinorBranchCross
import GridMinorAssembly
import SeparateCrossCoordinates

namespace ResearchCommons.GridMinorObstruction
open PopulationCounting CappedActualBags CappedConnectedBags CappedMinorBranchCross
open GridMinorAssembly CommonConnectedCut SeparateCrossCoordinates

/-- The natural ordered balanced capped host cannot contain a genuine large
square grid minor, even though shared unconstrained routing is possible. -/
theorem no_large_grid_minor {k : Nat} (p : InfiniteLabeledPopulation k k)
    (n : Nat) (large : k * fullRootCount p + 1 < n)
    (B : Nat → Nat → List Nat)
    (inhabited : ∀ i j, i < n → j < n → ∃ u, u ∈ B i j)
    (conn : ∀ i j, i < n → j < n → Connected (Adj p) (B i j))
    (row : ∀ i j, i < n → j+1 < n → Linking (Adj p) (B i j) (B i (j+1)))
    (col : ∀ i j, i+1 < n → j < n → Linking (Adj p) (B i j) (B (i+1) j))
    (disjoint : ∀ x y : Nat × Nat, x.1 < n ∧ x.2 < n → y.1 < n ∧ y.2 < n →
      ∀ u, u ∈ B x.1 x.2 → u ∈ B y.1 y.2 → x = y) :
    False :=
  no_large_connected_crosses p n large B inhabited
    (fun x y hx hy => disjoint x y ((mem_cells n x).mp hx) ((mem_cells n y).mp hy))
    (fun i j hi hj => branch_cross_connected (fun _ _ h => h.symm) n B conn row col
      i j hi hj (inhabited i j hi hj))

/-- Standalone common-bag counting with no joint cell assignment. It suffices
for one of the two covered sides to separate bag vertices. -/
theorem no_large_separated_cover {k : Nat} (p : InfiniteLabeledPopulation k k)
    (n cut : Nat) (large : k * fullRootCount p + 1 < n)
    (inc : Nat → Nat → Prop)
    (unq : ∀ v ∈ bagVertices p cut, ∀ i j, i < n → j < n → inc v i → inc v j → i = j)
    (cover : ∀ i, i < n → ∃ v ∈ bagVertices p cut, inc v i) : False :=
  (Nat.not_lt_of_ge (Nat.le_trans
    (width_from_one_separated_cover n (bagVertices p cut) inc unq cover) (bag_width p cut))) large

#print axioms no_large_grid_minor
#print axioms no_large_separated_cover
end ResearchCommons.GridMinorObstruction
