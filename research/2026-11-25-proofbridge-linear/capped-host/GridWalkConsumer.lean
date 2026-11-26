import CappedGridWalks

open PopulationCounting ResearchCommons.CappedConnectedBags ResearchCommons.CappedGridWalks

example {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (side : Nat) (f : Nat → Nat → Nat)
    (hrow : ∀ r c, r < side → c+1 < side → Adj p (f r c) (f r (c+1)))
    (hcol : ∀ r c, r+1 < side → c < side → Adj p (f r c) (f (r+1) c))
    (i j : Nat) (hi : i < side) (hj : j < side) :
    ∃ l r, l ≤ r ∧ ∀ t, Hits p (imageCross side f i j) t ↔ l ≤ t ∧ t ≤ r :=
  image_cross_hit_interval p side f hrow hcol i j hi hj

-- Without the coordinate bound, the claimed point can lie outside both arms.
theorem off_grid_control :
    (fun r c : Nat => 10*r+c) 0 2 ∉ imageCross 2 (fun r c => 10*r+c) 0 0 := by
  decide

#print axioms off_grid_control
