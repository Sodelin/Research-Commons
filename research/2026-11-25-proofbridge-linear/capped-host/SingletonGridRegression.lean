import GridMinorObstruction
import SingletonGridBranch

namespace ResearchCommons.SingletonGridRegression
open PopulationCounting CappedConnectedBags

/-- The old adjacency-embedding obstruction follows from the new branch-set
obstruction by an explicit singleton witness. This does not invoke the old
`no_large_grid` theorem. -/
theorem embedding_obstruction_via_minor {k : Nat}
    (p : InfiniteLabeledPopulation k k)
    (n : Nat) (large : k * fullRootCount p + 1 < n)
    (f : Nat → Nat → Nat)
    (hrow : ∀ r c, r < n → c+1 < n → Adj p (f r c) (f r (c+1)))
    (hcol : ∀ r c, r+1 < n → c < n → Adj p (f r c) (f (r+1) c))
    (inj : ∀ x y : Nat × Nat, x.1 < n ∧ x.2 < n → y.1 < n ∧ y.2 < n →
      f x.1 x.2 = f y.1 y.2 → x = y) : False :=
  GridMinorObstruction.no_large_grid_minor p n large (SingletonGridBranch.branch f)
    (fun r c _ _ => SingletonGridBranch.nonempty f r c)
    (fun r c _ _ => SingletonGridBranch.connected (Adj p) f r c)
    (fun r c hr hc => SingletonGridBranch.linked (hrow r c hr hc))
    (fun r c hr hc => SingletonGridBranch.linked (hcol r c hr hc))
    (fun _ _ hx hy _ hu hv => SingletonGridBranch.disjoint inj hx hy hu hv)

#print axioms embedding_obstruction_via_minor
end ResearchCommons.SingletonGridRegression
