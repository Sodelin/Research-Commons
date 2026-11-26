import CappedConnectedBags

namespace ResearchCommons.SingletonGridBranch
open CappedConnectedBags

def branch (f : Nat → Nat → Nat) (r c : Nat) : List Nat := [f r c]

theorem nonempty (f : Nat → Nat → Nat) (r c : Nat) :
    ∃ v, v ∈ branch f r c := ⟨f r c, by simp [branch]⟩

theorem connected (A : Nat → Nat → Prop) (f : Nat → Nat → Nat) (r c : Nat) :
    ∀ u ∈ branch f r c, ∀ v ∈ branch f r c, WalkInside A (branch f r c) u v := by
  intro u hu v hv
  have eq : u = v := (List.mem_singleton.mp hu).trans (List.mem_singleton.mp hv).symm
  subst v
  exact .stay hu

theorem linked {A : Nat → Nat → Prop} {f : Nat → Nat → Nat}
    {r c s t : Nat} (h : A (f r c) (f s t)) :
    ∃ u ∈ branch f r c, ∃ v ∈ branch f s t, A u v :=
  ⟨f r c, by simp [branch], f s t, by simp [branch], h⟩

theorem disjoint {n : Nat} {f : Nat → Nat → Nat}
    (inj : ∀ x y : Nat × Nat, x.1 < n ∧ x.2 < n → y.1 < n ∧ y.2 < n →
      f x.1 x.2 = f y.1 y.2 → x = y)
    {x y : Nat × Nat} {v : Nat}
    (hx : x.1 < n ∧ x.2 < n) (hy : y.1 < n ∧ y.2 < n)
    (mx : v ∈ branch f x.1 x.2) (my : v ∈ branch f y.1 y.2) :
    x = y :=
  inj x y hx hy ((List.mem_singleton.mp mx).symm.trans (List.mem_singleton.mp my))

#print axioms connected
#print axioms disjoint
end ResearchCommons.SingletonGridBranch
