import GridMinorCross
import CommonConnectedCut
import BranchBagProjection

namespace ResearchCommons.GridMinorAssembly
open PopulationCounting CappedActualBags CappedConnectedBags
open BranchBagProjection CommonConnectedCut

def cells (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i => (List.range n).map fun j => (i,j)

theorem mem_cells (n : Nat) (x : Nat × Nat) :
    x ∈ cells n ↔ x.1 < n ∧ x.2 < n := by
  constructor
  · intro h
    obtain ⟨i,hi,hs⟩ := List.mem_flatMap.mp h
    obtain ⟨j,hj,e⟩ := List.mem_map.mp hs
    rw [← e]
    exact ⟨List.mem_range.mp hi,List.mem_range.mp hj⟩
  · intro h
    exact List.mem_flatMap.mpr
      ⟨x.1,List.mem_range.mpr h.1,List.mem_map.mpr ⟨x.2,List.mem_range.mpr h.2,rfl⟩⟩

def cross (n : Nat) (B : Nat → Nat → List Nat) (i j : Nat) : List Nat :=
  (List.range n).flatMap (B i) ++ (List.range n).flatMap (fun r => B r j)

theorem in_row (n : Nat) (B : Nat → Nat → List Nat) {i j c u : Nat}
    (hc : c < n) (hu : u ∈ B i c) : u ∈ cross n B i j :=
  List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨c,List.mem_range.mpr hc,hu⟩))

theorem in_col (n : Nat) (B : Nat → Nat → List Nat) {i j r u : Nat}
    (hr : r < n) (hu : u ∈ B r j) : u ∈ cross n B i j :=
  List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨r,List.mem_range.mpr hr,hu⟩))

/-- Width obstruction factored at the connected lifted-cross interface. -/
theorem no_large_connected_crosses {k : Nat} (p : InfiniteLabeledPopulation k k)
    (n : Nat) (large : k * fullRootCount p + 1 < n) (B : Nat → Nat → List Nat)
    (inhabited : ∀ i j, i < n → j < n → ∃ u, u ∈ B i j)
    (disjoint : ∀ x y : Nat × Nat, x ∈ cells n → y ∈ cells n →
      ∀ u, u ∈ B x.1 x.2 → u ∈ B y.1 y.2 → x = y)
    (conn : ∀ i j, i < n → j < n → GridMinorCross.Connected (Adj p) (cross n B i j)) :
    False := by
  classical
  obtain ⟨cut,hcut⟩ := connected_common p (cells n) (fun x => cross n B x.1 x.2)
    (fun x hx => conn x.1 x.2 ((mem_cells n x).mp hx).1 ((mem_cells n x).mp hx).2) (by
      intro x hx y hy
      obtain ⟨u,hu⟩ := inhabited x.1 y.2 ((mem_cells n x).mp hx).1 ((mem_cells n y).mp hy).2
      exact ⟨u,in_row n B ((mem_cells n y).mp hy).2 hu,
        in_col n B ((mem_cells n x).mp hx).1 hu⟩)
  let cellOf (u : Nat) : Option (Nat × Nat) :=
    if h : ∃ x ∈ cells n, u ∈ B x.1 x.2 then some (Classical.choose h) else none
  have pick (x : Nat × Nat) (hx : x ∈ cells n) (u : Nat) (hu : u ∈ B x.1 x.2) :
      cellOf u = some x := by
    have h : ∃ y ∈ cells n, u ∈ B y.1 y.2 := ⟨x,hx,hu⟩
    have spec := Classical.choose_spec h
    simp only [cellOf,dif_pos h,disjoint _ _ spec.1 hx _ spec.2 hu]
  have width := width_from_branch_hits n (bagVertices p cut) cellOf (by
    intro i j hi hj
    obtain ⟨u,hu,hbag⟩ := hcut (i,j) ((mem_cells n (i,j)).mpr ⟨hi,hj⟩)
    rcases List.mem_append.mp hu with h | h
    · obtain ⟨c,hc,hmem⟩ := List.mem_flatMap.mp h
      exact ⟨u,hbag,(i,c),pick (i,c) ((mem_cells n (i,c)).mpr ⟨hi,List.mem_range.mp hc⟩) u hmem,Or.inl rfl⟩
    · obtain ⟨r,hr,hmem⟩ := List.mem_flatMap.mp h
      exact ⟨u,hbag,(r,j),pick (r,j) ((mem_cells n (r,j)).mpr ⟨List.mem_range.mp hr,hj⟩) u hmem,Or.inr rfl⟩)
  exact (Nat.not_lt_of_ge (Nat.le_trans width (bag_width p cut))) large

#print axioms no_large_connected_crosses
end ResearchCommons.GridMinorAssembly
