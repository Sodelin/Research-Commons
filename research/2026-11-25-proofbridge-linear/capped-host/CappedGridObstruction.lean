import CappedGridWalks
import CappedHostIntervals
import CappedGridCross

namespace ResearchCommons.CappedGridObstruction
open PopulationCounting ResearchCommons.CappedActualBags ResearchCommons.CappedConnectedBags
open ResearchCommons.CappedGridWalks ResearchCommons.CappedHostIntervals ResearchCommons.CappedGridCross

private def cells (side : Nat) : List (Nat × Nat) :=
  (List.range side).flatMap (fun i => (List.range side).map (fun j => (i,j)))

private theorem cell_mem (side : Nat) (x : Nat × Nat) :
    x ∈ cells side ↔ x.1 < side ∧ x.2 < side := by
  constructor
  · intro h
    obtain ⟨i, hi, hs⟩ := List.mem_flatMap.mp h
    obtain ⟨j,hj,e⟩ := List.mem_map.mp hs
    rw [← e]
    exact ⟨List.mem_range.mp hi, List.mem_range.mp hj⟩
  · intro h
    exact List.mem_flatMap.mpr
      ⟨x.1,List.mem_range.mpr h.1,List.mem_map.mpr ⟨x.2,List.mem_range.mpr h.2,rfl⟩⟩

/-- The one common cut meeting every embedded row-and-column cross. -/
theorem common_grid_cut {k d : Nat} (p : InfiniteLabeledPopulation k d)
    (side : Nat) (pos : 0 < side) (f : Nat → Nat → Nat)
    (hrow : ∀ r c, r < side → c+1 < side → Adj p (f r c) (f r (c+1)))
    (hcol : ∀ r c, r+1 < side → c < side → Adj p (f r c) (f (r+1) c)) :
    ∃ cut, ∀ i j, i < side → j < side → Hits p (imageCross side f i j) cut := by
  classical
  let E := fun (x : Nat × Nat) (h : x.1 < side ∧ x.2 < side) =>
    image_cross_hit_interval p side f hrow hcol x.1 x.2 h.1 h.2
  let I : Nat × Nat → BagInterval := fun x =>
    if h : x.1 < side ∧ x.2 < side then
      ⟨Classical.choose (E x h), Classical.choose (Classical.choose_spec (E x h))⟩
    else ⟨0,0⟩
  have spec (x : Nat × Nat) (h : x ∈ cells side) (t : Nat) :
      Hits p (imageCross side f x.1 x.2) t ↔ (I x).lo ≤ t ∧ t ≤ (I x).hi := by
    have hx := (cell_mem side x).mp h
    simp only [I, dif_pos hx]
    exact (Classical.choose_spec (Classical.choose_spec (E x hx))).2 t
  let base := I (0,0)
  let rest := (cells side).map I
  have repr (b : BagInterval) (h : b ∈ base :: rest) :
      ∃ x ∈ cells side, I x = b := by
    rcases List.mem_cons.mp h with e | m
    · exact ⟨(0,0),(cell_mem side _).mpr ⟨pos,pos⟩,e.symm⟩
    · exact List.mem_map.mp m
  have overlap : ∀ b ∈ base :: rest, ∀ c ∈ base :: rest,
      ∃ t : Nat, b.lo ≤ t ∧ t ≤ b.hi ∧ c.lo ≤ t ∧ t ≤ c.hi := by
    intro b hb c hc
    obtain ⟨x,hx,rfl⟩ := repr b hb
    obtain ⟨y,hy,rfl⟩ := repr c hc
    obtain ⟨t,a,z⟩ := image_crosses_pair_hit p side f x.1 x.2 y.1 y.2
      ((cell_mem side x).mp hx).1 ((cell_mem side y).mp hy).2
    have ha := (spec x hx t).mp a
    have hz := (spec y hy t).mp z
    exact ⟨t,ha.1,ha.2,hz.1,hz.2⟩
  obtain ⟨cut,hcut⟩ := commonBag base rest overlap
  refine ⟨cut,?_⟩
  intro i j hi hj
  have hm : (i,j) ∈ cells side := (cell_mem side _).mpr ⟨hi,hj⟩
  exact (spec (i,j) hm cut).2 (hcut (I (i,j)) (List.mem_cons_of_mem _
    (List.mem_map.mpr ⟨(i,j),hm,rfl⟩)))

/-- Grid obstruction in the actual naturally ordered, balanced child-cap host. -/
theorem no_large_grid {k : Nat} (p : InfiniteLabeledPopulation k k)
    (side : Nat) (large : k * fullRootCount p + 1 < side)
    (f : Nat → Nat → Nat)
    (hrow : ∀ r c, r < side → c+1 < side → Adj p (f r c) (f r (c+1)))
    (hcol : ∀ r c, r+1 < side → c < side → Adj p (f r c) (f (r+1) c))
    (inj : ∀ x y : Nat × Nat, x.1 < side ∧ x.2 < side → y.1 < side ∧ y.2 < side →
      f x.1 x.2 = f y.1 y.2 → x = y) : False := by
  classical
  obtain ⟨cut,hcut⟩ := common_grid_cut p side (by omega) f hrow hcol
  let pre : Nat → Option (Nat × Nat) := fun u =>
    if h : ∃ x ∈ cells side, f x.1 x.2 = u then some (Classical.choose h) else none
  let selected := (bagVertices p cut).filterMap pre
  have take (x : Nat × Nat) (hx : x ∈ cells side)
      (hb : f x.1 x.2 ∈ bagVertices p cut) : x ∈ selected := by
    apply List.mem_filterMap.mpr
    refine ⟨f x.1 x.2,hb,?_⟩
    have he : ∃ y ∈ cells side, f y.1 y.2 = f x.1 x.2 := ⟨x,hx,rfl⟩
    simp only [pre, dif_pos he]
    have prop := Classical.choose_spec he
    rw [inj (Classical.choose he) x ((cell_mem side _).mp prop.1) ((cell_mem side _).mp hx) prop.2]
  have hit : ∀ i j, i < side → j < side →
      ∃ x ∈ selected, x.1 = i ∨ x.2 = j := by
    intro i j hi hj
    obtain ⟨u,hu,hb⟩ := hcut i j hi hj
    rcases List.mem_append.mp hu with h | h
    · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp h
      exact ⟨(i,c),take (i,c) ((cell_mem side _).mpr ⟨hi,List.mem_range.mp hc⟩) hb,Or.inl rfl⟩
    · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp h
      exact ⟨(r,j),take (r,j) ((cell_mem side _).mpr ⟨List.mem_range.mp hr,hj⟩) hb,Or.inr rfl⟩
  have lb := crossHittingLowerBound side selected hit
  have ub := Nat.le_trans (List.length_filterMap_le pre (bagVertices p cut)) (bag_width p cut)
  change selected.length ≤ k * fullRootCount p + 1 at ub
  exact (Nat.not_lt_of_ge (Nat.le_trans lb ub)) large

#print axioms common_grid_cut
#print axioms no_large_grid
end ResearchCommons.CappedGridObstruction
