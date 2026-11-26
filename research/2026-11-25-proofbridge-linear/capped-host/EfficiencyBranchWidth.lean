import BranchBagProjection
import CappedActualBags

namespace ResearchCommons.EfficiencyBranchWidth
open PopulationCounting InfiniteConservation ResearchCommons.CappedActualBags
open ResearchCommons.BranchBagProjection

/-- Local compatibility on the chosen cut suffices: overlap elsewhere is irrelevant. -/
theorem width_from_locally_unique_hits {V : Type} {side : Nat}
    (bag : List V) (branch : Fin side × Fin side → List V)
    (unique : ∀ {v}, v ∈ bag → ∀ {x y}, v ∈ branch x → v ∈ branch y → x = y)
    (hit : ∀ i j : Fin side, ∃ x : Fin side × Fin side,
      (x.1 = i ∨ x.2 = j) ∧ ∃ v ∈ branch x, v ∈ bag) :
    side ≤ bag.length := by
  classical
  let cellOf (v : V) : Option (Nat × Nat) :=
    if h : ∃ x, v ∈ branch x then
      some ((Classical.choose h).1.val, (Classical.choose h).2.val)
    else none
  apply width_from_branch_hits side bag cellOf
  intro i j hi hj
  obtain ⟨x, cross, v, hv, hbag⟩ := hit ⟨i,hi⟩ ⟨j,hj⟩
  have hex : ∃ x, v ∈ branch x := ⟨x,hv⟩
  have same := unique hbag (Classical.choose_spec hex) hv
  refine ⟨v,hbag,(x.1.val,x.2.val),?_,?_⟩
  · simp only [cellOf,dif_pos hex,same]
  · exact cross.imp (congrArg Fin.val) (congrArg Fin.val)

/-- Cutting against the actual natural-order host costs only its proved width. -/
theorem actual_width_from_hits {k side : Nat} (p : InfiniteLabeledPopulation k k)
    (cut : Nat) (branch : Fin side × Fin side → List Nat)
    (unique : ∀ {v}, v ∈ bagVertices p cut → ∀ {x y}, v ∈ branch x → v ∈ branch y → x = y)
    (hit : ∀ i j : Fin side, ∃ x : Fin side × Fin side,
      (x.1 = i ∨ x.2 = j) ∧ ∃ v ∈ branch x, v ∈ bagVertices p cut) :
    side ≤ k * fullRootCount p + 1 :=
  Nat.le_trans (width_from_locally_unique_hits (bagVertices p cut) branch unique hit) (bag_width p cut)

theorem no_large_branch_model_of_common_cut {k side : Nat}
    (p : InfiniteLabeledPopulation k k) (large : k * fullRootCount p + 1 < side)
    (branch : Fin side × Fin side → List Nat)
    (disjoint : ∀ {x y} {v}, v ∈ branch x → v ∈ branch y → x = y)
    (common : ∃ cut, ∀ i j : Fin side, ∃ x : Fin side × Fin side,
      (x.1 = i ∨ x.2 = j) ∧ ∃ v ∈ branch x, v ∈ bagVertices p cut) : False := by
  obtain ⟨cut,hit⟩ := common
  exact (Nat.not_lt_of_ge (actual_width_from_hits p cut branch
    (by intro v hv x y hx hy; exact disjoint hx hy) hit)) large

/-- Raw-coordinate adapter used by the common-cut producer. -/
theorem no_large_branch_model_of_raw_hits {k side : Nat}
    (p : InfiniteLabeledPopulation k k) (large : k * fullRootCount p + 1 < side)
    (model : Nat → Nat → List Nat)
    (disjoint : ∀ a b c d : Fin side, ∀ v,
      v ∈ model a.val b.val → v ∈ model c.val d.val → a = c ∧ b = d)
    (common : ∃ cut, ∀ i j : Nat, i < side → j < side →
      ∃ a b : Nat, a < side ∧ b < side ∧ (a = i ∨ b = j) ∧
        ∃ v ∈ model a b, v ∈ bagVertices p cut) : False := by
  let branch (x : Fin side × Fin side) := model x.1.val x.2.val
  apply no_large_branch_model_of_common_cut p large branch
  · intro x y v hx hy
    obtain ⟨h1,h2⟩ := disjoint x.1 x.2 y.1 y.2 v hx hy
    exact Prod.ext h1 h2
  · obtain ⟨cut,h⟩ := common
    refine ⟨cut,?_⟩
    intro i j
    obtain ⟨a,b,ha,hb,cr,v,hv,hbag⟩ := h i.val j.val i.isLt j.isLt
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩), cr.imp Fin.ext Fin.ext, v,hv,hbag⟩

/-- Without local uniqueness the same single vertex can hit every cross. -/
theorem overlapping_negative_control :
    (∀ i j : Fin 2, ∃ x : Fin 2 × Fin 2, (x.1 = i ∨ x.2 = j) ∧
      ∃ v ∈ ([0] : List Nat), v ∈ ([0] : List Nat)) ∧
    ¬ 2 ≤ ([0] : List Nat).length := by
  exact ⟨fun i j => ⟨(i,j),Or.inl rfl,0,by simp,by simp⟩, by decide⟩

#print axioms width_from_locally_unique_hits
#print axioms actual_width_from_hits
#print axioms no_large_branch_model_of_common_cut
#print axioms no_large_branch_model_of_raw_hits
#print axioms overlapping_negative_control
end ResearchCommons.EfficiencyBranchWidth
