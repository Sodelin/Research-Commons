import CompactObstacleJordan

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.CompactArcNeighborhood
open Set Schoenflies

/-- A compact source arc has a Jordan neighborhood in EVERY prescribed open
neighborhood. This derives the neighborhood, not a one-exit pendant chart. -/
theorem arc_jordan_neighborhood {A U : Set Plane} (hA : IsArc A)
    (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ C : Set Plane, IsJordanCurve C ∧ A ⊆ inside C ∧ C ∪ inside C ⊆ U := by
  obtain ⟨R,hR,hAsq⟩ := Plane.exists_closedSquare_of_isBounded hA.isCompact.isBounded
  let S := Plane.closedSquare 0 (R+2)
  let z := Plane.mk (R+3) 0
  have hzS : z ∉ S := by
    intro hz
    have hh : max |R+3| |(0:ℝ)| ≤ R+2 := by
      simpa [S,z,Plane.closedSquare,Plane.supDist,Plane.supNorm] using hz
    rw [abs_of_nonneg (by linarith : 0 ≤ R+3),abs_zero,max_eq_left (by linarith)] at hh
    linarith
  have hAS : A ⊆ S := by
    intro x hx
    have hh := hAsq hx
    change Plane.supDist x 0 ≤ R at hh
    change Plane.supDist x 0 ≤ R+2
    linarith
  let L := insert z (S \ U)
  have hSc : IsCompact S := Metric.isCompact_of_isClosed_isBounded
    (Plane.isClosed_closedSquare 0 (R+2)) (Plane.isBounded_closedSquare 0 (R+2))
  have hLc : IsCompact L := (hSc.diff hU).insert z
  have hLne : L.Nonempty := ⟨z,Or.inl rfl⟩
  have hLA : Disjoint L A := by
    rw [Set.disjoint_left]
    intro x hx hxA
    rcases hx with rfl | hx
    · exact hzS (hAS hxA)
    · exact hx.2 (hAU hxA)
  obtain ⟨C,hC,hAin,hLout,hnear⟩ := compact_obstacle_jordan hA hLc hLne hLA
    (show (0:ℝ)<1 by norm_num)
  have hCsmall : C ⊆ Plane.closedSquare 0 (R+1) := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hnear x hx
    have hyR := hAsq hy
    change Plane.supDist y 0 ≤ R at hyR
    have htri := Plane.supDist_triangle x y 0
    change Plane.supDist x 0 ≤ R+1
    linarith
  have hCS : C ⊆ S := by
    intro x hx
    have hh := hCsmall hx
    change Plane.supDist x 0 ≤ R+1 at hh
    change Plane.supDist x 0 ≤ R+2
    linarith
  have hSout : Sᶜ ⊆ outside C := by
    intro x hx
    have hxC : x ∉ C := fun hxC => hx (hCS hxC)
    have hcomp : Sᶜ ⊆ connectedComponentIn Cᶜ x :=
      (Plane.isConnected_compl_closedSquare 0 (R+2)).isPreconnected.subset_connectedComponentIn
        hx (compl_subset_compl.2 hCS)
    refine ⟨hxC,?_⟩
    intro hb
    exact Plane.not_isBounded_compl_closedSquare 0 (R+2) (hb.subset hcomp)
  refine ⟨C,hC,hAin,?_⟩
  intro x hx
  by_contra hxU
  have hxout : x ∈ outside C := by
    by_cases hxS : x ∈ S
    · exact hLout (Or.inr ⟨hxS,hxU⟩)
    · exact hSout hxS
  rcases hx with hxC | hxIn
  · exact outside_subset_compl hxout hxC
  · exact Set.disjoint_left.1 disjoint_inside_outside hxIn hxout

#print axioms arc_jordan_neighborhood
end Nanuq.CompactArcNeighborhood
