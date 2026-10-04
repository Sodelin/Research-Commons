import G1ExactCircularOrderCarrier

/-! The exact inherited circular-split convention: rotate the complete taxon
list to its two boundary gaps, giving two consecutive blocks whose UNORDERED
finite-label sides are the actual split. Rotation and reversal invariance are
proved before lifting this predicate to the actual finite circle quotient. -/
namespace G1ActualCircularSplitCompatibility
set_option backward.isDefEq.respectTransparency false
open G1ExactCircularOrderCarrier
open scoped Classical
variable {X : Type*} [Fintype X]

def rawSplitCompatible (labels : List X) (cut : Finset (Finset X)) : Prop :=
  ∃ left right : List X, List.IsRotated labels (left ++ right) ∧ cut = {left.toFinset,right.toFinset}

lemma raw_compatible_rotation (labels other : List X) (h : List.IsRotated labels other)
    (cut : Finset (Finset X)) : rawSplitCompatible labels cut ↔ rawSplitCompatible other cut := by
  constructor
  · rintro ⟨left,right,hrot,hcut⟩
    exact ⟨left,right,h.symm.trans hrot,hcut⟩
  · rintro ⟨left,right,hrot,hcut⟩
    exact ⟨left,right,h.trans hrot,hcut⟩

lemma raw_compatible_reverse_forward (labels : List X) (cut : Finset (Finset X))
    (h : rawSplitCompatible labels cut) : rawSplitCompatible labels.reverse cut := by
  obtain ⟨left,right,hrot,hcut⟩ := h
  refine ⟨right.reverse,left.reverse,?_,?_⟩
  · simpa only [List.reverse_append] using hrot.reverse
  · simpa only [List.toFinset_reverse,Finset.pair_comm] using hcut

lemma raw_compatible_reverse (labels : List X) (cut : Finset (Finset X)) :
    rawSplitCompatible labels cut ↔ rawSplitCompatible labels.reverse cut := by
  constructor
  · exact raw_compatible_reverse_forward labels cut
  · intro h
    simpa only [List.reverse_reverse] using raw_compatible_reverse_forward labels.reverse cut h

lemma actual_dihedral_compatibility (r s : Representative X) (h : SameCircle X r s)
    (cut : Finset (Finset X)) : rawSplitCompatible r.val cut ↔ rawSplitCompatible s.val cut := by
  rcases h with h | h
  · exact raw_compatible_rotation r.val s.val h cut
  · exact (raw_compatible_reverse r.val cut).trans (raw_compatible_rotation r.val.reverse s.val h cut)

def SplitCompatible (circle : TaxonCircle X) (cut : Finset (Finset X)) : Prop :=
  Quotient.lift (fun r : Representative X => rawSplitCompatible r.val cut)
    (fun r s h => propext (actual_dihedral_compatibility r s h cut)) circle

theorem actual_circle_split_compatibility_iff (r : Representative X) (cut : Finset (Finset X)) :
    SplitCompatible (circleOf X r) cut ↔
      ∃ left right : List X, List.IsRotated r.val (left ++ right) ∧ cut = {left.toFinset,right.toFinset} :=
  Iff.rfl

noncomputable def compatibleOrders (splits : Finset (Finset (Finset X))) : Finset (TaxonCircle X) :=
  Finset.univ.filter (fun circle => ∀ cut ∈ splits, SplitCompatible circle cut)

theorem actual_all_split_compatible_orders_iff (splits : Finset (Finset (Finset X)))
    (circle : TaxonCircle X) : circle ∈ compatibleOrders splits ↔
      ∀ cut ∈ splits, SplitCompatible circle cut := by simp [compatibleOrders]

theorem every_actual_encoding_membership_iff (splits : Finset (Finset (Finset X)))
    (r : Representative X) : circleOf X r ∈ compatibleOrders splits ↔
      ∀ cut ∈ splits, ∃ left right : List X, List.IsRotated r.val (left ++ right) ∧
        cut = {left.toFinset,right.toFinset} := by
  simp only [actual_all_split_compatible_orders_iff,actual_circle_split_compatibility_iff]

/-- The blocks really partition the original complete taxon list. No repeated
taxa or hidden partial panel is permitted by the circular-order carrier. -/
theorem actual_compatible_blocks_partition (r : Representative X) (cut : Finset (Finset X))
    (h : SplitCompatible (circleOf X r) cut) :
    ∃ left right : List X, List.IsRotated r.val (left ++ right) ∧ cut = {left.toFinset,right.toFinset} ∧
      (left ++ right).Nodup ∧ left.toFinset ∪ right.toFinset = Finset.univ := by
  obtain ⟨left,right,hrot,hcut⟩ := h
  refine ⟨left,right,hrot,hcut,hrot.nodup_iff.mp r.property.1,?_⟩
  have hf := List.toFinset_eq_of_perm _ _ hrot.perm
  rw [r.property.2,List.toFinset_append] at hf
  exact hf.symm

#print axioms actual_dihedral_compatibility
#print axioms every_actual_encoding_membership_iff
end G1ActualCircularSplitCompatibility
