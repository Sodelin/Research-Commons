import guards.NanuqActualRootedCapIncidence

set_option debug.skipKernelTC false

/-! The full binary degree signature of the literal original-ID cap. Original
incident occurrences are bijected, so parallel arcs and hybrid incidences are
not collapsed. Rootedness, acyclicity, LSA and suppressed readout are separate
remaining admission fields. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

noncomputable def actualRootedCapOutEquiv (b : N.graph.Blob) (v : N.OriginalBlobVertex b) :
    {e : E // N.graph.source e = v.val} ≃
      {f : N.RootedCapArc b // (N.actualRootedCapGraph b).source f = Sum.inl v} where
  toFun e := ⟨N.actualRootedCapOutArc b e.val
      (by rw [e.property];exact v.property), by
    exact (N.actualRootedCapOutArc_source b e.val _).trans
      (congrArg Sum.inl (Subtype.ext e.property))⟩
  invFun f := ⟨N.actualRootedCapOriginalArc b f.val,
    N.actualRootedCapOriginalArc_source b f.val v f.property⟩
  left_inv e := Subtype.ext (N.actualRootedCapOutArc_original b e.val (by rw [e.property];exact v.property))
  right_inv f := Subtype.ext (N.actualRootedCapOutArc_roundtrip b f.val v f.property)

noncomputable def actualRootedCapInEquiv (b : N.graph.Blob) (v : N.OriginalBlobVertex b) :
    {e : E // N.graph.target e = v.val} ≃
      {f : N.RootedCapArc b // (N.actualRootedCapGraph b).target f = Sum.inl v} where
  toFun e := ⟨N.actualRootedCapInArc b e.val
      (by rw [e.property];exact v.property), by
    exact (N.actualRootedCapInArc_target b e.val _).trans
      (congrArg Sum.inl (Subtype.ext e.property))⟩
  invFun f := ⟨N.actualRootedCapOriginalArc b f.val,
    N.actualRootedCapOriginalArc_target b f.val v f.property⟩
  left_inv e := Subtype.ext (N.actualRootedCapInArc_original b e.val (by rw [e.property];exact v.property))
  right_inv f := Subtype.ext (N.actualRootedCapInArc_roundtrip b f.val v f.property)

theorem actual_rooted_cap_inner_degrees (b : N.graph.Blob) (v : N.OriginalBlobVertex b) :
    (N.actualRootedCapGraph b).inDegree (Sum.inl v) = N.graph.inDegree v.val ∧
      (N.actualRootedCapGraph b).outDegree (Sum.inl v) = N.graph.outDegree v.val := by
  classical
  constructor
  · unfold EdgeGraph.inDegree
    rw [← Fintype.card_subtype,← Fintype.card_subtype]
    exact (Fintype.card_congr (N.actualRootedCapInEquiv b v)).symm
  · unfold EdgeGraph.outDegree
    rw [← Fintype.card_subtype,← Fintype.card_subtype]
    exact (Fintype.card_congr (N.actualRootedCapOutEquiv b v)).symm

theorem actual_rooted_cap_root_degrees (b : N.graph.Blob) :
    (N.actualRootedCapGraph b).inDegree (N.actualRootedCapRoot b) = 0 ∧
      (N.actualRootedCapGraph b).outDegree (N.actualRootedCapRoot b) = 2 := by
  by_cases hb : b = N.graph.blobOf N.root
  · have hd := N.actual_rooted_cap_inner_degrees b ⟨N.root,hb.symm⟩
    simpa [actualRootedCapRoot,hb,N.root_degrees.1,N.root_degrees.2] using hd
  · exact N.actual_rooted_cap_fresh_root_degrees b hb

noncomputable def actualRootedCapLeaf (b : N.graph.Blob) : N.BlobPort b ↪ N.RootedCapVertex b where
  toFun p := Sum.inr (Sum.inl p)
  inj' _ _ h := Sum.inl.inj (Sum.inr.inj h)

theorem actual_rooted_cap_leaf_degrees (b : N.graph.Blob) (p : N.BlobPort b) :
    (N.actualRootedCapGraph b).inDegree (N.actualRootedCapLeaf b p) = 1 ∧
      (N.actualRootedCapGraph b).outDegree (N.actualRootedCapLeaf b p) = 0 :=
  N.actual_rooted_cap_port_degrees b p

theorem actual_rooted_cap_internal_degrees (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (v : N.RootedCapVertex b) (hr : v ≠ N.actualRootedCapRoot b)
    (hl : ∀ p, N.actualRootedCapLeaf b p ≠ v) :
    ((N.actualRootedCapGraph b).inDegree v = 1 ∧
      (N.actualRootedCapGraph b).outDegree v = 2) ∨
      (N.actualRootedCapGraph b).IsHybrid v := by
  rcases v with a | (p | t)
  · have har : a.val ≠ N.root := by
      intro h
      have hbr : b = N.graph.blobOf N.root := a.property.symm.trans (congrArg N.graph.blobOf h)
      exact hr (by simp [actualRootedCapRoot,hbr];exact Subtype.ext h)
    have hal : ∀ x, N.leaf x ≠ a.val := by
      intro x h
      exact hb x ((congrArg N.graph.blobOf h).trans a.property)
    have hd := N.actual_rooted_cap_inner_degrees b a
    rcases N.internal_degrees a.val har hal with ht | hh
    · exact Or.inl ⟨hd.1.trans ht.1,hd.2.trans ht.2⟩
    · exact Or.inr ⟨hd.1.trans hh.1,hd.2.trans hh.2⟩
  · exact False.elim (hl p rfl)
  · exact False.elim (hr (by simp [actualRootedCapRoot,t.property]))

theorem actual_four_port_cap_has_two_taxa (q : Fin 4 ↪ X) (b : N.graph.Blob)
    (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i))) :
    2 ≤ Fintype.card (N.BlobPort b) := by
  have h := Fintype.card_le_of_injective (fun i => N.blobProjection b hb (q i)) hinj
  simp only [Fintype.card_fin] at h
  exact Nat.le_trans (by decide : 2 ≤ 4) h
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_rooted_cap_inner_degrees
#print axioms Nanuq.Source.RootedBinary.actual_rooted_cap_internal_degrees
