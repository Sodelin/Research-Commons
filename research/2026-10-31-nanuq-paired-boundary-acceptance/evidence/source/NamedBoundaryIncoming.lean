import ActualTipBoundary

/-! UNCOMPILED. Recover the WHOLE incoming carriers from the SAME named raw
outside component, rather than infer intervening arcs from midpoint membership. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves NanuqFaithfulSupplierDrawing Set Schoenflies
open scoped Graph Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)
variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)

private theorem jordan_eq_of_same_outside {C C' : Set Schoenflies.Plane}
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C')
    (h : outside C=outside C') : C=C' := by
  rw [← (jordan_curve_theorem hC).frontier_outside,
    ← (jordan_curve_theorem hC').frontier_outside,h]

include hg hb in
/-- Full original incoming edge images lie on this named original boundary.
The >=3 and exact bigon branches are separate; singleton is not admitted. -/
theorem named_boundary_incoming_full
    (face : TaxonOuterFace D N.leaf)
    (hnt : ∃ u v : BlobVertex N.graph b, u≠v)
    {C : Set Schoenflies.Plane} (hC : IsJordanCurve C)
    (hface : Graph.face (graph (blobCurves D b)) (curve (blobCurves D b))
      (coordinates face.outside)=outside C)
    (e : CoreTip N b) (t : unitInterval) : coordinates (D.arc e.val.val t)∈C := by
  obtain ⟨u,v,huv⟩ := hnt
  by_cases hthree : ∃ a c d : BlobVertex N.graph b, a≠c ∧ a≠d ∧ c≠d
  · obtain ⟨e₀,s,t',es,hcycle,hC₀,hface₀,hports,hin⟩ :=
      actual_raw_outer_cycle_all_hybrid_incoming N D b hg hb face hthree
    have hEq := jordan_eq_of_same_outside hC₀ hC (hface₀.symm.trans hface)
    rw [← hEq]
    let h : BlobVertex N.graph b := ⟨N.graph.target e.val.val,e.val.property.2⟩
    obtain ⟨f,hf,hmem⟩ := hin h e.property e.val.val rfl
    apply Graph.mem_edgesCover_iff.mpr
    refine ⟨f,hmem,?_⟩
    rw [edgeArc_eq]
    refine ⟨D.arc e.val.val t,?_,rfl⟩
    refine ⟨t,?_⟩
    change D.arc f.val t = _
    rw [hf]
  · have hall : ∀ w : BlobVertex N.graph b, w=u ∨ w=v := by
      intro w
      by_cases hwu : w=u
      · exact Or.inl hwu
      · right
        by_contra hwv
        exact hthree ⟨u,v,w,huv,Ne.symm hwu,Ne.symm hwv⟩
    obtain ⟨f,g,hfg,hex,s,t',hcycle,hC₀,hset,hface₀,hports⟩ :=
      Nanuq.ActualBigonBoundary.actual_bigon_outer_boundary N D b hb face u v huv hall
    have hEq := jordan_eq_of_same_outside hC₀ hC (hface₀.symm.trans hface)
    rw [← hEq,← hset,pointSet_eq]
    refine ⟨D.arc e.val.val t,?_,rfl⟩
    right
    let k : BlobEdge N.graph b :=
      ⟨e.val.val,Nanuq.CapCurves.internal_not_bridge N b e.val,e.val.property.1⟩
    exact Set.mem_iUnion.mpr ⟨k,t,rfl⟩

#print axioms named_boundary_incoming_full
end Nanuq.OpenedCore
