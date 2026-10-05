import guards.NanuqActualGalledChildBridge

set_option debug.skipKernelTC false

/-! Every hybrid in the actual original-blob cap has a pendant port-taxon
child, derived from original galled detours and the hybrid-child bridge
lemma. No prescribed opened-tree representation is an input. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem actual_rooted_cap_hybrid_child_is_leaf (hg : N.graph.GalledDetour)
    (b : N.graph.Blob) (f : N.RootedCapArc b)
    (hh : (N.actualRootedCapGraph b).IsHybrid ((N.actualRootedCapGraph b).source f)) :
    ∃ p : N.BlobPort b, (N.actualRootedCapGraph b).target f = N.actualRootedCapLeaf b p := by
  rcases f with e | (p | t)
  · have hehy : N.graph.IsHybrid (N.graph.source e.val) :=
      (N.actual_rooted_cap_inner_hybrid_iff b ⟨N.graph.source e.val,e.property.1⟩).mp hh
    have he := N.actual_galled_hybrid_child_is_bridge hg e.val hehy
    exact False.elim (N.graph.bridge_blob_ne he (e.property.1.trans e.property.2.symm))
  · exact ⟨p,rfl⟩
  · have hd := (N.actual_rooted_cap_root_degrees b).1
    change (N.actualRootedCapGraph b).IsHybrid (N.actualRootedCapRoot b) at hh
    have h2 := hh.1
    omega

theorem actual_admitted_cap_hybrid_child_is_taxon (hg : N.graph.GalledDetour)
    (b : N.graph.Blob) (hb : N.NonleafBlob b) (f : N.RootedCapArc b)
    (hh : (N.actualEveryNonleafRootedCapSource b hb).graph.IsHybrid
      ((N.actualEveryNonleafRootedCapSource b hb).graph.source f)) :
    ∃ p, (N.actualEveryNonleafRootedCapSource b hb).graph.target f =
      (N.actualEveryNonleafRootedCapSource b hb).leaf p :=
  N.actual_rooted_cap_hybrid_child_is_leaf hg b f hh
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_admitted_cap_hybrid_child_is_taxon
