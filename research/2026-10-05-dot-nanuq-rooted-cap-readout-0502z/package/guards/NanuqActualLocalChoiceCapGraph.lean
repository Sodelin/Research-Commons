import guards.NanuqEdgeOccurrenceReadoutEquiv

set_option debug.skipKernelTC false

/-! Independently typed actual local-choice cap graph and original-ID edge
bijection to each full switching's cap. No exterior switching multiplicity
or desired quartet row is made a field. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X}

namespace OriginalBlobSwitching
variable {b : N.graph.Blob} (L : N.OriginalBlobSwitching b)

abbrev InternalChoiceEdge := {e : N.OriginalBlobArc b // L.keep e}
abbrev LocalCapEdge := Sum L.InternalChoiceEdge (N.BlobPort b)

noncomputable def localCappedGraph : EdgeGraph (N.CappedBlobVertex b) L.LocalCapEdge where
  source := Sum.elim (fun f => Sum.inl ⟨N.graph.source f.val.val,f.val.property.1⟩)
    (fun p => Sum.inl (N.originalPortInner b p))
  target := Sum.elim (fun f => Sum.inl ⟨N.graph.target f.val.val,f.val.property.2⟩) Sum.inr

def localCappedHybridMark : L.LocalCapEdge → Prop :=
  Sum.elim (fun f => N.graph.IsHybrid (N.graph.target f.val.val)) (fun _ => False)
end OriginalBlobSwitching

namespace Switching
variable (S : N.Switching)

noncomputable def originalRestrictionInternalEquiv (b : N.graph.Blob) :
    S.InternalBlobEdge b ≃ (S.restrictOriginalBlobSwitching b).InternalChoiceEdge where
  toFun f := ⟨⟨f.val.val,f.property⟩,f.val.property⟩
  invFun f := ⟨⟨f.val.val,f.property⟩,f.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def originalRestrictionCapEquiv (b : N.graph.Blob) :
    S.CappedBlobEdge b ≃ (S.restrictOriginalBlobSwitching b).LocalCapEdge :=
  Equiv.sumCongr (S.originalRestrictionInternalEquiv b) (Equiv.refl _)

theorem original_restriction_cap_source (b : N.graph.Blob) (f : S.CappedBlobEdge b) :
    (S.restrictOriginalBlobSwitching b).localCappedGraph.source (S.originalRestrictionCapEquiv b f) =
      (S.actualCappedBlobGraph b).source f := by
  cases f <;> rfl

theorem original_restriction_cap_target (b : N.graph.Blob) (f : S.CappedBlobEdge b) :
    (S.restrictOriginalBlobSwitching b).localCappedGraph.target (S.originalRestrictionCapEquiv b f) =
      (S.actualCappedBlobGraph b).target f := by
  cases f <;> rfl

theorem original_restriction_cap_hybrid_mark (b : N.graph.Blob) (f : S.CappedBlobEdge b) :
    (S.restrictOriginalBlobSwitching b).localCappedHybridMark (S.originalRestrictionCapEquiv b f) ↔
      S.actualCappedHybridMark b f := by
  cases f <;> exact Iff.rfl

theorem actual_local_choice_cap_resolution_iff (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i))) (r : Nanuq.Quartet.Resolution) :
    (S.restrictOriginalBlobSwitching b).localCappedGraph.Resolves
      (fun i => Sum.inr (N.blobProjection b hb (q i))) r ↔ r = S.resolve q := by
  have hi := (S.actualCappedBlobGraph b).resolves_edge_equiv_iff
    (S.restrictOriginalBlobSwitching b).localCappedGraph
    (S.originalRestrictionCapEquiv b) (S.original_restriction_cap_source b)
    (S.original_restriction_cap_target b)
    (fun i => Sum.inr (N.blobProjection b hb (q i))) r
  exact hi.symm.trans (S.actual_capped_quartet_resolution_iff q b hb hinj r)
end Switching
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.Switching.actual_local_choice_cap_resolution_iff
