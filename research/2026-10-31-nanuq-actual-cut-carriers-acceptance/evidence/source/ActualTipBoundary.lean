import ActualCutCarriers
import RawCycleIncoming
import ActualBigonBoundary

/-! UNCOMPILED source-facing join. SAME original raw boundary, actual labelled
occurrence points, and explicit nontrivial-blob case split. No circular order
or noncrossing theorem is assumed. Singleton remains separate. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves NanuqFaithfulSupplierDrawing Set
open scoped Graph Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)
variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)
local notation "M" => N.actualEveryNonleafRootedCapSource b hb

/-- Shared use of port attachments and incoming occurrence midpoints. These
are source-derived boundary facts, not an arbitrary order certificate. -/
theorem all_tip_points_on_boundary {C : Set Schoenflies.Plane}
    (hp : ∀ p : N.BlobPort b, coordinates (D.point (N.originalPortInner b p).val) ∈ C)
    (he : ∀ e : CoreTip N b, coordinates (D.arc e.val.val Nanuq.CapCurves.oneHalf) ∈ C) :
    ∀ t : (M).OpenedTip, tipPoint N D b hg hb t ∈ C := by
  intro t
  rcases t with p | e
  · change coordinates (D.point (N.originalPortInner b p.val).val) ∈ C
    exact hp p.val
  · change coordinates (D.arc (occurrenceRaw N b hb e).val.val Nanuq.CapCurves.oneHalf) ∈ C
    exact he (occurrenceRaw N b hb e)

/-- All actual opened occurrence tips lie on one original raw Jordan boundary.
The >=3 cycle provider and exact two-ID bigon provider are separate branches.
Neither a root cap outside stub nor an arbitrary drawing is substituted. -/
theorem actual_nontrivial_tip_boundary (face : TaxonOuterFace D N.leaf)
    (hnt : ∃ u v : BlobVertex N.graph b, u≠v) :
    ∃ C : Set Schoenflies.Plane, Schoenflies.IsJordanCurve C ∧
      Graph.face (graph (blobCurves D b)) (curve (blobCurves D b))
        (coordinates face.outside) = Schoenflies.outside C ∧
      ∀ t : (M).OpenedTip, tipPoint N D b hg hb t ∈ C := by
  obtain ⟨u,v,huv⟩ := hnt
  by_cases hthree : ∃ a c d : BlobVertex N.graph b, a≠c ∧ a≠d ∧ c≠d
  · obtain ⟨e₀,s,t,es,hcycle,hC,hface,hports,hin⟩ :=
      actual_raw_outer_cycle_all_hybrid_incoming N D b hg hb face hthree
    refine ⟨Graph.edgesCover (curve (blobCurves D b)) (e₀::es),hC,hface,?_⟩
    apply all_tip_points_on_boundary N D b hg hb hports
    intro e
    let h : BlobVertex N.graph b := ⟨N.graph.target e.val.val,e.val.property.2⟩
    obtain ⟨f,hf,hmem⟩ := hin h e.property e.val.val rfl
    apply Graph.mem_edgesCover_iff.mpr
    refine ⟨f,hmem,?_⟩
    rw [edgeArc_eq]
    refine ⟨D.arc e.val.val Nanuq.CapCurves.oneHalf,?_,rfl⟩
    refine ⟨Nanuq.CapCurves.oneHalf,?_⟩
    change D.arc f.val Nanuq.CapCurves.oneHalf = _
    rw [hf]
  · have hall : ∀ w : BlobVertex N.graph b, w=u ∨ w=v := by
      intro w
      by_cases hwu : w=u
      · exact Or.inl hwu
      · right
        by_contra hwv
        exact hthree ⟨u,v,w,huv,Ne.symm hwu,Ne.symm hwv⟩
    obtain ⟨e,f,hef,hex,s,t,hcycle,hC,hset,hface,hports⟩ :=
      Nanuq.ActualBigonBoundary.actual_bigon_outer_boundary N D b hb face u v huv hall
    refine ⟨Graph.edgesCover (curve (blobCurves D b)) [e,f],hC,hface,?_⟩
    apply all_tip_points_on_boundary N D b hg hb hports
    intro k
    rw [← hset,pointSet_eq]
    refine ⟨D.arc k.val.val Nanuq.CapCurves.oneHalf,?_,rfl⟩
    right
    let g : BlobEdge N.graph b :=
      ⟨k.val.val,Nanuq.CapCurves.internal_not_bridge N b k.val,k.val.property.1⟩
    exact Set.mem_iUnion.mpr ⟨g,Nanuq.CapCurves.oneHalf,rfl⟩

/-- Coherent source-facing input to the still-separate closed-disk noncrossing
lemma. One C is chosen BEFORE all cuts and all queried tip occurrences. -/
theorem actual_all_cut_carriers_one_boundary (face : TaxonOuterFace D N.leaf)
    (hnt : ∃ u v : BlobVertex N.graph b, u≠v) :
    ∃ C : Set Schoenflies.Plane, Schoenflies.IsJordanCurve C ∧
      Function.Injective (tipPoint N D b hg hb) ∧
      (∀ t : (M).OpenedTip, tipPoint N D b hg hb t ∈ C) ∧
      ∀ k : N.OriginalBlobArc b,
        IsCompact (sourceCarrier N D b hg k) ∧ IsConnected (sourceCarrier N D b hg k) ∧
        IsCompact (targetCarrier N D b hg k) ∧ IsConnected (targetCarrier N D b hg k) ∧
        Disjoint (sourceCarrier N D b hg k) (targetCarrier N D b hg k) ∧
        sourceCarrier N D b hg k ⊆ C ∪ Schoenflies.inside C ∧
        targetCarrier N D b hg k ⊆ C ∪ Schoenflies.inside C := by
  obtain ⟨C,hC,hface,htips⟩ := actual_nontrivial_tip_boundary N D b hg hb face hnt
  refine ⟨C,hC,tipPoint_injective N D b hg hb hnt,htips,?_⟩
  intro k
  obtain ⟨ha,hac,hb',hbc,hab⟩ := actual_cut_carriers N D b hg hb k
  obtain ⟨hA,hB⟩ := actual_cut_carriers_closed_disk N D b hg k
    (coordinates face.outside) C hface
  exact ⟨ha,hac,hb',hbc,hab,hA,hB⟩

#print axioms actual_nontrivial_tip_boundary
#print axioms actual_all_cut_carriers_one_boundary
end Nanuq.OpenedCore
