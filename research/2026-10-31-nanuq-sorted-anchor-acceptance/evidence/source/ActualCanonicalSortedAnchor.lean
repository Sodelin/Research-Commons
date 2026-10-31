import ActualSortedAnchor

/-! UNCOMPILED same-witness extension: all literal query means and all
non-diagonal anchors use the ONE source-derived boundary/rank/mask/Tree.
Repeated query cases are included; no global given-order claim. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves NanuqFaithfulSupplierDrawing Set Schoenflies
open Nanuq.GraphSyntax Nanuq.GraphReceiver Nanuq.AdjacentCertificate Nanuq.Restriction Nanuq.ActualFinite
open scoped Graph Classical
local notation "Plane" => Schoenflies.Plane
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)
variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)
local notation "M" => N.actualEveryNonleafRootedCapSource b hb
local notation "hl" => N.actual_admitted_cap_hybrid_child_is_taxon hg b hb

theorem actual_canonical_sorted_anchor_receiver
    (face : TaxonOuterFace D N.leaf)
    (hnt : ∃ u v : BlobVertex N.graph b, u≠v) :
    ∃ (n mask : Nat) (rank : N.BlobPort b ≃ Fin n)
      (C : Set Plane) (f : ℝ → Plane) (θ : (M).OpenedTip → ℝ)
      (xs : List (M).OpenedTip) (k : Nat) (T : Tree),
      2≤n ∧ mask<2^n ∧ IsJordanCurve C ∧
      Graph.face (graph (blobCurves D b)) (curve (blobCurves D b))
        (coordinates face.outside)=outside C ∧
      IsLoop f ∧ f '' unitInterval=C ∧
      (∀ t, θ t∈Ico (0:ℝ) 1 ∧ f (θ t)=tipPoint N D b hg hb t) ∧
      Function.Injective θ ∧ xs.Nodup ∧ (∀ t, t∈xs) ∧
      xs.Pairwise (fun a c => θ a≤θ c) ∧ k≤1 ∧
      (xs.rotate k).map (fun t => (rank ((M).openedTipLabel hl t)).val)=occurrenceLabels n mask ∧
      T.size=(occurrenceLabels n mask).length-1 ∧
      (∀ q : Fin 4 ↪ N.BlobPort b,
        (M).rawDisplayedQuartets q=finiteResolutionSet T (occurrenceLabels n mask)
          ⟨(rank (q 0)).val,(rank (q 1)).val,(rank (q 2)).val,(rank (q 3)).val⟩ ∧
        (M).rawQuartetMean q=Nanuq.Quartet.distinctMean (finiteResolutionSet T (occurrenceLabels n mask)
          ⟨(rank (q 0)).val,(rank (q 1)).val,(rank (q 2)).val,(rank (q 3)).val⟩)) ∧
      (∀ (q : Fin 4 ↪ X) (hinj : Function.Injective (fun i => N.blobProjection b hb (q i))),
        N.rawDisplayedQuartets q=finiteResolutionSet T (occurrenceLabels n mask)
          ⟨(rank (N.blobProjection b hb (q 0))).val,(rank (N.blobProjection b hb (q 1))).val,
           (rank (N.blobProjection b hb (q 2))).val,(rank (N.blobProjection b hb (q 3))).val⟩ ∧
        N.rawQuartetMean q=Nanuq.Quartet.distinctMean (finiteResolutionSet T (occurrenceLabels n mask)
          ⟨(rank (N.blobProjection b hb (q 0))).val,(rank (N.blobProjection b hb (q 1))).val,
           (rank (N.blobProjection b hb (q 2))).val,(rank (N.blobProjection b hb (q 3))).val⟩)) ∧
      (∀ q : Fin 4 ↪ N.BlobPort b,
        (twiceMean (quartets n) (codedPattern T (occurrenceLabels n mask) n)
          (rank (q 0)).val (rank (q 1)).val (rank (q 2)).val (rank (q 3)).val : ℚ)=
          2*(M).rawQuartetMean q) ∧
      (∀ v : Fin 4 → N.BlobPort b, v 2≠v 3 →
        (anchor (quartets n) (codedPattern T (occurrenceLabels n mask) n)
          (rank (v 2)).val (rank (v 3)).val (rank (v 0)).val (rank (v 1)).val : ℚ)=
          (M).actualTupleAnchor v) := by
  classical
  obtain ⟨n,mask,rank,C,f,θ,xs,k,T,hn,hm,hC,hface,hf,himage,hθ,hθinj,hnd,hall,
    horder,hk,hblocks,hsize,hlocal,hglobal⟩ :=
    actual_canonical_distinct_receiver N D b hg hb face hnt
  have hmean (q : Fin 4 ↪ N.BlobPort b) := (hlocal q).2
  refine ⟨n,mask,rank,C,f,θ,xs,k,T,hn,hm,hC,hface,hf,himage,hθ,hθinj,hnd,hall,
    horder,hk,hblocks,hsize,hlocal,hglobal,?_,?_⟩
  · intro q
    exact actual_sorted_query_mean (M) n mask rank T hsize hmean q
  · intro v hv
    exact actual_sorted_anchor (M) n mask rank T hsize hmean v hv

#print axioms actual_canonical_sorted_anchor_receiver
end Nanuq.OpenedCore
