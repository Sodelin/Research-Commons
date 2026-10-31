import ActualFiniteDistinctMean

/-! UNCOMPILED coherent original-source local mean receiver. ONE actual
boundary/order supplies canonical ranks and one finite Tree for all queries.
The original raw DISTINCT set/mean is transported, not redefined. -/
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

theorem actual_canonical_distinct_receiver
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
           (rank (N.blobProjection b hb (q 2))).val,(rank (N.blobProjection b hb (q 3))).val⟩)) := by
  classical
  obtain ⟨code,C,f,θ,xs,k,base,dup,s,oldLab,oldT,hC,hface,hf,himage,hθ,hθinj,hnd,hall,horder,
    hcuts,hgaps,hcyclic,hk,hbase,hblocks,hfront,hsource,hold,holdsize,holdfinite⟩ :=
    actual_ordered_block_finite_receiver N D b hg hb face hnt
  have support := actual_block_support code ((M).openedTipLabel hl)
    ((M).opened_tip_label_surjective hl) xs hall k base dup hblocks
  obtain ⟨rank,hrank⟩ := exists_canonical_port_rank code base hbase support
  have hc : Fintype.card (N.BlobPort b)=base.length := by
    simpa only [Fintype.card_fin] using Fintype.card_congr rank
  have hn : 2≤base.length := by
    have htwo := (M).at_least_two_taxa
    change 2≤Fintype.card (N.BlobPort b) at htwo
    omega
  have hfin : xs.toFinset=Finset.univ := by ext t; simp [hall t]
  have hxcard : Fintype.card (M).OpenedTip=xs.length := by
    simpa only [hfin,Finset.card_univ] using List.toFinset_card_of_nodup hnd
  have hs : 2≤xs.length := by rw [← hxcard]; exact (M).opened_at_least_two_tips hl
  obtain ⟨lab,T,hlab,hT,hfinite⟩ := canonical_syntax_receiver
    ((M).openedHybridGraph hl) (M).openedTipVertex ((M).openedTipLabel hl)
    code xs k base dup s oldLab hfront hs hk hbase hblocks hold hsource rank hrank
  let rankCode : N.BlobPort b ↪ Nat :=
    ⟨fun x => (rank x).val,fun _ _ h => rank.injective (Fin.ext h)⟩
  have hlocal := actual_distinct_set_and_mean_finite (M) hl rankCode lab T
    (occurrenceLabels base.length (restrictedMask base dup)) hlab hfinite
  have hcanonical : (xs.rotate k).map (fun t => (rank ((M).openedTipLabel hl t)).val)=
      occurrenceLabels base.length (restrictedMask base dup) := by
    calc
      _ = ((xs.rotate k).map (fun t => code ((M).openedTipLabel hl t))).map base.idxOf := by
        simp only [List.map_map,Function.comp_def,hrank]
      _ = (blocks base dup).map base.idxOf := congrArg (List.map base.idxOf) hblocks
      _ = _ := restricted_blocks_canonical base hbase dup
  refine ⟨base.length,restrictedMask base dup,rank,C,f,θ,xs,k,T,hn,
    restrictedMask_bound base dup,hC,hface,hf,himage,hθ,hθinj,hnd,hall,horder,hk,hcanonical,hT,hlocal,?_⟩
  intro q hinj
  have hcap := N.actual_four_port_rooted_cap_distinct_set_and_mean q b hb hinj
  have h := hlocal (N.actualRootedCapQuartet q b hb hinj)
  exact ⟨hcap.1.trans h.1,hcap.2.trans h.2⟩

#print axioms actual_canonical_distinct_receiver
end Nanuq.OpenedCore
