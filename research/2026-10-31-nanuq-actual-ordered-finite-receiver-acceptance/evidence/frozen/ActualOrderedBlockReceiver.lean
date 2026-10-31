import ActualBoundaryBlocks
import RotatedFiniteReceiver
import NanuqActualOpenedRootedAdmission

/-! UNCOMPILED actual source-to-ordered finite Tree join. One boundary/block
witness is selected once. The ordered syntax is quartet-equivalent for every
label map, not falsely asserted to retain the original directed Represents. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves NanuqFaithfulSupplierDrawing Set Schoenflies
open Nanuq.BoundaryOrder Nanuq.GraphSyntax Nanuq.GraphReceiver Nanuq.AdjacentCertificate
open scoped Graph Classical
local notation "Plane" => Schoenflies.Plane
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)
variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)
local notation "M" => N.actualEveryNonleafRootedCapSource b hb
local notation "hl" => N.actual_admitted_cap_hybrid_child_is_taxon hg b hb
local notation "OG" => RootedBinary.openedHybridGraph (N.actualEveryNonleafRootedCapSource b hb)
  (N.actual_admitted_cap_hybrid_child_is_taxon hg b hb)

theorem actual_ordered_block_finite_receiver
    (face : TaxonOuterFace D N.leaf)
    (hnt : ∃ u v : BlobVertex N.graph b, u≠v) :
    ∃ (code : N.BlobPort b ↪ Nat) (C : Set Plane) (f : ℝ → Plane) (θ : (M).OpenedTip → ℝ) (xs : List (M).OpenedTip)
      (k : Nat) (base : List Nat) (dup : Nat → Bool)
      (s : BinarySyntax (M).OpenedHybridVertex) (label : (M).OpenedHybridVertex → Nat) (T : Tree),
      IsJordanCurve C ∧
      Graph.face (graph (blobCurves D b)) (curve (blobCurves D b))
        (coordinates face.outside)=outside C ∧
      IsLoop f ∧ f '' unitInterval=C ∧
      (∀ t, θ t∈Ico (0:ℝ) 1 ∧ f (θ t)=tipPoint N D b hg hb t) ∧
      Function.Injective θ ∧ xs.Nodup ∧ (∀ t, t∈xs) ∧
      xs.Pairwise (fun a c => θ a≤θ c) ∧
      (∀ (k : (M).OpenedHybridEdge) (a c d e : (M).OpenedTip),
        (OG).OrientedQuartet k ((M).openedTipVertex a) ((M).openedTipVertex c)
          ((M).openedTipVertex d) ((M).openedTipVertex e) →
        ¬((θ a<θ d ∧ θ d<θ c ∧ θ c<θ e) ∨
          (θ d<θ a ∧ θ a<θ e ∧ θ e<θ c))) ∧
      (∀ a c : (M).OpenedTip, θ a<θ c →
        (M).openedTipLabel hl a=(M).openedTipLabel hl c →
        (∀ w, ¬(θ a<θ w ∧ θ w<θ c)) ∨
          (∀ w, ¬(θ w<θ a ∨ θ c<θ w))) ∧
      (∀ a c : (M).OpenedTip, a≠c →
        (M).openedTipLabel hl a=(M).openedTipLabel hl c →
        Nanuq.Restriction.CyclicGap (xs.map (fun t => code ((M).openedTipLabel hl t)))
          (code ((M).openedTipLabel hl a)) (code ((M).openedTipLabel hl a))) ∧
      k≤1 ∧ base.Nodup ∧
      (xs.rotate k).map (fun t => code ((M).openedTipLabel hl t))=Nanuq.Restriction.blocks base dup ∧
      s.frontier=xs.map (M).openedTipVertex ∧
      (∀ (lab : (M).OpenedHybridVertex → Nat) a b c d,
        LabelledQuartet (OG) lab a b c d ↔ (encode lab s).Witness [] a b c d) ∧
      (∀ t, label ((M).openedTipVertex t)=code ((M).openedTipLabel hl t)) ∧
      T.size=(Nanuq.Restriction.blocks base dup).length-1 ∧
      (∀ (q : Quartet) (r a b c d : Nat), q.parts r=(a,b,c,d) → a≠b → c≠d →
        (LabelledQuartet (OG) label a b c d ↔
          ∃ e∈T.internalIntervals 1,
            edgeWitness (Nanuq.Restriction.blocks base dup) e.1 e.2 q r=true)) := by
  classical
  obtain ⟨code,C,f,θ,xs,hC,hface,hf,himage,hθ,hθinj,hnd,hall,horder,hcuts,hgaps,hcyclic,
      k,base,dup,hk,hbase,hblocks⟩ := actual_boundary_block_normal_form N D b hg hb face hnt
  obtain ⟨s,hfront,hsource⟩ := rooted_tree_order_receiver
    ((M).actualOpenedRootedSource hl) ((M).opened_hybrid_uniqueIncoming hl)
    xs θ hnd hall hθinj horder hcuts
  let label : (M).OpenedHybridVertex → Nat := fun v =>
    if h : ∃ t, (M).openedTipVertex t=v then code ((M).openedTipLabel hl (Classical.choose h)) else 0
  have hlabel (t : (M).OpenedTip) : label ((M).openedTipVertex t)=code ((M).openedTipLabel hl t) := by
    have ht : ∃ u, (M).openedTipVertex u=(M).openedTipVertex t := ⟨t,rfl⟩
    dsimp [label]
    rw [dif_pos ht]
    exact congrArg (fun u => code ((M).openedTipLabel hl u))
      ((M).openedTipVertex.injective (Classical.choose_spec ht))
  have hleaves : (encode label s).leaves=xs.map (fun t => code ((M).openedTipLabel hl t)) := by
    simp only [encode_leaves,hfront,List.map_map,Function.comp_def,hlabel]
  have hfin : xs.toFinset=Finset.univ := by ext t; simp [hall t]
  have hcard : Fintype.card (M).OpenedTip=xs.length := by
    simpa only [hfin,Finset.card_univ] using List.toFinset_card_of_nodup hnd
  have hsize : 2≤(encode label s).leaves.length := by
    simpa only [hleaves,List.length_map,← hcard] using (M).opened_at_least_two_tips hl
  obtain ⟨T,hTsize,hfinite⟩ := rotated_finite_receiver (encode label s) hsize k hk
  have hrot : (encode label s).leaves.rotate k=Nanuq.Restriction.blocks base dup := by
    rw [hleaves,← List.map_rotate]
    exact hblocks
  refine ⟨code,C,f,θ,xs,k,base,dup,s,label,T,hC,hface,hf,himage,hθ,hθinj,hnd,hall,horder,
    hcuts,hgaps,hcyclic,hk,hbase,hblocks,hfront,hsource,hlabel,?_,?_⟩
  · simpa only [hrot] using hTsize
  · intro q r a b c d hparts hab hcd
    have h := (hsource label a b c d).trans (hfinite q r a b c d hparts hab hcd)
    simpa only [hrot] using h

#print axioms actual_ordered_block_finite_receiver
end Nanuq.OpenedCore
