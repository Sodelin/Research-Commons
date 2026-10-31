import ActualDuplicateCyclicGaps
import FiniteLabelBlocks
import NanuqActualOpenedBinaryDegrees

/-! UNCOMPILED actual block normal form. An injective finite code is CHOSEN,
not imposed as a new original-network hypothesis. The same actual boundary,
occurrence list and source cut constraints are retained before rotation. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves NanuqFaithfulSupplierDrawing Set Schoenflies
open Nanuq.BoundaryOrder
open scoped Graph Classical
local notation "Plane" => Schoenflies.Plane
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)
variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)
local notation "M" => N.actualEveryNonleafRootedCapSource b hb
local notation "hl" => N.actual_admitted_cap_hybrid_child_is_taxon hg b hb
local notation "OG" => RootedBinary.openedHybridGraph (N.actualEveryNonleafRootedCapSource b hb)
  (N.actual_admitted_cap_hybrid_child_is_taxon hg b hb)

theorem actual_boundary_block_normal_form
    (face : TaxonOuterFace D N.leaf)
    (hnt : ∃ u v : BlobVertex N.graph b, u≠v) :
    ∃ (code : N.BlobPort b ↪ Nat) (C : Set Plane) (f : ℝ → Plane) (θ : (M).OpenedTip → ℝ) (xs : List (M).OpenedTip),
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
      (∃ k base dup, k≤1 ∧ base.Nodup ∧
        (xs.rotate k).map (fun t => code ((M).openedTipLabel hl t))=
          Nanuq.Restriction.blocks base dup) := by
  classical
  let code : N.BlobPort b ↪ Nat :=
    { toFun := fun x => (Fintype.equivFin (N.BlobPort b) x).val
      inj' := fun _ _ h => (Fintype.equivFin (N.BlobPort b)).injective (Fin.val_injective h) }
  obtain ⟨C,f,θ,xs,hC,hface,hf,himage,hθ,hθinj,hnd,hall,horder,hcuts,hgaps,hcyclic⟩ :=
    actual_duplicate_cyclic_gaps N D b hg hb code face hnt
  have hmult : ∀ x, (Finset.univ.filter (fun t : (M).OpenedTip =>
      (M).openedTipLabel hl t=x)).card≤2 := by
    intro x
    rw [(M).actual_opened_tip_multiplicity hl x]
    split_ifs <;> omega
  have hblocks := Nanuq.Restriction.finite_label_blocks xs hnd hall
    ((M).openedTipLabel hl) ((M).opened_tip_label_surjective hl)
    code code.injective hmult (N.actual_nonleaf_blob_has_two_ports b hb) hcyclic
  exact ⟨code,C,f,θ,xs,hC,hface,hf,himage,hθ,hθinj,hnd,hall,horder,hcuts,hgaps,hcyclic,hblocks⟩

#print axioms actual_boundary_block_normal_form
end Nanuq.OpenedCore
