import ActualCutNoncrossing
import ActualPairedBoundary

/-! UNCOMPILED. A coherent actual-source witness for the finite-order receiver.
Independent existential boundaries are NOT conjoined. Choose the named original
raw frontier once, then derive both cut noninterlacing and empty pair arcs there. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves NanuqFaithfulSupplierDrawing Set Schoenflies
open scoped Graph Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)
variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)
local notation "M" => N.actualEveryNonleafRootedCapSource b hb
local notation "hl" => N.actual_admitted_cap_hybrid_child_is_taxon hg b hb
local notation "OG" => RootedBinary.openedHybridGraph (N.actualEveryNonleafRootedCapSource b hb)
  (N.actual_admitted_cap_hybrid_child_is_taxon hg b hb)

/-- Noninterlacing at ANY named raw boundary with the SAME actual outside.
This is the nonexistential use-site form needed to combine the two providers. -/
theorem actual_named_boundary_noninterlacing
    (face : TaxonOuterFace D N.leaf)
    {C : Set Schoenflies.Plane} (hC : IsJordanCurve C)
    (hface : Graph.face (graph (blobCurves D b)) (curve (blobCurves D b))
      (coordinates face.outside)=outside C)
    (f : (M).OpenedHybridEdge) (a c d e : (M).OpenedTip) (hac : a≠c) (hde : d≠e)
    (hq : (OG).OrientedQuartet f ((M).openedTipVertex a) ((M).openedTipVertex c)
      ((M).openedTipVertex d) ((M).openedTipVertex e))
    (A₁ A₂ : Set Schoenflies.Plane)
    (hcut : IsCutPair C (tipPoint N D b hg hb a) (tipPoint N D b hg hb c) A₁ A₂) :
    ¬(tipPoint N D b hg hb d∈A₁ ∧ tipPoint N D b hg hb e∈A₂) := by
  intro halt
  obtain ⟨k,hfk,ha,hc,hd,he⟩ :=
    actual_quartet_carrier_membership N D b hg hb f a c d e hac hde hq
  obtain ⟨hP,hPc,hQ,hQc,hPQ⟩ := actual_cut_carriers N D b hg hb k
  obtain ⟨hPdisk,hQdisk⟩ := actual_cut_carriers_closed_disk N D b hg k
    (coordinates face.outside) C hface
  exact Nanuq.ClosedDiskNoncrossing.closed_disk_noninterlacing hC hcut
    hP hPc.isPreconnected hQ hQc.isPreconnected hPQ hPdisk hQdisk
    ha hc hd he halt.1 halt.2

/-- ONE original raw Jordan boundary, selected before every original cut and
all actual equal-label pairs. Its raw-face identity remains in the output.
Finite circular-order/syntax interpretation and global original C remain separate. -/
theorem actual_shared_boundary_receiver
    (face : TaxonOuterFace D N.leaf)
    (hnt : ∃ u v : BlobVertex N.graph b, u≠v) :
    ∃ C : Set Schoenflies.Plane, IsJordanCurve C ∧
      Graph.face (graph (blobCurves D b)) (curve (blobCurves D b))
        (coordinates face.outside)=outside C ∧
      Function.Injective (tipPoint N D b hg hb) ∧
      (∀ t : (M).OpenedTip, tipPoint N D b hg hb t∈C) ∧
      (∀ (f : (M).OpenedHybridEdge) (a c d e : (M).OpenedTip), a≠c → d≠e →
        (OG).OrientedQuartet f ((M).openedTipVertex a) ((M).openedTipVertex c)
          ((M).openedTipVertex d) ((M).openedTipVertex e) →
        ∀ A₁ A₂ : Set Schoenflies.Plane,
          IsCutPair C (tipPoint N D b hg hb a) (tipPoint N D b hg hb c) A₁ A₂ →
          ¬(tipPoint N D b hg hb d∈A₁ ∧ tipPoint N D b hg hb e∈A₂)) ∧
      (∀ a c : (M).OpenedTip, a≠c → (M).openedTipLabel hl a=(M).openedTipLabel hl c →
        ∃ B : Set Schoenflies.Plane, B⊆C ∧
          IsArcBetween B (tipPoint N D b hg hb a) (tipPoint N D b hg hb c) ∧
          ∀ w : (M).OpenedTip, tipPoint N D b hg hb w∈B ↔ w=a ∨ w=c) := by
  obtain ⟨C,hC,hface,htips⟩ := actual_nontrivial_tip_boundary N D b hg hb face hnt
  refine ⟨C,hC,hface,tipPoint_injective N D b hg hb hnt,htips,?_,?_⟩
  · intro f a c d e hac hde hq A₁ A₂ hcut
    exact actual_named_boundary_noninterlacing N D b hg hb face hC hface
      f a c d e hac hde hq A₁ A₂ hcut
  · intro a c hac hlab
    exact actual_paired_tip_empty_boundary_arc N D b hg hb face hnt hC hface a c hac hlab

#print axioms actual_named_boundary_noninterlacing
#print axioms actual_shared_boundary_receiver
end Nanuq.OpenedCore
