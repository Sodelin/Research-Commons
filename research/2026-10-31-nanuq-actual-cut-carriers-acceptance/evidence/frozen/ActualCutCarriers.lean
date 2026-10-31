import CutSideCarrier
import ActualCoreCutClasses
import ActualCoreTipIdentity
import ActualOpenedCutLocality
import ActualCoreCurves

/-! UNCOMPILED coherent source draft. Actual original cut classes give compact,
connected, disjoint carriers in the SAME drawing. Boundary order/noncrossing
is not assumed or concluded. The full opened tree remains the syntax object. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves NanuqFaithfulSupplierDrawing Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)
variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)
local notation "M" => N.actualEveryNonleafRootedCapSource b hb
local notation "OG" => RootedBinary.openedHybridGraph (N.actualEveryNonleafRootedCapSource b hb)
  (N.actual_admitted_cap_hybrid_child_is_taxon hg b hb)

def tipPoint (t : (M).OpenedTip) : Schoenflies.Plane :=
  coordinates (corePoint N D b (collapse N b hg hb ((M).openedTipVertex t)))

theorem tipPoint_injective (hnt : ∃ u v : BlobVertex N.graph b, u≠v) :
    Function.Injective (tipPoint N D b hg hb) :=
  coordinates.injective.comp ((corePoint_injective N D b).comp
    (collapse_opened_tips_injective N b hg hb hnt))

def sourceCarrier (k : N.OriginalBlobArc b) : Set Schoenflies.Plane :=
  Nanuq.CutSideCarrier.carrier (coreGraph N b hg) (actualCoreCurves N D b hg)
    k ((coreGraph N b hg).source k)

def targetCarrier (k : N.OriginalBlobArc b) : Set Schoenflies.Plane :=
  Nanuq.CutSideCarrier.carrier (coreGraph N b hg) (actualCoreCurves N D b hg)
    k ((coreGraph N b hg).target k)

/-- Exact membership in the original opened-tree cut, not a new partition. -/
theorem tip_sourceCarrier_iff (k : N.OriginalBlobArc b) (t : (M).OpenedTip) :
    tipPoint N D b hg hb t ∈ sourceCarrier N D b hg k ↔
      (OG).ReachWithout (coreEdgeLift N b hg hb k)
        ((OG).source (coreEdgeLift N b hg hb k)) ((M).openedTipVertex t) := by
  change coordinates ((actualCoreCurves N D b hg).point
    (collapse N b hg hb ((M).openedTipVertex t))) ∈ _ ↔ _
  rw [sourceCarrier,Nanuq.CutSideCarrier.point_mem_carrier_iff,
    actual_opened_core_cut_iff,core_edge_collapsed_source]

theorem tip_targetCarrier_iff (k : N.OriginalBlobArc b) (t : (M).OpenedTip) :
    tipPoint N D b hg hb t ∈ targetCarrier N D b hg k ↔
      (OG).ReachWithout (coreEdgeLift N b hg hb k)
        ((OG).target (coreEdgeLift N b hg hb k)) ((M).openedTipVertex t) := by
  change coordinates ((actualCoreCurves N D b hg).point
    (collapse N b hg hb ((M).openedTipVertex t))) ∈ _ ↔ _
  rw [targetCarrier,Nanuq.CutSideCarrier.point_mem_carrier_iff,
    actual_opened_core_cut_iff,core_edge_collapsed_target]

/-- Separation is derived from the actual opened tree, with the exact forbidden ID. -/
theorem actual_cut_carriers (k : N.OriginalBlobArc b) :
    IsCompact (sourceCarrier N D b hg k) ∧ IsConnected (sourceCarrier N D b hg k) ∧
    IsCompact (targetCarrier N D b hg k) ∧ IsConnected (targetCarrier N D b hg k) ∧
    Disjoint (sourceCarrier N D b hg k) (targetCarrier N D b hg k) := by
  exact ⟨Nanuq.CutSideCarrier.carrier_compact _ _ _ _,
    Nanuq.CutSideCarrier.carrier_connected _ _ _ _,
    Nanuq.CutSideCarrier.carrier_compact _ _ _ _,
    Nanuq.CutSideCarrier.carrier_connected _ _ _ _,
    Nanuq.CutSideCarrier.carriers_disjoint _ _ _ _ _
      (actual_core_all_bridges N b hg hb k)⟩

/-- The actual raw-cycle supplier discharges hface at the geometric use site.
This implication never asserts strict interior for boundary-touching carriers. -/
theorem actual_cut_carriers_closed_disk (k : N.OriginalBlobArc b)
    (o : Schoenflies.Plane) (C : Set Schoenflies.Plane)
    (hface : Graph.face (graph (blobCurves D b)) (curve (blobCurves D b)) o =
      Schoenflies.outside C) :
    sourceCarrier N D b hg k ⊆ C ∪ Schoenflies.inside C ∧
    targetCarrier N D b hg k ⊆ C ∪ Schoenflies.inside C := by
  have h := actualCoreCurves_closed_disk N D b hg o C hface
  exact ⟨(Nanuq.CutSideCarrier.carrier_subset _ _ _ _).trans h,
    (Nanuq.CutSideCarrier.carrier_subset _ _ _ _).trans h⟩

/-- Every nontrivial original quartet witness supplies the retained cut ID and
four SAME-drawing points in its two compact, connected, disjoint carriers. -/
theorem actual_quartet_carrier_membership (f : (M).OpenedHybridEdge)
    (a c d e : (M).OpenedTip) (hac : a≠c) (hde : d≠e)
    (hq : (OG).OrientedQuartet f ((M).openedTipVertex a) ((M).openedTipVertex c)
      ((M).openedTipVertex d) ((M).openedTipVertex e)) :
    ∃ k : N.OriginalBlobArc b, f=coreEdgeLift N b hg hb k ∧
      tipPoint N D b hg hb a ∈ sourceCarrier N D b hg k ∧
      tipPoint N D b hg hb c ∈ sourceCarrier N D b hg k ∧
      tipPoint N D b hg hb d ∈ targetCarrier N D b hg k ∧
      tipPoint N D b hg hb e ∈ targetCarrier N D b hg k := by
  obtain ⟨k,rfl⟩ := actual_opened_quartet_core_id N b hg hb f a c d e hac hde hq
  exact ⟨k,rfl,(tip_sourceCarrier_iff N D b hg hb k a).mpr hq.1,
    (tip_sourceCarrier_iff N D b hg hb k c).mpr hq.2.1,
    (tip_targetCarrier_iff N D b hg hb k d).mpr hq.2.2.1,
    (tip_targetCarrier_iff N D b hg hb k e).mpr hq.2.2.2⟩

#print axioms actual_cut_carriers
#print axioms actual_quartet_carrier_membership
end Nanuq.OpenedCore
