import ActualTipBoundary
import ClosedDiskNoncrossing

/-! UNCOMPILED actual-source receiver. One original raw boundary is selected
before every actual opened-tree quartet cut. This does not yet encode the
given GLOBAL taxon circular order or assert adjacent duplicate labels. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock
open G1OuterLabelledMultigraphCurves Set Schoenflies
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)
variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)
local notation "M" => N.actualEveryNonleafRootedCapSource b hb
local notation "OG" => RootedBinary.openedHybridGraph (N.actualEveryNonleafRootedCapSource b hb)
  (N.actual_admitted_cap_hybrid_child_is_taxon hg b hb)

/-- Genuine geometric no-alternation for the original opened occurrence-tip
cut witnesses. No order certificate, strict-interior carrier premise, generic
ordered tree, or switching source is substituted. Singleton remains separate. -/
theorem actual_opened_cuts_noninterlacing
    (face : TaxonOuterFace D N.leaf)
    (hnt : ∃ u v : BlobVertex N.graph b, u≠v) :
    ∃ C : Set Schoenflies.Plane, IsJordanCurve C ∧
      Function.Injective (tipPoint N D b hg hb) ∧
      (∀ t : (M).OpenedTip, tipPoint N D b hg hb t∈C) ∧
      ∀ (f : (M).OpenedHybridEdge) (a c d e : (M).OpenedTip), a≠c → d≠e →
        (OG).OrientedQuartet f ((M).openedTipVertex a) ((M).openedTipVertex c)
          ((M).openedTipVertex d) ((M).openedTipVertex e) →
        ∀ A₁ A₂ : Set Schoenflies.Plane,
          IsCutPair C (tipPoint N D b hg hb a) (tipPoint N D b hg hb c) A₁ A₂ →
          ¬(tipPoint N D b hg hb d∈A₁ ∧ tipPoint N D b hg hb e∈A₂) := by
  obtain ⟨C,hC,hinj,htips,hcarriers⟩ :=
    actual_all_cut_carriers_one_boundary N D b hg hb face hnt
  refine ⟨C,hC,hinj,htips,?_⟩
  intro f a c d e hac hde hq A₁ A₂ hcut halt
  obtain ⟨k,hfk,ha,hc,hd,he⟩ :=
    actual_quartet_carrier_membership N D b hg hb f a c d e hac hde hq
  obtain ⟨hP,hPc,hQ,hQc,hPQ,hPdisk,hQdisk⟩ := hcarriers k
  exact Nanuq.ClosedDiskNoncrossing.closed_disk_noninterlacing hC hcut
    hP hPc.isPreconnected hQ hQc.isPreconnected hPQ hPdisk hQdisk
    ha hc hd he halt.1 halt.2

#print axioms actual_opened_cuts_noninterlacing
end Nanuq.OpenedCore
