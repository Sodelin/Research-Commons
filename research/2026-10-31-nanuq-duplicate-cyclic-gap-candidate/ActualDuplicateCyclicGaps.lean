import ActualFiniteBoundaryOrder
import SortedGaps

/-! UNCOMPILED. Exact existing CyclicGap receiver for the actual equal-label
occurrence pairs, retaining the SAME original boundary/order/cut witness.
The Nat code is merely an output encoding and is not a new network premise. -/
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

theorem actual_duplicate_cyclic_gaps
    (code : N.BlobPort b → Nat)
    (face : TaxonOuterFace D N.leaf)
    (hnt : ∃ u v : BlobVertex N.graph b, u≠v) :
    ∃ (C : Set Plane) (f : ℝ → Plane) (θ : (M).OpenedTip → ℝ) (xs : List (M).OpenedTip),
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
          (code ((M).openedTipLabel hl a)) (code ((M).openedTipLabel hl a))) := by
  classical
  obtain ⟨C,f,θ,xs,hC,hface,hf,himage,hθ,hθinj,hnd,hall,horder,hcuts,hgaps⟩ :=
    actual_finite_boundary_order N D b hg hb face hnt
  refine ⟨C,f,θ,xs,hC,hface,hf,himage,hθ,hθinj,hnd,hall,horder,hcuts,hgaps,?_⟩
  intro a c hac hlab
  let label : (M).OpenedTip → Nat := fun t => code ((M).openedTipLabel hl t)
  have hθne : θ a≠θ c := fun h => hac (hθinj h)
  have hlabel : label a=label c := congrArg code hlab
  rcases lt_or_gt_of_ne hθne with hlt | hgt
  · have h := Nanuq.Restriction.sorted_empty_gap_cyclicGap xs θ label hnd hθinj horder
      a c (hall a) (hall c) hlt (hgaps a c hlt hlab)
    rcases h with h | h
    · simpa only [← hlabel] using h
    · simpa only [← hlabel] using h
  · have h := Nanuq.Restriction.sorted_empty_gap_cyclicGap xs θ label hnd hθinj horder
      c a (hall c) (hall a) hgt (hgaps c a hgt hlab.symm)
    rcases h with h | h
    · simpa only [← hlabel] using h
    · simpa only [← hlabel] using h

#print axioms actual_duplicate_cyclic_gaps
end Nanuq.OpenedCore
