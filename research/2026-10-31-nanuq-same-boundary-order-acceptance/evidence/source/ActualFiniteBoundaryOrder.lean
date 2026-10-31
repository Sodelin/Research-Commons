import LoopOccurrenceOrder

/-! UNCOMPILED. Actual source occurrence order derived from one original raw
Jordan loop, with all cut and duplicate-label conditions in that same order.
The subsequent ordered-tree/list-block receiver and global C transport remain open. -/
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

/-- ONE boundary, loop, injective parameter map and sorted occurrence list.
No-alternation and empty duplicate gaps are DERIVED at this same choice. -/
theorem actual_finite_boundary_order
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
          (∀ w, ¬(θ w<θ a ∨ θ c<θ w))) := by
  obtain ⟨C,hC,hface,hinj,htips,hcuts,hpairs⟩ :=
    actual_shared_boundary_receiver N D b hg hb face hnt
  obtain ⟨f,θ,xs,hf,himage,hθ,hθinj,hnd,hall,horder⟩ :=
    finite_occurrence_parameters hC (tipPoint N D b hg hb) hinj htips
  refine ⟨C,f,θ,xs,hC,hface,hf,himage,hθ,hθinj,hnd,hall,horder,?_,?_⟩
  · intro k a c d e hq halt
    have hac : a≠c := by
      intro heq
      rcases halt with ⟨had,hdc,hce⟩ | ⟨hda,hae,hec⟩ <;> subst c <;> linarith
    have hde : d≠e := by
      intro heq
      rcases halt with ⟨had,hdc,hce⟩ | ⟨hda,hae,hec⟩ <;> subst e <;> linarith
    have hacθ : θ a<θ c := by
      rcases halt with ⟨had,hdc,hce⟩ | ⟨hda,hae,hec⟩ <;> linarith
    have hcut := parameter_cut_pair hf (hθ a).1 (hθ c).1 hacθ
    rw [himage,(hθ a).2,(hθ c).2] at hcut
    rcases halt with ⟨had,hdc,hce⟩ | ⟨hda,hae,hec⟩
    · apply hcuts k a c d e hac hde hq _ _ hcut
      constructor
      · exact ⟨θ d,⟨had.le,hdc.le⟩,(hθ d).2⟩
      · exact Or.inr ⟨θ e,⟨hce.le,(hθ e).1.2.le⟩,(hθ e).2⟩
    · apply hcuts k a c d e hac hde hq _ _ hcut.symm
      constructor
      · exact Or.inl ⟨θ d,⟨(hθ d).1.1,hda.le⟩,(hθ d).2⟩
      · exact ⟨θ e,⟨hae.le,hec.le⟩,(hθ e).2⟩
  · intro a c hac hlab
    have hne : a≠c := by intro heq; subst c; exact (lt_irrefl _ hac)
    obtain ⟨B,hBC,hB,honly⟩ := hpairs a c hne hlab
    apply empty_pair_arc_parameter_gap hf θ (fun t => (hθ t).1) hac
      (B:=B)
    · simpa only [(hθ a).2,(hθ c).2] using hB
    · exact himage.symm ▸ hBC
    · intro w
      simpa only [(hθ w).2] using honly w

#print axioms actual_finite_boundary_order
end Nanuq.OpenedCore
