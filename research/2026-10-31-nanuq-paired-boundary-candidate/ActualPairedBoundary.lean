import HybridTailGeometry

/-! UNCOMPILED source-facing paired occurrence witness. The output is a
literal arc of the SAME original Jordan boundary with no intervening actual
occurrence point, not an assumed finite circular ordering. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves NanuqFaithfulSupplierDrawing Set Schoenflies
open Nanuq.CapCurves
open scoped Graph Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)
variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)
local notation "M" => N.actualEveryNonleafRootedCapSource b hb
local notation "hl" => N.actual_admitted_cap_hybrid_child_is_taxon hg b hb

/-- Distinct equal-labelled actual tips are the two incoming occurrences of
one hybrid. This reuses the original hybrid-child taxon injectivity, not a new
restriction on the label map. -/
theorem equal_label_distinct_are_hybrid_occurrences
    (a c : (M).OpenedTip) (hac : a≠c)
    (hlab : (M).openedTipLabel hl a=(M).openedTipLabel hl c) :
    ∃ e f : (M).HybridParentOccurrence, a=Sum.inr e ∧ c=Sum.inr f ∧ e≠f ∧
      (M).graph.target e.val=(M).graph.target f.val := by
  rcases a with p | e <;> rcases c with q | f
  · have hpq : p.val=q.val := hlab
    exact False.elim (hac (congrArg Sum.inl (Subtype.ext hpq)))
  · have hn := (M).hybridChildTaxon_not_ordinary hl ⟨(M).graph.target f.val,f.property⟩
    exact False.elim (hn (by
      change p.val=(M).hybridChildTaxon hl ⟨(M).graph.target f.val,f.property⟩ at hlab
      rw [← hlab]
      exact p.property))
  · have hn := (M).hybridChildTaxon_not_ordinary hl ⟨(M).graph.target e.val,e.property⟩
    exact False.elim (hn (by
      change (M).hybridChildTaxon hl ⟨(M).graph.target e.val,e.property⟩=q.val at hlab
      rw [hlab]
      exact q.property))
  · refine ⟨e,f,rfl,rfl,fun h => hac (congrArg Sum.inr h),?_⟩
    exact congrArg Subtype.val ((M).hybridChildTaxon_injective hl hlab)

/-- Geometric paired adjacency witness on the actual named raw boundary.
Whole-tail coverage comes from original face identity, not midpoint membership. -/
theorem actual_paired_tip_empty_boundary_arc
    (face : TaxonOuterFace D N.leaf)
    (hnt : ∃ u v : BlobVertex N.graph b, u≠v)
    {C : Set Schoenflies.Plane} (hC : IsJordanCurve C)
    (hface : Graph.face (graph (blobCurves D b)) (curve (blobCurves D b))
      (coordinates face.outside)=outside C)
    (a c : (M).OpenedTip) (hac : a≠c)
    (hlab : (M).openedTipLabel hl a=(M).openedTipLabel hl c) :
    ∃ B : Set Schoenflies.Plane, B⊆C ∧
      IsArcBetween B (tipPoint N D b hg hb a) (tipPoint N D b hg hb c) ∧
      ∀ w : (M).OpenedTip, tipPoint N D b hg hb w∈B ↔ w=a ∨ w=c := by
  obtain ⟨e,f,rfl,rfl,hef,ht⟩ := equal_label_distinct_are_hybrid_occurrences N b hg hb a c hac hlab
  let er := occurrenceRaw N b hb e
  let fr := occurrenceRaw N b hb f
  have herfr : er≠fr := by
    intro heq
    apply hef
    apply Subtype.ext
    rw [← occurrenceRaw_original N b hb e,← occurrenceRaw_original N b hb f]
    exact congrArg Sum.inl (congrArg Subtype.val heq)
  have htarget : N.graph.target er.val.val=N.graph.target fr.val.val := by
    rw [← occurrenceRaw_original N b hb e,← occurrenceRaw_original N b hb f] at ht
    change Sum.inl (⟨N.graph.target er.val.val,er.val.property.2⟩ : N.OriginalBlobVertex b)=
      Sum.inl (⟨N.graph.target fr.val.val,fr.val.property.2⟩ : N.OriginalBlobVertex b) at ht
    exact congrArg Subtype.val (Sum.inl.inj ht)
  let B := incomingTail N D b er ∪ incomingTail N D b fr
  have hB : IsArcBetween B (tipPoint N D b hg hb (Sum.inr e))
      (tipPoint N D b hg hb (Sum.inr f)) :=
    paired_incoming_tail_arc N D b er fr herfr htarget
  have htail : ∀ k : CoreTip N b, incomingTail N D b k ⊆ C := by
    intro k z hz
    obtain ⟨t,ht,rfl⟩ := hz
    let tI : unitInterval := ⟨t,by constructor <;> linarith [ht.1,ht.2]⟩
    rw [show curve D k.val.val t=coordinates (D.arc k.val.val tI) from curve_on_interval D k.val.val tI]
    exact named_boundary_incoming_full N D b hg hb face hnt hC hface k tI
  refine ⟨B,Set.union_subset (htail er) (htail fr),hB,?_⟩
  intro w
  constructor
  · intro hw
    have hinj := tipPoint_injective N D b hg hb hnt
    rcases hw with hw | hw
    · left
      have hv := incomingTail_only_core_tip N D b er (collapse N b hg hb ((M).openedTipVertex w)) hw
      apply hinj
      change coordinates (corePoint N D b (collapse N b hg hb ((M).openedTipVertex w))) =
        coordinates (corePoint N D b (Sum.inr er))
      rw [hv]
    · right
      have hv := incomingTail_only_core_tip N D b fr (collapse N b hg hb ((M).openedTipVertex w)) hw
      apply hinj
      change coordinates (corePoint N D b (collapse N b hg hb ((M).openedTipVertex w))) =
        coordinates (corePoint N D b (Sum.inr fr))
      rw [hv]
  · rintro (rfl | rfl)
    · exact hB.left_mem
    · exact hB.right_mem

/-- One original named raw boundary supports every actual equal-label pair.
Finite circular-order interpretation, singleton and global assembly are separate. -/
theorem actual_one_boundary_paired_tip_arcs
    (face : TaxonOuterFace D N.leaf)
    (hnt : ∃ u v : BlobVertex N.graph b, u≠v) :
    ∃ C : Set Schoenflies.Plane, IsJordanCurve C ∧
      Graph.face (graph (blobCurves D b)) (curve (blobCurves D b))
        (coordinates face.outside)=outside C ∧
      (∀ t : (M).OpenedTip, tipPoint N D b hg hb t∈C) ∧
      ∀ a c : (M).OpenedTip, a≠c → (M).openedTipLabel hl a=(M).openedTipLabel hl c →
        ∃ B : Set Schoenflies.Plane, B⊆C ∧
          IsArcBetween B (tipPoint N D b hg hb a) (tipPoint N D b hg hb c) ∧
          ∀ w : (M).OpenedTip, tipPoint N D b hg hb w∈B ↔ w=a ∨ w=c := by
  obtain ⟨C,hC,hface,htips⟩ := actual_nontrivial_tip_boundary N D b hg hb face hnt
  exact ⟨C,hC,hface,htips,fun a c hac hlab =>
    actual_paired_tip_empty_boundary_arc N D b hg hb face hnt hC hface a c hac hlab⟩

#print axioms equal_label_distinct_are_hybrid_occurrences
#print axioms actual_paired_tip_empty_boundary_arc
#print axioms actual_one_boundary_paired_tip_arcs
end Nanuq.OpenedCore
