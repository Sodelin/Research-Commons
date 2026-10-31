import ActualOpenedCore
import PortAttachmentLabels

/-! UNCOMPILED SOURCE DRAFT. Exact original opened-tip identities survive
core contraction on nontrivial blobs. Singleton deliberately separate. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (b : N.graph.Blob)
variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)
local notation "M" => N.actualEveryNonleafRootedCapSource b hb

/-- All actual occurrence tips, including both copies of a hybrid child label,
remain distinct under the actual core collapse. This is vertex identity, not
cyclic adjacency or a global taxon-order assertion. -/
theorem collapse_opened_tips_injective
    (hnt : ∃ u v : BlobVertex N.graph b, u ≠ v) :
    Function.Injective (fun t : (M).OpenedTip =>
      collapse N b hg hb ((M).openedTipVertex t)) := by
  intro a c h
  rcases a with p | e <;> rcases c with q | f
  · have hinner : N.originalPortInner b p.val = N.originalPortInner b q.val :=
      congrArg Subtype.val (Sum.inl.inj h)
    have hp : p.val = q.val :=
      Nanuq.PortAttachmentLabels.original_port_inner_injective N b hnt hinner
    exact congrArg Sum.inl (Subtype.ext hp)
  · cases h
  · cases h
  · have hraw : (occurrenceRaw N b hb e).val = (occurrenceRaw N b hb f).val :=
      congrArg Subtype.val (Sum.inr.inj h)
    have he : e.val = f.val :=
      (occurrenceRaw_original N b hb e).symm.trans
        ((congrArg Sum.inl hraw).trans (occurrenceRaw_original N b hb f))
    exact congrArg Sum.inr (Subtype.ext he)

#print axioms collapse_opened_tips_injective
end Nanuq.OpenedCore
