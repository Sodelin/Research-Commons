import ActualBoundaryBlocks
import Mathlib.Data.List.Rotate

/-! UNCOMPILED support-derived canonical ranks. idxOf is used only on the
actual base support, never asserted globally injective. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.GraphReceiver
open Nanuq.Restriction Nanuq.BoundaryOrder
open scoped Classical
variable {X O : Type*}

theorem actual_block_support (code : X ↪ Nat) (label : O → X)
    (surj : Function.Surjective label) (xs : List O) (hall : ∀ t, t∈xs)
    (k : Nat) (base : List Nat) (dup : Nat → Bool)
    (hblocks : (xs.rotate k).map (fun t => code (label t))=blocks base dup) :
    ∀ z, z∈base ↔ ∃ x, code x=z := by
  intro z
  rw [← mem_blocks_iff base dup z,← hblocks,List.mem_map]
  constructor
  · rintro ⟨t,_,ht⟩
    exact ⟨label t,ht⟩
  · rintro ⟨x,hx⟩
    obtain ⟨t,rfl⟩ := surj x
    exact ⟨t,List.mem_rotate.mpr (hall t),hx⟩

theorem exists_canonical_port_rank (code : X ↪ Nat) (base : List Nat)
    (hnd : base.Nodup) (support : ∀ z, z∈base ↔ ∃ x, code x=z) :
    ∃ rank : X ≃ Fin base.length, ∀ x, (rank x).val=base.idxOf (code x) := by
  let f : X → Fin base.length := fun x =>
    ⟨base.idxOf (code x),List.idxOf_lt_length_iff.mpr ((support _).mpr ⟨x,rfl⟩)⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply code.injective
    exact (List.idxOf_inj ((support _).mpr ⟨x,rfl⟩)).mp (congrArg Fin.val h)
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨x,hx⟩ := (support base[j]).mp (List.getElem_mem j.isLt)
    refine ⟨x,Fin.ext ?_⟩
    change base.idxOf (code x)=j.val
    rw [hx]
    exact hnd.idxOf_getElem j.val j.isLt
  exact ⟨Equiv.ofBijective f ⟨hinj,hsurj⟩,fun _ => rfl⟩

#print axioms exists_canonical_port_rank
end Nanuq.GraphReceiver
