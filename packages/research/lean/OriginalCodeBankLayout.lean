import G7OriginalAdmission
import NativeOrderedBankLayout

/-!
Source-only use-site of the checked generic index layout.

This file has not been elaborated in the complete native import context.
It reuses the original finite-code decoder and registry, preserving its
explicit BinaryValid/RegistryValid premises and original parent bits.
-/
namespace Astra.OriginalCodeBankLayout

open Nanuq.Source
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open UnifiedLean.Source.NativeParentRouting

variable {X ID : Type*} [Fintype X] [Fintype ID]
variable [DecidableEq X] [DecidableEq ID] {nh : ℕ}

/-- The supplied ID order must be the native ORIGINAL hybrid occurrence order. -/
noncomputable def layout (c : Code X ID) (hb : BinaryValid c)
    (hr : RegistryValid c) (idOrder : ID ≃ Fin nh) :
    (NV (X := X) (ID := ID) ⊕
      (Option (NE (X := X) (ID := ID)) ⊕ Hybrid (sourceOfValid c hb))) ≃
      Fin (vertexCount (Fintype.card X) (Fintype.card ID) +
        edgeCount (Fintype.card X) (Fintype.card ID) + 1 + nh) :=
  Astra.NativeOrderedBankLayout.bankEquiv
    (Equiv.refl (NV (X := X) (ID := ID)))
    (Equiv.refl (NE (X := X) (ID := ID)))
    ((decodedIDs c hb hr).symm.trans idOrder)

theorem age_position (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (idOrder : ID ≃ Fin nh) (v : NV (X := X) (ID := ID)) :
    (layout c hb hr idOrder (.inl v)).val = v.val := by
  simp [layout]

theorem edge_position (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (idOrder : ID ≃ Fin nh) (e : NE (X := X) (ID := ID)) :
    (layout c hb hr idOrder (.inr (.inl (some e)))).val =
      vertexCount (Fintype.card X) (Fintype.card ID) + e.val := by
  simp [layout]

theorem ancestral_position (c : Code X ID) (hb : BinaryValid c)
    (hr : RegistryValid c) (idOrder : ID ≃ Fin nh) :
    (layout c hb hr idOrder (.inr (.inl none))).val =
      vertexCount (Fintype.card X) (Fintype.card ID) +
        edgeCount (Fintype.card X) (Fintype.card ID) := by
  simp [layout]

theorem hybrid_position (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (idOrder : ID ≃ Fin nh) (i : ID) :
    (layout c hb hr idOrder (.inr (.inr (decodedIDs c hb hr i)))).val =
      vertexCount (Fintype.card X) (Fintype.card ID) +
        edgeCount (Fintype.card X) (Fintype.card ID) + 1 + (idOrder i).val := by
  simp [layout]

/-- Reuse the exact existing original-parent occurrence theorem. -/
theorem parent_occurrence (c : Code X ID) (hb : BinaryValid c)
    (hr : RegistryValid c) (i : ID) (b : Bool) :
    ((decodedRegistry c hb hr).parents (decodedIDs c hb hr i)).parent b =
      codeParent c i b :=
  decoded_parent_exact c hb hr i b

end Astra.OriginalCodeBankLayout
