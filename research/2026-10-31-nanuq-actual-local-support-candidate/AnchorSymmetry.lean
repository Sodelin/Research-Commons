import ActualSortedAnchor

/-! UNCOMPILED coherent local-support helper. These identities concern the
EXACT stored finite definitions, including repeated coordinates. No source
probability exchangeability, circular-order certificate or new premise. -/
set_option debug.skipKernelTC false
namespace Nanuq.ActualFinite
open Nanuq.AdjacentCertificate

theorem quartetIndex_anchor_swap (qs : List Quartet) (x y p q : Nat) :
    quartetIndex qs x y p q = quartetIndex qs x y q p := by
  simp [quartetIndex, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

theorem quartetIndex_query_swap (qs : List Quartet) (x y p q : Nat) :
    quartetIndex qs x y p q = quartetIndex qs y x p q := by
  simp [quartetIndex, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

theorem twiceMean_anchor_swap (qs : List Quartet) (pattern x y p q : Nat) :
    twiceMean qs pattern x y p q = twiceMean qs pattern x y q p := by
  simp only [twiceMean, quartetAt, quartetIndex_anchor_swap qs x y p q]

theorem twiceMean_query_swap (qs : List Quartet) (pattern x y p q : Nat) :
    twiceMean qs pattern x y p q = twiceMean qs pattern y x p q := by
  have hb (a b : Bool) : (a != b) = (b != a) := by cases a <;> cases b <;> rfl
  simp only [twiceMean, quartetAt, quartetIndex_query_swap qs x y p q, hb]

theorem anchor_anchor_swap (qs : List Quartet) (pattern p q x y : Nat) :
    anchor qs pattern p q x y = anchor qs pattern q p x y := by
  simp only [anchor, twiceMean_anchor_swap qs pattern x y p q]
  simp only [eq_comm, and_comm, or_comm, or_left_comm, or_assoc]

theorem anchor_query_swap (qs : List Quartet) (pattern p q x y : Nat) :
    anchor qs pattern p q x y = anchor qs pattern p q y x := by
  simp only [anchor, twiceMean_query_swap qs pattern x y p q]
  simp only [eq_comm, and_comm, or_comm, or_left_comm, or_assoc]

theorem alpha_anchor_swap (n : Nat) (qs : List Quartet) (pattern p q i j : Nat) :
    alpha n qs pattern p q i j = alpha n qs pattern q p i j := by
  simp only [alpha, anchor_anchor_swap qs pattern p q]

theorem alpha_gap_swap (n : Nat) (qs : List Quartet) (pattern p q i j : Nat) :
    alpha n qs pattern p q i j = alpha n qs pattern p q j i := by
  simp only [alpha]
  rw [anchor_query_swap qs pattern p q j i,
    anchor_query_swap qs pattern p q ((j+1)%n) ((i+1)%n),
    anchor_query_swap qs pattern p q j ((i+1)%n),
    anchor_query_swap qs pattern p q ((j+1)%n) i]
  omega

end Nanuq.ActualFinite
