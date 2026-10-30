import Reroot
import AdjacentSemantics
import Init.Data.BitVec.Lemmas
set_option debug.skipKernelTC false
namespace Nanuq.Restriction

def blocks (labels : List Nat) (dup : Nat → Bool) : List Nat :=
  labels.flatMap (fun x => if dup x then [x,x] else [x])

theorem blocks_filter (labels : List Nat) (dup keep : Nat → Bool) :
    (blocks labels dup).filter keep = blocks (labels.filter keep) dup := by
  induction labels with
  | nil => rfl
  | cons x xs ih =>
    cases hd : dup x <;> cases hk : keep x <;> simp [blocks,hd,hk,List.filter_append] at ih ⊢ <;> exact ih

theorem blocks_map (labels : List Nat) (dup dup' : Nat → Bool) (f : Nat → Nat)
    (h : ∀ x∈labels, dup' (f x)=dup x) :
    (blocks labels dup).map f = blocks (labels.map f) dup' := by
  induction labels with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : ∀ x∈xs, dup' (f x)=dup x := by intro y hy; exact h y (by simp [hy])
    cases hd : dup x <;> simp [blocks,hx,hd] <;> exact ih ht

def restrictedMask (labels : List Nat) (dup : Nat → Bool) : Nat :=
  (BitVec.ofBoolListLE (labels.map dup)).toNat

theorem restrictedMask_bound (labels : List Nat) (dup : Nat → Bool) :
    restrictedMask labels dup < 2^labels.length := by
  simpa only [restrictedMask,List.length_map] using
    (BitVec.ofBoolListLE (labels.map dup)).isLt

theorem restrictedMask_bit (labels : List Nat) (dup : Nat → Bool) (x : Nat) (hx : x∈labels) :
    (restrictedMask labels dup).testBit (labels.idxOf x) = dup x := by
  simp only [restrictedMask,BitVec.testBit_toNat,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,
    List.getElem?_map,List.getElem?_idxOf hx]
  rfl

theorem map_idxOf_nodup (labels : List Nat) (h : labels.Nodup) :
    labels.map labels.idxOf = List.range labels.length := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,h.idxOf_getElem]

theorem restricted_blocks_canonical (labels : List Nat) (h : labels.Nodup) (dup : Nat → Bool) :
    (blocks labels dup).map labels.idxOf =
      Nanuq.AdjacentCertificate.occurrenceLabels labels.length (restrictedMask labels dup) := by
  rw [blocks_map labels dup (restrictedMask labels dup).testBit labels.idxOf
    (fun x hx => restrictedMask_bit labels dup x hx),map_idxOf_nodup labels h]
  rfl

#print axioms restricted_blocks_canonical
#print axioms blocks_filter
end Nanuq.Restriction
