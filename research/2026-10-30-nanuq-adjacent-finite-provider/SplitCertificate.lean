import TreeEdgeSemantics
set_option debug.skipKernelTC false
namespace Nanuq.AdjacentCertificate

def checkNode (c : Nat → Nat → Nat) (m : Nat) (table : Table) (lo len : Nat) : Bool :=
  if 2 ≤ len ∧ lo+len ≤ m then
    (List.range len).all (fun k => if 0 < k then
      (table lo k).all (fun a => (table (lo+k) (len-k)).all
        (fun b => decide ((a ||| b ||| c lo len) ∈ table lo len)))
    else true)
  else true

theorem closed_of_rows (c : Nat → Nat → Nat) (m : Nat) (table : Table)
    (leaves : (List.range m).all (fun lo => decide (0 ∈ table lo 1)) = true)
    (rows : ∀ lo len, lo < m → len ≤ m → checkNode c m table lo len = true) :
    Closed c m table := by
  constructor
  · intro lo hlo
    exact of_decide_eq_true (List.all_eq_true.mp leaves lo (List.mem_range.mpr hlo))
  · intro lo len hlen hbound k hk hklen a ha b hb
    have h := rows lo len (by omega) (by omega)
    have hc : 2 ≤ len ∧ lo+len ≤ m := ⟨hlen,hbound⟩
    simp only [checkNode,if_pos hc,List.all_eq_true] at h
    have hh := h k (List.mem_range.mpr hklen)
    simp only [if_pos hk,List.all_eq_true] at hh
    exact of_decide_eq_true (hh a ha b hb)

theorem rows_of_finite_check (c : Nat → Nat → Nat) (m : Nat) (table : Table)
    (h : (List.range m).all (fun lo =>
      (List.range (m+1)).all (checkNode c m table lo)) = true) :
    ∀ lo len, lo < m → len ≤ m → checkNode c m table lo len = true := by
  intro lo len hlo hlen
  exact List.all_eq_true.mp (List.all_eq_true.mp h lo (List.mem_range.mpr hlo)) len
    (List.mem_range.mpr (by omega))

#print axioms closed_of_rows
end Nanuq.AdjacentCertificate
