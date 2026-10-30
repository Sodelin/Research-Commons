import MeanSemantics
set_option debug.skipKernelTC false
namespace Nanuq.AdjacentCertificate

def queryOK (qs : List Quartet) (x y p q : Nat) : Bool :=
  if x≠y ∧ x≠p ∧ x≠q ∧ y≠p ∧ y≠q ∧ p≠q then
    decide (quartetIndex qs x y p q < qs.length) &&
    [x,y,p,q].all (fun z => (quartetAt qs x y p q).labels.contains z)
  else true

def queriesOK (n : Nat) : Bool :=
  (List.range n).all fun x => (List.range n).all fun y =>
    (List.range n).all fun p => (List.range n).all fun q => queryOK (quartets n) x y p q


theorem query_valid_of_check (n : Nat) (h : queriesOK n = true)
    (x y p q : Nat) (hx : x<n) (hy : y<n) (hp : p<n) (hq : q<n)
    (distinct : x≠y ∧ x≠p ∧ x≠q ∧ y≠p ∧ y≠q ∧ p≠q) :
    quartetIndex (quartets n) x y p q < (quartets n).length := by
  simp only [queriesOK,List.all_eq_true] at h
  have hh := h x (List.mem_range.mpr hx) y (List.mem_range.mpr hy)
    p (List.mem_range.mpr hp) q (List.mem_range.mpr hq)
  simp only [queryOK,if_pos distinct,Bool.and_eq_true] at hh
  exact of_decide_eq_true hh.1

#print axioms query_valid_of_check
end Nanuq.AdjacentCertificate
