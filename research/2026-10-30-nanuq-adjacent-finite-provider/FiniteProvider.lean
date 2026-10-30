import AllAdjacentCopies
import BoundaryFormula
set_option debug.skipKernelTC false
namespace Nanuq.AdjacentCertificate

def treePattern (n mask : Nat) (t : Tree) : Nat :=
  t.summary (edgeContribution (occurrenceLabels n mask) (quartets n)) 1

theorem finite_anchor_nonnegative (n mask : Nat) (hn : 3≤n ∧ n≤6) (hm : mask<2^n)
    (t : Tree) (hs : t.size = (occurrenceLabels n mask).length-1)
    (p q i j : Nat) (hp : p<n) (hq : q<n) (hi : i<n) (hj : j<n)
    (hpq : p<q) (hij : i<j) :
    0 ≤ alpha n (quartets n) (treePattern n mask t) p q i j :=
  nonneg_of_check _ _ _ (all_adjacent_copy_trees n mask hn hm t hs) _ _ _ _ hp hq hi hj hpq hij

theorem finite_absent_boundary_zero (n mask : Nat) (hn : 3≤n ∧ n≤6) (hm : mask<2^n)
    (t : Tree) (hs : t.size = (occurrenceLabels n mask).length-1)
    (p q i j : Nat) (hp : p<n) (hq : q<n) (hi : i<n) (hj : j<n)
    (hpq : p<q) (hij : i<j) (nonadj : i+1<j ∧ ¬(i=0 ∧ j+1=n))
    (absent : displayedPair (quartets n) (treePattern n mask t) ((i+1)%n) j i ((j+1)%n) = false) :
    alpha n (quartets n) (treePattern n mask t) p q i j = 0 :=
  absent_zero_of_check _ _ _ (all_adjacent_copy_trees n mask hn hm t hs)
    _ _ _ _ hp hq hi hj hpq hij nonadj absent

theorem bounded_queries (n : Nat) (hn : 3≤n ∧ n≤6) : queriesOK n = true := by
  rcases hn with ⟨hlo,hhi⟩
  interval_cases n
  · exact queries3
  · exact queries4
  · exact queries5
  · exact queries6

theorem actual_query_code_valid (n mask : Nat) (hn : 3≤n ∧ n≤6) (hm : mask<2^n)
    (t : Tree) (hs : t.size = (occurrenceLabels n mask).length-1)
    (x y p q : Nat) (hx : x<n) (hy : y<n) (hp : p<n) (hq : q<n)
    (distinct : x≠y ∧ x≠p ∧ x≠q ∧ y≠p ∧ y≠q ∧ p≠q) :
    code (treePattern n mask t) (quartetIndex (quartets n) x y p q) ∈ ([1,4,5] : List Nat) :=
  code_valid_of_check _ _ _ (all_adjacent_copy_trees n mask hn hm t hs) _
    (query_valid_of_check _ (bounded_queries n hn) _ _ _ _ hx hy hp hq distinct)

#print axioms finite_anchor_nonnegative
#print axioms finite_absent_boundary_zero
#print axioms actual_query_code_valid
#print axioms Tree.code_physical_iff
#print axioms twiceMean_exact
#print axioms boundary_anchor_positive_iff
#print axioms pendant_anchor_two
end Nanuq.AdjacentCertificate
