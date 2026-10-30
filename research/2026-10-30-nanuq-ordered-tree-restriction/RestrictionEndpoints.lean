import AllSizeCodes
import ZeroTransport
set_option debug.skipKernelTC false
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

/-- Original uniform DISTINCT-resolution rational mean at arbitrary size.
The inherited integer expression is exact, not a rounding surrogate. -/
theorem all_size_mean_exact (n mask : Nat) (T : Tree)
    (hs : T.size=(occurrenceLabels n mask).length-1)
    (x y p z : Nat) (hx : x<n) (hy : y<n) (hp : p<n) (hz : z<n)
    (hxy : x≠y) (hxp : x≠p) (hxz : x≠z) (hyp : y≠p) (hyz : y≠z) (hpz : p≠z) :
    (twiceMean (quartets n) (codedPattern T (occurrenceLabels n mask) n) x y p z : ℚ) =
      2 * (((List.range 3).filter (fun r =>
        (code (codedPattern T (occurrenceLabels n mask) n) (quartetIndex (quartets n) x y p z)).testBit r)).filter
        (fun r => (quartetAt (quartets n) x y p z).side r x != (quartetAt (quartets n) x y p z).side r y)).length /
      (((List.range 3).filter (fun r =>
        (code (codedPattern T (occurrenceLabels n mask) n) (quartetIndex (quartets n) x y p z)).testBit r)).length : ℚ) :=
  twiceMean_exact _ _ _ _ _ _ (all_size_query_code_valid n mask T hs x y p z hx hy hp hz hxy hxp hxz hyp hyz hpz)

theorem all_size_boundary_anchor_positive (n mask : Nat) (T : Tree)
    (hn : 3≤n) (hs : T.size=(occurrenceLabels n mask).length-1)
    (i j : Nat) (hi : i<n) (hj : j<n) (hij : i<j)
    (nonadj : i+1<j ∧ ¬(i=0 ∧ j+1=n)) :
    (0<alpha n (quartets n) (codedPattern T (occurrenceLabels n mask) n) i ((j+1)%n) i j) ↔
      displayedPair (quartets n) (codedPattern T (occurrenceLabels n mask) n) ((i+1)%n) j i ((j+1)%n)=true := by
  have hd := boundary_query_distinct n i j hn hi hj hij nonadj
  have hn0 : 0<n := by omega
  have valid := all_size_query_code_valid n mask T hs ((i+1)%n) j i ((j+1)%n)
    (Nat.mod_lt _ hn0) hj hi (Nat.mod_lt _ hn0) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2
  exact boundary_anchor_positive_iff _ _ i ((i+1)%n) j ((j+1)%n)
    (Ne.symm hd.2.1) (Ne.symm hd.2.2.2.1) hd.2.2.2.2.2 hd.1 hd.2.2.1 hd.2.2.2.2.1 valid

theorem cyclic_pendant_anchor_two (n : Nat) (qs : List Quartet) (pattern i : Nat)
    (hn : 3≤n) (hi : i<n) :
    alpha n qs pattern i ((((i+1)%n)+1)%n) i ((i+1)%n)=2 := by
  have hn0 : 0<n := by omega
  exact pendant_anchor_two qs pattern i ((i+1)%n) ((((i+1)%n)+1)%n)
    (Ne.symm (next_ne n i (by omega) hi)) (Ne.symm (next_next_ne n i hn hi))
    (Ne.symm (next_ne n ((i+1)%n) (by omega) (Nat.mod_lt _ hn0)))

#print axioms canonical_restriction
#print axioms finite_restriction
#print axioms construct_transport
#print axioms coefficient_transport
#print axioms all_size_anchor_nonnegative
#print axioms all_size_absent_boundary_zero
#print axioms all_size_query_code_valid
#print axioms all_size_mean_exact
#print axioms all_size_boundary_anchor_positive
#print axioms cyclic_pendant_anchor_two
end Nanuq.Restriction
