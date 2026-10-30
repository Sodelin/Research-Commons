import MeanSemantics
set_option debug.skipKernelTC false
namespace Nanuq.AdjacentCertificate

theorem boundary_anchor_formula (qs : List Quartet) (pattern a b c d : Nat)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    anchor qs pattern a d a c + anchor qs pattern a d b d -
    anchor qs pattern a d a d - anchor qs pattern a d b c =
    2 - (twiceMean qs pattern b c a d : Int) := by
  simp [anchor,hab,hac,had,hbc,hbd,hcd,Ne.symm hab,Ne.symm hac,Ne.symm had]
theorem twiceMean_lt_two_iff (qs : List Quartet) (pattern x y p q : Nat)
    (valid : code pattern (quartetIndex qs x y p q) ∈ ([1,4,5] : List Nat)) :
    twiceMean qs pattern x y p q < 2 ↔ displayedPair qs pattern x y p q = true := by
  let present := (List.range 3).filter (fun r => (code pattern (quartetIndex qs x y p q)).testBit r)
  let sep := fun r => (quartetAt qs x y p q).side r x != (quartetAt qs x y p q).side r y
  have card := present_card_one_or_two _ valid
  have hratio : 2*(present.filter sep).length / present.length < 2 ↔ (present.filter sep).length < present.length := by
    change present.length = 1 ∨ present.length = 2 at card
    rcases card with h | h <;> rw [h] <;> omega
  change 2*(present.filter sep).length / present.length < 2 ↔ _
  rw [hratio, List.length_filter_lt_length_iff_exists]
  simp only [present,sep,List.mem_filter,displayedPair,List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨r,⟨hr,hbit⟩,hs⟩
    exact ⟨r,hr,hbit,by simpa using hs⟩
  · rintro ⟨r,hr,hbit,hs⟩
    exact ⟨r,⟨hr,hbit⟩,by simpa using hs⟩
theorem boundary_anchor_positive_iff (qs : List Quartet) (pattern a b c d : Nat)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hbc : b≠c) (hbd : b≠d) (hcd : c≠d)
    (valid : code pattern (quartetIndex qs b c a d) ∈ ([1,4,5] : List Nat)) :
    0 < anchor qs pattern a d a c + anchor qs pattern a d b d -
      anchor qs pattern a d a d - anchor qs pattern a d b c ↔
      displayedPair qs pattern b c a d = true := by
  rw [boundary_anchor_formula qs pattern a b c d hab hac had hbc hbd hcd]
  have hcast : 0 < 2 - (twiceMean qs pattern b c a d : Int) ↔ twiceMean qs pattern b c a d < 2 := by omega
  rw [hcast,twiceMean_lt_two_iff qs pattern b c a d valid]

theorem pendant_anchor_two (qs : List Quartet) (pattern a b d : Nat)
    (hab : a≠b) (had : a≠d) (hbd : b≠d) :
    anchor qs pattern a d a b + anchor qs pattern a d b d -
      anchor qs pattern a d a d - anchor qs pattern a d b b = 2 := by
  simp [anchor,hab,had,hbd,Ne.symm hab]
#print axioms boundary_anchor_formula
#print axioms twiceMean_lt_two_iff
#print axioms boundary_anchor_positive_iff
#print axioms pendant_anchor_two
end Nanuq.AdjacentCertificate
