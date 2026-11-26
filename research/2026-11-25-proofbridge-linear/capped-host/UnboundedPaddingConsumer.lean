import UnboundedPadding
import CappedLabeledGrid

namespace ResearchCommons.CappedPaddingLanguage
open ResearchCommons.CappedLabeledGrid

/-- The revised certificate drops in for the checked grid's old rank proof. -/
theorem existing_grid_preserves_via_wellFounded {V : Type} (base : V → V → Option Nat)
    (n k : Nat) (word : Nat → Nat) :
    Realizes (joined base (@edge n k)) word ↔ Realizes base word :=
  padding_preserves_of_bounded_rise base (@edge n k) rank (2*n) rank_bounded rank_rises word

#print axioms existing_grid_preserves_via_wellFounded
end ResearchCommons.CappedPaddingLanguage
