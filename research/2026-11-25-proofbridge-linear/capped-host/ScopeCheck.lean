import CappedConnectedBags
open ResearchCommons.CappedConnectedBags

namespace ResearchCommons.ScopeCheck
def cycle (x y : Fin 8) : Prop :=
  (x.val + 1) % 8 = y.val ∨ (y.val + 1) % 8 = x.val
instance (x y : Fin 8) : Decidable (cycle x y) := by unfold cycle; infer_instance

set_option maxHeartbeats 2000000 in
theorem no_four_cycle :
    ∀ a b c d : Fin 8,
      ¬ (a ≠ c ∧ b ≠ d ∧ cycle a b ∧ cycle b c ∧ cycle c d ∧ cycle d a) := by decide

#print axioms no_four_cycle
end ResearchCommons.ScopeCheck

namespace ResearchCommons.ScopeCheck

-- Pair adjacent vertices along the subdivided square; indices 0,1,2,3
-- run around the square, not in row-major order.
def fiber (i : Fin 4) : List (Fin 8) :=
  [⟨2*i.val, by omega⟩, ⟨2*i.val+1, by omega⟩]

def link (i j : Fin 4) : Prop :=
  ∃ a, a ∈ fiber i ∧ ∃ b, b ∈ fiber j ∧ cycle a b

instance (i j : Fin 4) : Decidable (link i j) := by unfold link; infer_instance

set_option maxHeartbeats 2000000 in
theorem strict_transfer_control :
    (∀ i : Fin 4, ∃ a b, a ≠ b ∧ fiber i = [a,b] ∧ cycle a b) ∧
    (∀ i j : Fin 4, i ≠ j → ∀ a : Fin 8, a ∈ fiber i → a ∉ fiber j) ∧
    link 0 1 ∧ link 1 2 ∧ link 2 3 ∧ link 3 0 ∧
    (∀ a b c d : Fin 8,
      ¬ (a ≠ c ∧ b ≠ d ∧ cycle a b ∧ cycle b c ∧ cycle c d ∧ cycle d a)) := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, no_four_cycle⟩

#print axioms strict_transfer_control
end ResearchCommons.ScopeCheck
