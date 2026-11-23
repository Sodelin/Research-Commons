import Lean

namespace GoldbachCutoff

/-- Exact decomposition, after scaling finite rational quantities if necessary. -/
theorem long_changes_by_at_most_twice_short_error
    (total shortA shortB longA longB model eps : Int)
    (splitA : total = shortA + longA)
    (splitB : total = shortB + longB)
    (lowA : model - eps ≤ shortA) (highA : shortA ≤ model + eps)
    (lowB : model - eps ≤ shortB) (highB : shortB ≤ model + eps) :
    -2 * eps ≤ longA - longB ∧ longA - longB ≤ 2 * eps := by
  omega

#print axioms long_changes_by_at_most_twice_short_error
end GoldbachCutoff
