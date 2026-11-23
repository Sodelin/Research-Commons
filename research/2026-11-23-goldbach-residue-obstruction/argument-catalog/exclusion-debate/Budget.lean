import Lean

namespace GoldbachDebate

/-- After clearing denominators of positive rational weights, work over integers. -/
theorem target_positive_of_budget
    (target neighbor actualMain neighborMain lowerLoss upperLeak : Int)
    (aggregateLower : actualMain + neighborMain - lowerLoss ≤ target + neighbor)
    (neighborUpper : neighbor ≤ neighborMain + upperLeak)
    (budget : lowerLoss + upperLeak < actualMain) :
    0 < target := by
  omega

/-- Equality of the budget with the main term does not force positivity. -/
example :
    (5 : Int) + 8 - 2 ≤ 0 + 11 ∧ (11 : Int) ≤ 8 + 3 ∧
    (2 : Int) + 3 = 5 := by decide

#print axioms target_positive_of_budget
end GoldbachDebate
