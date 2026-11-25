import Lean

namespace ResearchCommons.GoldbachTranspose

def IsMobiusSign (x : Int) : Prop := x = -1 ∨ x = 0 ∨ x = 1

/-- The exact sign identity for summing the two ordered orientations.
The zero cases retain the squarefreeness masks. -/
theorem orderedSignPair (q h : Int) (hq : IsMobiusSign q) (hh : IsMobiusSign h) :
    (if q ≠ 0 then h else 0) - (if h ≠ 0 then q else 0) =
      (if q * h = -1 then 2 * h else 0) := by
  rcases hq with hq | hq | hq <;> rcases hh with hh | hh | hh <;>
    rw [hq, hh] <;> decide

/-- An arbitrary common signed factor may represent a symmetric endpoint weight
and the oriented log ratio of the first ordered term. -/
theorem weightedOrderedSignPair (q h w : Int) (hq : IsMobiusSign q)
    (hh : IsMobiusSign h) :
    ((if q ≠ 0 then h else 0) - (if h ≠ 0 then q else 0)) * w =
      (if q * h = -1 then 2 * h else 0) * w := by
  rw [orderedSignPair q h hq hh]

#print axioms orderedSignPair
#print axioms weightedOrderedSignPair

end ResearchCommons.GoldbachTranspose
