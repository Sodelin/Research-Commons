import GoldbachTranspose

open ResearchCommons.GoldbachTranspose

theorem exactWeightedReuse (q h w : Int) (hq : IsMobiusSign q) (hh : IsMobiusSign h) :
    ((if q ≠ 0 then h else 0) - (if h ≠ 0 then q else 0)) * w =
      (if q * h = -1 then 2 * h else 0) * w :=
  weightedOrderedSignPair q h w hq hh

#print axioms exactWeightedReuse
