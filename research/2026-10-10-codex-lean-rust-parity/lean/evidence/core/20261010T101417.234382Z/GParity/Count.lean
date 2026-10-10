import GParity.Rational

/-! Exact numerical evaluation of the inherited conditional-count bound.
The arithmetic result does not provide the source/count premise. -/
namespace GParity.Count

structure Input where
  b : Rat
  epsilon : Rat
  sigma : Rat
  M : Rat
  deriving Repr

structure Output where
  delta : Rat
  bound : Rat
  ceiling : Nat
  deriving Repr

def compute (i : Input) : Output :=
  let delta := min i.epsilon (i.sigma / (2 * (i.M + 1)))
  let bound := 2 * (1 + delta) / (i.b * delta)
  { delta, bound, ceiling := (bound.num.toNat + bound.den - 1) / bound.den }

end GParity.Count
