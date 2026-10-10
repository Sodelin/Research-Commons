import GParity.Rational

/-! Deterministic exact strict Fourier--Motzkin execution. Projection preserves
zero rows in input order, then combines positive outer/negative inner rows. No
row rescaling or deduplication occurs. Original-row multipliers follow every
projection step. The formal source-typed arithmetic theorem is supplied by
`StrictAffineElimination`; refinement of this wire representation is a separate
checked module, rather than an assumption of this executable. -/
namespace GParity.Affine
open GParity.Rational

structure Row where
  coeff : List Rat
  bound : Rat
  strict : Bool
  weights : List Rat
  deriving Repr, BEq

def Row.eval (r : Row) (x : List Rat) : Rat := dot r.coeff x

def Row.holds (r : Row) (x : List Rat) : Bool :=
  if r.strict then decide (r.eval x < r.bound) else decide (r.eval x ≤ r.bound)

def Row.last (r : Row) : Rat := r.coeff.getLast?.getD 0

def Row.drop (n : Nat) (r : Row) : Row := { r with coeff := r.coeff.take n }

def Row.combine (n : Nat) (p m : Row) : Row :=
  let cp := -m.last
  let cm := p.last
  { coeff := (p.coeff.take n).zipWith (fun a b => cp*a + cm*b) (m.coeff.take n)
    bound := cp*p.bound + cm*m.bound
    strict := m.strict || p.strict
    weights := p.weights.zipWith (fun a b => cp*a + cm*b) m.weights }

def zeros (rows : List Row) : List Row := rows.filter (fun r => r.last == 0)
def positives (rows : List Row) : List Row := rows.filter (fun r => decide (0 < r.last))
def negatives (rows : List Row) : List Row := rows.filter (fun r => decide (r.last < 0))

def projectedSize (rows : List Row) : Nat :=
  (zeros rows).length + (positives rows).length * (negatives rows).length

def projectList (n : Nat) (rows : List Row) : List Row :=
  (zeros rows).map (Row.drop n) ++
  (positives rows).flatMap (fun p => (negatives rows).map (Row.combine n p))

structure Endpoint where
  value : Rat
  strict : Bool
  deriving Repr

def endpoint (n : Nat) (r : Row) (x : List Rat) : Endpoint :=
  ⟨(r.bound - dot (r.coeff.take n) x) / r.last, r.strict⟩

def lowerExtremum (xs : List Endpoint) : Option Endpoint := xs.foldl
  (fun acc x => match acc with
    | none => some x
    | some y =>
        if y.value < x.value then some x
        else if x.value == y.value then some ⟨y.value, y.strict || x.strict⟩
        else some y) none

def upperExtremum (xs : List Endpoint) : Option Endpoint := xs.foldl
  (fun acc x => match acc with
    | none => some x
    | some y =>
        if x.value < y.value then some x
        else if x.value == y.value then some ⟨y.value, y.strict || x.strict⟩
        else some y) none

def chooseLast (n : Nat) (rows : List Row) (x : List Rat) : Rat :=
  let lower := lowerExtremum ((negatives rows).map (fun r => endpoint n r x))
  let upper := upperExtremum ((positives rows).map (fun r => endpoint n r x))
  match lower, upper with
  | none, none => 0
  | some a, none => a.value + 1
  | none, some b => b.value - 1
  | some a, some b => if a.value < b.value then (a.value + b.value) / 2 else a.value

inductive Outcome where
  | sat : List Rat → Outcome
  | unsat : Row → Outcome
  | unknown : Nat → Nat → Nat → Outcome
  deriving Repr

def solve : Nat → List Row → Nat → Outcome
  | 0, rows, _ =>
      match rows.find? (fun r => !(r.holds [])) with
      | some r => .unsat r
      | none => .sat []
  | n+1, rows, cap =>
      let required := projectedSize rows
      if cap < required then .unknown (n+1) required cap
      else
        match solve n (projectList n rows) cap with
        | .sat x => .sat (x ++ [chooseLast n rows x])
        | .unsat r => .unsat r
        | .unknown n required cap => .unknown n required cap

def checkWitness (n : Nat) (rows : List Row) (x : List Rat) : Bool :=
  x.length == n && rows.all (fun r => r.coeff.length == n) && rows.all (fun r => r.holds x)

/-- Independent arithmetic checking of the emitted contradiction against the
original rows; no projection trace is required by the consumer. -/
def checkContradiction (n : Nat) (rows : List Row) (weights : List Rat) : Bool :=
  let weighted := rows.zip weights
  let bounds : Rat := weighted.foldl (fun a rw => a + rw.2 * rw.1.bound) 0
  weights.length == rows.length && rows.all (fun r => r.coeff.length == n) &&
    weights.all (fun w => decide (0 ≤ w)) &&
    (List.range n).all (fun j =>
      weighted.foldl (fun a rw => a + rw.2 * (rw.1.coeff[j]?.getD 0)) 0 == 0) &&
    (decide (bounds < 0) ||
      (bounds == 0 && weighted.any (fun rw => rw.1.strict && decide (0 < rw.2))))

end GParity.Affine
