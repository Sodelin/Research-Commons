import Init.Data.Rat
import Std

/-! Exact arithmetic and canonical wire parsing. Rational operations are the
standard Lean `Rat` implementation, whose denominator is positive and whose
numerator and denominator are coprime. Input integers are bounded at 256 bits;
derived arithmetic is unrestricted exact arithmetic. -/
namespace GParity.Rational

def wire (q : Rat) : String := s!"{q.num}/{q.den}"

def parseNat (s : String) : Option Nat := do
  let n ← s.toNat?
  if toString n == s then some n else none

def parseInt (s : String) : Option Int := do
  let n ← s.toInt?
  if toString n == s then some n else none

def parse (s : String) : Option Rat := do
  match s.splitOn "/" with
  | [a, b] =>
      let num ← parseInt a
      let den ← parseNat b
      if den == 0 || num.natAbs ≥ 2^256 || den ≥ 2^256 then none
      else
        let q := mkRat num den
        if wire q == s then some q else none
  | _ => none

def dot (a x : List Rat) : Rat :=
  (a.zipWith (· * ·) x).foldl (· + ·) 0

def line (label : String) (xs : List Rat) : String :=
  label ++ toString xs.length ++
    (if xs.isEmpty then "" else " " ++ String.intercalate " " (xs.map wire)) ++ "\n"

end GParity.Rational
