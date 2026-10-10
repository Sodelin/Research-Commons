import GParity.Rational

/-! Effective sparse rational polynomials, with a fixed original-variable bank.
This module is an executable carrier; mathematical refinements are separate. -/
namespace GParity.Polynomial

structure Term where
  exponent : List Nat
  coefficient : Rat
  deriving Repr, BEq
abbrev Poly := List Term

def lexLE : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then lexLE as bs else a < b

def normalize (terms : Poly) : Poly :=
  let sums := terms.foldl (fun (m : Std.HashMap (List Nat) Rat) t =>
    m.insert t.exponent (m.getD t.exponent 0 + t.coefficient)) {}
  ((sums.toList.filter (fun (_,q) => q != 0)).map (fun (e,q) => ⟨e,q⟩)).mergeSort
    (fun a b => lexLE a.exponent b.exponent)

def constant (d : Nat) (q : Rat) : Poly :=
  if q == 0 then [] else [⟨List.replicate d 0,q⟩]
def variable (d i : Nat) : Poly :=
  [⟨(List.range d).map (fun j => if j == i then 1 else 0),1⟩]
def scale (q : Rat) (p : Poly) : Poly :=
  if q == 0 then [] else p.map (fun t => { t with coefficient := q*t.coefficient })
def add (p q : Poly) : Poly := normalize (p ++ q)
def multiply (p q : Poly) : Poly := normalize (p.flatMap (fun a => q.map (fun b =>
  ⟨a.exponent.zipWith (· + ·) b.exponent, a.coefficient*b.coefficient⟩)))
def power (d : Nat) (p : Poly) : Nat → Poly
  | 0 => constant d 1
  | n+1 => multiply p (power d p n)
def sum (ps : List Poly) : Poly := ps.foldl add []

end GParity.Polynomial
