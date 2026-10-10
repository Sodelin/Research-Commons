import GParity.Affine
import GParity.Count

namespace GParity.Protocol
open GParity.Rational GParity.Affine

structure AffineInput where
  n : Nat
  cap : Nat
  rows : List Row
  deriving Repr

inductive Request where
  | affine : AffineInput → Request
  | count : GParity.Count.Input → Request
  deriving Repr

def parseRow (n m i : Nat) (line : String) : Option Row := do
  match line.splitOn " " with
  | rel :: bound :: coeff =>
      let strict ← if rel == "LE" then some false else if rel == "LT" then some true else none
      let bound ← parse bound
      let coeff ← coeff.mapM parse
      if coeff.length != n then none
      else some { coeff, bound, strict, weights := (List.range m).map (fun j => if i == j then 1 else 0) }
  | _ => none

def parseRequest (raw : String) : Option Request := do
  if raw.utf8ByteSize > 65536 || !raw.endsWith "\n" ||
      !(raw.toList.all (fun c => c.toNat < 128)) then none
  else
    let lines := raw.splitOn "\n"
    let header ← lines.head?
    match header.splitOn " " with
    | ["RC1", "AFFINE", ns, ms, caps] =>
        let n ← parseNat ns
        let m ← parseNat ms
        let cap ← parseNat caps
        if n > 8 || m > 64 || cap > 4096 || lines.length != m+2 then none
        else
          let rows ← ((lines.drop 1).take m).zipIdx.mapM (fun (s,i) => parseRow n m i s)
          some (.affine ⟨n, cap, rows⟩)
    | ["RC1", "COUNT", bs, es, ss, ms] =>
        if lines.length != 2 then none
        else
          let b ← parse bs
          let epsilon ← parse es
          let sigma ← parse ss
          let M ← parse ms
          if b ≤ 0 || epsilon ≤ 0 || sigma ≤ 0 || M < 0 then none
          else some (.count ⟨b, epsilon, sigma, M⟩)
    | _ => none

def envelope (command raw body : String) : String :=
  s!"RC1 RESULT {command}\nBEGIN_REQUEST\n{raw}END_REQUEST\n{body}END\n"

def execute (raw : String) : String × UInt32 :=
  match parseRequest raw with
  | none => ("RC1 ERROR INVALID_REQUEST\n", 1)
  | some (.affine i) =>
      match solve i.n i.rows i.cap with
      | .sat x =>
          if checkWitness i.n i.rows x then
            (envelope "AFFINE" raw ("STATUS SAT\n" ++ line "WITNESS " x ++
              line "EVAL " (i.rows.map (fun r => r.eval x))), 0)
          else ("RC1 ERROR INTERNAL_CERTIFICATE\n", 1)
      | .unsat r =>
          if checkContradiction i.n i.rows r.weights then
            (envelope "AFFINE" raw ("STATUS UNSAT\n" ++ line "MULTIPLIERS " r.weights ++
              s!"BOUND {wire r.bound}\nSTRICT {if r.strict then "1" else "0"}\n"), 0)
          else ("RC1 ERROR INTERNAL_CERTIFICATE\n", 1)
      | .unknown n required cap =>
          (envelope "AFFINE" raw s!"STATUS UNKNOWN\nLIMIT {n} {required} {cap}\n", 2)
  | some (.count i) =>
      let o := GParity.Count.compute i
      (envelope "COUNT" raw (s!"STATUS CONDITIONAL_ARITHMETIC\nDELTA {wire o.delta}\n" ++
        s!"BOUND {wire o.bound}\nCEILING {o.ceiling}\nGATE UNKNOWN_SOURCE_PROVIDER\n"), 2)

end GParity.Protocol
