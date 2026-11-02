import GParity.Affine

/-! Literal original-ID natural cells, compiled to one joint rational bank.
The finite graph predicate follows `RootedBinary`; its typed-source refinement
and the intended active-exposure interpretation remain explicit obligations.
The ordered row convention preserves duplicates and maps to the inherited
finite-set compiler by semantic equality, not by a finset iteration order. -/
namespace GParity.Chart
open GParity.Rational GParity.Affine

structure Edge where
  source : Nat
  target : Nat
  deriving Repr
structure Hybrid where
  vertex : Nat
  incoming0 : Nat
  incoming1 : Nat
  deriving Repr
structure Source where
  vertices : Nat
  root : Nat
  edges : List Edge
  leaves : List Nat
  hybrids : List Hybrid
  deriving Repr
inductive AgeAtom where
  | node : Nat → AgeAtom
  | fixed : Rat → AgeAtom
  deriving Repr
inductive Comparison where
  | strict | weak | equal
  deriving Repr, BEq
structure AgeConstraint where
  kind : Comparison
  left : AgeAtom
  right : AgeAtom
  deriving Repr
structure Bound where
  value : Rat
  strict : Bool
  deriving Repr
structure Interval where
  lower : Option Bound
  upper : Option Bound
  deriving Repr
structure Exposure where
  population : Option Nat
  younger : AgeAtom
  older : AgeAtom
  interval : Interval
  deriving Repr
structure Input where
  source : Source
  chronology : List AgeConstraint
  exposures : List Exposure
  coins : List Interval
  cap : Nat
  deriving Repr

def Source.dimension (s : Source) : Nat := s.vertices + s.edges.length + 1 + s.hybrids.length
def Source.inDegree (s : Source) (v : Nat) : Nat := (s.edges.filter (fun e => e.target == v)).length
def Source.outDegree (s : Source) (v : Nat) : Nat := (s.edges.filter (fun e => e.source == v)).length
def Source.isHybrid (s : Source) (v : Nat) : Bool := s.inDegree v == 2 && s.outDegree v == 1

/-- Finite transitive closure; blocked vertices exclude both path endpoints. -/
def Source.reachable (s : Source) (start : Nat) (blocked : Option Nat) : List Nat :=
  if blocked == some start then [] else
  (List.range s.vertices).foldl (fun visited _ =>
    s.edges.foldl (fun visited e =>
      if visited.contains e.source && blocked != some e.target &&
          blocked != some e.source && !visited.contains e.target
      then visited ++ [e.target] else visited) visited) [start]

def Source.valid (s : Source) : Bool :=
  s.vertices > 0 && s.root < s.vertices && s.leaves.length ≥ 2 &&
  s.edges.all (fun e => e.source < s.vertices && e.target < s.vertices) &&
  s.leaves.all (fun v => v < s.vertices) &&
  s.leaves.eraseDups.length == s.leaves.length &&
  s.inDegree s.root == 0 && s.outDegree s.root == 2 &&
  s.leaves.all (fun v => s.inDegree v == 1 && s.outDegree v == 0) &&
  (s.hybrids.map (·.vertex)).eraseDups.length == s.hybrids.length &&
  s.hybrids.all (fun h => h.vertex < s.vertices && s.isHybrid h.vertex &&
    h.incoming0 < s.edges.length && h.incoming1 < s.edges.length &&
    h.incoming0 != h.incoming1 &&
    (s.edges[h.incoming0]?.map (·.target)) == some h.vertex &&
    (s.edges[h.incoming1]?.map (·.target)) == some h.vertex) &&
  (List.range s.vertices).all (fun v =>
    if v == s.root || s.leaves.contains v then true else
      (s.inDegree v == 1 && s.outDegree v == 2) ||
      (s.isHybrid v && (s.hybrids.map (·.vertex)).contains v)) &&
  s.edges.all (fun e => !(s.reachable e.target none).contains e.source) &&
  (List.range s.vertices).all (fun v => (s.reachable s.root none).contains v) &&
  (List.range s.vertices).all (fun v => v == s.root ||
    s.leaves.any (fun leaf => (s.reachable s.root (some v)).contains leaf))

structure Form where
  coeff : List Rat
  constant : Rat
  deriving Repr
def Form.const (n : Nat) (q : Rat) : Form := ⟨List.replicate n 0, q⟩
def Form.variable (n i : Nat) : Form := ⟨(List.range n).map (fun j => if i == j then 1 else 0), 0⟩
def Form.sub (f g : Form) : Form := ⟨f.coeff.zipWith (· - ·) g.coeff, f.constant - g.constant⟩
def Form.scale (q : Rat) (f : Form) : Form := ⟨f.coeff.map (fun a => q*a), q*f.constant⟩
def ageForm (s : Source) : AgeAtom → Form
  | .node i => Form.variable s.dimension i
  | .fixed q => Form.const s.dimension q

def affineRow (strict : Bool) (f g : Form) : Row :=
  ⟨f.coeff.zipWith (· - ·) g.coeff, g.constant-f.constant, strict, []⟩
def comparisonRows (kind : Comparison) (f g : Form) : List Row :=
  let row := affineRow (kind == .strict) f g
  if kind == .equal then [row, affineRow false g f] else [row]
def scaledRows (interval : Interval) (duration inverse : Form) : List Row :=
  (match interval.lower with
   | none => [] | some b => [affineRow b.strict (inverse.scale b.value) duration]) ++
  (match interval.upper with
   | none => [] | some b => [affineRow b.strict duration (inverse.scale b.value)])

def emitRows (input : Input) : List Row :=
  let s := input.source
  let n := s.dimension
  let zero := Form.const n 0
  let one := Form.const n 1
  let coin := fun h => Form.variable n (s.vertices+s.edges.length+1+h)
  let rows :=
    s.edges.flatMap (fun e => comparisonRows .strict (Form.variable n e.target) (Form.variable n e.source)) ++
    s.leaves.flatMap (fun v => comparisonRows .equal (Form.variable n v) zero) ++
    (List.range (s.edges.length+1)).flatMap (fun e => comparisonRows .strict zero (Form.variable n (s.vertices+e))) ++
    (List.range s.hybrids.length).flatMap (fun h => comparisonRows .strict zero (coin h)) ++
    (List.range s.hybrids.length).flatMap (fun h => comparisonRows .strict (coin h) one) ++
    input.chronology.flatMap (fun c => comparisonRows c.kind (ageForm s c.left) (ageForm s c.right)) ++
    input.exposures.flatMap (fun e => scaledRows e.interval
      ((ageForm s e.older).sub (ageForm s e.younger))
      (Form.variable n (s.vertices + e.population.getD s.edges.length))) ++
    input.coins.zipIdx.flatMap (fun (c,h) => scaledRows c (coin h) one)
  rows.zipIdx.map (fun (r,i) => { r with weights := (List.range rows.length).map (fun j => if i == j then 1 else 0) })

def bankNames (s : Source) : List String :=
  (List.range s.vertices).map (fun i => s!"AGE:{i}") ++
  (List.range s.edges.length).map (fun i => s!"RATE:{i}") ++ ["RATE:A"] ++
  (List.range s.hybrids.length).map (fun i => s!"COIN:{i}")

def parseAge (v : Nat) (token : String) : Option AgeAtom := do
  match token.splitOn ":" with
  | ["V", i] =>
      let i ← parseNat i
      if i < v then some (.node i) else none
  | ["Q", q] => some (.fixed (← parse q))
  | _ => none
def parseBound (token : String) : Option (Option Bound) := do
  if token == "NONE" then some none else
  match token.splitOn ":" with
  | ["LE", q] => some (some ⟨← parse q, false⟩)
  | ["LT", q] => some (some ⟨← parse q, true⟩)
  | _ => none
def parsePopulation (e : Nat) (token : String) : Option (Option Nat) := do
  if token == "A" then some none else
  match token.splitOn ":" with
  | ["E", i] =>
      let i ← parseNat i
      if i < e then some (some i) else none
  | _ => none

def parseChart (v e l h c x cap : Nat) (lines : List String) : Option Input := do
  if v < 3 || v > 32 || e < 2 || e > 32 || l < 2 || l > v ||
      h > v || c > 32 || x > 32 || cap > 4096 || v+e+1+h > 32 ||
      lines.length != 2+e+l+2*h+c+x then none
  else
    let root ← match (← lines.head?).splitOn " " with
      | ["ROOT", r] => parseNat r | _ => none
    let edges ← (lines.drop 1 |>.take e).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["EDGE", id, a, b] =>
          if (← parseNat id) != i then none else
          some (⟨← parseNat a, ← parseNat b⟩ : Edge)
      | _ => none)
    let leaves ← (lines.drop (1+e) |>.take l).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["LEAF", id, a] => if (← parseNat id) != i then none else parseNat a
      | _ => none)
    let hybrids ← (lines.drop (1+e+l) |>.take h).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["HYBRID", id, a, p, q] =>
          if (← parseNat id) != i then none else
          some (⟨← parseNat a, ← parseNat p, ← parseNat q⟩ : Hybrid)
      | _ => none)
    let chronology ← (lines.drop (1+e+l+h) |>.take c).mapM (fun s => do
      match s.splitOn " " with
      | ["AGE", kind, a, b] =>
          let kind ← if kind == "LT" then some Comparison.strict else
            if kind == "LE" then some Comparison.weak else if kind == "EQ" then some Comparison.equal else none
          some (⟨kind, ← parseAge v a, ← parseAge v b⟩ : AgeConstraint)
      | _ => none)
    let exposures ← (lines.drop (1+e+l+h+c) |>.take x).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["EXPOSURE", id, p, a, b, lo, hi] =>
          if (← parseNat id) != i then none else
          some (⟨← parsePopulation e p, ← parseAge v a, ← parseAge v b,
            ⟨← parseBound lo, ← parseBound hi⟩⟩ : Exposure)
      | _ => none)
    let coins ← (lines.drop (1+e+l+h+c+x) |>.take h).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["COIN", id, lo, hi] =>
          if (← parseNat id) != i then none else
          some (⟨← parseBound lo, ← parseBound hi⟩ : Interval)
      | _ => none)
    let input : Input := ⟨⟨v,root,edges,leaves,hybrids⟩,chronology,exposures,coins,cap⟩
    if !input.source.valid || (emitRows input).length > 128 then none else some input

def matrix (input : Input) (rows : List Row) : String :=
  s!"BANK {input.source.dimension} " ++ String.intercalate " " (bankNames input.source) ++ "\n" ++
  s!"MATRIX {input.source.dimension} {rows.length} {input.cap}\n" ++
  String.join (rows.map (fun r => (if r.strict then "LT " else "LE ") ++ wire r.bound ++
    " " ++ String.intercalate " " (r.coeff.map wire) ++ "\n")) ++
  "END_MATRIX\nGATE SOURCE_ADMISSION_NOT_ESTABLISHED\n"

end GParity.Chart
