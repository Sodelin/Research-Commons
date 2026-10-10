import GParity.Chart
import GParity.Polynomial

/-! Effective full-joint original-edge frontier genealogy compiler.
The algorithm is attributed to the 1 October supplied-source Python compiler.
Its source-program, physical image, and observed-bin refinements remain separate.
No independent marginal factorization replaces the retained frontier. -/
namespace GParity.Law
open GParity.Rational GParity.Polynomial

inductive Tree where
  | leaf : Nat → Tree
  | node : Tree → Tree → Tree
  deriving Repr, BEq
def Tree.least : Tree → Nat
  | .leaf i => i
  | .node a b => min a.least b.least
def Tree.wire : Tree → String
  | .leaf i => toString i
  | .node a b => "(" ++ a.wire ++ "," ++ b.wire ++ ")"
def Tree.leaves : Tree → List Nat
  | .leaf i => [i]
  | .node a b => a.leaves ++ b.leaves
def Tree.clusters : Tree → List (List Nat)
  | .leaf _ => []
  | t@(.node a b) => t.leaves :: (a.clusters ++ b.clusters)
def join (a b : Tree) : Tree := if a.least < b.least then .node a b else .node b a
abbrev Forest := List Tree
abbrev Frontier := List Forest
def forest (ts : Forest) : Forest := ts.mergeSort (fun a b => a.least ≤ b.least)
def forestWire (fs : Forest) : String := "[" ++ String.intercalate "," (fs.map Tree.wire) ++ "]"
def frontierWire (fs : Frontier) : String := String.intercalate "|" (fs.map forestWire)
def chooseTwo (k : Nat) : Nat := k*(k-1)/2

inductive Mechanism where
  | common | independent
  deriving Repr
structure Input where
  source : GParity.Chart.Source
  samples : List Nat
  mechanism : Mechanism
  stateCap : Nat
  termCap : Nat
  historyCap : Nat
  deriving Repr
def Input.dimension (i : Input) : Nat := i.source.edges.length+i.source.hybrids.length
structure Limit where
  kind : String
  vertex : Nat
  required : Nat
  cap : Nat
  deriving Repr
abbrev ForestCounts := List (Forest × Nat)

def addCount (states : ForestCounts) (fs : Forest) (n : Nat) : ForestCounts :=
  if states.any (fun (f,_) => f == fs) then
    states.map (fun (f,c) => (f, if f == fs then c+n else c))
  else states ++ [(fs,n)]
def mergeLevel (states : ForestCounts) : ForestCounts :=
  states.foldl (fun ans (fs,count) =>
    fs.zipIdx.foldl (fun ans (a,i) => fs.zipIdx.foldl (fun ans (b,j) =>
      if i < j then
        let others := fs.zipIdx.filterMap (fun (t,k) => if k == i || k == j then none else some t)
        addCount ans (forest (join a b :: others)) count
      else ans) ans) ans) []

def levelsGo (cap : Nat) : Nat → ForestCounts → List ForestCounts → Except Nat (List ForestCounts)
  | 0, _, acc => .ok acc
  | fuel+1, states, acc =>
      let k := ((states.head?).map (fun (f,_) => f.length)).getD 0
      if k ≤ 1 then .ok (acc ++ [states]) else
      let needed := states.length*chooseTwo k
      if needed > cap then .error needed else
      levelsGo cap fuel (mergeLevel states) (acc ++ [states])
def mergeLevels (start : Forest) (cap : Nat) : Except Nat (List ForestCounts) :=
  levelsGo cap (start.length+1) [(start,1)] []

def pathPolynomial (d edge k j : Nat) : Poly :=
  let rates := ((List.range (k-j+1)).map (fun r => chooseTwo (j+r)))
  normalize (rates.map (fun a =>
    let denominator := (rates.filter (· != a)).foldl
      (fun (z : Int) b => z*(Int.ofNat b-Int.ofNat a)) 1
    ⟨(List.range d).map (fun i => if i == edge then a else 0),
      (1 : Rat)/Rat.ofInt denominator⟩))

abbrev EdgeKernel := List (Forest × Poly)
def edgeKernel (d edge : Nat) (start : Forest) (cap : Nat) : Except Nat EdgeKernel := do
  if start.isEmpty then return [([],constant d 1)]
  let levels ← mergeLevels start cap
  return (levels.flatMap (fun states => states.map (fun (fs,count) =>
    (fs, scale (Rat.ofInt (Int.ofNat count)) (pathPolynomial d edge start.length fs.length))))).mergeSort
    (fun a b => forestWire a.1 ≤ forestWire b.1)
def rootKernel (start : Forest) (cap : Nat) : Except Nat (List (Tree × Rat)) := do
  let levels ← mergeLevels start cap
  let final := (levels.getLast?).getD []
  let denominator := ((List.range (start.length-1)).map (fun r => chooseTwo (r+2))).foldl (· * ·) 1
  return (final.filterMap (fun (fs,count) => fs.head?.map (fun t =>
    (t, Rat.ofInt (Int.ofNat count)/Rat.ofInt (Int.ofNat denominator))))).mergeSort
    (fun a b => a.1.wire ≤ b.1.wire)

def bits : Nat → List (List Bool)
  | 0 => [[]]
  | k+1 => (bits k).map (false :: ·) ++ (bits k).map (true :: ·)
def routes (d coordinate : Nat) (mechanism : Mechanism) (fs : Forest) : List (List Forest × Poly) :=
  let g := GParity.Polynomial.coordinate d coordinate
  let other := add (constant d 1) (scale (-1) g)
  match mechanism with
  | .common => [([fs,[]],g),([[],fs],other)]
  | .independent => (bits fs.length).map (fun bs =>
      let left := (fs.zip bs).filterMap (fun (t,b) => if b then none else some t)
      let right := (fs.zip bs).filterMap (fun (t,b) => if b then some t else none)
      ([left,right],multiply (power d g left.length) (power d other right.length)))

def topologicalGo (s : GParity.Chart.Source) : Nat → List Nat → List Nat → List Nat → List Nat
  | 0, _, _, ans => ans
  | fuel+1, todo, degrees, ans =>
      match todo.find? (fun v => (degrees[v]?).getD 0 == 0) with
      | none => ans
      | some v =>
          let degrees := s.edges.foldl (fun ds e => if e.source == v then
            ds.set e.target (((ds[e.target]?).getD 0)-1) else ds) degrees
          topologicalGo s fuel (todo.filter (· != v)) degrees (ans ++ [v])
def topological (s : GParity.Chart.Source) : List Nat :=
  topologicalGo s s.vertices (List.range s.vertices) ((List.range s.vertices).map s.inDegree) []

structure Prepared where
  base : Frontier
  edges : List Nat
  kernels : List EdgeKernel
  incoming : Poly
  route : Poly
  roots : Option (List (Tree × Rat))
  deriving Repr
def Prepared.stateWork (p : Prepared) : Nat :=
  match p.roots with
  | some rs => rs.length
  | none => (p.kernels.map List.length).foldl (· * ·) 1
def Prepared.termWork (p : Prepared) : Nat :=
  match p.roots with
  | some rs => p.incoming.length*rs.length
  | none => p.incoming.length*p.route.length*
      (p.kernels.map (fun k => (k.map (fun (_,q) => q.length)).foldl (· + ·) 0)).foldl (· * ·) 1
abbrev States := List (Frontier × Poly)

def prepare (input : Input) (v : Nat) (states : States) : Except Limit (List Prepared) := do
  let s := input.source
  let d := input.dimension
  let outgoing := s.edges.zipIdx.filterMap (fun (e,i) => if e.source == v then some i else none)
  let incoming := s.edges.zipIdx.filterMap (fun (e,i) => if e.target == v then some i else none)
  let sampled := input.samples.zipIdx.filterMap (fun (taxon,i) =>
    if (s.leaves[taxon]?) == some v then some (Tree.leaf i) else none)
  let mut prepared := []
  for (frontier,probability) in states do
    let live := forest (sampled ++ outgoing.flatMap (fun e => (frontier[e]?).getD []))
    let base := frontier.zipIdx.map (fun (f,e) => if outgoing.contains e then [] else f)
    if v == s.root then
      if base.any (fun f => !f.isEmpty) then throw ⟨"INTERNAL",v,0,0⟩
      let roots ← (rootKernel live input.historyCap).mapError (fun required =>
        ⟨"HISTORY",v,required,input.historyCap⟩)
      prepared := prepared ++ [⟨base,[],[],probability,constant d 1,some roots⟩]
    else
      let (edges,routed) := if incoming.length == 1 then
          (incoming,[([live],constant d 1)]) else
          let hybrid := ((s.hybrids.zipIdx.find? (fun (h,_) => h.vertex == v))).getD (⟨0,0,0⟩,0)
          ([hybrid.1.incoming0,hybrid.1.incoming1],
            routes d (s.edges.length+hybrid.2) input.mechanism live)
      for (groups,route) in routed do
        let kernels ← (groups.zip edges).mapM (fun (group,edge) =>
          (edgeKernel d edge group input.historyCap).mapError (fun required =>
            ⟨"HISTORY",v,required,input.historyCap⟩))
        prepared := prepared ++ [⟨base,edges,kernels,probability,route,none⟩]
  return prepared

def products : List EdgeKernel → List (List (Forest × Poly))
  | [] => [[]]
  | k :: ks => k.flatMap (fun item => (products ks).map (item :: ·))
def insertState (table : Std.HashMap String (Frontier × Poly)) (fs : Frontier) (p : Poly) :=
  let key := frontierWire fs
  let previous := ((table[key]?).map (·.2)).getD []
  table.insert key (fs,add previous p)
def insertTree (table : Std.HashMap String (Tree × Poly)) (tree : Tree) (p : Poly) :=
  let previous := ((table[tree.wire]?).map (·.2)).getD []
  table.insert tree.wire (tree,add previous p)

def emitPrepared (prepared : List Prepared) : States × List (Tree × Poly) := Id.run do
  let mut states : Std.HashMap String (Frontier × Poly) := {}
  let mut roots : Std.HashMap String (Tree × Poly) := {}
  for p in prepared do
    match p.roots with
    | some rs =>
        for (tree,q) in rs do
          roots := insertTree roots tree (scale q p.incoming)
    | none =>
        for transitions in products p.kernels do
          let fs := (p.edges.zip transitions).foldl (fun f (e,(group,_)) => f.set e group) p.base
          let q := transitions.foldl (fun q (_,k) => multiply q k) (multiply p.incoming p.route)
          states := insertState states fs q
  let stateList := ((states.toList.map (·.2)).filter (fun (_,p) => !p.isEmpty)).mergeSort
    (fun a b => frontierWire a.1 ≤ frontierWire b.1)
  let rootList := ((roots.toList.map (·.2)).filter (fun (_,p) => !p.isEmpty)).mergeSort
    (fun a b => a.1.wire ≤ b.1.wire)
  return (stateList,rootList)

def compileGo (input : Input) : List Nat → States → Except Limit (List (Tree × Poly))
  | [], _ => .ok []
  | v :: vs, states => do
      let prepared ← prepare input v states
      let stateWork := (prepared.map Prepared.stateWork).foldl (· + ·) 0
      if stateWork > input.stateCap then throw ⟨"STATE",v,stateWork,input.stateCap⟩
      let termWork := (prepared.map Prepared.termWork).foldl (· + ·) 0
      if termWork > input.termCap then throw ⟨"TERM",v,termWork,input.termCap⟩
      let (states,roots) := emitPrepared prepared
      if v == input.source.root then return roots else compileGo input vs states

def signature (s : Nat) (tree : Tree) : String :=
  let cuts := tree.clusters.filterMap (fun cluster =>
    let left := cluster.mergeSort (· ≤ ·)
    let right := (List.range s).filter (fun i => !left.contains i)
    if left.length ≥ 2 && right.length ≥ 2 then
      some (if lexLE left right then (left,right) else (right,left)) else none)
  let cuts := cuts.eraseDups.mergeSort (fun a b =>
    if a.1 == b.1 then lexLE a.2 b.2 else lexLE a.1 b.1)
  let side := fun xs => "[" ++ String.intercalate "," (xs.map toString) ++ "]"
  "[" ++ String.intercalate ";" (cuts.map (fun (a,b) => side a ++ "|" ++ side b)) ++ "]"
def unrooted (s : Nat) (rooted : List (Tree × Poly)) : List (String × Poly) :=
  let table := rooted.foldl (fun (m : Std.HashMap String Poly) (t,p) =>
    let key := signature s t
    m.insert key (add (m.getD key []) p)) {}
  (table.toList.filter (fun (_,p) => !p.isEmpty)).mergeSort (fun a b => a.1 ≤ b.1)
def compile (input : Input) : Except Limit (List (Tree × Poly) × List (String × Poly)) := do
  if (topological input.source).length != input.source.vertices then throw ⟨"INTERNAL",input.source.root,0,0⟩
  let rooted ← compileGo input (topological input.source).reverse
    [(List.replicate input.source.edges.length [],constant input.dimension 1)]
  return (rooted,unrooted input.samples.length rooted)

def parseLaw (v e l h samples stateCap termCap historyCap : Nat) (lines : List String) : Option Input := do
  if v < 3 || v > 32 || e < 2 || e > 32 || l < 2 || l > v || h > v ||
      v+e+1+h > 32 || samples < 1 || samples > 4 || stateCap > 4096 ||
      termCap > 65536 || historyCap > 4096 || lines.length != 3+e+l+h+samples then none
  else
    let mechanism ← match (← lines.head?).splitOn " " with
      | ["MECHANISM","COMMON"] => some Mechanism.common
      | ["MECHANISM","INDEPENDENT"] => some Mechanism.independent
      | _ => none
    let root ← match (← lines[1]?).splitOn " " with
      | ["ROOT",r] => parseNat r | _ => none
    let edges ← (lines.drop 2 |>.take e).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["EDGE",id,a,b] =>
          if (← parseNat id) != i then none else some (⟨← parseNat a,← parseNat b⟩ : GParity.Chart.Edge)
      | _ => none)
    let leaves ← (lines.drop (2+e) |>.take l).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["LEAF",id,a] => if (← parseNat id) != i then none else parseNat a
      | _ => none)
    let hybrids ← (lines.drop (2+e+l) |>.take h).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["HYBRID",id,a,p,q] =>
          if (← parseNat id) != i then none else
          some (⟨← parseNat a,← parseNat p,← parseNat q⟩ : GParity.Chart.Hybrid)
      | _ => none)
    let sampled ← (lines.drop (2+e+l+h) |>.take samples).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["SAMPLE",id,taxon] =>
          let taxon ← parseNat taxon
          if (← parseNat id) != i || taxon ≥ l then none else some taxon
      | _ => none)
    let source : GParity.Chart.Source := ⟨v,root,edges,leaves,hybrids⟩
    if !source.valid then none else some ⟨source,sampled,mechanism,stateCap,termCap,historyCap⟩

def preamble (input : Input) : String :=
  let variables := (List.range input.source.edges.length).map (fun i => s!"X:{i}") ++
    (List.range input.source.hybrids.length).map (fun i => s!"G:{i}")
  s!"VARIABLES {input.dimension} " ++ String.intercalate " " variables ++
    "\nGATE SOURCE_ADMISSION_NOT_ESTABLISHED\n"
def polynomialWire (p : Poly) : String := String.join (p.map (fun t =>
  "TERM " ++ wire t.coefficient ++ " " ++ String.intercalate " " (t.exponent.map toString) ++ "\n"))
def tableBody (input : Input) (rooted : List (Tree × Poly)) (unrooted : List (String × Poly)) : String :=
  preamble input ++ s!"STATUS TABLE\nROOTED {rooted.length}\n" ++
    String.join (rooted.map (fun (t,p) => s!"TREE {t.wire} {p.length}\n" ++ polynomialWire p)) ++
    s!"UNROOTED {unrooted.length}\n" ++
    String.join (unrooted.map (fun (t,p) => s!"SPLIT {t} {p.length}\n" ++ polynomialWire p))
def unknownBody (input : Input) (limit : Limit) : String :=
  preamble input ++ s!"STATUS UNKNOWN\nLIMIT {limit.kind} {limit.vertex} {limit.required} {limit.cap}\n"

end GParity.Law
