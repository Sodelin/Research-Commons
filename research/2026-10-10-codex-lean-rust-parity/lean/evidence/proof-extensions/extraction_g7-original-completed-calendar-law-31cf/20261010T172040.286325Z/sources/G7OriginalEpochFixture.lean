import G7FullEpochSupport
import G6TwoTipChartFixture
import Mathlib.Tactic.FinCases
import Lean.Data.Json

/-!
# Original sparse whole-epoch evaluator fixtures

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Executes the support baseline whose generic full polynomial identity is proved
in G7FullEpochSupport. Complete ordered selected views, literal original Code
witnesses, all population IDs and the full entering register are serialized.
The exact normal-form serializer is a finite test utility; no universal Rust
or serializer refinement theorem is asserted. Draft pending fresh checking.
-/
namespace UnifiedLean.G7.OriginalEpochFixture
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.SparseRowProducts GProgram.G7.FullEpochSupport

abbrev N := UnifiedLean.G6.TwoTipChartFixture.source

def singletonState {n : Nat} (location : Fin n → Location (Fin 3) (Fin 2))
    (register : Fin 3 → Bool) : State (Fin 3) (Fin 2) (Fin n) where
  live := Finset.univ
  ancestor x := x
  genealogy := Genealogy.leaf
  location := location
  register := register
  history := []

theorem singletonState_valid {n : Nat} (location : Fin n → Location (Fin 3) (Fin 2))
    (register : Fin 3 → Bool) : Valid (singletonState location register) := by
  constructor
  · intro x; exact Finset.mem_univ x
  · intro l _; rfl
  · intro l _ x; simp [singletonState,Genealogy.leaves]
  · intro l _; trivial

def rootState (n : Nat) : State (Fin 3) (Fin 2) (Fin n) :=
  singletonState (fun _ => .rootPopulation N.root) (fun _ => false)

theorem rootState_sourceValid (n : Nat) (sample : Fin n → Fin 2) :
    SourceValid N sample (rootState n) := by
  refine ⟨singletonState_valid _ _,?_⟩
  intro x
  exact ⟨rfl,N.rooted (N.leaf (sample x))⟩

def rootCode (n : Nat) (sample : Fin n → Fin 2) : Code N sample :=
  encodeActual N sample (rootState n) (rootState_sourceValid n sample)

def twoEdgeSample (x : Fin 4) : Fin 2 := if x.val < 2 then 0 else 1
def twoEdgeState : State (Fin 3) (Fin 2) (Fin 4) :=
  singletonState (fun x => .edge (twoEdgeSample x)) (fun _ => false)

theorem twoEdgeState_sourceValid : SourceValid N twoEdgeSample twoEdgeState := by
  refine ⟨singletonState_valid _ _,?_⟩
  intro x
  change N.graph.DReach (N.graph.target (twoEdgeSample x)) (N.leaf (twoEdgeSample x))
  exact .refl

def twoEdgeCode : Code N twoEdgeSample :=
  encodeActual N twoEdgeSample twoEdgeState twoEdgeState_sourceValid

def edgeAncestralSample (x : Fin 4) : Fin 2 := if x.val < 3 then 0 else 1
def edgeAncestralState (register : Fin 3 → Bool) : State (Fin 3) (Fin 2) (Fin 4) :=
  singletonState (fun x => if x.val < 2 then .edge 0 else .rootPopulation N.root) register

theorem edgeAncestralState_sourceValid (register : Fin 3 → Bool) :
    SourceValid N edgeAncestralSample (edgeAncestralState register) := by
  refine ⟨singletonState_valid _ _,?_⟩
  intro x
  fin_cases x
  · exact .refl
  · exact .refl
  · exact ⟨rfl,N.rooted (N.leaf 0)⟩
  · exact ⟨rfl,N.rooted (N.leaf 1)⟩

def edgeAncestralCode (register : Fin 3 → Bool) : Code N edgeAncestralSample :=
  encodeActual N edgeAncestralSample (edgeAncestralState register)
    (edgeAncestralState_sourceValid register)

def nodeState : State (Fin 3) (Fin 2) (Fin 2) :=
  singletonState (fun _ => .node 1) (fun _ => false)

theorem nodeState_sourceValid : SourceValid N (fun _ : Fin 2 => (0 : Fin 2)) nodeState := by
  refine ⟨singletonState_valid _ _,?_⟩
  intro x
  change N.graph.DReach (N.leaf 0) (N.leaf 0)
  exact .refl

def nodeCode : Code N (fun _ : Fin 2 => (0 : Fin 2)) :=
  encodeActual N _ nodeState nodeState_sourceValid

def carriedNodeState : State (Fin 3) (Fin 2) (Fin 4) where
  live := {2,3}
  ancestor x := if x = 3 then 3 else 2
  genealogy x := if x = 2 then .graft (.graft (.leaf 0) (.leaf 1)) (.leaf 2) else .leaf x
  location x := if x = 2 then .node 1 else .rootPopulation N.root
  register _ := false
  history := []

theorem carriedNodeState_valid : Valid carriedNodeState := by
  letI := forestValidDecidable carriedNodeState
  exact of_decide_eq_true (by decide)

theorem carriedNodeState_sourceValid : SourceValid N edgeAncestralSample carriedNodeState := by
  refine ⟨carriedNodeState_valid,?_⟩
  intro x
  fin_cases x
  · exact .refl
  · exact .refl
  · exact .refl
  · exact ⟨rfl,N.rooted (N.leaf 1)⟩

def carriedNodeCode : Code N edgeAncestralSample :=
  encodeActual N edgeAncestralSample carriedNodeState carriedNodeState_sourceValid

def permutedSample (x : Fin 3) : Fin 2 := if x = 1 then 1 else 0
def permutedState : State (Fin 3) (Fin 2) (Fin 3) :=
  singletonState (fun x => if x = 1 then .rootPopulation N.root else .edge 0) (fun _ => false)

theorem permutedState_sourceValid : SourceValid N permutedSample permutedState := by
  refine ⟨singletonState_valid _ _,?_⟩
  intro x
  fin_cases x
  · exact .refl
  · exact ⟨rfl,N.rooted (N.leaf 1)⟩
  · exact .refl

def permutedCode : Code N permutedSample :=
  encodeActual N permutedSample permutedState permutedState_sourceValid

/-- Same literal test encodings as the accepted population fixture; kept here
so its standalone main is not imported into this independent epoch context. -/
def rationalText (q : Rat) : String := toString q.num ++ "/" ++ toString q.den
def treeJson {n : Nat} : Genealogy (Fin n) → Lean.Json
  | .leaf x => Lean.toJson x.val
  | .graft a b => Lean.Json.arr #[treeJson a,treeJson b]

def locationJson {v e : Nat} : Location (Fin v) (Fin e) → Lean.Json
  | .node x => Lean.Json.arr #[Lean.Json.str "V",Lean.toJson x.val]
  | .edge x => Lean.Json.arr #[Lean.Json.str "E",Lean.toJson x.val]
  | .rootPopulation x => Lean.Json.arr #[Lean.Json.str "A",Lean.toJson x.val]

def snapshotJson {v e n : Nat} {N : RootedBinary (Fin v) (Fin e) (Fin 2)}
    {sample : Fin n → Fin 2} (s : Code N sample) : Lean.Json :=
  let ids := FinEnum.toList (Fin n)
  Lean.Json.mkObj [
    ("live",Lean.toJson ((ids.filter fun x => decide (x ∈ s.val.live)).map Fin.val)),
    ("ancestor",Lean.toJson (ids.map fun x => (s.val.ancestor x).val)),
    ("genealogy",Lean.Json.arr (ids.map (fun x => match s.val.genealogy x with
      | none => Lean.Json.null | some g => treeJson g.val)).toArray),
    ("location",Lean.Json.arr (ids.map (fun x => match s.val.population x with
      | none => Lean.Json.null | some place => locationJson place)).toArray),
    ("register",Lean.toJson ((FinEnum.toList (Fin v)).map s.val.register))]

def viewJson {v e n : Nat} {N : RootedBinary (Fin v) (Fin e) (Fin 2)}
    {sample : Fin n → Fin 2} (a : SelectedIndex N sample Finset.univ) : Lean.Json :=
  let ids := FinEnum.toList (Fin n)
  Lean.Json.mkObj [
    ("genealogy",Lean.Json.arr (ids.map (fun x => match a.val.genealogy x with
      | none => Lean.Json.null | some g => treeJson g)).toArray),
    ("location",Lean.Json.arr (ids.map (fun x => match a.val.population x with
      | none => Lean.Json.null | some place => locationJson place)).toArray),
    ("register",Lean.toJson ((FinEnum.toList (Fin v)).map a.val.register))]

def lexLe : List Nat → List Nat → Bool
  | [],_ => true
  | _::_,[] => false
  | a::as,b::bs => if a < b then true else if a = b then lexLe as bs else false

def powers {e : Nat} (coordinates : List (Option (Fin e))) (m : List (Option (Fin e) × Nat)) :
    List Nat := coordinates.map fun i => ((m.filter fun z => z.1 == i).map Prod.snd).sum

def normalizedTerms {e : Nat} (coordinates : List (Option (Fin e))) (p : Sparse (Option (Fin e))) :
    List (List Nat × Rat) :=
  let expanded := p.map fun z => (powers coordinates z.1,z.2)
  let monomials := (expanded.map Prod.fst).eraseDups.mergeSort lexLe
  (monomials.map fun m =>
    (m,expanded.foldl (fun q z => if z.1 = m then q + z.2 else q) 0))
      |>.filter (fun z => z.2 != 0)

def termsJson (p : List (List Nat × Rat)) : Lean.Json :=
  Lean.Json.arr (p.map fun z =>
    Lean.Json.arr #[Lean.toJson z.1,Lean.Json.str (rationalText z.2)]).toArray

def contextJson {v e n : Nat} (N : RootedBinary (Fin v) (Fin e) (Fin 2))
    {sample : Fin n → Fin 2} (labels : Fin n → Nat) (s : Code N sample)
    (hybrids : List (Nat × Nat × Nat)) : Lean.Json :=
  Lean.Json.mkObj [
    ("vertices",Lean.toJson v),("root",Lean.toJson N.root.val),
    ("edges",Lean.toJson ((FinEnum.toList (Fin e)).map fun i =>
      ((N.graph.source i).val,(N.graph.target i).val))),
    ("leaves",Lean.toJson ((FinEnum.toList (Fin 2)).map fun x => (N.leaf x).val)),
    ("hybrids",Lean.Json.arr (hybrids.map fun h =>
      Lean.Json.arr #[Lean.toJson h.1,Lean.toJson h.2.1,Lean.toJson h.2.2]).toArray),
    ("global_labels",Lean.toJson ((FinEnum.toList (Fin n)).map labels)),
    ("local_samples",Lean.toJson ((FinEnum.toList (Fin n)).map fun x => (sample x).val)),
    ("register",Lean.toJson ((FinEnum.toList (Fin v)).map s.val.register)),
    ("start",snapshotJson s)]

def fixtureJson {v e n : Nat} (name : String) (N : RootedBinary (Fin v) (Fin e) (Fin 2))
    {sample : Fin n → Fin 2} (labels : Fin n → Nat) (s : Code N sample)
    (hybrids : List (Nat × Nat × Nat)) : Lean.Json :=
  let coordinates : List (Option (Fin e)) := (FinEnum.toList (Fin e)).map some ++ [none]
  let rows := epochRows N s
  let keys := (rows.map fun row => project N Finset.univ row.1).eraseDups
  let output := keys.flatMap fun key =>
    match rows.find? (fun row => project N Finset.univ row.1 == key) with
    | none => []
    | some witness =>
      let terms := normalizedTerms coordinates (readRows (project N Finset.univ) rows key)
      if terms.isEmpty then [] else [Lean.Json.mkObj [
        ("view",viewJson key),("witness",snapshotJson witness.1),("coefficients",termsJson terms)]]
  Lean.Json.mkObj [
    ("schema",Lean.Json.str "source_epoch_probe_v1"),("fixture",Lean.Json.str name),
    ("context",contextJson N labels s hybrids),
    ("variables",Lean.Json.arr (coordinates.map fun i => locationJson (place N i)).toArray),
    ("rows",Lean.Json.arr output.toArray)]

def fixtureNamed (name : String) : Option Lean.Json :=
  match name with
  | "empty" => some (fixtureJson name N Fin.val (rootCode 0 (fun x => Fin.elim0 x)) [])
  | "oneAncestral" => some (fixtureJson name N Fin.val (rootCode 1 (fun _ => 0)) [])
  | "twoEdgePanels" => some (fixtureJson name N Fin.val twoEdgeCode [])
  | "edgeAncestral" => some (fixtureJson name N Fin.val (edgeAncestralCode (fun _ => false)) [])
  | "nodeIdentity" => some (fixtureJson name N Fin.val nodeCode [])
  | "carriedNodeExterior" => some (fixtureJson name N Fin.val carriedNodeCode [])
  | "permutedRestricted" => some (fixtureJson name N
      (fun x => if x = 0 then 3 else if x = 1 then 0 else 2) permutedCode [])
  | "frozenRegister" => some (fixtureJson name N Fin.val (edgeAncestralCode (fun v => v != 1)) [])
  | _ => none

def run (args : List String) : IO UInt32 := do
  match args with
  | [name] =>
      match fixtureNamed name with
      | none => IO.eprintln "unknown original epoch fixture"; pure 2
      | some output => IO.println output.compress; pure 0
  | _ => IO.eprintln "one fixture name required"; pure 2

#print axioms twoEdgeState_sourceValid
#print axioms edgeAncestralState_sourceValid
#print axioms carriedNodeState_sourceValid
end UnifiedLean.G7.OriginalEpochFixture
