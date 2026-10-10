import G7EffectiveBoundaryCoefficients
import G7OriginalParallelEpochFixture
import Lean.Data.Json

/-!
# Twelve typed original conditional boundary controls

Contributor: Codex / lean_reuse_successor, 2026-10-10.
The original two-tip and separately admitted parallel graph/registry are reused.
Every entering Code is encodeActual of an independently proved SourceValid
state. The actual sparse pulse/deterministic refinement is the mathematical
baseline; normalization and JSON are finite test utilities. No general native
parser, source admission or serialization theorem is asserted.
Fresh source checks, complete audit and evaluator comparisons remain pending.
-/
namespace UnifiedLean.G7.OriginalBoundaryFixture
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveFullEpochCoefficients GProgram.G7.SparseRowProducts
open GProgram.G7.EffectiveBoundaryCoefficients

abbrev N2 := UnifiedLean.G7.OriginalEpochFixture.N
abbrev NP := UnifiedLean.G7.OriginalParallelEpochFixture.source
def parents : GProgram.G2.OriginalHybridParents NP :=
  UnifiedLean.G7.OriginalParallelEpochFixture.registry.parents
    (UnifiedLean.G7.OriginalParallelEpochFixture.ids 0)

def singletonState {v e n : Nat} (location : Fin n → Location (Fin v) (Fin e))
    (register : Fin v → Bool) : State (Fin v) (Fin e) (Fin n) where
  live := Finset.univ
  ancestor x := x
  genealogy := Genealogy.leaf
  location := location
  register := register
  history := []

theorem singletonState_valid {v e n : Nat} (location : Fin n → Location (Fin v) (Fin e))
    (register : Fin v → Bool) : Valid (singletonState location register) := by
  constructor
  · intro x; exact Finset.mem_univ x
  · intro l _; rfl
  · intro l _ x; simp [singletonState,Genealogy.leaves]
  · intro l _; trivial

def falseRegister (v : Fin 5) : Bool := v.val % 2 == 0
def trueRegister (v : Fin 5) : Bool := v.val == 3 || v.val % 2 == 0
def repeatRegister (v : Fin 5) : Bool := v.val == 1

def siteState (n : Nat) (register : Fin 5 → Bool) : State (Fin 5) (Fin 5) (Fin n) :=
  singletonState (fun _ => .node 3) register

theorem siteState_sourceValid (n : Nat) (register : Fin 5 → Bool) :
    SourceValid NP (fun _ : Fin n => (1 : Fin 2)) (siteState n register) := by
  refine ⟨?_,?_⟩
  · constructor
    · intro x; exact Finset.mem_univ x
    · intro l _; rfl
    · intro l _ x; simp [siteState,singletonState,Genealogy.leaves]
    · intro l _; trivial
  · intro x
    exact Relation.ReflTransGen.single ⟨(4 : Fin 5),rfl,rfl⟩

def siteCode (n : Nat) (register : Fin 5 → Bool) : Code NP (fun _ : Fin n => (1 : Fin 2)) :=
  encodeActual NP _ (siteState n register) (siteState_sourceValid n register)

def outsideSample (x : Fin 2) : Fin 2 := if x = 0 then 1 else 0
def outsideState (register : Fin 5 → Bool) : State (Fin 5) (Fin 5) (Fin 2) :=
  singletonState (fun x => if x = 0 then .edge 2 else .node 1) register

theorem outsideState_sourceValid (register : Fin 5 → Bool) :
    SourceValid NP outsideSample (outsideState register) := by
  refine ⟨singletonState_valid _ _,?_⟩
  intro x
  fin_cases x
  · exact Relation.ReflTransGen.single ⟨(4 : Fin 5),rfl,rfl⟩
  · exact .refl

def outsideCode (register : Fin 5 → Bool) : Code NP outsideSample :=
  encodeActual NP _ (outsideState register) (outsideState_sourceValid register)

def repeatState : State (Fin 5) (Fin 5) (Fin 2) :=
  singletonState (fun x => if x = 0 then .node 3 else .node 1) repeatRegister

theorem repeatState_sourceValid : SourceValid NP outsideSample repeatState := by
  refine ⟨singletonState_valid _ _,?_⟩
  intro x
  fin_cases x
  · exact Relation.ReflTransGen.single ⟨(4 : Fin 5),rfl,rfl⟩
  · exact .refl

def repeatCode : Code NP outsideSample :=
  encodeActual NP _ repeatState repeatState_sourceValid

def carriedSample (x : Fin 4) : Fin 2 := if x = 3 then 0 else 1
def carriedState : State (Fin 5) (Fin 5) (Fin 4) where
  live := {2,3}
  ancestor x := if x = 3 then 3 else 2
  genealogy x := if x = 2 then .graft (.graft (.leaf 0) (.leaf 1)) (.leaf 2) else .leaf x
  location x := if x = 2 then .node 3 else .node 1
  register := falseRegister
  history := []

theorem carriedState_sourceValid : SourceValid NP carriedSample carriedState := by
  refine ⟨?_,?_⟩
  · letI := forestValidDecidable carriedState
    exact of_decide_eq_true (by decide)
  · intro x
    fin_cases x
    · exact Relation.ReflTransGen.single ⟨(4 : Fin 5),rfl,rfl⟩
    · exact Relation.ReflTransGen.single ⟨(4 : Fin 5),rfl,rfl⟩
    · exact Relation.ReflTransGen.single ⟨(4 : Fin 5),rfl,rfl⟩
    · exact .refl

def carriedCode : Code NP carriedSample :=
  encodeActual NP _ carriedState carriedState_sourceValid

def exitSample (x : Fin 3) : Fin 2 := if x = 2 then 0 else 1
def exitState : State (Fin 5) (Fin 5) (Fin 3) :=
  singletonState (fun x => if x = 0 then .edge 2 else if x = 1 then .edge 3 else .node 1)
    falseRegister

theorem exitState_sourceValid : SourceValid NP exitSample exitState := by
  refine ⟨singletonState_valid _ _,?_⟩
  intro x
  fin_cases x
  · exact Relation.ReflTransGen.single ⟨(4 : Fin 5),rfl,rfl⟩
  · exact Relation.ReflTransGen.single ⟨(4 : Fin 5),rfl,rfl⟩
  · exact .refl

def exitCode : Code NP exitSample := encodeActual NP _ exitState exitState_sourceValid

def permutedSample (x : Fin 3) : Fin 2 := if x = 1 then 0 else 1
def permutedState : State (Fin 5) (Fin 5) (Fin 3) :=
  singletonState (fun x => if x = 1 then .node 1 else .node 3) falseRegister

theorem permutedState_sourceValid : SourceValid NP permutedSample permutedState := by
  refine ⟨singletonState_valid _ _,?_⟩
  intro x
  fin_cases x
  · exact Relation.ReflTransGen.single ⟨(4 : Fin 5),rfl,rfl⟩
  · exact .refl
  · exact Relation.ReflTransGen.single ⟨(4 : Fin 5),rfl,rfl⟩

def permutedCode : Code NP permutedSample :=
  encodeActual NP _ permutedState permutedState_sourceValid

def ordinaryState : State (Fin 3) (Fin 2) (Fin 2) :=
  singletonState (fun x => .node (N2.leaf x)) (fun v => v != 1)

theorem ordinaryState_sourceValid : SourceValid N2 (fun x : Fin 2 => x) ordinaryState := by
  refine ⟨singletonState_valid _ _,?_⟩
  intro x
  exact .refl

theorem ordinary_degree : N2.graph.inDegree (N2.graph.target (0 : Fin 2)) = 1 := by decide

def ordinaryCode : Code N2 (fun x : Fin 2 => x) :=
  encodeActual N2 _ ordinaryState ordinaryState_sourceValid

def rootState : State (Fin 3) (Fin 2) (Fin 2) :=
  singletonState (fun _ => .node N2.root) (fun v => v != 2)

theorem rootState_sourceValid : SourceValid N2 (fun x : Fin 2 => x) rootState := by
  refine ⟨singletonState_valid _ _,?_⟩
  intro x
  exact N2.rooted (N2.leaf x)

def rootCode : Code N2 (fun x : Fin 2 => x) := encodeActual N2 _ rootState rootState_sourceValid

def powers {h : Nat} (m : List (Fin h × Nat)) : List Nat :=
  (FinEnum.toList (Fin h)).map fun i => ((m.filter fun z => z.1 == i).map Prod.snd).sum

def normalizedTerms {h : Nat} (p : Sparse (Fin h)) : List (List Nat × Rat) :=
  let expanded := p.map fun z => (powers z.1,z.2)
  let monomials := (expanded.map Prod.fst).eraseDups.mergeSort
    UnifiedLean.G7.OriginalEpochFixture.lexLe
  (monomials.map fun m =>
    (m,expanded.foldl (fun q z => if z.1 = m then q + z.2 else q) 0))
      |>.filter (fun z => z.2 != 0)

def rowsJson {v e n h : Nat} {N : RootedBinary (Fin v) (Fin e) (Fin 2)}
    {sample : Fin n → Fin 2} (rows : Rows (Fin h) (Code N sample)) : Lean.Json :=
  let keys := (rows.map fun row => project N Finset.univ row.1).eraseDups
  let output := keys.flatMap fun key =>
    match rows.find? (fun row => project N Finset.univ row.1 == key) with
    | none => []
    | some witness =>
      let terms := normalizedTerms (readRows (project N Finset.univ) rows key)
      if terms.isEmpty then [] else [Lean.Json.mkObj [
        ("view",UnifiedLean.G7.OriginalEpochFixture.viewJson key),
        ("witness",UnifiedLean.G7.OriginalEpochFixture.snapshotJson witness.1),
        ("coefficients",UnifiedLean.G7.OriginalEpochFixture.termsJson terms)]]
  Lean.Json.arr output.toArray

def fixtureJson {v e n h : Nat} (name : String) (N : RootedBinary (Fin v) (Fin e) (Fin 2))
    {sample : Fin n → Fin 2} (labels : Fin n → Nat) (s : Code N sample)
    (hybrids : List (Nat × Nat × Nat)) (action : Lean.Json) (owners : Nat)
    (rows : Rows (Fin h) (Code N sample)) : Lean.Json :=
  let assignments := rows.length
  let termContributions := (rows.map fun row => (normalizedTerms row.2).length).sum
  Lean.Json.mkObj [
    ("schema",Lean.Json.str "source_boundary_probe_v1"),("fixture",Lean.Json.str name),
    ("context",UnifiedLean.G7.OriginalEpochFixture.contextJson N labels s hybrids),
    ("action",action),
    ("variables",Lean.Json.arr ((FinEnum.toList (Fin h)).map fun i =>
      Lean.Json.arr #[Lean.Json.str "ORIGINAL_GAMMA",Lean.toJson i.val]).toArray),
    ("rows",rowsJson rows),
    ("work",Lean.Json.mkObj [("owners",Lean.toJson owners),
      ("assignments",Lean.toJson assignments),("destinations",Lean.toJson assignments),
      ("term_contributions",Lean.toJson termContributions)]),
    ("source_admission_verified",Lean.Json.bool false)]

def hybridFixture {n : Nat} (name : String) {sample : Fin n → Fin 2}
    (labels : Fin n → Nat) (s : Code NP sample) (independent : Bool) : Lean.Json :=
  let owners := (FinEnum.toList (AtNode (sourceState s) parents.hybrid)).length
  let rows : Rows (Fin 1) (Code NP sample) :=
    if independent then pulseRows (0 : Fin 1) parents s else commonRows parents s
  fixtureJson name NP labels s [(3,2,3)]
    (Lean.Json.arr #[Lean.Json.str (if independent then "INDEPENDENT" else "COMMON"),Lean.toJson (0 : Nat)])
    owners rows

def fixtureNamed (name : String) : Option Lean.Json :=
  match name with
  | "emptyCommon" => some (hybridFixture name Fin.val (siteCode 0 trueRegister) false)
  | "emptyIndependent" => some (hybridFixture name Fin.val (siteCode 0 falseRegister) true)
  | "commonFalse" => some (hybridFixture name Fin.val (siteCode 2 falseRegister) false)
  | "commonTrue" => some (hybridFixture name Fin.val (siteCode 2 trueRegister) false)
  | "independentTwo" => some (hybridFixture name Fin.val (siteCode 2 trueRegister) true)
  | "carriedOwnerOutside" => some (hybridFixture name Fin.val carriedCode true)
  | "noOwnerAtSite" => some (hybridFixture name Fin.val (outsideCode trueRegister) true)
  | "registerRepeat" => some (hybridFixture name Fin.val repeatCode false)
  | "permutedIndependent" => some (hybridFixture name
      (fun x => if x = 0 then 3 else if x = 1 then 0 else 2) permutedCode true)
  | "parallelExit" => some (fixtureJson name NP Fin.val exitCode [(3,2,3)]
      (Lean.Json.arr #[Lean.Json.str "EXIT",Lean.toJson (2 : Nat)]) 1
      (pureRows (I := Fin 1) (exitCodeEffective NP exitCode 2)))
  | "ordinaryEntry" => some (fixtureJson name N2 Fin.val ordinaryCode []
      (Lean.Json.arr #[Lean.Json.str "ORDINARY",Lean.toJson (0 : Nat)]) 1
      (pureRows (I := Fin 0) (ordinaryCodeEffective N2 ordinaryCode 0)))
  | "rootEntry" => some (fixtureJson name N2 Fin.val rootCode []
      (Lean.Json.arr #[Lean.Json.str "ROOT"]) 2
      (pureRows (I := Fin 0) (rootCodeEffective N2 rootCode)))
  | _ => none

def run (args : List String) : IO UInt32 := do
  match args with
  | [name] =>
      match fixtureNamed name with
      | none => IO.eprintln "unknown original boundary fixture"; pure 2
      | some output => IO.println output.compress; pure 0
  | _ => IO.eprintln "one fixture name required"; pure 2

#print axioms siteState_sourceValid
#print axioms carriedState_sourceValid
#print axioms ordinary_degree
end UnifiedLean.G7.OriginalBoundaryFixture
