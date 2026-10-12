import G7OriginalEpochFixture
import G7OriginalAdmission

/-!
# Separately admitted original parallel-occurrence epoch fixture

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Both parallel incoming edges retain different original occurrence IDs. The
inherited binary/source/registry predicates, rather than the native validator,
admit this literal graph. Whole-epoch extraction uses the same proved support
baseline and finite test serializer as the eight ordinary contexts.
Fresh checking/audit/evaluator comparison remain pending.
-/
namespace UnifiedLean.G7.OriginalParallelEpochFixture
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G7.EffectivePopulationCoefficients

def graphCode : GProgram.G7.OriginalFiniteEncoding.Code (Fin 2) (Fin 1) :=
  ⟨fun e => if e.val = 0 then ⟨0,by decide⟩ else if e.val = 1 then ⟨0,by decide⟩
      else if e.val = 4 then ⟨3,by decide⟩ else ⟨2,by decide⟩,
    fun e => if e.val = 0 then ⟨1,by decide⟩ else if e.val = 1 then ⟨2,by decide⟩
      else if e.val = 4 then ⟨4,by decide⟩ else ⟨3,by decide⟩,
    ⟨0,by decide⟩,
    fun x => if x.val = 0 then ⟨1,by decide⟩ else ⟨4,by decide⟩,
    fun _ => ⟨3,by decide⟩,
    fun _ b => if b then ⟨3,by decide⟩ else ⟨2,by decide⟩⟩

theorem graphCode_valid : GProgram.G7.OriginalAdmission.BinaryValid graphCode := by decide
theorem graphCode_registryValid : GProgram.G7.OriginalAdmission.RegistryValid graphCode := by decide
theorem graphCode_cutChild : GProgram.G7.OriginalAdmission.CutChild graphCode := by decide

def source : RootedBinary (Fin 5) (Fin 5) (Fin 2) :=
  GProgram.G7.OriginalAdmission.sourceOfValid graphCode graphCode_valid

def registry : UnifiedLean.Source.NativeParentRouting.OriginalParentRegistry source :=
  GProgram.G7.OriginalAdmission.decodedRegistry graphCode graphCode_valid graphCode_registryValid

def ids : Fin 1 ≃ UnifiedLean.Source.NativeParentRouting.Hybrid source :=
  GProgram.G7.OriginalAdmission.decodedIDs graphCode graphCode_valid graphCode_registryValid

theorem parentOccurrence_exact (i : Fin 1) (b : Bool) :
    (registry.parents (ids i)).parent b = if b then (3 : Fin 5) else 2 :=
  GProgram.G7.OriginalAdmission.decoded_parent_exact graphCode graphCode_valid graphCode_registryValid i b

def sample (_ : Fin 4) : Fin 2 := 1
def initialState : State (Fin 5) (Fin 5) (Fin 4) where
  live := Finset.univ
  ancestor x := x
  genealogy := Genealogy.leaf
  location x := if x.val < 2 then .edge 2 else .edge 3
  register v := v.val % 2 == 0
  history := []

theorem initialState_valid : Valid initialState := by
  constructor
  · intro x; exact Finset.mem_univ x
  · intro l _; rfl
  · intro l _ x; simp [initialState,Genealogy.leaves]
  · intro l _; trivial

theorem initialState_sourceValid : SourceValid source sample initialState := by
  refine ⟨initialState_valid,?_⟩
  intro x
  have h : source.graph.DReach (3 : Fin 5) (4 : Fin 5) :=
    Relation.ReflTransGen.single ⟨(4 : Fin 5),rfl,rfl⟩
  fin_cases x <;> exact h

def initialCode : Code source sample :=
  encodeActual source sample initialState initialState_sourceValid

def fixture : Lean.Json :=
  UnifiedLean.G7.OriginalEpochFixture.fixtureJson "parallelPanels" source
    (fun x => if x = 0 then 2 else if x = 1 then 0 else if x = 2 then 3 else 1)
    initialCode [(3,2,3)]

def run (args : List String) : IO UInt32 := do
  match args with
  | ["parallelPanels"] => IO.println fixture.compress; pure 0
  | _ => UnifiedLean.G7.OriginalEpochFixture.run args

#print axioms graphCode_valid
#print axioms graphCode_registryValid
#print axioms parentOccurrence_exact
#print axioms initialState_sourceValid
end UnifiedLean.G7.OriginalParallelEpochFixture
