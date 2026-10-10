import G7EffectiveFullEpochCoefficients
import G7OriginalAdmission

/-! Bounded executable checks on an explicitly admitted two-tip original
source. These check compiled computation, not merely proof-level equality.
The nontrivial two-copy population diagonal is X; a one-copy full epoch has
unit mass at the unchanged full view. No native_decide trust extension. -/
namespace GProgram.G7.EffectiveCoefficientSmoke
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveFullEpochCoefficients

/-- Two distinct original edge IDs are ordinary root-to-tip arcs here. -/
def forkCode : GProgram.G7.OriginalFiniteEncoding.Code (Fin 2) (Fin 0) :=
  ⟨fun _ => 0,fun e => e.succ,0,fun x => x.succ,
    fun i => Fin.elim0 i,fun i => Fin.elim0 i⟩

theorem fork_valid : GProgram.G7.OriginalAdmission.BinaryValid forkCode := by decide

theorem fork_cut_child : GProgram.G7.OriginalAdmission.CutChild forkCode := by decide

def source := GProgram.G7.OriginalAdmission.sourceOfValid forkCode fork_valid

def rootState (n : Nat) : State (Fin 3) (Fin 2) (Fin n) where
  live := Finset.univ
  ancestor := id
  genealogy := Genealogy.leaf
  location _ := .rootPopulation source.root
  register _ := false
  history := []

theorem rootState_valid (n : Nat) (sample : Fin n → Fin 2) :
    SourceValid source sample (rootState n) := by
  constructor
  · constructor
    · intro x; simp [rootState]
    · intro l _; rfl
    · intro l _ x; simp [rootState,Genealogy.leaves,eq_comm]
    · intro l _; trivial
  · intro x
    exact ⟨rfl,source.rooted (source.leaf (sample x))⟩

def atRoot (n : Nat) : Code source (fun _ : Fin n => (0 : Fin 2)) :=
  encodeActual source _ (rootState n) (rootState_valid n _)

def rationalValue (p : Sparse (Option (Fin 2))) (x : ℚ) : ℚ :=
  (p.map fun z => z.2 * (z.1.map fun a => x ^ a.2).prod).sum

def populationDiagonal : ℚ :=
  ((coefficients source 2 (atRoot 2) (atRoot 2)).map
    fun z => z.2 * (1/2 : ℚ)^z.1).sum

def fullOneCopy : Sparse (Option (Fin 2)) :=
  epochCoefficients source (atRoot 1) (project source Finset.univ (atRoot 1))

#eval populationDiagonal
#guard populationDiagonal == (1/2 : ℚ)
#eval rationalValue fullOneCopy (1/2)
#guard rationalValue fullOneCopy (1/2) == 1

end GProgram.G7.EffectiveCoefficientSmoke
