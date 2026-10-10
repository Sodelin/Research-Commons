import G7SourceStateRelabelling
import UnifiedLean.Source.FiniteSourceSnapshot
import UnifiedLean.Source.UniformizedSourceStep

/-!
Original finite snapshot transport, preserving the entire unranked genealogy.
Contributor: dot, 2026-10-09. No arbitrary marginal kernel is a premise.
-/
namespace GProgram.G7.SnapshotRelabelling
open Nanuq.Source GProgram.SourceForest
open GProgram.G7.OriginalRelabelling
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
variable {V E W F Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable [Fintype Copy] [DecidableEq Copy]

def snapshot (v : V ≃ W) (e : E ≃ F) (s : Snapshot V E Copy) : Snapshot W F Copy where
  live := s.live
  ancestor := s.ancestor
  genealogy := s.genealogy
  population l := (s.population l).map (GProgram.G7.SourceStateRelabelling.location v e)
  register a := s.register (v.symm a)

theorem decode_commutes (v : V ≃ W) (e : E ≃ F) (root : V) (s : Snapshot V E Copy) :
    decodeSnapshot (v root) (snapshot v e s) = GProgram.G7.SourceStateRelabelling.state v e (decodeSnapshot root s) := by
  cases s with
  | mk live ancestor genealogy population register =>
    simp only [decodeSnapshot,snapshot,GProgram.G7.SourceStateRelabelling.state,List.map_nil]
    congr 1
    funext l
    cases population l <;> rfl

theorem encode_commutes (v : V ≃ W) (e : E ≃ F) (s : State V E Copy) (hs : Valid s) :
    snapshot v e (encodeSnapshot s hs) = encodeSnapshot (GProgram.G7.SourceStateRelabelling.state v e s) (GProgram.G7.SourceStateRelabelling.valid v e s hs) := by
  apply Snapshot.ext
  · rfl
  · rfl
  · rfl
  · funext l
    by_cases h : l ∈ s.live <;> simp [snapshot,encodeSnapshot,GProgram.G7.SourceStateRelabelling.state,h]
  · rfl

theorem snapshot_valid (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (sample : Copy → X) (s : AdmittedSnapshot N sample) :
    SourceValid (network N v e) sample (decodeSnapshot (network N v e).root (snapshot v e s.val)) := by
  rw [show (network N v e).root = v N.root from rfl,decode_commutes]
  exact GProgram.G7.SourceStateRelabelling.sourceValid N v e sample _ s.property

noncomputable def code (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) : Code (network N v e) sample :=
  ⟨snapshot v e s.val,snapshot_valid N v e sample s⟩

theorem code_state (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) :
    state (code N v e s) = GProgram.G7.SourceStateRelabelling.state v e (state s) := decode_commutes v e N.root s.val

theorem admittedCode_commutes (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (sample : Copy → X) (s : State V E Copy) (hs : SourceValid N sample s) :
    code N v e (admittedCode N sample s hs) =
      admittedCode (network N v e) sample (GProgram.G7.SourceStateRelabelling.state v e s) (GProgram.G7.SourceStateRelabelling.sourceValid N v e sample s hs) := by
  apply Subtype.ext
  exact encode_commutes v e s hs.forest

/-- Every original-copy genealogy, including all retained old subtrees, is
unchanged by the actual population-ID transport. -/
theorem entire_genealogy_preserved (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) :
    (state (code N v e s)).genealogy = (state s).genealogy := by
  rw [code_state]
  rfl

#print axioms snapshot_valid
#print axioms admittedCode_commutes
#print axioms entire_genealogy_preserved
end GProgram.G7.SnapshotRelabelling
