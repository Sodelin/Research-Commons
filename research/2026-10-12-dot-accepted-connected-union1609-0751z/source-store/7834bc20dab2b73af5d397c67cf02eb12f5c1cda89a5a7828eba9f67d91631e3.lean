import G7OriginalAdmission

namespace GProgram.G7.AdmissionChecks
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission

/-- A genuine parallel-edge private bigon above taxon 1: root 0, ordinary
node 2, hybrid 3, leaves 1 and 4. Both parent arcs share endpoints. -/
def parallelBigon : Code (Fin 2) (Fin 1) := by
  simp only [Code, vertexCount, edgeCount, Fintype.card_fin]
  exact ⟨![0,0,2,2,3], ![1,2,3,3,4], 0, ![1,4], ![3], fun _ b => if b then 3 else 2⟩
def duplicateParent : Code (Fin 2) (Fin 1) := by
  simp only [Code, vertexCount, edgeCount, Fintype.card_fin]
  exact ⟨![0,0,2,2,3], ![1,2,3,3,4], 0, ![1,4], ![3], fun _ _ => 2⟩
def wrongHybridID : Code (Fin 2) (Fin 1) := by
  simp only [Code, vertexCount, edgeCount, Fintype.card_fin]
  exact ⟨![0,0,2,2,3], ![1,2,3,3,4], 0, ![1,4], ![2], fun _ b => if b then 3 else 2⟩

#eval decide (BinaryValid parallelBigon ∧ CutChild parallelBigon ∧ RegistryValid parallelBigon)
#eval decide (RegistryValid duplicateParent)
#eval decide (RegistryValid wrongHybridID)
#eval (registeredBinaryCutChildCodes (X:=Fin 2) (ID:=Fin 0)).card
end GProgram.G7.AdmissionChecks
