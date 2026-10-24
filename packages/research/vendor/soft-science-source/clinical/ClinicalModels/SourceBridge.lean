import ClinicalModels.SourceTables

namespace ClinicalModels.SourceBridge
open PublishedCBT

def phaseIndex : Phase → Nat
  | .start => 0 | .stimulus => 1 | .approach => 2
  | .interact => 3 | .avoid => 4 | .safetyCost => 5

def column (table : List (List Int)) (phase : Phase) : List Int :=
  table.map fun row => row[phaseIndex phase]!

def bitColumn (b : Bool) : List Int := if b then [0,1] else [1,0]

def affectColumn : Affect → List Int
  | .positive => [1,0,0] | .negative => [0,1,0] | .harm => [0,0,1]

def phaseColumn : Phase → List Int
  | .start => [1,0,0,0,0,0] | .stimulus => [0,1,0,0,0,0]
  | .approach => [0,0,1,0,0,0] | .interact => [0,0,0,1,0,0]
  | .avoid => [0,0,0,0,1,0] | .safetyCost => [0,0,0,0,0,1]

def weightsColumn (w : Int × Int × Int) : List Int := [w.1,w.2.1,w.2.2]

/-- Every reconstructed spider/arousal column matches the selected source matrices. -/
theorem source_sensory_columns (p : Phase) :
    column SourceTables.spiderDanger p = bitColumn (seesSpider p) ∧
    column SourceTables.spiderSafe p = bitColumn (seesSpider p) ∧
    column SourceTables.arousalDanger p = bitColumn (highArousal p) ∧
    column SourceTables.arousalSafe p = bitColumn (highArousal p) := by
  cases p <;> decide

theorem source_affective_columns (p : Phase) :
    column SourceTables.affectDanger p = affectColumn (affect true p) ∧
    column SourceTables.affectSafe p = affectColumn (affect false p) := by
  cases p <;> decide

theorem source_transition_columns (p : Phase) :
    column SourceTables.transitionApproach p = phaseColumn (approachStep p) ∧
    column SourceTables.transitionAvoid p = phaseColumn (avoidStep p) := by
  cases p <;> decide

theorem source_implicit_columns (u c : Int) (p : Phase) :
    column (SourceTables.implicitDanger u c) p = weightsColumn (implicitDanger u p) ∧
    column (SourceTables.implicitSafe u c) p = weightsColumn (implicitSafe u c p) := by
  cases p <;> constructor <;> rfl

end ClinicalModels.SourceBridge
