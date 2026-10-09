import NaturalCellAffineCompiler

/-! Actual bounded executions of the proved arithmetic decision procedure.
These regressions are not substituted for its all-input correctness theorem. -/
namespace UnifiedLean.G6.AffineRegression
open UnifiedLean.G6.StrictAffineElimination

def emptySystem : Finset (Row 2) := ∅
def strictZero : Finset (Row 0) := {⟨Fin.elim0,0,true⟩}
def weakZero : Finset (Row 0) := {⟨Fin.elim0,0,false⟩}
def singletonSystem : Finset (Row 1) := {⟨![1],0,false⟩,⟨![-1],0,false⟩}
def mixedOpenClosed : Finset (Row 1) := {⟨![-1],0,true⟩,⟨![1],1,false⟩}
def strictSingleton : Finset (Row 1) := {⟨![1],0,true⟩,⟨![-1],0,false⟩}
def oppositeSignsNo : Finset (Row 2) := {⟨![1,1],0,false⟩,⟨![-1,-1],0,true⟩}
def oppositeSignsYes : Finset (Row 2) := {⟨![1,1],2,false⟩,⟨![-1,1],0,false⟩}

#eval ("empty", decideFeasible 2 emptySystem)
#eval ("strict zero contradiction", decideFeasible 0 strictZero)
#eval ("weak zero", decideFeasible 0 weakZero)
#eval ("weak singleton", decideFeasible 1 singletonSystem)
#eval ("mixed open/closed", decideFeasible 1 mixedOpenClosed)
#eval ("strict singleton contradiction", decideFeasible 1 strictSingleton)
#eval ("opposite-sign projection NO", decideFeasible 2 oppositeSignsNo)
#eval ("opposite-sign projection YES", decideFeasible 2 oppositeSignsYes)

def runRegression : IO Unit := do
  let tests : List (String × Bool × Bool) := [
    ("empty", decideFeasible 2 emptySystem, true),
    ("strict zero", decideFeasible 0 strictZero, false),
    ("weak zero", decideFeasible 0 weakZero, true),
    ("singleton", decideFeasible 1 singletonSystem, true),
    ("mixed", decideFeasible 1 mixedOpenClosed, true),
    ("strict singleton", decideFeasible 1 strictSingleton, false),
    ("opposite NO", decideFeasible 2 oppositeSignsNo, false),
    ("opposite YES", decideFeasible 2 oppositeSignsYes, true)]
  for (name,actual,expected) in tests do
    if actual != expected then
      throw (IO.userError s!"Regression failed: {name}")
  IO.println "8 bounded Boolean regression checks passed"
#eval runRegression
end UnifiedLean.G6.AffineRegression
