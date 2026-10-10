import G7OriginalWordFixture
import G7CalendarPhaseConsumers
import Mathlib.Tactic.FinCases

/-!
# Three completed literal words from the frozen original calendar controls

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Reuses the admitted N2/NP sources, once-drawn natural initialization, actual
ordered source coefficients and genuine rational ancestral completion.
The three literal words and their sample maps are the frozen calendar producer's
derived children. No date, phase or interval-occurrence engine is introduced.
The inherited Finset.toList tie order is not identified with ascending IDs;
the separately checked phase-Perm consumer transports the physical source PMF.
This finite evaluator comparison is distinct from a universal native calendar,
dictionary or serializer refinement. Sole-scheduler kernel/audit/execution pending.
-/

namespace UnifiedLean.G7.OriginalCompletedCalendarFixture

open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open GProgram.G7.EffectiveCompletedWordCoefficients
open GProgram.G7.SymbolicProgramPolynomial
open UnifiedLean.G7.OriginalWordFixture

def twoTipAge (v : Fin 3) : Rat := if v = 0 then 2 else 0
def serialAge (v : Fin 3) : Rat :=
  if v = 0 then 3 / 2 else if v = 1 then -3 / 2 else 1 / 4
def parallelAge (v : Fin 5) : Rat :=
  if v = 0 then 3 else if v = 2 then 2 else if v = 3 then 1 else 0

noncomputable def twoTipCalendar : Calendar N2.graph where
  age v := twoTipAge v
  edge_older e := by
    have h0 : twoTipAge 0 = 2 := by decide
    have h1 : twoTipAge 1 = 0 := by decide
    have h2 : twoTipAge 2 = 0 := by decide
    fin_cases e
    · change ((twoTipAge 1 : Rat) : ℝ) < ((twoTipAge 0 : Rat) : ℝ)
      rw [h1,h0]
      norm_num
    · change ((twoTipAge 2 : Rat) : ℝ) < ((twoTipAge 0 : Rat) : ℝ)
      rw [h2,h0]
      norm_num

noncomputable def serialCalendar : Calendar N2.graph where
  age v := serialAge v
  edge_older e := by
    have h0 : serialAge 0 = 3 / 2 := by decide
    have h1 : serialAge 1 = -3 / 2 := by decide
    have h2 : serialAge 2 = 1 / 4 := by decide
    fin_cases e
    · change ((serialAge 1 : Rat) : ℝ) < ((serialAge 0 : Rat) : ℝ)
      rw [h1,h0]
      norm_num
    · change ((serialAge 2 : Rat) : ℝ) < ((serialAge 0 : Rat) : ℝ)
      rw [h2,h0]
      norm_num

noncomputable def parallelCalendar : Calendar NP.graph where
  age v := parallelAge v
  edge_older e := by
    have h0 : parallelAge 0 = 3 := by decide
    have h1 : parallelAge 1 = 0 := by decide
    have h2 : parallelAge 2 = 2 := by decide
    have h3 : parallelAge 3 = 1 := by decide
    have h4 : parallelAge 4 = 0 := by decide
    fin_cases e
    · change ((parallelAge 1 : Rat) : ℝ) < ((parallelAge 0 : Rat) : ℝ)
      rw [h1,h0]
      norm_num
    · change ((parallelAge 2 : Rat) : ℝ) < ((parallelAge 0 : Rat) : ℝ)
      rw [h2,h0]
      norm_num
    · change ((parallelAge 3 : Rat) : ℝ) < ((parallelAge 2 : Rat) : ℝ)
      rw [h3,h2]
      norm_num
    · change ((parallelAge 3 : Rat) : ℝ) < ((parallelAge 2 : Rat) : ℝ)
      rw [h3,h2]
      norm_num
    · change ((parallelAge 4 : Rat) : ℝ) < ((parallelAge 3 : Rat) : ℝ)
      rw [h4,h3]
      norm_num

def twoTipWord : List (Symbol (Fin 1) (Fin 3) (Fin 2)) :=
  [.enter 1,.enter 2,.interval 0,.exit 0,.exit 1,.enter 0]

def serialWord : List (Symbol (Fin 2) (Fin 3) (Fin 2)) :=
  [.enter 1,.interval 0,.enter 2,.interval 1,.exit 0,.exit 1,.enter 0]

/-- JSON utilities and finite normalization are exactly the accepted word
fixture's utilities. The terminal readout is the unchanged actual completion
provider, rather than a fitted forest completion recurrence. -/
def completedFixtureJson {v e n j : Nat}
    (name : String) (N : RootedBinary (Fin v) (Fin e) (Fin 2))
    (sample : Fin n → Fin 2) (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (hybridIDs : List (Hybrid N))
    (hybridIndex : Hybrid N → Nat) (hybrids : List (Nat × Nat × Nat))
    (word : List (Symbol (Fin j) (Fin v) (Fin e))) : Lean.Json :=
  let coordinates := coordinateList (j := j) N hybridIDs
  let rows := completedNaturalWordRows N sample H common word
  let request := Lean.Json.mkObj [
    ("context",contextJson N sample Fin.val hybrids),
    ("initial",Lean.Json.mkObj [("kind",Lean.Json.str "NATURAL")]),
    ("common",Lean.toJson (hybridIDs.map common)),("slots",Lean.toJson j),
    ("word",Lean.Json.arr (word.map symbolJson).toArray),
    ("terminal",Lean.Json.str "ANCESTRAL_COMPLETE"),("limits",limitsJson)]
  Lean.Json.mkObj [
    ("schema",Lean.Json.str "source_original_word_coefficients_v1"),
    ("fixture",Lean.Json.str name),("request",request),
    ("variables",Lean.Json.arr (coordinates.map (variableJson N hybridIndex)).toArray),
    ("rows",rowsJson coordinates rows)]

def twoTipFixture {n j : Nat} (name : String) (sample : Fin n → Fin 2)
    (word : List (Symbol (Fin j) (Fin 3) (Fin 2))) : Lean.Json :=
  completedFixtureJson name N2 sample registry2 (fun _ => false) []
    (fun h => False.elim (UnifiedLean.G6.TwoTipChartFixture.noHybrid h)) [] word

def fixtureNamed (name : String) : Option Lean.Json :=
  match name with
  | "twoTipCalendar" => some (twoTipFixture name (fun x : Fin 2 => x) twoTipWord)
  | "serialNegativeTips" => some (twoTipFixture name repeatedSample serialWord)
  | "parallelCommonCalendar" => some (completedFixtureJson name NP parallelFiniteSample
      OriginalParallelEpochFixture.registry (fun _ => true)
      [OriginalParallelEpochFixture.ids 0]
      (fun h => (OriginalParallelEpochFixture.ids.symm h).val)
      [(3,2,3)] parallelFiniteWord)
  | _ => none

def run (args : List String) : IO UInt32 := do
  match args with
  | [name] =>
      match fixtureNamed name with
      | none => IO.eprintln "unknown original completed calendar fixture"; pure 2
      | some output => IO.println output.compress; pure 0
  | _ => IO.eprintln "one fixture name required"; pure 2

#print axioms twoTipCalendar
#print axioms serialCalendar
#print axioms parallelCalendar
#print axioms polynomial_completedNaturalWordRows
end UnifiedLean.G7.OriginalCompletedCalendarFixture
