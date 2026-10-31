import G7EffectiveAncestralCompletion
import G7OriginalEpochFixture
import Lean.Data.Json

/-!
# Six actual original rational ancestral-completion controls

Contributor: Codex / lean_reuse_successor, 2026-10-10.
The exact unchanged ordered-half-rate coefficients are read only on the
proved literal merger support. Their constant terms give complete selected
fibres with a nonzero literal witness. The genuine inherited completion limit
is bound by G7EffectiveAncestralCompletion, with nonempty original Copy and
all-copy ancestral-root support. JSON is a finite fixture utility, not a
universal serializer or native Rust refinement theorem. Fresh checks pending.
-/
namespace UnifiedLean.G7.OriginalCompletionFixture
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceAncestralCompletion
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.EffectiveAncestralCompletion

abbrev N := UnifiedLean.G7.OriginalEpochFixture.N
def register (v : Fin 3) : Bool := v.val % 2 == 0

def flatState (n : Nat) : State (Fin 3) (Fin 2) (Fin n) :=
  UnifiedLean.G7.OriginalEpochFixture.singletonState
    (fun _ => .rootPopulation N.root) register

theorem flatState_sourceValid (n : Nat) (sample : Fin n → Fin 2) :
    SourceValid N sample (flatState n) := by
  refine ⟨UnifiedLean.G7.OriginalEpochFixture.singletonState_valid _ _,?_⟩
  intro x
  exact ⟨rfl,N.rooted (N.leaf (sample x))⟩

def flatCode (n : Nat) (sample : Fin n → Fin 2) : Code N sample :=
  encodeActual N sample (flatState n) (flatState_sourceValid n sample)

lemma encoded_ancestral {n : Nat} (sample : Fin n → Fin 2)
    (s : State (Fin 3) (Fin 2) (Fin n)) (hs : SourceValid N sample s)
    (hroot : ∀ x, copyLocation s x = .rootPopulation N.root) :
    AncestralRoot N (encodeActual N sample s hs) := by
  intro x
  change copyLocation (decodeSnapshot N.root (encodeSnapshot s hs.forest)) x = _
  rw [decode_encode_copyLocation]
  exact hroot x

theorem flatCode_ancestral (n : Nat) (sample : Fin n → Fin 2) :
    AncestralRoot N (flatCode n sample) :=
  encoded_ancestral sample (flatState n) (flatState_sourceValid n sample) (fun _ => rfl)

def carriedSample (x : Fin 4) : Fin 2 := if x = 3 then 1 else 0
def carriedState : State (Fin 3) (Fin 2) (Fin 4) where
  live := {2,3}
  ancestor x := if x = 3 then 3 else 2
  genealogy x := if x = 2 then .graft (.graft (.leaf 0) (.leaf 1)) (.leaf 2) else .leaf x
  location _ := .rootPopulation N.root
  register := register
  history := []

theorem carriedState_sourceValid : SourceValid N carriedSample carriedState := by
  refine ⟨?_,?_⟩
  · letI := forestValidDecidable carriedState
    exact of_decide_eq_true (by decide)
  · intro x
    exact ⟨rfl,N.rooted (N.leaf (carriedSample x))⟩

def carriedCode : Code N carriedSample :=
  encodeActual N carriedSample carriedState carriedState_sourceValid

theorem carriedCode_ancestral : AncestralRoot N carriedCode :=
  encoded_ancestral carriedSample carriedState carriedState_sourceValid (fun _ => rfl)

def fixtureJson {n : Nat} (name : String) {sample : Fin n → Fin 2}
    (labels : Fin n → Nat) (s : Code N sample) (_hs : AncestralRoot N s) : Lean.Json :=
  let rows := rationalRows N s
  let keys := (rows.map fun row => project N Finset.univ row.1).eraseDups
  let output := keys.flatMap fun key =>
    let q := readRational (project N Finset.univ) rows key
    if q = 0 then [] else
      match rows.find? (fun row => project N Finset.univ row.1 == key && row.2 != 0) with
      | none => []
      | some witness => [Lean.Json.mkObj [
          ("view",UnifiedLean.G7.OriginalEpochFixture.viewJson key),
          ("witness",UnifiedLean.G7.OriginalEpochFixture.snapshotJson witness.1),
          ("weight",Lean.Json.str (UnifiedLean.G7.OriginalEpochFixture.rationalText q))]]
  Lean.Json.mkObj [
    ("schema",Lean.Json.str "source_completion_probe_v1"),("fixture",Lean.Json.str name),
    ("context",UnifiedLean.G7.OriginalEpochFixture.contextJson N labels s []),
    ("rows",Lean.Json.arr output.toArray)]

def oneSample (_ : Fin 1) : Fin 2 := 1
def threeSample (x : Fin 3) : Fin 2 := if x = 2 then 1 else 0
def permutedLabels (x : Fin 4) : Nat :=
  if x = 0 then 3 else if x = 1 then 0 else if x = 2 then 2 else 1

def fixtureNamed : String → Option Lean.Json
  | "completion1" => some (fixtureJson "completion1" Fin.val
      (flatCode 1 oneSample) (flatCode_ancestral 1 oneSample))
  | "completion2" => some (fixtureJson "completion2" Fin.val
      (flatCode 2 id) (flatCode_ancestral 2 id))
  | "completion3" => some (fixtureJson "completion3" Fin.val
      (flatCode 3 threeSample) (flatCode_ancestral 3 threeSample))
  | "completion4" => some (fixtureJson "completion4" Fin.val
      (flatCode 4 carriedSample) (flatCode_ancestral 4 carriedSample))
  | "completionCarriedNonminimum" => some (fixtureJson "completionCarriedNonminimum" Fin.val
      carriedCode carriedCode_ancestral)
  | "completionPermutedFour" => some (fixtureJson "completionPermutedFour" permutedLabels
      (flatCode 4 carriedSample) (flatCode_ancestral 4 carriedSample))
  | _ => none

def run (args : List String) : IO UInt32 := do
  let stdout ← IO.getStdout
  match args with
  | [name] =>
    match fixtureNamed name with
    | some result => stdout.putStrLn result.compress; return 0
    | none => return 2
  | _ => return 2

#print axioms flatState_sourceValid
#print axioms encoded_ancestral
#print axioms carriedState_sourceValid
#print axioms carriedCode_ancestral
end UnifiedLean.G7.OriginalCompletionFixture
