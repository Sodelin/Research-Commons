import UnifiedLean.G6.PrivateRegisterErasure

/-!
UNCHECKED additive SAME-graph actual-merger/source-step consumer.
CLOUD-PRIVATE-REGISTER-STEP-SOL-2252Z, 7 October 2026.
The imported root erasure constructor is pinned to the split-branch derivative
SHA256 b9c845b56653599d0015e63d3d400e574fbec5955cde5b95271b4e4d5d8777c4.
Original UniformizedSourceStep supplies Choice, stepDestination and sourceStep.
No desired destination/kernel equation is an input premise. No compiler,
boundary/program/history/cross-graph/observation theorem is claimed.
-/

namespace UnifiedLean.G6.PrivateRegisterSourceStep
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.G6.PrivateRegisterErasure
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The original holding destination is the entering admitted Code itself. -/
theorem erase_actual_holding_destination (N : RootedBinary V E X)
    {sample : Copy → X} (P : Finset V) (s : Code N sample) :
    erasePrivateCode N P (stepDestination N s none) =
      stepDestination N (erasePrivateCode N P s) none := rfl

/-- Erase the actual legal merger after admitted snapshot coding, or merge
the erased entering Code with its SAME current original ordered pair.
The source-valid merger proof and all snapshot proof fields are reconstructed
by the original destination and root erasure constructors. -/
theorem erase_actual_merger_destination (N : RootedBinary V E X)
    {sample : Copy → X} (P : Finset V) (s : Code N sample) (p : Choice N s) :
    erasePrivateCode N P (stepDestination N s (some p)) =
      stepDestination N (erasePrivateCode N P s)
        (some (eraseChoiceEquiv N P s p)) := by
  apply Subtype.ext
  apply Snapshot.ext <;> rfl

/-- The Option catalogue transports the actual hold and original merger
choices; it does not manufacture a new choice distribution. -/
theorem erase_actual_destination (N : RootedBinary V E X)
    {sample : Copy → X} (P : Finset V) (s : Code N sample)
    (q : Option (Choice N s)) :
    erasePrivateCode N P (stepDestination N s q) =
      stepDestination N (erasePrivateCode N P s)
        (q.map (eraseChoiceEquiv N P s)) := by
  cases q with
  | none => exact erase_actual_holding_destination N P s
  | some p => exact erase_actual_merger_destination N P s p

/-- Both holding normalization and each original rho/2 merger weight are
unchanged. Choice uses only the unchanged live/location projections. -/
theorem erase_actual_choiceMass (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (P : Finset V)
    (s : Code N sample) (q : Option (Choice N s)) :
    choiceMass N r (erasePrivateCode N P s)
        (q.map (eraseChoiceEquiv N P s)) = choiceMass N r s q := by
  cases q <;> rfl

/-- On this SAME graph the root erasure catalogue equivalence is literally
the identity on Option E and ordered Copy pairs. The two dependent Choice
types reduce to the same live/population membership type. -/
theorem erase_actual_choicePMF (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (P : Finset V)
    (s : Code N sample) :
    choicePMF N r (erasePrivateCode N P s) = choicePMF N r s := by
  rfl

/-- Actual one-step kernel pushforward, derived from the unchanged actual
holding/ordered-pair PMF and the proved actual destination commutation.
It preserves the complete SAME-graph entering genealogy and population data;
it is not a guarded calendar or a cross-graph forest law. -/
theorem actual_sourceStep_erasure (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (P : Finset V)
    (s : Code N sample) :
    (sourceStep N r s).map (erasePrivateCode N P) =
      sourceStep N r (erasePrivateCode N P s) := by
  have hdest : erasePrivateCode N P ∘ stepDestination N s =
      stepDestination N (erasePrivateCode N P s) := by
    funext q
    cases q with
    | none => exact erase_actual_holding_destination N P s
    | some p => exact erase_actual_merger_destination N P s p
  unfold sourceStep
  rw [PMF.map_comp, hdest, erase_actual_choicePMF N r P s]

#print axioms erase_actual_holding_destination
#print axioms erase_actual_merger_destination
#print axioms erase_actual_destination
#print axioms erase_actual_choiceMass
#print axioms erase_actual_choicePMF
#print axioms actual_sourceStep_erasure

end UnifiedLean.G6.PrivateRegisterSourceStep
