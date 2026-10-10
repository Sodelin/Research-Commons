import UnifiedLean.G6.PrivateRegisterErasure
import UnifiedLean.Source.SourceBoundaryKernels

/-!
UNCHECKED actual SAME-graph boundary consumer. The defined operations preserve
all current forest fields and original physical IDs. COMMON may only read an
outside register site; INDEPENDENT still draws the actual CURRENT AtNode coins.
No source-law, cross-graph carrier or observation equality is an input.
Outside the sole frozen165 build. CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026.
-/
namespace UnifiedLean.G6.PrivateRegisterBoundary
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.G6.PrivateRegisterErasure
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem erase_exitCode (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) (e : E) :
    erasePrivateCode N P (exitCode N s e) =
      exitCode N (erasePrivateCode N P s) e := by
  apply Subtype.ext
  rfl

theorem erase_ordinaryCode (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) (e : E) :
    erasePrivateCode N P (ordinaryCode N s e) =
      ordinaryCode N (erasePrivateCode N P s) e := by
  apply Subtype.ext
  rfl

theorem erase_rootCode (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) :
    erasePrivateCode N P (rootCode N s) =
      rootCode N (erasePrivateCode N P s) := by
  apply Subtype.ext
  rfl

/-- AtNode has the identical actual live/location membership type after erasure. -/
theorem erase_pulseCode {N : RootedBinary V E X} {sample : Copy → X}
    (P : Finset V) (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (coin : AtNode (state s) H.hybrid → Bool) :
    erasePrivateCode N P (pulseCode H s coin) =
      pulseCode H (erasePrivateCode N P s) coin := by
  apply Subtype.ext
  rfl

theorem actual_independent_pulse_erasure {N : RootedBinary V E X}
    {sample : Copy → X} (P : Finset V) (H : GProgram.G2.OriginalHybridParents N)
    (gamma : unitInterval) (s : Code N sample) :
    (independentPulseKernel H gamma s).map (erasePrivateCode N P) =
      independentPulseKernel H gamma (erasePrivateCode N P s) := by
  rw [independentPulseKernel, PMF.map_comp]
  change (currentCoinPMF (AtNode (state s) H.hybrid) gamma).map
    ((erasePrivateCode N P) ∘ pulseCode H s) =
      (currentCoinPMF (AtNode (state s) H.hybrid) gamma).map
        (pulseCode H (erasePrivateCode N P s))
  congr 1

/-- No read of a private register bit is allowed in the retained word. This is
an explicit operation property, not an assumed probability-law identity. -/
def NoPrivateRead (N : RootedBinary V E X) (P : Finset V) :
    BoundaryOperation N → Prop
  | .common H => H.hybrid ∉ P
  | _ => True

theorem actual_boundary_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (op : BoundaryOperation N) (s : Code N sample)
    (hop : NoPrivateRead N P op) :
    (boundaryKernel N op s).map (erasePrivateCode N P) =
      boundaryKernel N op (erasePrivateCode N P s) := by
  cases op with
  | exit e =>
      simp only [boundaryKernel, PMF.pure_map, erase_exitCode]
  | ordinary e degree =>
      simp only [boundaryKernel, PMF.pure_map, erase_ordinaryCode]
  | root =>
      simp only [boundaryKernel, PMF.pure_map, erase_rootCode]
  | independent H gamma =>
      exact actual_independent_pulse_erasure P H gamma s
  | common H =>
      have hH : H.hybrid ∉ P := hop
      simp only [boundaryKernel, PMF.pure_map]
      rw [erase_pulseCode, erasePrivateCode_register_outside N P s H.hybrid hH]
      rfl

#print axioms erase_exitCode
#print axioms erase_ordinaryCode
#print axioms erase_rootCode
#print axioms erase_pulseCode
#print axioms actual_independent_pulse_erasure
#print axioms actual_boundary_erasure

end UnifiedLean.G6.PrivateRegisterBoundary
