import UnifiedLean.G6.PrivateRegisterErasure
import G7EffectiveSourceEnumeration

/-!
Source-only aligned register erasure for the existing selected projection.
Contributor: Codex lean_reuse_successor, 2026-10-11. Not compiled or accepted.

Only the original V register slots in P are set to false. Both selected
ordered genealogy and original population maps are retained. This value
composition introduces no seed, stochastic kernel, history engine or native
encoding relation. For the full observer use keep = Finset.univ; one private
site uses P = {v} with v its original vertex, not its hybrid ordinal.

The carried-forest readout already has G1OriginalWholeCausalView.whole_forest_eq.
No new forest theorem or reconstruction premise is introduced here.
-/
namespace GProgram.G6.ErasedSelectedProjection
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.G6.PrivateRegisterErasure
open GProgram.G7.EffectiveSourceEnumeration
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Erase exactly the supplied original-vertex slots of a selected value. -/
noncomputable def eraseSelected (P : Finset V) (v : SelectedView V E Copy) :
    SelectedView V E Copy :=
  { v with register := fun x => if x ∈ P then false else v.register x }

/-- Source-code erasure commutes with the existing selected value projection. -/
theorem project_erasePrivateCode_value (N : RootedBinary V E X)
    {sample : Copy → X} (P : Finset V) (keep : Finset Copy) (s : Code N sample) :
    (project N keep (erasePrivateCode N P s)).val =
      eraseSelected P (project N keep s).val := by
  apply SelectedView.ext <;> rfl

end GProgram.G6.ErasedSelectedProjection
