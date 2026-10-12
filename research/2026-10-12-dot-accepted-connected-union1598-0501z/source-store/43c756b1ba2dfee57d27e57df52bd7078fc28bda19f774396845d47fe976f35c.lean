import G7ConstructivePanelJoin
import G7EffectiveFullEpochCoefficients

/-!
# Executable original panel joins with explicit literal Code witnesses

Contributor: Codex / lean_reuse_successor, 2026-10-10.
The data constructor is the constructive range proof's state, using the
inherited executable sourceState/encodeActual/project counterparts. No witness
is extracted from a Prop-valued existence statement and no Code universe is
searched. Draft source; fresh compilation and complete audit are required.
-/
namespace GProgram.G7.EffectivePanelJoin
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.ConstructivePanelJoin
open GProgram.G7.FiniteForestReassembly

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

def joinedStateEffective (keep : Finset Copy)
    (a : State V E (SelectedCopy keep))
    (b : State V E (SelectedCopy (Finset.univ \ keep))) : State V E Copy where
  live := Finset.univ.filter (fun x => if hx : x ∈ keep then
    (⟨x,hx⟩ : SelectedCopy keep) ∈ a.live else
    (⟨x,complement_mem keep x hx⟩ : SelectedCopy (Finset.univ \ keep)) ∈ b.live)
  ancestor x := if hx : x ∈ keep then (a.ancestor ⟨x,hx⟩).val
    else (b.ancestor ⟨x,complement_mem keep x hx⟩).val
  genealogy x := if hx : x ∈ keep then mapLabels Subtype.val (a.genealogy ⟨x,hx⟩)
    else mapLabels Subtype.val (b.genealogy ⟨x,complement_mem keep x hx⟩)
  location x := if hx : x ∈ keep then a.location ⟨x,hx⟩
    else b.location ⟨x,complement_mem keep x hx⟩
  register := a.register
  history := []

lemma joinedStateEffective_eq (keep : Finset Copy)
    (a : State V E (SelectedCopy keep))
    (b : State V E (SelectedCopy (Finset.univ \ keep))) :
    joinedStateEffective keep a b = joinedState keep a b := rfl

def joinedCode (N : RootedBinary V E X) {sample : Copy → X} (keep : Finset Copy)
    (a : Code N (selectedSample sample keep))
    (b : Code N (selectedSample sample (Finset.univ \ keep))) : Code N sample :=
  encodeActual N sample (joinedStateEffective keep (sourceState a) (sourceState b)) (by
    change SourceValid N sample (joinedState keep (state a) (state b))
    exact joinedState_sourceValid keep (state a) (state b) N sample a.property b.property)

lemma joinedCode_eq_joinCode (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (a : Code N (selectedSample sample keep))
    (b : Code N (selectedSample sample (Finset.univ \ keep))) :
    joinedCode N keep a b = joinCode keep N a b := by
  apply Subtype.ext
  rfl

def joinedSelected (N : RootedBinary V E X) {sample : Copy → X} (keep : Finset Copy)
    (a : Code N (selectedSample sample keep))
    (b : Code N (selectedSample sample (Finset.univ \ keep))) :
    SelectedIndex N sample Finset.univ := project N Finset.univ (joinedCode N keep a b)

theorem joinedSelected_eq (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy)
    (a : Code N (selectedSample sample keep))
    (b : Code N (selectedSample sample (Finset.univ \ keep))) :
    joinedSelected N keep a b = joinSelected N s keep
      (project N Finset.univ a, project N Finset.univ b) := by
  unfold joinedSelected
  rw [project_eq N Finset.univ (joinedCode N keep a b),joinSelected_eq]
  apply Subtype.ext
  rw [GProgram.G7.ConstructivePanelJoin.joinIndex_value]
  change selectedView (state (joinedCode N keep a b)) Finset.univ = _
  rw [joinedCode_eq_joinCode,joinCode_view,project_eq N Finset.univ a,
    project_eq N Finset.univ b]
  rfl

#print axioms joinedCode_eq_joinCode
#print axioms joinedSelected_eq
end GProgram.G7.EffectivePanelJoin
