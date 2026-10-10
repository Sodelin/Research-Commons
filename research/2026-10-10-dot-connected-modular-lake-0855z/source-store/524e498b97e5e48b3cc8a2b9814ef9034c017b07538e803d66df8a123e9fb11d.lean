import G1UnrankedSingleExitLabel

/-!
# Source-derived UNRANKED K-label continuation and actual phase insertion

Contributor: dot, 2026-10-03. The continuation is constructed from the SAME
actual original future process. Every supported label has an actual physical
exit-state witness. Its representation independence is DERIVED. Invalid labels
have a harmless fallback; they never occur on the actual phase-law support.
-/
namespace G1ActualUnrankedKMacro
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedSourceView G1UnrankedActualFuture G1UnrankedSingleExitLabel
open G1JointUnrankedForestAssembly G1ActualJointProgram G1SameOriginalExteriorContinuation
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Exterior causal state includes the SAME original register even if the
exterior panel is empty. K retains the entire rooted labelled unranked forest. -/
abbrev KExitData (V E Copy : Type*) := Finset (UnrankedTree Copy) × UnrankedView V E Copy

noncomputable def actualKExitData (N : RootedBinary V E X) {sample : Copy → X}
    (inside outside : Finset Copy) (s : Code N sample) : KExitData V E Copy :=
  (sourceUnrankedForest (state s) inside,unrankedView (selectedView (state s) outside))

/-- Physical source exit conditions. No desired kernel/output equality or
fitted demographic scalar is included. Both are derived by agenda admission. -/
def PhysicalKExit (N : RootedBinary V E X) {sample : Copy → X}
    (inside outside : Finset Copy) (p : Location V E) (s : Code N sample) : Prop :=
  PrunedPanelSeparated (state s) inside outside ∧ ∀ x ∈ inside, copyLocation (state s) x = p

noncomputable def actualKContinuation {Obs : Type*} (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (p : Location V E)
    (future : List (ProgramStep N)) (fallback : Code N sample)
    (readout : UnrankedView V E Copy → Obs) (data : KExitData V E Copy) : PMF Obs :=
  if h : ∃ s : Code N sample, PhysicalKExit N inside outside p s ∧ actualKExitData N inside outside s = data then
    (sourceProgram N r future (Classical.choose h)).map
      (fun d => readout (unrankedView (selectedView (state d) (inside ∪ outside))))
  else (sourceProgram N r future fallback).map
    (fun d => readout (unrankedView (selectedView (state d) (inside ∪ outside))))

/-- The constructed K-only continuation equals the SAME actual original
future row at every real physical source exit; current IDs/orientations vanish. -/
theorem actualKContinuation_at_actual_exit {Obs : Type*} (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (p : Location V E)
    (future : List (ProgramStep N)) (fallback s : Code N sample)
    (hphysical : PhysicalKExit N inside outside p s) (readout : UnrankedView V E Copy → Obs) :
    actualKContinuation N r inside outside p future fallback readout (actualKExitData N inside outside s) =
      (sourceProgram N r future s).map
        (fun d => readout (unrankedView (selectedView (state d) (inside ∪ outside)))) := by
  have hw : ∃ z : Code N sample, PhysicalKExit N inside outside p z ∧
      actualKExitData N inside outside z = actualKExitData N inside outside s := ⟨s,hphysical,rfl⟩
  rw [actualKContinuation,dif_pos hw]
  obtain ⟨hzphysical,hdata⟩ := Classical.choose_spec hw
  have hK : sourceUnrankedForest (state (Classical.choose hw)) inside = sourceUnrankedForest (state s) inside :=
    congrArg Prod.fst hdata
  have hout : unrankedView (selectedView (state (Classical.choose hw)) outside) =
      unrankedView (selectedView (state s) outside) := congrArg Prod.snd hdata
  have hreg : (state (Classical.choose hw)).register = (state s).register :=
    unranked_view_register _ _ hout
  exact actual_K_only_original_future N r inside outside future (Classical.choose hw) s p
    hzphysical.1 hphysical.1 hK hzphysical.2 hphysical.2 hreg hout readout

/-- The actual isolated phase is replaced through its source-derived complete
UNRANKED K/exterior/register label. The SAME original future process continues;
no desired programme equality or continuation law is a hypothesis. -/
theorem actual_K_only_phase_future_insertion {Obs : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (inside outside : Finset Copy)
    (p : Location V E) (phase future : List (ProgramStep N)) (s : Code N sample)
    (hphysical : ∀ d ∈ (sourceProgram N r phase s).support, PhysicalKExit N inside outside p d)
    (readout : UnrankedView V E Copy → Obs) :
    (sourceProgram N r (phase ++ future) s).map
      (fun d => readout (unrankedView (selectedView (state d) (inside ∪ outside)))) =
      ((sourceProgram N r phase s).map (actualKExitData N inside outside)).bind
        (actualKContinuation N r inside outside p future s readout) := by
  rw [actual_source_program_append,PMF.map_bind,PMF.bind_map]
  apply bind_eq_of_eq_on_support
  intro d hd
  exact (actualKContinuation_at_actual_exit N r inside outside p future s d (hphysical d hd) readout).symm

/-- Original carried trees may have arbitrarily many descendant labels.
UNRANKED K alone is inserted before the SAME source future and full grafting. -/
theorem actual_K_only_carried_forest_future {Desc : Type*} [DecidableEq Desc]
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (inside outside : Finset Copy) (p : Location V E) (phase future : List (ProgramStep N))
    (s : Code N sample)
    (hphysical : ∀ d ∈ (sourceProgram N r phase s).support, PhysicalKExit N inside outside p d)
    (input : Copy → Genealogy Desc) :
    (sourceProgram N r (phase ++ future) s).map
      (fun d => (sourceUnrankedForest (state d) (inside ∪ outside)).image (G1OpaqueSourceGrafting.graftUnranked input)) =
      ((sourceProgram N r phase s).map (actualKExitData N inside outside)).bind
        (actualKContinuation N r inside outside p future s
          (fun v => (unrankedViewForest v).image (G1OpaqueSourceGrafting.graftUnranked input))) := by
  simpa only [sourceUnrankedForest,actual_unranked_view_forest] using
    actual_K_only_phase_future_insertion N r inside outside p phase future s hphysical
      (fun v => (unrankedViewForest v).image (G1OpaqueSourceGrafting.graftUnranked input))

#print axioms actual_K_only_phase_future_insertion
#print axioms actual_K_only_carried_forest_future
end G1ActualUnrankedKMacro
