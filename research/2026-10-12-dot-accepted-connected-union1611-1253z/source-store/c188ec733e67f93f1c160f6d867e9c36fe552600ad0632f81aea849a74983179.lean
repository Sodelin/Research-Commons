import G1ActualUnrankedKMacro

/-!
# Final actual joint phase replaced by K plus evolving exterior state

Contributor: dot, 2026-10-03. K is computed on the TRUE smaller current-root
source. The exterior is the concurrent original source process. The SAME
original future runs from their UNRANKED K/exterior/register label.
-/
namespace G1ActualKProductInsertion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedSourceView G1UnrankedActualFuture G1ActualUnrankedKMacro
open G1ActualJointProgram G1ActualJointEpoch G1ActualJointOpaqueContext
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Source-derived complete unranked current-root K. Source initialization,
original rates, graph, site parameters/operations and SAME Γ remain actual. -/
noncomputable def actualCurrentRootK (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (s : Code N sample)
    (inside : Finset Copy) (hi : inside ⊆ (state s).live) : PMF (Finset (UnrankedTree Copy)) :=
  (currentPanelProgramLaw N r phase s inside hi).map unrankedForest

noncomputable def actualExteriorUnrankedState (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (s : Code N sample)
    (outside : Finset Copy) (ho : outside ⊆ (state s).live) : PMF (UnrankedView V E Copy) :=
  (currentPanelProgramLaw N r phase s outside ho).map unrankedView

/-- Actual phase law at its K/exterior interface is the product of the TRUE
small current-root K source and concurrently evolving true exterior source. -/
theorem actual_K_exterior_interface_product (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (phase : List (ProgramStep N))
    (s : Code N sample) (hi : inside ⊆ (state s).live) (ho : outside ⊆ (state s).live)
    (hsep : SeparatedAgenda N r inside outside phase s) :
    (sourceProgram N r phase s).map (actualKExitData N inside outside) =
      independentProduct (actualCurrentRootK N r phase s inside hi)
        (actualExteriorUnrankedState N r phase s outside ho) := by
  have h := congrArg (fun p => p.map (fun v : SelectedView V E Copy × SelectedView V E Copy =>
      (unrankedForest v.1,unrankedView v.2)))
    (actual_joint_smaller_current_sources N r inside outside phase s hi ho hsep)
  rw [independentProduct_map] at h
  change (sourceProgram N r phase s).map (fun d =>
    (unrankedForest (selectedView (state d) inside),
      unrankedView (selectedView (state d) outside))) = _
  simpa only [PMF.map_comp,Function.comp_def,actualKExitData,sourceUnrankedForest,
    actualCurrentRootK,actualExteriorUnrankedState] using h

/-- Final SOURCE-native contextual G1 insertion at the original one-population
exit. K alone is UNRANKED; all original clades, SAME Γ and exterior causal state
survive. Actual future root/cross-panel operations remain unrestricted. -/
theorem actual_unranked_K_product_same_original_future {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (inside outside : Finset Copy) (p : Location V E) (phase future : List (ProgramStep N))
    (s : Code N sample) (hi : inside ⊆ (state s).live) (ho : outside ⊆ (state s).live)
    (hsep : SeparatedAgenda N r inside outside phase s)
    (hphysical : ∀ d ∈ (sourceProgram N r phase s).support, PhysicalKExit N inside outside p d)
    (readout : UnrankedView V E Copy → Obs) :
    (sourceProgram N r (phase ++ future) s).map
      (fun d => readout (unrankedView (selectedView (state d) (inside ∪ outside)))) =
      (independentProduct (actualCurrentRootK N r phase s inside hi)
        (actualExteriorUnrankedState N r phase s outside ho)).bind
          (actualKContinuation N r inside outside p future s readout) := by
  rw [actual_K_only_phase_future_insertion N r inside outside p phase future s hphysical,
    actual_K_exterior_interface_product N r inside outside phase s hi ho hsep]

/-- Every already-formed entering subtree is restored in the complete future
original rooted unranked forest. Desc may be infinite; no leaf-count cap exists. -/
theorem actual_unranked_K_product_carried_forest {Desc : Type*} [DecidableEq Desc]
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (inside outside : Finset Copy) (p : Location V E) (phase future : List (ProgramStep N))
    (s : Code N sample) (hi : inside ⊆ (state s).live) (ho : outside ⊆ (state s).live)
    (hsep : SeparatedAgenda N r inside outside phase s)
    (hphysical : ∀ d ∈ (sourceProgram N r phase s).support, PhysicalKExit N inside outside p d)
    (input : Copy → Genealogy Desc) :
    (sourceProgram N r (phase ++ future) s).map
      (fun d => (sourceUnrankedForest (state d) (inside ∪ outside)).image
        (G1OpaqueSourceGrafting.graftUnranked input)) =
      (independentProduct (actualCurrentRootK N r phase s inside hi)
        (actualExteriorUnrankedState N r phase s outside ho)).bind
          (actualKContinuation N r inside outside p future s
            (fun v => (unrankedViewForest v).image (G1OpaqueSourceGrafting.graftUnranked input))) := by
  rw [actual_K_only_carried_forest_future N r inside outside p phase future s hphysical,
    actual_K_exterior_interface_product N r inside outside phase s hi ho hsep]

#print axioms actual_unranked_K_product_same_original_future
#print axioms actual_unranked_K_product_carried_forest
end G1ActualKProductInsertion
