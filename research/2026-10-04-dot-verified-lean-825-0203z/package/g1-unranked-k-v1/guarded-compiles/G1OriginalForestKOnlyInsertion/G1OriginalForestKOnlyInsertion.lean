import G1ActualKProductInsertion

/-!
# Original physical forest assembled from the current-root unranked K

Contributor: dot, 2026-10-03. The old descendant-labelled actual source is
reconstructed, rather than defining the desired output law as a macro field.
Only CURRENT entering roots count toward the component cap. Exterior roots
and carried original subtrees are unrestricted.
-/
namespace G1OriginalForestKOnlyInsertion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedSourceView G1UnrankedActualFuture G1ActualUnrankedKMacro
open G1ActualJointProgram G1ActualJointEpoch G1ActualJointOpaqueContext
open G1ActualKProductInsertion G1OriginalCurrentRootReconstruction G1ContextualForestReplacement
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Exact larger-source output uses only the actual unranked K, the evolving
exterior state/history and SAME Γ, followed by the SAME original future.
Every already-formed original entering subtree is restored in the actual
complete rooted unranked forest. No output equality is supplied as a premise. -/
theorem actual_original_forest_K_only_insertion
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (inside outside : Finset Copy) (p : Location V E) (phase future : List (ProgramStep N))
    (s : Code N sample) (hi : inside ⊆ (state s).live) (ho : outside ⊆ (state s).live)
    (partition : inside ∪ outside = (state s).live)
    (hsep : SeparatedAgenda N r inside outside phase s)
    (hphysical : ∀ d ∈ (sourceProgram N r phase s).support, PhysicalKExit N inside outside p d) :
    (sourceProgram N r (phase ++ future) s).map (rootForest N) =
      (independentProduct (actualCurrentRootK N r phase s inside hi)
        (actualExteriorUnrankedState N r phase s outside ho)).bind
          (actualKContinuation N r inside outside p future s
            (fun v => (unrankedViewForest v).image
              (G1OpaqueSourceGrafting.graftUnranked (state s).genealogy))) := by
  rw [actual_original_whole_forest_kernel_law,originalCurrentRootKernel,PMF.map_comp]
  simpa only [Function.comp_def,partition] using
    (actual_unranked_K_product_carried_forest N r inside outside p phase future s hi ho hsep
      hphysical (state s).genealogy)

#print axioms actual_original_forest_K_only_insertion
end G1OriginalForestKOnlyInsertion
