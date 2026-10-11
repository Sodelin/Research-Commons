import G4SpecifiedCombEvent
import G7SelectedCompletionPolynomial
import G5CompletionPairPersistence
import UnifiedLean.Source.SourceCompletedUnrankedTree

/-!
# Specified comb on the actual selected completed topology

Contributor: dot (OpenAI), 11 October 2026.
UNCOMPILED source-only consumer of the separately reviewed coefficient draft.
The existing observer discards population, register and survivor identifiers,
retaining exactly the original-labelled child-swap genealogy quotient. We
identify its singleton event with the internal B-coordinate completion event.
The source law and completion kernel are unchanged. Full Copy coverage by B
and the A-list is explicit; no larger-panel acquisition or physical cut,
exposure, cross-arity scaling or natural-bank average is supplied here.
-/
namespace DotG34.SpecifiedCombSelectedObservation
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceCompletedUnrankedTree
open GProgram.G5.CompletionPairPersistence
open GProgram.G7.SelectedCompletionPolynomial
open DotG34.SpecifiedCombEvent DotG34.SpecifiedCombEvent.ActualCompletion
open scoped Classical BigOperators ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Nonempty Copy]

/-- Every supported completed forest has precisely B's completed tree.
This identifies the actual topology observer, not the hidden Code carrier. -/
lemma supported_completed_forest_at_B (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (hroot : AncestralRoot N s) (b : Copy) (d : Code N sample)
    (hd : d ∈ (completionKernel N r s).support) :
    sourceUnrankedForest (state d) Finset.univ =
      {toUnranked ((state d).genealogy ((state d).ancestor b))} := by
  ext q
  rw [mem_sourceUnrankedForest,Finset.mem_singleton]
  constructor
  · rintro ⟨x,_,t,ht,hq⟩
    rw [full_prune] at ht
    have he := Option.some.inj ht
    have ha := completion_all_pairs N r s d hroot hd x b
    exact hq.symm.trans ((congrArg toUnranked he).symm.trans
      (congrArg (fun a => toUnranked ((state d).genealogy a)) ha))
  · intro hq
    exact ⟨b,Finset.mem_univ b,(state d).genealogy ((state d).ancestor b),
      full_prune _,hq.symm⟩

/-- The exact singleton topology event has the internal tree-event mass.
Only actual completion support is used, including zero-weight rows correctly. -/
theorem actual_completed_forest_singleton_mass (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (hroot : AncestralRoot N s) (b : Copy) (target : UnrankedTree Copy) :
    ((completionKernel N r s).map
      (fun d => sourceUnrankedForest (state d) Finset.univ)) {target} =
      completionTreeLaw N r b s target := by
  rw [completionTreeLaw,PMF.map_apply,PMF.map_apply]
  apply tsum_congr
  intro d
  by_cases hd : completionKernel N r s d = 0
  · simp only [hd,ite_self]
  · have hs := (PMF.mem_support_iff _ _).mpr hd
    rw [supported_completed_forest_at_B N r s hroot b d hs]
    simp only [Finset.singleton_inj]

/-- Reuse the existing actual full selected projection theorem, then erase
hidden coordinates using the inherited unranked forest observer. -/
theorem selected_completed_forest_law (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (hroot : AncestralRoot N s) :
    (selectedCompletion N r (projection N Finset.univ s)).map
      (fun a => unrankedForest a.val) =
    (completionKernel N r s).map
      (fun d => sourceUnrankedForest (state d) Finset.univ) := by
  rw [← actual_source_completion_projection N r s hroot,PMF.map_comp]
  rfl

/-- The coefficient now evaluates the actual passive selected-topology event.
One specified labelled comb is tested, not a union of B-spine combs. -/
theorem actual_selected_specified_comb_probability (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (b : Copy) (as : List Copy) (hroot : AncestralRoot N s)
    (hflat : ∀ x, (state s).genealogy ((state s).ancestor x) = .leaf x)
    (hcover : ∀ x, x = b ∨ x ∈ as) (hnodup : as.Nodup) (hb : b ∉ as)
    (hnonempty : as ≠ []) :
    ((selectedCompletion N r (projection N Finset.univ s)).map
      (fun a => unrankedForest a.val)) {toUnranked (comb b as)} =
      ENNReal.ofReal (2^as.length /
        ((Nat.factorial (as.length+1) : ℝ) * (Nat.factorial as.length : ℝ))) := by
  rw [selected_completed_forest_law N r s hroot,
    actual_completed_forest_singleton_mass N r s hroot b]
  exact actual_flat_specified_comb_probability N r s b as hroot hflat
    hcover hnodup hb hnonempty

#print axioms supported_completed_forest_at_B
#print axioms actual_completed_forest_singleton_mass
#print axioms selected_completed_forest_law
#print axioms actual_selected_specified_comb_probability
end DotG34.SpecifiedCombSelectedObservation
