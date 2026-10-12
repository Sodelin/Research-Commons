import G7NaturalCalendarRelabelling
import UnifiedLean.Source.SourceCompletionHarmonic
import UnifiedLean.Source.SourceCompletedUnrankedTree

/-! Graph relabelling of the existing actual embedded jump, ancestral completion
and natural completed unranked readout. Contributor: dot,2026-10-09.
Completion and its physical clock binding are inherited, not reproved.
-/
namespace GProgram.G7.CompletedUnrankedRelabelling
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open GProgram.G7.OriginalRelabelling GProgram.G7.CalendarNodeRelabelling
open GProgram.G7.SnapshotRelabelling GProgram.G7.SourceStepRelabelling
open GProgram.G7.NaturalCalendarRelabelling
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceEmbeddedJumpLaw
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceCompletedUnrankedTree UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceNaturalInitialization
open scoped Classical
variable {V E W F Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable [Fintype Copy] [DecidableEq Copy]

@[simp] theorem jump_mass (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (q : Option (Choice N s)) :
    jumpMass (network N v e) (rates e r) (code N v e s)
      ((Equiv.optionCongr (choices N v e s)) q) = jumpMass N r s q := by
  cases q <;> simp [jumpMass]

theorem jump_choice (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :
    (sourceJumpChoice N r s).map (Equiv.optionCongr (choices N v e s)) =
      sourceJumpChoice (network N v e) (rates e r) (code N v e s) := by
  apply PMF.ext
  intro b
  obtain ⟨a,rfl⟩ := (Equiv.optionCongr (choices N v e s)).surjective b
  rw [pmf_map_equiv_apply,sourceJumpChoice_apply,sourceJumpChoice_apply,jump_mass]

theorem jump_step (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :
    (sourceJumpStep N r s).map (code N v e) =
      sourceJumpStep (network N v e) (rates e r) (code N v e s) := by
  unfold sourceJumpStep
  rw [PMF.map_comp]
  have hf : (code N v e ∘ stepDestination N s) =
      stepDestination (network N v e) (code N v e s) ∘ Equiv.optionCongr (choices N v e s) := by
    funext q
    exact GProgram.G7.SourceStepRelabelling.destination N v e s q
  rw [hf,← PMF.map_comp,jump_choice]

theorem ancestral_completion (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (k : Nat) (s : Code N sample) :
    (ancestralCompletion N r k s).map (code N v e) =
      ancestralCompletion (network N v e) (rates e r) k (code N v e s) := by
  induction k generalizing s with
  | zero => simp only [ancestralCompletion,PMF.pure_map]
  | succ k ih =>
    rw [ancestralCompletion,PMF.map_bind]
    simp_rw [ih]
    change (sourceJumpStep N r s).bind
      (ancestralCompletion (network N v e) (rates e r) k ∘ code N v e) = _
    rw [← PMF.bind_map,jump_step]
    rfl

theorem completion_kernel (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :
    (completionKernel N r s).map (code N v e) =
      completionKernel (network N v e) (rates e r) (code N v e s) :=
  ancestral_completion N v e r _ s

theorem natural_completed (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (c : Hybrid N → Bool) (r : PositivePairRates E) :
    (naturalCompletedLaw N C sample H p c r).map (code N v e) =
      naturalCompletedLaw (network N v e) (calendar N v e C) sample (registry N v e H)
        (inheritance N v e p) (common N v e c) (rates e r) := by
  unfold naturalCompletedLaw
  rw [PMF.map_bind]
  simp_rw [ancestral_completion]
  change (naturalCalendarLaw N C sample H p c r).bind
    (ancestralCompletion (network N v e) (rates e r) (Fintype.card Copy) ∘ code N v e) = _
  rw [← PMF.bind_map,natural_calendar]

@[simp] theorem unranked_readout (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) (keep : Finset Copy) :
    sourceUnrankedForest (state (code N v e s)) keep = sourceUnrankedForest (state s) keep := by
  rw [code_state]
  rfl

/-- The actual inherited completed rooted unranked source law, with named
copy leaves unchanged. This is an observation equality, not only a hidden
snapshot equality, and uses the generated calendar including every tie. -/
theorem natural_completed_unranked (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (c : Hybrid N → Bool) (r : PositivePairRates E) :
    naturalCompletedUnrankedLaw N C sample H p c r =
      naturalCompletedUnrankedLaw (network N v e) (calendar N v e C) sample (registry N v e H)
        (inheritance N v e p) (common N v e c) (rates e r) := by
  unfold naturalCompletedUnrankedLaw
  rw [← natural_completed N v e C sample H p c r,PMF.map_comp]
  congr 1

#print axioms completion_kernel
#print axioms natural_completed
#print axioms natural_completed_unranked
end GProgram.G7.CompletedUnrankedRelabelling
