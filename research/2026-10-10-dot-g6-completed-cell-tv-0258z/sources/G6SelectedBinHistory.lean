import ActualCalendarEndpointHistory
import G7SelectedCompletionPolynomial
import UnifiedLean.Source.UnrankedGenealogyObservation

/-!
The actual fixed-bin endpoint decoder factors through the FULL selected
endpoint history, including its entering selected state. The last completion
row retains the old bin matrix and is projected with the accepted actual
ancestral kernel theorem. No endpoint-only sufficiency claim is made.
Contributor: dot (OpenAI), 10 October 2026. Uncompiled candidate.
-/
namespace UnifiedLean.G6.SelectedBinHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open GProgram.G2.SourceFiniteHistory GProgram.G2.ActualPairCoalescence
open UnifiedLean.G6.BinHistory
open CloudG3.ActualCalendarEndpointHistory CloudG3.CompleteCalendarJointLaw
open GProgram.G7.SelectedCompletionPolynomial
open scoped Classical
variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def selectedTagUpdate (N : RootedBinary V E X) {sample : Copy → X}
    (a d : SelectedIndex N sample Finset.univ) (tag : Tag) (B : Copy → Copy → Tag)
    (x y : Copy) : Tag :=
  if ¬ sameBlock a.val x y ∧ sameBlock d.val x y then tag else B x y

/-- Tag writing uses exactly the old/destination ancestry relation retained by
full selected views. It reads no latent representative ID or private seed. -/
theorem actual_tag_update_projects (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (tag : Tag) (B : Copy → Copy → Tag) :
    selectedTagUpdate N (projection N Finset.univ s) (projection N Finset.univ d) tag B =
      tagUpdate N s d tag B := by
  funext x y
  have hs := selected_same_block (state s) s.property.forest Finset.univ
    (Finset.mem_univ x) (Finset.mem_univ y)
  have hd := selected_same_block (state d) d.property.forest Finset.univ
    (Finset.mem_univ x) (Finset.mem_univ y)
  simp only [selectedTagUpdate,projection,tagUpdate,hs,hd]

noncomputable def selectedStepTags (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (tag : Tag) (a d : SelectedIndex N sample Finset.univ)
    (B : Copy → Copy → Tag) : Copy → Copy → Tag := match op with
  | .interval _ => selectedTagUpdate N a d tag B
  | .boundary _ => B

theorem actual_step_tags_project (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (tag : Tag) (s d : Code N sample) (B : Copy → Copy → Tag) :
    selectedStepTags N op tag (projection N Finset.univ s) (projection N Finset.univ d) B =
      endpointStepTags N op tag s d B := by
  cases op with
  | interval h => exact actual_tag_update_projects N s d tag B
  | boundary b => rfl

noncomputable def projectTagged (N : RootedBinary V E X) {sample : Copy → X}
    (q : Code N sample × (Copy → Copy → Tag)) :
    SelectedIndex N sample Finset.univ × (Copy → Copy → Tag) :=
  (projection N Finset.univ q.1,q.2)

noncomputable def selectedHistoryReadout (N : RootedBinary V E X) {sample : Copy → X} :
    (word : List (ProgramStep N × Tag)) → SelectedIndex N sample Finset.univ →
    (Copy → Copy → Tag) → (Fin (physicalOps N word).length → SelectedIndex N sample Finset.univ) →
      SelectedIndex N sample Finset.univ × (Copy → Copy → Tag)
  | [],a,B,_ => (a,B)
  | q::word,a,B,h => by
      change (Fin ((physicalOps N word).length+1) → SelectedIndex N sample Finset.univ) at h
      exact selectedHistoryReadout N word (h 0)
        (selectedStepTags N q.1 q.2 a (h 0) B) (Fin.tail h)

/-- Literal same-record factorization of the complete endpoint-history decoder.
Every interval endpoint remains present; boundaries do not reset the bins. -/
theorem actual_endpoint_history_readout_projects (N : RootedBinary V E X)
    {sample : Copy → X} (word : List (ProgramStep N × Tag)) (s : Code N sample)
    (B : Copy → Copy → Tag) (h : Fin (physicalOps N word).length → Code N sample) :
    projectTagged N (endpointHistoryReadout N word s B h) =
      selectedHistoryReadout N word (projection N Finset.univ s) B
        (historyProjection (projection N Finset.univ) h) := by
  induction word generalizing s B with
  | nil => rfl
  | cons q word ih =>
      rcases q with ⟨op,tag⟩
      change (Fin ((physicalOps N word).length+1) → Code N sample) at h
      change projectTagged N (endpointHistoryReadout N word (h 0)
        (endpointStepTags N op tag s (h 0) B) (Fin.tail h)) =
        selectedHistoryReadout N word (projection N Finset.univ (h 0))
          (selectedStepTags N op tag (projection N Finset.univ s)
            (projection N Finset.univ (h 0)) B)
          (Fin.tail (historyProjection (projection N Finset.univ) h))
      rw [ih,actual_step_tags_project]
      rfl

noncomputable def selectedForestBins (N : RootedBinary V E X) {sample : Copy → X}
    (q : SelectedIndex N sample Finset.univ × (Copy → Copy → Tag)) :
    Finset (UnrankedTree Copy) × (Copy → Copy → Tag) :=
  (unrankedForest q.1.val,q.2)

/-- This is the same ordinary unranked forest/bin pair used by G5 and G6. -/
theorem actual_forest_bins_project (N : RootedBinary V E X) {sample : Copy → X}
    (q : Code N sample × (Copy → Copy → Tag)) :
    selectedForestBins N (projectTagged N q) =
      (sourceUnrankedForest (state q.1) Finset.univ,q.2) := rfl

/-- Any source-independent observed reader factors after the same complete
history. No raw Code reader is admitted by this statement. -/
theorem actual_observed_history_projects {O : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (word : List (ProgramStep N × Tag)) (s : Code N sample)
    (B : Copy → Copy → Tag) (h : Fin (physicalOps N word).length → Code N sample)
    (readout : (Finset (UnrankedTree Copy) × (Copy → Copy → Tag)) → O) :
    readout (sourceUnrankedForest (state (endpointHistoryReadout N word s B h).1) Finset.univ,
      (endpointHistoryReadout N word s B h).2) =
      readout (selectedForestBins N (selectedHistoryReadout N word
        (projection N Finset.univ s) B (historyProjection (projection N Finset.univ) h))) := by
  rw [← actual_endpoint_history_readout_projects,actual_forest_bins_project]

section Completion
variable [Nonempty Copy]

noncomputable def selectedJointTail (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag)
    (q : SelectedIndex N sample Finset.univ × (Copy → Copy → Tag)) :
    PMF (SelectedIndex N sample Finset.univ × (Copy → Copy → Tag)) :=
  (selectedCompletion N r q.1).map (fun d => (d,selectedTagUpdate N q.1 d tag q.2))

/-- Infinite ancestral completion is appended to the carried old bins in the
same conditional row; no independent remixing of past and completion occurs. -/
theorem actual_joint_tail_projects (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) (q : Code N sample × (Copy → Copy → Tag))
    (hq : AncestralRoot N q.1) :
    (jointTailKernel N r tag q).map (projectTagged N) =
      selectedJointTail N r tag (projectTagged N q) := by
  unfold jointTailKernel selectedJointTail
  dsimp only [projectTagged]
  rw [← actual_source_completion_projection N r q.1 hq]
  rw [PMF.map_comp,PMF.map_comp]
  congr 1
  funext d
  apply Prod.ext
  · rfl
  · exact (actual_tag_update_projects N q.1 d tag q.2).symm

/-- The root-support premise is local to the actual entering law; callers use
the admitted calendar's proved ancestral support, not a desired-law equality. -/
theorem actual_joint_completion_projects (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag)
    (law : PMF (Code N sample × (Copy → Copy → Tag)))
    (hroot : ∀ q ∈ law.support, AncestralRoot N q.1) :
    (law.bind (jointTailKernel N r tag)).map (projectTagged N) =
      (law.map (projectTagged N)).bind (selectedJointTail N r tag) := by
  rw [PMF.map_bind,PMF.bind_map]
  apply bind_congr_on_support
  intro q hq
  exact actual_joint_tail_projects N r tag q (hroot q hq)

end Completion
#print axioms actual_tag_update_projects
#print axioms actual_endpoint_history_readout_projects
#print axioms actual_observed_history_projects
#print axioms actual_joint_tail_projects
#print axioms actual_joint_completion_projects
end UnifiedLean.G6.SelectedBinHistory
