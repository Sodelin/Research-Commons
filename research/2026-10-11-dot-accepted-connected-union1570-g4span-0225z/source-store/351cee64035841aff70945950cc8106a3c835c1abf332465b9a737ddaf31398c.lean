import G5ObservedSafeTripleSupport
import G5RootCutChart
import G5AncestralTwoCutLaw

/-!
# The same observed support consumer at every finite cut age
Contributor: dot / OpenAI, 10 October 2026.
UNCOMPILED CANDIDATE. Reuses the earlier 9 October ancestral-cut drafts and the
accepted same-original-ancestral-interval extension. Root and above-root cuts
are not replaced by a new model or an observed population label.
-/
namespace GProgram.G5.AllAgeObservedSupport
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.NativeCurrentPortCompiler UnifiedLean.Source.SourceAncestralCompletion
open GProgram.G2.ChronologicalPathReadout
open GProgram.G5.HiddenRegisterTimedProjectivity GProgram.G5.ObservedBinHistory
open GProgram.G5.TwoCutSourceWord GProgram.G5.TwoCutPartitionDecoder
open GProgram.G5.OriginalProgramSurvival GProgram.G5.OriginalSelectedPosterior
open GProgram.G5.EnumeratedTripleRow GProgram.G5.EnumeratedPosteriorGerm
open GProgram.G5.ActualConditionalPartition GProgram.G5.ActualActivatedPrefix
open GProgram.G5.OriginalEpochChart GProgram.G5.OlderSideCutChart
open GProgram.G5.TriplePartitionReadout GProgram.G5.ActualFrozenTripleRow
open GProgram.G5.ObservedSafeTripleSupport GProgram.G5.RootCutChart GProgram.G5.AncestralTwoCutLaw
open GProgram.G5.PosteriorJointCell
attribute [local instance] GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
open scoped Classical NNReal ENNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

/-- A read-only observation contract produced by the actual source at the cut.
This is an internal consumer interface, not a field of source admission. -/
def ActualCutReadout (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Fin 3 → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (t : ℝ)
    (past : List (ProgramStep N)) (epsilon : ℝ) : Prop :=
  0 < epsilon ∧
  (∀ s : ActualSeed N (originalTripleCodePosterior N sample p r past), ∀ x,
    copyLocation (state s.val) x = originalPlace N (codePopulation N s.val x)) ∧
  ∀ u : ℝ≥0, (u : ℝ) < epsilon →
    (naturalObservedFullLaw N C sample H p common r).map
      (fun o => let B := observedAgeBins (twoCutBin t (t+u)) o
        (binPartition (Equiv.refl _) 0 B,binPartition (Equiv.refl _) 1 B)) =
      (cutJoint N sample p r past u).toMeasure

/-- The original root and every older finite cut have the same ordinary
observation/conditional-source interface, using the unchanged ancestral clock. -/
theorem actual_root_cut_readout (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Fin 3 → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (t : ℝ)
    (ht : C.age N.root ≤ t) :
    ActualCutReadout N C sample H p common r t (rootPast N C H p common t) 1 := by
  refine ⟨by norm_num,?_,?_⟩
  · intro s x
    have hroot := actual_root_posterior_support N C sample H p common r t s x
    simp only [codePopulation,hroot,originalPlace]
  · intro u _
    have ho := actual_observed_ancestral_two_cut_law N C sample H p common r
      (Real.toNNReal (t-C.age N.root)) u (Equiv.refl _)
    dsimp only at ho
    rw [root_past_exact_age N C H p common t ht] at ho
    exact ho

/-- Every finite age from contemporaneous sampling onward has a derived
actual prefix, positive future window and ordinary two-cut observed readout.
The endpoint convention processes the whole tied boundary batch first. -/
theorem actual_all_age_cut_readout (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Fin 3 → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a0 t : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0) (ht : a0 ≤ t) :
    ∃ (past : List (ProgramStep N)) (epsilon : ℝ),
      ActualCutReadout N C sample H p common r t past epsilon := by
  by_cases hroot : t < C.age N.root
  · obtain ⟨pre,guard,next,post,hsplit,hleft,hright⟩ := original_older_gap_exists N C t
      (by simpa only [first_date_of_contemporaneous_tips N C a0 htips] using ht) hroot
    refine ⟨cutPast N C H p common pre guard t,next-t,sub_pos.mpr hright,
      actual_cut_posterior_placement N C sample H p common r a0 t htips
        pre post guard next hsplit hleft hright hroot,?_⟩
    exact actual_cut_joint_observed N C sample H p common r pre post guard next t hsplit hleft hright
  · exact ⟨rootPast N C H p common t,1,
      actual_root_cut_readout N C sample H p common r t (le_of_not_gt hroot)⟩

section TwoSources
variable {V₂ E₂ : Type*} [DecidableEq V₂] [DecidableEq E₂] [Fintype V₂] [Fintype E₂]

/-- The common observable joint reader supplies equal conditioning mass and
therefore equal conditional germs. This helper's cut interfaces are supplied
by the actual source theorem in the terminal theorem below. -/
theorem cut_readouts_identify_occupancy
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Fin 3 → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : GProgram.G5.Calendar N₂.graph)
    (sample₂ : Fin 3 → X) (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂)
    (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (t : ℝ) (past : List (ProgramStep N)) (past₂ : List (ProgramStep N₂))
    (epsilon epsilon₂ : ℝ)
    (hread : ActualCutReadout N C sample H p common r t past epsilon)
    (hread₂ : ActualCutReadout N₂ C₂ sample₂ H₂ p₂ common₂ r₂ t past₂ epsilon₂)
    (heq : naturalObservedFullLaw N C sample H p common r =
      naturalObservedFullLaw N₂ C₂ sample₂ H₂ p₂ common₂ r₂) :
    ∀ gene, (∃ s : ActualSeed N (originalTripleCodePosterior N sample p r past),
      ancestorPartition (codePopulation N s.val) = gene) ↔
      ∃ s : ActualSeed N₂ (originalTripleCodePosterior N₂ sample₂ p₂ r₂ past₂),
        ancestorPartition (codePopulation N₂ s.val) = gene := by
  have hepsilon : 0 < min epsilon epsilon₂ := lt_min hread.1 hread₂.1
  have hjoint (u : ℝ≥0) (hu : (u : ℝ) < min epsilon epsilon₂) :
      cutJoint N sample p r past u = cutJoint N₂ sample₂ p₂ r₂ past₂ u := by
    apply PMF.toMeasure_injective
    rw [←hread.2.2 u (hu.trans_le (min_le_left _ _)),
      ←hread₂.2.2 u (hu.trans_le (min_le_right _ _)),heq]
  have hmarginal := congrArg (fun mu : PMF (Fin 5 × Fin 5) => mu.map Prod.fst)
    (hjoint 0 (by exact hepsilon))
  rw [cut_joint_first_marginal,cut_joint_first_marginal] at hmarginal
  have hden : (originalProgramLaw N sample p r past).toOuterMeasure
      {d | indexedPartition N (Equiv.refl _) d = 0} =
      (originalProgramLaw N₂ sample₂ p₂ r₂ past₂).toOuterMeasure
        {d | indexedPartition N₂ (Equiv.refl _) d = 0} := by
    have h := congrArg (fun mu : PMF (Fin 5) => mu.toOuterMeasure {0}) hmarginal
    rw [PMF.toOuterMeasure_map_apply,PMF.toOuterMeasure_map_apply] at h
    exact h
  apply actual_source_occupancy_support_of_right_germ N N₂ (Equiv.refl _) r r₂
    (originalTripleCodePosterior N sample p r past) (originalTripleCodePosterior N₂ sample₂ p₂ r₂ past₂)
    (original_triple_posterior_starts_singleton N sample p r past)
    (original_triple_posterior_starts_singleton N₂ sample₂ p₂ r₂ past₂)
    (fun s => codePopulation N s.val) (fun s => codePopulation N₂ s.val) hread.2.1 hread₂.2.1 hepsilon
  intro gene u hu
  rw [actual_conditional_partition_cell,actual_conditional_partition_cell,hden]
  change (cutJoint N sample p r past u (0,gene) * _).toReal =
    (cutJoint N₂ sample₂ p₂ r₂ past₂ u (0,gene) * _).toReal
  rw [hjoint u hu]

/-- The observed-law hypothesis alone gives actual occupancy support at every
finite requested age, including a cut above one root and below the other.
It does not assume equal hidden posteriors or equal original root ages. -/
theorem equal_observed_laws_all_age_actual_occupancy
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Fin 3 → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : GProgram.G5.Calendar N₂.graph)
    (sample₂ : Fin 3 → X) (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂)
    (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0)
    (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0) (ht : a0 ≤ t)
    (heq : naturalObservedFullLaw N C sample H p common r =
      naturalObservedFullLaw N₂ C₂ sample₂ H₂ p₂ common₂ r₂) :
    ∃ (past : List (ProgramStep N)) (past₂ : List (ProgramStep N₂)) (epsilon epsilon₂ : ℝ),
      ActualCutReadout N C sample H p common r t past epsilon ∧
      ActualCutReadout N₂ C₂ sample₂ H₂ p₂ common₂ r₂ t past₂ epsilon₂ ∧
      ∀ gene, (∃ s : ActualSeed N (originalTripleCodePosterior N sample p r past),
        ancestorPartition (codePopulation N s.val) = gene) ↔
        ∃ s : ActualSeed N₂ (originalTripleCodePosterior N₂ sample₂ p₂ r₂ past₂),
          ancestorPartition (codePopulation N₂ s.val) = gene := by
  obtain ⟨past,epsilon,hread⟩ := actual_all_age_cut_readout N C sample H p common r a0 t htips ht
  obtain ⟨past₂,epsilon₂,hread₂⟩ := actual_all_age_cut_readout N₂ C₂ sample₂ H₂ p₂ common₂ r₂ a0 t htips₂ ht
  exact ⟨past,past₂,epsilon,epsilon₂,hread,hread₂,
    cut_readouts_identify_occupancy N C sample H p common r N₂ C₂ sample₂ H₂ p₂ common₂ r₂
      t past past₂ epsilon epsilon₂ hread hread₂ heq⟩
end TwoSources

#print axioms actual_root_cut_readout
#print axioms actual_all_age_cut_readout
#print axioms cut_readouts_identify_occupancy
#print axioms equal_observed_laws_all_age_actual_occupancy
end GProgram.G5.AllAgeObservedSupport
