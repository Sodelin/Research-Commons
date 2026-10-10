import G5SafePrefixRouteBridge
import G5OlderSideCutConditionalLaw

/-!
# Ordinary triple observation equality to safe geometric support

Contributor: dot / OpenAI, 10 October 2026.
UNCOMPILED INTEGRATION CANDIDATE. This composes the existing actual observed
joint-law, Bayes-cell and positive frozen-germ providers with the separately
reviewed candidate actual safe-position support bridge. It does not assume
equality of hidden state laws or posterior measures. The observed reader is
exactly the same source-independent two-cut partition reader on both graphs.
-/
namespace GProgram.G5.ObservedSafeTripleSupport
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.NativeCurrentPortCompiler
open GProgram.G2.ChronologicalPathReadout
open GProgram.G5.HiddenRegisterTimedProjectivity GProgram.G5.ObservedBinHistory
open GProgram.G5.TwoCutSourceWord GProgram.G5.TwoCutPartitionDecoder
open GProgram.G5.ObservedTwoCutPartitionLaw GProgram.G5.OriginalProgramSurvival
open GProgram.G5.OriginalSelectedPosterior GProgram.G5.EnumeratedTripleRow
open GProgram.G5.EnumeratedPosteriorGerm GProgram.G5.ActualConditionalPartition
open GProgram.G5.ActualActivatedPrefix GProgram.G5.ActivatedPosteriorPlacement
open GProgram.G5.OriginalEpochChart GProgram.G5.PhysicalCutChart GProgram.G5.OlderSideCutChart
open GProgram.G5.TriplePartitionReadout GProgram.G5.ActualFrozenTripleRow
open GProgram.G5.PosteriorJointCell GProgram.G5.SafePrefixRouteBridge
open GProgram.G5.OriginalCoinLaw
attribute [local instance] GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
open scoped Classical NNReal ENNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

noncomputable def cutPast (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (pre : List ℝ) (guard t : ℝ) : List (ProgramStep N) :=
  prefixThrough N C H (originalGamma p) common pre guard ++ [.interval (Real.toNNReal (t-guard))]

noncomputable def cutJoint (N : RootedBinary V E X) (sample : Fin 3 → X)
    (p : HybridProbabilities N) (r : PositivePairRates E) (past : List (ProgramStep N))
    (u : ℝ≥0) : PMF (Fin 5 × Fin 5) :=
  (originalProgramLaw N sample p r past).bind (fun d =>
    (sourceProgram N r [.interval u] d).map (fun e =>
      (indexedPartition N (Equiv.refl _) d,indexedPartition N (Equiv.refl _) e)))

/-- Fixed-chart specialization of the accepted physical two-cut identity.
Both cuts use ordinary timed observations with the register already erased. -/
theorem actual_cut_joint_observed (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Fin 3 → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (pre post : List ℝ) (guard next t : ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (hleft : guard ≤ t) (hright : t < next) (u : ℝ≥0) (hu : (u : ℝ) < next-t) :
    (naturalObservedFullLaw N C sample H p common r).map
      (fun o => let B := observedAgeBins (twoCutBin t (t+u)) o
        (binPartition (Equiv.refl _) 0 B,binPartition (Equiv.refl _) 1 B)) =
      (cutJoint N sample p r (cutPast N C H p common pre guard t) u).toMeasure := by
  have hw := actual_original_epoch_word N C H (originalGamma p) common pre guard next post hsplit
  rw [older_gap_three_parts hleft hright u hu] at hw
  have ho := actual_observed_two_cut_partition_law N C sample H p common r
    (prefixThrough N C H (originalGamma p) common pre guard)
    (boundaryOperations N C H (originalGamma p) common next ++
      calendarTail N C H (originalGamma p) common next post)
    (Real.toNNReal (t-guard)) u (Real.toNNReal (next-t-u)) hw (Equiv.refl _)
  have hage : firstOriginalDate N C +
      (programDuration N (prefixThrough N C H (originalGamma p) common pre guard) : ℝ) +
        (Real.toNNReal (t-guard) : ℝ) = t := by
    rw [prefix_age_is_guard N C H (originalGamma p) common pre guard next post hsplit,
      Real.coe_toNNReal _ (sub_nonneg.mpr hleft)]
    ring
  dsimp only at ho
  rw [hage] at ho
  exact ho

lemma cut_joint_first_marginal (N : RootedBinary V E X) (sample : Fin 3 → X)
    (p : HybridProbabilities N) (r : PositivePairRates E) (past : List (ProgramStep N))
    (u : ℝ≥0) :
    (cutJoint N sample p r past u).map Prod.fst =
      (originalProgramLaw N sample p r past).map (indexedPartition N (Equiv.refl _)) :=
  joint_first_marginal _ _ _ _

/-- The population location identity for this cut is a conclusion of the
actual initialized source, not an assumed posterior admission. -/
lemma actual_cut_posterior_placement (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Fin 3 → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a0 t : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0)
    (pre post : List ℝ) (guard next : ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (hleft : guard ≤ t) (hright : t < next) (hroot : t < C.age N.root)
    (s : ActualSeed N (originalTripleCodePosterior N sample p r (cutPast N C H p common pre guard t)))
    (x : Fin 3) : copyLocation (state s.val) x = originalPlace N (codePopulation N s.val x) := by
  have hdsource := ((PMF.mem_support_filter_iff
    (actual_full_code_event_witness N sample p r Finset.univ (cutPast N C H p common pre guard t))).mp s.property).2
  obtain ⟨reg,_,hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdsource
  obtain ⟨e,he,_⟩ := actual_cut_supported_locations_active N C sample reg H p common r a0 t htips
    pre post guard next hsplit hleft hright hroot s.val hdr x
  simp only [codePopulation,he,originalPlace]

section TwoSources
variable {V₂ E₂ : Type*} [DecidableEq V₂] [DecidableEq E₂] [Fintype V₂] [Fintype E₂]

/-- Ordinary observed-law equality gives equal actual posterior occupancy
support. The two hidden graphs, rates, registers and posteriors may differ.
The denominator equality is recovered from the first marginal of the SAME
observed joint law; it is not supplied as a separate assumption. -/
theorem observed_law_identifies_actual_cut_occupancy
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Fin 3 → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : GProgram.G5.Calendar N₂.graph)
    (sample₂ : Fin 3 → X) (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂)
    (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0)
    (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    (pre post pre₂ post₂ : List ℝ) (guard next guard₂ next₂ : ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (hsplit₂ : sortedOriginalDates N₂ C₂ = pre₂ ++ guard₂ :: next₂ :: post₂)
    (hleft : guard ≤ t) (hright : t < next) (hroot : t < C.age N.root)
    (hleft₂ : guard₂ ≤ t) (hright₂ : t < next₂) (hroot₂ : t < C₂.age N₂.root)
    (heq : naturalObservedFullLaw N C sample H p common r =
      naturalObservedFullLaw N₂ C₂ sample₂ H₂ p₂ common₂ r₂) :
    let past := cutPast N C H p common pre guard t
    let past₂ := cutPast N₂ C₂ H₂ p₂ common₂ pre₂ guard₂ t
    ∀ gene, (∃ s : ActualSeed N (originalTripleCodePosterior N sample p r past),
      ancestorPartition (codePopulation N s.val) = gene) ↔
      ∃ s : ActualSeed N₂ (originalTripleCodePosterior N₂ sample₂ p₂ r₂ past₂),
        ancestorPartition (codePopulation N₂ s.val) = gene := by
  dsimp only
  let past := cutPast N C H p common pre guard t
  let past₂ := cutPast N₂ C₂ H₂ p₂ common₂ pre₂ guard₂ t
  let epsilon := min (next-t) (next₂-t)
  have hepsilon : 0 < epsilon := lt_min (sub_pos.mpr hright) (sub_pos.mpr hright₂)
  have hjoint (u : ℝ≥0) (hu : (u : ℝ) < epsilon) :
      cutJoint N sample p r past u = cutJoint N₂ sample₂ p₂ r₂ past₂ u := by
    apply PMF.toMeasure_injective
    rw [← actual_cut_joint_observed N C sample H p common r pre post guard next t hsplit hleft hright u
      (hu.trans_le (min_le_left _ _)),
      ← actual_cut_joint_observed N₂ C₂ sample₂ H₂ p₂ common₂ r₂ pre₂ post₂ guard₂ next₂ t hsplit₂ hleft₂ hright₂ u
      (hu.trans_le (min_le_right _ _)),heq]
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
    (fun s => codePopulation N s.val) (fun s => codePopulation N₂ s.val)
    (actual_cut_posterior_placement N C sample H p common r a0 t htips
      pre post guard next hsplit hleft hright hroot)
    (actual_cut_posterior_placement N₂ C₂ sample₂ H₂ p₂ common₂ r₂ a0 t htips₂
      pre₂ post₂ guard₂ next₂ hsplit₂ hleft₂ hright₂ hroot₂) hepsilon
  intro gene u hu
  rw [actual_conditional_partition_cell,actual_conditional_partition_cell,hden]
  change (cutJoint N sample p r past u (0,gene) * _).toReal =
    (cutJoint N₂ sample₂ p₂ r₂ past₂ u (0,gene) * _).toReal
  rw [hjoint u hu]
end TwoSources

/-- Exact conversion from the actual stochastic posterior to the structural
binary-choice partition predicate, using the one-register support iff. -/
theorem actual_cut_partition_iff_choices
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (B : Finset X) (tip : Fin 3 ↪ X) (htip : ∀ g, tip g ∈ B)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0)
    (pre post : List ℝ) (guard next : ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (hleft : guard ≤ t) (hright : t < next) (hroot : t < C.age N.root)
    (hsafe : GProgram.G5.SafePast.SafeAt N C B t)
    (D : ∀ g, NativeCurrentDescription N C H (tip g) t) (gene : Fin 5) :
    let past := cutPast N C H p common pre guard t
    (∃ s : ActualSeed N (originalTripleCodePosterior N tip p r past),
      ancestorPartition (codePopulation N s.val) = gene) ↔
      ∃ choice : Fin 3 → Fin 2,
        ancestorPartition (fun g => some (binaryPositions (descriptionPositions N C hcut H (D g)) (choice g))) = gene := by
  dsimp only
  let past := cutPast N C H p common pre guard t
  have hs (place : Fin 3 → Option E) := actual_safe_cut_population_support_iff N C hcut H p common r
    B tip htip a0 t htips pre post guard next hsplit hleft hright hroot hsafe D place
  constructor
  · rintro ⟨s,hgene⟩
    have hm : codePopulation N s.val ∈ ((originalTripleCodePosterior N tip p r past).map
        (codePopulation N)).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨s.val,s.property,rfl⟩
    obtain ⟨choice,hchoice⟩ := (hs _).mp hm
    exact ⟨choice,(congrArg ancestorPartition (funext hchoice)).symm.trans hgene⟩
  · rintro ⟨choice,hgene⟩
    have hm := (hs (fun g => some (binaryPositions (descriptionPositions N C hcut H (D g)) (choice g)))).mpr
      ⟨choice,fun _ => rfl⟩
    obtain ⟨d,hd,hplace⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    exact ⟨⟨d,hd⟩,(congrArg ancestorPartition hplace).trans hgene⟩


section FullConnection
variable {V₂ E₂ : Type*} [DecidableEq V₂] [DecidableEq E₂] [Fintype V₂] [Fintype E₂]

/-- The named observed-to-decoder connection on a genuine selected original
triple. The two actual physical prefixes, positive conditional events and
finite-source mixture supports are all constructed internally. Only equality
of the ordinary hidden-register TIMED GENEALOGY laws is an observed premise. -/
theorem equal_observed_triple_laws_equal_safe_partition_feasibility
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : GProgram.G5.Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂)
    (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (B : Finset X) (tip : Fin 3 ↪ X) (htip : ∀ g, tip g ∈ B)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0)
    (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0) (ht : a0 ≤ t)
    (hroot : t < C.age N.root) (hroot₂ : t < C₂.age N₂.root)
    (hsafe : GProgram.G5.SafePast.SafeAt N C B t)
    (hsafe₂ : GProgram.G5.SafePast.SafeAt N₂ C₂ B t)
    (D : ∀ g, NativeCurrentDescription N C H (tip g) t)
    (D₂ : ∀ g, NativeCurrentDescription N₂ C₂ H₂ (tip g) t)
    (heq : naturalObservedFullLaw N C tip H p common r =
      naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    ∀ gene : Fin 5,
      (∃ choice : Fin 3 → Fin 2,
        ancestorPartition (fun g => some (binaryPositions (descriptionPositions N C hcut H (D g)) (choice g))) = gene) ↔
      (∃ choice : Fin 3 → Fin 2,
        ancestorPartition (fun g => some (binaryPositions (descriptionPositions N₂ C₂ hcut₂ H₂ (D₂ g)) (choice g))) = gene) := by
  obtain ⟨pre,guard,next,post,hsplit,hleft,hright⟩ := original_older_gap_exists N C t
    (by simpa only [first_date_of_contemporaneous_tips N C a0 htips] using ht) hroot
  obtain ⟨pre₂,guard₂,next₂,post₂,hsplit₂,hleft₂,hright₂⟩ := original_older_gap_exists N₂ C₂ t
    (by simpa only [first_date_of_contemporaneous_tips N₂ C₂ a0 htips₂] using ht) hroot₂
  have hobs := observed_law_identifies_actual_cut_occupancy N C tip H p common r
    N₂ C₂ tip H₂ p₂ common₂ r₂ a0 t htips htips₂ pre post pre₂ post₂ guard next guard₂ next₂
    hsplit hsplit₂ hleft hright hroot hleft₂ hright₂ hroot₂ heq
  intro gene
  exact (actual_cut_partition_iff_choices N C hcut H p common r B tip htip a0 t htips
    pre post guard next hsplit hleft hright hroot hsafe D gene).symm.trans
    ((hobs gene).trans
      (actual_cut_partition_iff_choices N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ B tip htip a0 t htips₂
        pre₂ post₂ guard₂ next₂ hsplit₂ hleft₂ hright₂ hroot₂ hsafe₂ D₂ gene))
end FullConnection

#print axioms actual_cut_joint_observed
#print axioms observed_law_identifies_actual_cut_occupancy
#print axioms actual_cut_partition_iff_choices
#print axioms equal_observed_triple_laws_equal_safe_partition_feasibility
end GProgram.G5.ObservedSafeTripleSupport
