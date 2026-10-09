import G5OriginalProgramSurvival
import UnifiedLean.Source.SourceCrossCarrierNatural

/-!
# Exact selected-singleton conditioning of the ORIGINAL finite source program

Contributor: Codex integration G5 lane, 2026-10-08.
STATUS: SOURCE DRAFT / COMPILER UNCHECKED. No compiler was run by this lane.

G5-B bounded consumer of the independently accepted original-view posterior
hand bridge. Source projectivity is reused, then the ACTUAL full code law is
restricted to the selected genealogy event before projection. Its measured
denominator is proved positive. Normalization transports the complete finite
latent view, including original populations, register and pruned old trees.
Full-copy and selected-copy no-ANY-merger events are not equated.

This is finite-program source conditioning. Original physical time-at-t cut
binding, every structurally feasible route seed's positive mass, the actual
five-partition future row and observed right-germ assembly remain G5-B/C1
debts. No declaration concludes the full M3/HG decoder or genealogy-to-germ
theorem. Population/register coordinates remain hidden.
-/
namespace GProgram.G5.OriginalSelectedPosterior
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCrossCarrierNatural
open GProgram.G5.OriginalProgramSurvival
open scoped Classical NNReal ENNReal

section Restriction
variable {A O : Type*}

/-- Finite/countable PMF Bayes numerator, expressed as restriction of the
unconditioned source rather than a desired posterior-law premise. -/
lemma filter_outer_mass (p : PMF A) (D B : Set A)
    (h : ∃ a ∈ D, a ∈ p.support) :
    (p.filter D h).toOuterMeasure B =
      p.toOuterMeasure (D ∩ B) * (p.toOuterMeasure D)⁻¹ := by
  calc
    (p.filter D h).toOuterMeasure B = ∑' a, B.indicator (p.filter D h) a :=
      PMF.toOuterMeasure_apply _ _
    _ =
        ∑' a, (D ∩ B).indicator p a * (p.toOuterMeasure D)⁻¹ := by
      apply tsum_congr
      intro a
      by_cases haD : a ∈ D <;> by_cases haB : a ∈ B <;>
        simp [haD, haB, PMF.filter_apply, PMF.toOuterMeasure_apply]
    _ = p.toOuterMeasure (D ∩ B) * (p.toOuterMeasure D)⁻¹ := by
      rw [PMF.toOuterMeasure_apply, ENNReal.tsum_mul_right]

/-- Restricting the original code event before projection is exactly
conditioning its pushforward on the SAME event in the projected view. -/
theorem filter_map_pullback (p : PMF A) (f : A → O) (D : Set O)
    (hA : ∃ a ∈ f ⁻¹' D, a ∈ p.support)
    (hO : ∃ o ∈ D, o ∈ (p.map f).support) :
    (p.filter (f ⁻¹' D) hA).map f = (p.map f).filter D hO := by
  apply PMF.ext
  intro o
  calc
    ((p.filter (f ⁻¹' D) hA).map f) o =
        ((p.filter (f ⁻¹' D) hA).map f).toOuterMeasure {o} :=
      (PMF.toOuterMeasure_apply_singleton _ _).symm
    _ = (p.filter (f ⁻¹' D) hA).toOuterMeasure (f ⁻¹' {o}) :=
      PMF.toOuterMeasure_map_apply _ _ _
    _ = p.toOuterMeasure ((f ⁻¹' D) ∩ (f ⁻¹' {o})) *
        (p.toOuterMeasure (f ⁻¹' D))⁻¹ := filter_outer_mass _ _ _ _
    _ = (p.map f).toOuterMeasure (D ∩ {o}) *
        ((p.map f).toOuterMeasure D)⁻¹ := by
      rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
      rfl
    _ = ((p.map f).filter D hO).toOuterMeasure {o} :=
      (filter_outer_mass _ _ _ _).symm
    _ = ((p.map f).filter D hO) o := PMF.toOuterMeasure_apply_singleton _ _

lemma event_mass_real_positive (p : PMF A) (D : Set A)
    (h : ∃ a ∈ D, a ∈ p.support) : 0 < (p.toOuterMeasure D).toReal := by
  have hz : p.toOuterMeasure D ≠ 0 := by
    intro hz
    have hd := (p.toOuterMeasure_apply_eq_zero_iff D).mp hz
    obtain ⟨a, ha, hs⟩ := h
    exact Set.disjoint_left.mp hd hs ha
  have ht : p.toOuterMeasure D ≠ ⊤ := by
    rw [PMF.toOuterMeasure_apply]
    exact p.tsum_coe_indicator_ne_top D
  exact ENNReal.toReal_pos hz ht

end Restriction

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- This is an event in the finite ORIGINAL selected internal view, including
its original labels. It reads no new population/register observation. -/
def selectedSingletonEvent (N : RootedBinary V E X) (sample : Copy → X)
    (keep : Finset Copy) : Set (JoinedIndex N sample keep) :=
  {v | SingletonSelected keep v.val}

theorem actual_full_code_event_witness (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (ops : List (ProgramStep N)) :
    ∃ d ∈ (fun d => joinedProjection N keep (.inl d)) ⁻¹'
      selectedSingletonEvent N sample keep,
      d ∈ (originalProgramLaw N sample p r ops).support := by
  obtain ⟨d, hd, hds⟩ := actual_initialized_program_singleton_witness N sample p r keep ops
  exact ⟨d, hds, hd⟩

theorem actual_full_view_event_witness (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (ops : List (ProgramStep N)) :
    ∃ v ∈ selectedSingletonEvent N sample keep,
      v ∈ ((originalProgramLaw N sample p r ops).map
        (fun d => joinedProjection N keep (.inl d))).support := by
  obtain ⟨d, hd, hds⟩ := actual_initialized_program_singleton_witness N sample p r keep ops
  exact ⟨joinedProjection N keep (.inl d), hds,
    (PMF.mem_support_map_iff _ _ _).mpr ⟨d, hd, rfl⟩⟩

/-- The independently initialized smaller source's event has positive mass
by actual original-program transport, not a fresh conditional-source premise. -/
theorem actual_small_code_event_witness (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (ops : List (ProgramStep N)) :
    ∃ d ∈ (fun d => joinedProjection N keep (.inr d)) ⁻¹'
      selectedSingletonEvent N sample keep,
      d ∈ (originalProgramLaw N (selectedSample sample keep) p r ops).support := by
  have he := original_initialized_register_program_law N sample keep p r ops
  have hw := actual_full_view_event_witness N sample p r keep ops
  change ∃ v ∈ selectedSingletonEvent N sample keep,
    v ∈ (((originalRegisterPMF N p).bind (fun register => sourceProgram N r ops
      (UnifiedLean.Source.SourceInitializedCalendar.initialCode N sample register))).map
      (fun d => joinedProjection N keep (.inl d))).support at hw
  rw [he] at hw
  obtain ⟨v, hv, hvs⟩ := hw
  obtain ⟨d, hd, hdv⟩ := (PMF.mem_support_map_iff _ _ _).mp hvs
  refine ⟨d, ?_, hd⟩
  change joinedProjection N keep (.inr d) ∈ selectedSingletonEvent N sample keep
  rwa [hdv]

noncomputable def originalFullPosterior (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (ops : List (ProgramStep N)) : PMF (JoinedIndex N sample keep) :=
  ((originalProgramLaw N sample p r ops).filter
    ((fun d => joinedProjection N keep (.inl d)) ⁻¹' selectedSingletonEvent N sample keep)
    (actual_full_code_event_witness N sample p r keep ops)).map
      (fun d => joinedProjection N keep (.inl d))

noncomputable def originalSmallPosterior (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (ops : List (ProgramStep N)) : PMF (JoinedIndex N sample keep) :=
  ((originalProgramLaw N (selectedSample sample keep) p r ops).filter
    ((fun d => joinedProjection N keep (.inr d)) ⁻¹' selectedSingletonEvent N sample keep)
    (actual_small_code_event_witness N sample p r keep ops)).map
      (fun d => joinedProjection N keep (.inr d))

/-- Both ACTUAL measured denominators agree before normalization. -/
theorem actual_conditioning_denominator_eq (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (ops : List (ProgramStep N)) :
    (originalProgramLaw N sample p r ops).toOuterMeasure
        ((fun d => joinedProjection N keep (.inl d)) ⁻¹' selectedSingletonEvent N sample keep) =
      (originalProgramLaw N (selectedSample sample keep) p r ops).toOuterMeasure
        ((fun d => joinedProjection N keep (.inr d)) ⁻¹' selectedSingletonEvent N sample keep) := by
  have he := original_initialized_register_program_law N sample keep p r ops
  exact (PMF.toOuterMeasure_map_apply _ _ _).symm.trans
    ((congrArg (fun q : PMF (JoinedIndex N sample keep) =>
      q.toOuterMeasure (selectedSingletonEvent N sample keep)) he).trans
        (PMF.toOuterMeasure_map_apply _ _ _))

theorem actual_conditioning_denominator_positive (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (ops : List (ProgramStep N)) :
    0 < ((originalProgramLaw N sample p r ops).toOuterMeasure
      ((fun d => joinedProjection N keep (.inl d)) ⁻¹' selectedSingletonEvent N sample keep)).toReal :=
  event_mass_real_positive _ _ (actual_full_code_event_witness N sample p r keep ops)

/-- Every restricted latent-view numerator agrees as well. Ordinary marginal
projectivity alone is not asserted to be a conditioning theorem. -/
theorem actual_conditioning_numerator_eq (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (ops : List (ProgramStep N)) (B : Set (JoinedIndex N sample keep)) :
    (originalProgramLaw N sample p r ops).toOuterMeasure
        ((fun d => joinedProjection N keep (.inl d)) ⁻¹'
          (selectedSingletonEvent N sample keep ∩ B)) =
      (originalProgramLaw N (selectedSample sample keep) p r ops).toOuterMeasure
        ((fun d => joinedProjection N keep (.inr d)) ⁻¹'
          (selectedSingletonEvent N sample keep ∩ B)) := by
  have he := original_initialized_register_program_law N sample keep p r ops
  exact (PMF.toOuterMeasure_map_apply _ _ _).symm.trans
    ((congrArg (fun q : PMF (JoinedIndex N sample keep) =>
      q.toOuterMeasure (selectedSingletonEvent N sample keep ∩ B)) he).trans
        (PMF.toOuterMeasure_map_apply _ _ _))

/-- The exact ORIGINAL code restriction and its measured positive denominator
give the Bayes mass, before invoking any source-to-germ interpretation. -/
theorem actual_original_posterior_mass (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (ops : List (ProgramStep N)) (v : JoinedIndex N sample keep) :
    originalFullPosterior N sample p r keep ops v =
      (originalProgramLaw N sample p r ops).toOuterMeasure
          ((fun d => joinedProjection N keep (.inl d)) ⁻¹'
            (selectedSingletonEvent N sample keep ∩ {v})) *
        ((originalProgramLaw N sample p r ops).toOuterMeasure
          ((fun d => joinedProjection N keep (.inl d)) ⁻¹'
            selectedSingletonEvent N sample keep))⁻¹ := by
  unfold originalFullPosterior
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    filter_outer_mass]
  rfl

/-- The COMPLETE finite latent selected-view posterior is transported.
Extra full-source roots and their old trees are integrated, not excluded. -/
theorem actual_original_program_selected_posterior (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (ops : List (ProgramStep N)) :
    originalFullPosterior N sample p r keep ops = originalSmallPosterior N sample p r keep ops := by
  have he : (originalProgramLaw N sample p r ops).map
        (fun d => joinedProjection N keep (.inl d)) =
      (originalProgramLaw N (selectedSample sample keep) p r ops).map
        (fun d => joinedProjection N keep (.inr d)) :=
    original_initialized_register_program_law N sample keep p r ops
  have hf := actual_full_view_event_witness N sample p r keep ops
  have hs : ∃ v ∈ selectedSingletonEvent N sample keep,
      v ∈ ((originalProgramLaw N (selectedSample sample keep) p r ops).map
        (fun d => joinedProjection N keep (.inr d))).support := by
    rw [← he]
    exact hf
  unfold originalFullPosterior originalSmallPosterior
  rw [filter_map_pullback _ _ _ _ hf, filter_map_pullback _ _ _ _ hs]
  apply PMF.ext
  intro v
  simp only [PMF.filter_apply, he]

/-- Support is characterized by actually supported ORIGINAL endpoints.
This is not a definition of all structurally feasible original route seeds. -/
theorem actual_original_posterior_support_iff (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (ops : List (ProgramStep N)) (v : JoinedIndex N sample keep) :
    v ∈ (originalFullPosterior N sample p r keep ops).support ↔
      ∃ d, d ∈ (originalProgramLaw N sample p r ops).support ∧
        SingletonSelected keep (selectedView (state d) keep) ∧
        joinedProjection N keep (.inl d) = v := by
  unfold originalFullPosterior
  rw [PMF.mem_support_map_iff]
  constructor
  · rintro ⟨d, hd, hdv⟩
    have hi := (PMF.mem_support_filter_iff
      (actual_full_code_event_witness N sample p r keep ops)).mp hd
    exact ⟨d, hi.2, hi.1, hdv⟩
  · rintro ⟨d, hd, hds, hdv⟩
    exact ⟨d, (PMF.mem_support_filter_iff
      (actual_full_code_event_witness N sample p r keep ops)).mpr ⟨hds, hd⟩, hdv⟩

#print axioms filter_outer_mass
#print axioms filter_map_pullback
#print axioms event_mass_real_positive
#print axioms actual_full_code_event_witness
#print axioms actual_full_view_event_witness
#print axioms actual_small_code_event_witness
#print axioms actual_conditioning_denominator_eq
#print axioms actual_conditioning_denominator_positive
#print axioms actual_conditioning_numerator_eq
#print axioms actual_original_posterior_mass
#print axioms actual_original_program_selected_posterior
#print axioms actual_original_posterior_support_iff
end GProgram.G5.OriginalSelectedPosterior
