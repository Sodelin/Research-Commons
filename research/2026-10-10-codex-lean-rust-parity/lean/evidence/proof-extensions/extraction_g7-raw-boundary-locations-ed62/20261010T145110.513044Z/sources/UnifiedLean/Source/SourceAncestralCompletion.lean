import UnifiedLean.Source.SourceEmbeddedJumpLaw
import UnifiedLean.Source.SourceNaturalInitialization

/-!
# Finite actual ORIGINAL ancestral merger completion

Contributor: dot, 2026-10-02. Reuses the accepted G2 generator/jump → calendar
→ ancestral-completion route at its UNRANKED endpoint scope. After the actual
calendar's proved root arrival, the actual exponential-winner jump PMF performs
source mergers until at most one live root remains. This is a genuine finite
PMF, with completion support DERIVED from original rates/root locations and
strict live-card descent. Eventual continuous-time limit and canonical
smaller-copy unranked transport remain separate connected obligations.
-/
namespace UnifiedLean.Source.SourceAncestralCompletion
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceFirstMarkDistribution
open UnifiedLean.Source.SourceEmbeddedJumpLaw
open UnifiedLean.Source.SourceNaturalInitialization
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def AncestralRoot (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) : Prop :=
  ∀ x : Copy, copyLocation (state s) x = .rootPopulation N.root

lemma ancestral_live_location (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) {a : Copy} (ha : a ∈ (state s).live) :
    (state s).location a = .rootPopulation N.root := by
  have hrep : (state s).ancestor a = a := s.property.forest.representative a ha
  have hh := hs a
  change (state s).location ((state s).ancestor a) = .rootPopulation N.root at hh
  rw [hrep] at hh
  exact hh

lemma choice_empty_of_terminal_card (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hc : liveCard s ≤ 1) : IsEmpty (Choice N s) := by
  refine ⟨fun p => ?_⟩
  have hp := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  exact hp.different ((Finset.card_le_one.mp hc) _ hp.first_live _ hp.second_live)

lemma ancestral_choice_exists (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) (hc : 1 < liveCard s) : Nonempty (Choice N s) := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hc
  refine ⟨⟨none,⟨(a,b),Finset.mem_offDiag.mpr ⟨?_,?_,hab⟩⟩⟩⟩
  · exact Finset.mem_filter.mpr ⟨ha,ancestral_live_location N s hs ha⟩
  · exact Finset.mem_filter.mpr ⟨hb,ancestral_live_location N s hs hb⟩

lemma ancestral_merger_preserved (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) (p : Choice N s) :
    AncestralRoot N (stepDestination N s (some p)) := by
  intro x
  let hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  unfold state stepDestination admittedCode
  rw [decode_encode_copyLocation,merge_population_preserved _ hm x]
  exact hs x

lemma source_jump_absorbs_terminal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hc : liveCard s ≤ 1) :
    sourceJumpStep N r s = PMF.pure s := by
  letI := choice_empty_of_terminal_card N s hc
  have hz : totalRate N r s = 0 := by simp [totalRate]
  have hp : sourceJumpChoice N r s = PMF.pure none := by
    apply PMF.ext
    intro q
    cases q with
    | none => simp [sourceJumpChoice_apply,jumpMass,hz]
    | some p => exact isEmptyElim p
  rw [sourceJumpStep,hp,PMF.pure_map]
  rfl

lemma source_jump_support_cases (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceJumpStep N r s).support) :
    (d = s ∧ totalRate N r s = 0) ∨ ∃ p : Choice N s, d = stepDestination N s (some p) := by
  obtain ⟨q,hq,heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  cases q with
  | none =>
      left
      refine ⟨heq.symm,?_⟩
      by_contra hz
      have hn := (PMF.mem_support_iff _ _).mp hq
      rw [sourceJumpChoice_apply] at hn
      simp only [jumpMass,if_neg hz,ENNReal.ofReal_zero,ne_eq,not_true_eq_false] at hn
  | some p => exact Or.inr ⟨p,heq.symm⟩

noncomputable def ancestralCompletion (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : Nat → Code N sample → PMF (Code N sample)
  | 0,s => PMF.pure s
  | n+1,s => (sourceJumpStep N r s).bind (ancestralCompletion N r n)

lemma ancestral_completion_fixed_terminal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (hc : liveCard s ≤ 1) :
    ancestralCompletion N r n s = PMF.pure s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ancestralCompletion,source_jump_absorbs_terminal N r s hc,PMF.pure_bind,ih]

/-- The original positive ancestral population completes after finitely many
actual merger jumps. No completion probability/support field is assumed. -/
theorem ancestral_completion_terminal_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (hs : AncestralRoot N s)
    (hn : liveCard s ≤ n) {d : Code N sample}
    (hd : d ∈ (ancestralCompletion N r n s).support) : AncestralRoot N d ∧ liveCard d ≤ 1 := by
  induction n generalizing s with
  | zero =>
      have heq : d = s := by simpa only [ancestralCompletion,PMF.mem_support_pure_iff] using hd
      subst d
      exact ⟨hs,by omega⟩
  | succ n ih =>
      by_cases hc : liveCard s ≤ 1
      · rw [ancestral_completion_fixed_terminal N r (n+1) s hc] at hd
        have heq : d = s := by simpa only [PMF.mem_support_pure_iff] using hd
        subst d
        exact ⟨hs,hc⟩
      · obtain ⟨p0⟩ := ancestral_choice_exists N s hs (lt_of_not_ge hc)
        have hpos := current_pair_total_positive N r s p0
        obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
        rcases source_jump_support_cases N r s hm with ⟨_,hz⟩ | ⟨p,hp⟩
        · exact False.elim (hpos.ne' hz)
        · subst m
          exact ih _ (ancestral_merger_preserved N s hs p)
            (by have hcard := merger_destination_card N s p; omega) hdm

/-- A nonempty ORIGINAL copy carrier cannot end in an empty genealogy. -/
lemma admitted_live_card_positive [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) : 0 < liveCard s := by
  obtain ⟨x⟩ := ‹Nonempty Copy›
  exact Finset.card_pos.mpr ⟨(state s).ancestor x,s.property.forest.ancestor_live x⟩

/-- Same original graph/parameters/register prior, now followed by genuine
ancestral merger completion. The finite PMF carries the complete old forests. -/
noncomputable def naturalCompletedLaw (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) : PMF (Code N sample) :=
  (naturalCalendarLaw N C sample H p common r).bind (ancestralCompletion N r (Fintype.card Copy))

/-- Actual graph-generated initialization and calendar, not an externally
supplied ancestral entry condition, yield exactly ONE final ancestral tree. -/
theorem natural_completed_one_tree_support [Nonempty Copy] (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) {d : Code N sample}
    (hd : d ∈ (naturalCompletedLaw N C sample H p common r).support) :
    AncestralRoot N d ∧ liveCard d = 1 := by
  obtain ⟨s,hs,hdc⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hroot := natural_calendar_ancestral_support N C sample H p common r hs
  obtain ⟨hr,hc⟩ := ancestral_completion_terminal_support N r (Fintype.card Copy) s hroot
    (Finset.card_le_univ s.val.live) hdc
  exact ⟨hr,by have hp := admitted_live_card_positive N d; omega⟩

#print axioms ancestral_completion_terminal_support
#print axioms natural_completed_one_tree_support
end UnifiedLean.Source.SourceAncestralCompletion
