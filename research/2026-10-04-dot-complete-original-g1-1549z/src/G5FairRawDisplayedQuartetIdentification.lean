import G5ChronologicalQuartetWitnessTransfer

/-!
# Fresh M2 identifies the full ACTUAL RAW displayed resolved-quartet union
Contributor: dot / OpenAI, 2026-10-03.
This theorem joins actual observed pair clocks, attained chronology/deletion,
ALL-COMMON group paths, fair coupled group counts, and actual switching edge-cut
soundness/completeness. It retains arbitrary finite binary cut-child sources,
original parallel edges, unknown positive edge/ancestral rates and COMMON/I
comparisons. The target is the inherited actual rawDisplayedQuartets definition.
No extra normalized reduction or semidirected convention theorem is claimed.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.SafePast
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.NativePairCalendarObservation UnifiedLean.Source.NativeFairCurrentPosition
open UnifiedLean.Source.NativePairClockLaw
open scoped Classical
variable {V E X V₂ E₂ : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E] [LinearOrder X]
variable [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]

lemma original_quartet_witness_after_sampling (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (q : Fin 4 ↪ X) (a : CommonSeed N) {s t : ℝ}
    (htips : ∀ x : X, C.age (N.leaf x) = s) (hw : OriginalQuartetSideWitness N C H a t q) : s ≤ t := by
  obtain ⟨e,ha,hside⟩ := hw
  rcases hside with h | h
  · have hh := C.age_le_of_directed (((commonRoutes N C H a).valid (q 0)).target_reaches_end_of_mem h.1)
    rw [htips] at hh
    exact hh.trans ha.1
  · have hh := C.age_le_of_directed (((commonRoutes N C H a).valid (q 2)).target_reaches_end_of_mem h.1)
    rw [htips] at hh
    exact hh.trans ha.1

theorem equal_fair_pair_laws_raw_displayed_first_quartet
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    {s : ℝ} (htips : ∀ x : X, C.age (N.leaf x) = s) (htips₂ : ∀ x : X, C₂.age (N₂.leaf x) = s)
    (heq : ∀ x y : X, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) (q : Fin 4 ↪ X) :
    Nanuq.Quartet.Resolution.xy_zw ∈ N.rawDisplayedQuartets q ↔
      Nanuq.Quartet.Resolution.xy_zw ∈ N₂.rawDisplayedQuartets q := by
  have htime := contemporaneous_pair_laws_identify_all_quartet_witness_ages N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂
    Finset.univ q (fun _ => Finset.mem_univ _) (fun x _ => htips x) (fun x _ => htips₂ x)
    (fun x _ y _ hne => heq x y hne)
  rw [raw_displayed_first_quartet_iff_calendar_witness N C H q,
    raw_displayed_first_quartet_iff_calendar_witness N₂ C₂ H₂ q]
  constructor
  · rintro ⟨a,t,hw⟩
    obtain ⟨a₂,hw₂⟩ := (htime t (original_quartet_witness_after_sampling N C H q a htips hw)).mp ⟨a,hw⟩
    exact ⟨a₂,t,hw₂⟩
  · rintro ⟨a₂,t,hw₂⟩
    obtain ⟨a,hw⟩ := (htime t (original_quartet_witness_after_sampling N₂ C₂ H₂ q a₂ htips₂ hw₂)).mpr ⟨a₂,hw₂⟩
    exact ⟨a,t,hw⟩

lemma raw_quartet_mem_iff_selected_resolves (N : RootedBinary V E X) (q : Fin 4 ↪ X)
    (r : Nanuq.Quartet.Resolution) :
    r ∈ N.rawDisplayedQuartets q ↔ ∃ S : N.Switching, S.graph.Resolves (fun i => N.leaf (q i)) r := by
  simp only [RootedBinary.rawDisplayedQuartets,Nanuq.Quartet.displayed,Finset.mem_image,Finset.mem_univ,true_and]
  apply exists_congr
  intro S
  exact eq_comm.trans (S.resolves_iff_eq_resolve q r).symm

/-- All three labeled resolutions are reduced to the first-pair pattern by
an actual permutation of the ORIGINAL quartet embedding. -/
def resolutionPermutation : Nanuq.Quartet.Resolution → (Fin 4 ↪ Fin 4)
  | .xy_zw => Function.Embedding.refl _
  | .xz_yw => ⟨![0,2,1,3],by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
  | .xw_yz => ⟨![0,3,1,2],by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

lemma raw_quartet_mem_iff_permuted_first (N : RootedBinary V E X) (q : Fin 4 ↪ X)
    (r : Nanuq.Quartet.Resolution) :
    r ∈ N.rawDisplayedQuartets q ↔
      Nanuq.Quartet.Resolution.xy_zw ∈ N.rawDisplayedQuartets ((resolutionPermutation r).trans q) := by
  rw [raw_quartet_mem_iff_selected_resolves,raw_quartet_mem_iff_selected_resolves]
  apply exists_congr
  intro S
  cases r <;> simp [EdgeGraph.Resolves,resolutionPermutation,Function.Embedding.trans_apply]

/-- Full original RAW displayed quartet identification from genuinely fresh
DISTINCT ordinary original-tip pair laws. The two sources/modes can differ.
This statement contains no supplied chronology, group paths, moment data,
switching witness relation, output equality, planarity or level bound. -/
theorem equal_fair_pair_calendar_laws_identify_raw_displayed_quartets
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    {s : ℝ} (htips : ∀ x : X, C.age (N.leaf x) = s) (htips₂ : ∀ x : X, C₂.age (N₂.leaf x) = s)
    (heq : ∀ x y : X, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    ∀ q : Fin 4 ↪ X, N.rawDisplayedQuartets q = N₂.rawDisplayedQuartets q := by
  intro q
  ext resolved
  rw [raw_quartet_mem_iff_permuted_first N q resolved,raw_quartet_mem_iff_permuted_first N₂ q resolved]
  exact equal_fair_pair_laws_raw_displayed_first_quartet N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂
    htips htips₂ heq ((resolutionPermutation resolved).trans q)

#print axioms equal_fair_pair_laws_raw_displayed_first_quartet
#print axioms equal_fair_pair_calendar_laws_identify_raw_displayed_quartets
end GProgram.G5.AttainedChronology
