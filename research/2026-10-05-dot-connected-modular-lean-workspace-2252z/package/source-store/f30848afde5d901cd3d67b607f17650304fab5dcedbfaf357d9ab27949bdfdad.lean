import G5SafeCommonGroupQuartetTransfer
import G5SynchronizedObservableChronology

/-!
# All-age safe original quartet transfer, including unequal source root ages
Contributor: dot / OpenAI, 2026-10-03.
If one source is already ancestral, its actual full germ forces all distinct
retained original groups in the other safe source to be surely together. Thus
neither source can have a proper quartet-side edge at that age. Both-below-root
ages use the actual coupled group-selector source/count bridge.
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

lemma original_quartet_witness_below_root (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a : CommonSeed N) (q : Fin 4 ↪ X) {t : ℝ}
    (hw : OriginalQuartetSideWitness N C H a t q) : t < C.age N.root := by
  obtain ⟨e,ha,_⟩ := hw
  exact ha.2.trans_le (C.age_le_of_directed (N.rooted (N.graph.source e)))

lemma original_quartet_witness_cross_separate (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a : CommonSeed N) (q : Fin 4 ↪ X) {t : ℝ}
    (hw : OriginalQuartetSideWitness N C H a t q) :
    ¬SharesPopulation N (commonRoutes N C H a) C t (q 0) (q 2) := by
  obtain ⟨e,ha,hside⟩ := hw
  rintro ⟨p,h0,h2⟩
  rcases hside with h | h
  · have hep := occupies_unique N C (commonRoutes N C H a) (show Occupies N (commonRoutes N C H a) C t (q 0) (some e) from ⟨h.1,ha⟩) h0
    subst p
    exact h.2.2.1 h2.1
  · have hep := occupies_unique N C (commonRoutes N C H a) (show Occupies N (commonRoutes N C H a) C t (q 2) (some e) from ⟨h.1,ha⟩) h2
    subst p
    exact h.2.2.1 h0.1

lemma sharesPopulation_symm (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) {x y : X} {t : ℝ} (h : SharesPopulation N R C t x y) :
    SharesPopulation N R C t y x := by
  obtain ⟨p,hx,hy⟩ := h
  exact ⟨p,hy,hx⟩

/-- Actual ancestry in the comparison source forces no proper original
quartet witness in the other safe source. No root-clock oracle is observed. -/
theorem no_safe_quartet_witness_against_ancestral_source
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    (B : Finset X) {t : ℝ} (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ t)
    (hsafe : SafeAt N C B t) (ht₂ : C₂.age N₂.root ≤ t)
    (q : Fin 4 ↪ X) (rep : Fin 4 → X) (hrep : ∀ i, rep i ∈ B)
    (hpaths : ∀ a : CommonSeed N, ∀ i : Fin 4,
      SharesPopulation N (commonRoutes N C H a) C t (q i) (rep i))
    (heq : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    ¬∃ a : CommonSeed N, OriginalQuartetSideWitness N C H a t q := by
  rintro ⟨a,hw⟩
  have hmeet : SharesPopulation N (commonRoutes N C H a) C t (q 0) (q 2) := by
    by_cases hsame : rep 0 = rep 2
    · have hp2 := hpaths a 2
      rw [←hsame] at hp2
      exact sharesPopulation_trans N C _ (hpaths a 0) (sharesPopulation_symm N C _ hp2)
    · have hc := congrArg (fun f : ℝ →₀ ℝ => f 0) (equal_pair_calendar_laws_identify_full_coefficients
        N C H (fairParameters N) r common N₂ C₂ H₂ (fairParameters N₂) r₂ common₂
        (rep 0) (rep 2) hsame t (heq _ (hrep 0) _ (hrep 2) hsame))
      rw [full_pair_ancestral_zero_coefficient N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ (rep 0) (rep 2) ht₂] at hc
      have hgroups := (observed_full_safe_pair_support N C hcut H r common B (hrep 0) (hrep 2) hsame
        (hl _ (hrep 0)) (hl _ (hrep 2)) hsafe).1.mp hc (commonRoutes N C H a)
      exact sharesPopulation_trans N C _ (sharesPopulation_trans N C _ (hpaths a 0) hgroups)
        (sharesPopulation_symm N C _ (hpaths a 2))
  exact original_quartet_witness_cross_separate N C H a q hw hmeet

/-- Exact stage witness equivalence at ALL ages; unequal roots/rates and
COMMON/I observations are retained. Original groups use one shared map. -/
theorem equal_fair_pair_laws_all_age_safe_original_quartet_witness
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    (B : Finset X) {t : ℝ}
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ t) (hl₂ : ∀ x ∈ B, C₂.age (N₂.leaf x) ≤ t)
    (hsafe : SafeAt N C B t) (hsafe₂ : SafeAt N₂ C₂ B t)
    (q : Fin 4 ↪ X) (rep : Fin 4 → X) (hrep : ∀ i, rep i ∈ B)
    (hpaths : ∀ a : CommonSeed N, ∀ i : Fin 4,
      SharesPopulation N (commonRoutes N C H a) C t (q i) (rep i))
    (hpaths₂ : ∀ a : CommonSeed N₂, ∀ i : Fin 4,
      SharesPopulation N₂ (commonRoutes N₂ C₂ H₂ a) C₂ t (q i) (rep i))
    (heq : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    (∃ a : CommonSeed N, OriginalQuartetSideWitness N C H a t q) ↔
      (∃ a : CommonSeed N₂, OriginalQuartetSideWitness N₂ C₂ H₂ a t q) := by
  by_cases ht : t < C.age N.root
  · by_cases ht₂ : t < C₂.age N₂.root
    · let tip : {x : X // x ∈ B} ↪ X := ⟨Subtype.val,Subtype.val_injective⟩
      let owner : Fin 4 → {x : X // x ∈ B} := fun i => ⟨rep i,hrep i⟩
      exact equal_fair_pair_laws_safe_original_quartet_witness N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂
        B tip (fun g => g.property) hl hl₂ ht ht₂ hsafe hsafe₂ q owner hpaths hpaths₂ heq
    · apply iff_of_false
      · exact no_safe_quartet_witness_against_ancestral_source N C hcut H r common N₂ C₂ H₂ r₂ common₂
          B hl hsafe (le_of_not_gt ht₂) q rep hrep hpaths heq
      · rintro ⟨a,hw⟩; exact ht₂ (original_quartet_witness_below_root N₂ C₂ H₂ a q hw)
  · apply iff_of_false
    · rintro ⟨a,hw⟩; exact ht (original_quartet_witness_below_root N C H a q hw)
    · exact no_safe_quartet_witness_against_ancestral_source N₂ C₂ hcut₂ H₂ r₂ common₂ N C H r common
        B hl₂ hsafe₂ (le_of_not_gt ht) q rep hrep hpaths₂ (fun x hx y hy hne => (heq x hx y hy hne).symm)

#print axioms no_safe_quartet_witness_against_ancestral_source
#print axioms equal_fair_pair_laws_all_age_safe_original_quartet_witness
end GProgram.G5.AttainedChronology
