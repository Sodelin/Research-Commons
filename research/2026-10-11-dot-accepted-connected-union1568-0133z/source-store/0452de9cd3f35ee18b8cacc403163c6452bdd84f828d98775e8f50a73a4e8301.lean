import G5SafeCommonGroupSelector
import UnifiedLean.Source.NativePairCalendarObservation

/-!
# Actual original quartet witnesses transfer on synchronized safe stages
Contributor: dot / OpenAI, 2026-10-03.
All distinct original group-pair laws yield counts for the actual current source
selectors. Coupled group choices are realized by one original common register.
The prior derived original group path invariant supplies exact original-label
population witnesses. The below-root stage interface is explicit.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.SafePast GProgram.G5.QuartetKernel GProgram.G5.OriginalCoinLaw
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.NativeCurrentPortCompiler UnifiedLean.Source.NativeFairCurrentPosition
open UnifiedLean.Source.NativePairCalendarObservation UnifiedLean.Source.NativePairClockLaw
open scoped Classical
variable {V E X G : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E] [DecidableEq G] [LinearOrder X]

/-- The ORIGINAL quartet witness is exactly the current coupled original-group
readout. The premise is the previously proved chronological path invariant. -/
theorem original_quartet_witness_iff_group_read
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (tip : G ↪ X) {t : ℝ}
    (D : ∀ g : G, NativeCurrentDescription N C H (tip g) t)
    (q : Fin 4 ↪ X) (owner : Fin 4 → G)
    (hpaths : ∀ a : CommonSeed N, ∀ i : Fin 4,
      SharesPopulation N (commonRoutes N C H a) C t (q i) (tip (owner i))) :
    (∃ a : CommonSeed N, OriginalQuartetSideWitness N C H a t q) ↔
    (∃ a : CommonSeed N, quartetAt (fun i => descriptionRead N C hcut H (D (owner i)) a)) := by
  apply exists_congr
  intro a
  let read : Fin 4 → E := fun i => descriptionRead N C hcut H (D (owner i)) a
  have hocc (i : Fin 4) : Occupies N (commonRoutes N C H a) C t (q i) (some (read i)) := by
    have hp := description_read_native_source_spec N C hcut H (D (owner i)) (fun _ h => a h)
    exact (shared_population_membership_iff N C (commonRoutes N C H a) (hpaths a i) (some (read i))).mpr hp
  have hmem (i : Fin 4) (e : E) (ha : C.Active t e) :
      e ∈ (commonRoutes N C H a).edges (q i) ↔ e = read i := by
    constructor
    · intro he
      exact ((commonRoutes N C H a).valid (q i)).active_unique C he (hocc i).1 ha (hocc i).2
    · intro he
      exact he.symm ▸ (hocc i).1
  constructor
  · rintro ⟨e,ha,hside⟩
    simp only [hmem 0 e ha,hmem 1 e ha,hmem 2 e ha,hmem 3 e ha] at hside
    change quartetAt read
    unfold quartetAt
    rcases hside with h | h <;> grind
  · intro hw
    change quartetAt read at hw
    rcases hw with h | h
    · refine ⟨read 0,(hocc 0).2,?_⟩
      simp only [hmem 0 _ (hocc 0).2,hmem 1 _ (hocc 0).2,hmem 2 _ (hocc 0).2,hmem 3 _ (hocc 0).2]
      exact Or.inl ⟨True.intro,h.1,h.2.1,h.2.2⟩
    · refine ⟨read 2,(hocc 2).2,?_⟩
      simp only [hmem 0 _ (hocc 2).2,hmem 1 _ (hocc 2).2,hmem 2 _ (hocc 2).2,hmem 3 _ (hocc 2).2]
      exact Or.inr ⟨True.intro,h.1,h.2.1,h.2.2⟩

section DifferentSources
variable {V₂ E₂ : Type*} [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]

/-- Actual source coupled-group quartet readouts, for arbitrary repeated
original groups, are identified using only DISTINCT original group-pair laws. -/
theorem equal_fair_pair_laws_safe_group_quartet_read
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    (B : Finset X) (tip : G ↪ X) (htip : ∀ g, tip g ∈ B) {t : ℝ}
    (ht : t < C.age N.root) (ht₂ : t < C₂.age N₂.root)
    (hsafe : SafeAt N C B t) (hsafe₂ : SafeAt N₂ C₂ B t)
    (D : ∀ g : G, NativeCurrentDescription N C H (tip g) t)
    (D₂ : ∀ g : G, NativeCurrentDescription N₂ C₂ H₂ (tip g) t) (owner : Fin 4 → G)
    (heq : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    (∃ a : CommonSeed N, quartetAt (fun i => descriptionRead N C hcut H (D (owner i)) a)) ↔
      (∃ a : CommonSeed N₂, quartetAt (fun i => descriptionRead N₂ C₂ hcut₂ H₂ (D₂ (owner i)) a)) := by
  rw [safe_common_group_quartet_read_iff_coupled N C hcut H B tip htip hsafe D owner,
    safe_common_group_quartet_read_iff_coupled N₂ C₂ hcut₂ H₂ B tip htip hsafe₂ D₂ owner]
  apply arbitrary_coupled_witness_iff_of_distinct_group_counts
  intro g h hne
  have htipne : tip g ≠ tip h := fun he => hne (tip.injective he)
  have hc := congrArg (fun f : ℝ →₀ ℝ => f 0) (equal_pair_calendar_laws_identify_coefficients
    N C H (fairParameters N) r common N₂ C₂ H₂ (fairParameters N₂) r₂ common₂
    (tip g) (tip h) htipne ht ht₂ (heq _ (htip g) _ (htip h) htipne))
  rw [safe_calendar_constant_count N C hcut H r common B (htip g) (htip h) htipne ht hsafe (D g) (D h),
    safe_calendar_constant_count N₂ C₂ hcut₂ H₂ r₂ common₂ B (htip g) (htip h) htipne ht₂ hsafe₂ (D₂ g) (D₂ h)] at hc
  exact_mod_cast (show (pairCount (binaryPositions (descriptionPositions N C hcut H (D g)))
      (binaryPositions (descriptionPositions N C hcut H (D h))) : ℝ) =
      (pairCount (binaryPositions (descriptionPositions N₂ C₂ hcut₂ H₂ (D₂ g)))
      (binaryPositions (descriptionPositions N₂ C₂ hcut₂ H₂ (D₂ h))) : ℝ) by linarith)

/-- Connected ORIGINAL quartet-side witness equivalence on a common safe
stage. Current descriptions are derived from original sampling/calendar ages. -/
theorem equal_fair_pair_laws_safe_original_quartet_witness
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    (B : Finset X) (tip : G ↪ X) (htip : ∀ g, tip g ∈ B) {t : ℝ}
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ t) (hl₂ : ∀ x ∈ B, C₂.age (N₂.leaf x) ≤ t)
    (ht : t < C.age N.root) (ht₂ : t < C₂.age N₂.root)
    (hsafe : SafeAt N C B t) (hsafe₂ : SafeAt N₂ C₂ B t)
    (q : Fin 4 ↪ X) (owner : Fin 4 → G)
    (hpaths : ∀ a : CommonSeed N, ∀ i : Fin 4,
      SharesPopulation N (commonRoutes N C H a) C t (q i) (tip (owner i)))
    (hpaths₂ : ∀ a : CommonSeed N₂, ∀ i : Fin 4,
      SharesPopulation N₂ (commonRoutes N₂ C₂ H₂ a) C₂ t (q i) (tip (owner i)))
    (heq : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    (∃ a : CommonSeed N, OriginalQuartetSideWitness N C H a t q) ↔
      (∃ a : CommonSeed N₂, OriginalQuartetSideWitness N₂ C₂ H₂ a t q) := by
  let D : ∀ g : G, NativeCurrentDescription N C H (tip g) t :=
    fun g => Classical.choice (original_current_description_exists N C H (tip g) (hl _ (htip g)) ht)
  let D₂ : ∀ g : G, NativeCurrentDescription N₂ C₂ H₂ (tip g) t :=
    fun g => Classical.choice (original_current_description_exists N₂ C₂ H₂ (tip g) (hl₂ _ (htip g)) ht₂)
  rw [original_quartet_witness_iff_group_read N C hcut H tip D q owner hpaths,
    original_quartet_witness_iff_group_read N₂ C₂ hcut₂ H₂ tip D₂ q owner hpaths₂]
  exact equal_fair_pair_laws_safe_group_quartet_read N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂
    B tip htip ht ht₂ hsafe hsafe₂ D D₂ owner heq
end DifferentSources

#print axioms original_quartet_witness_iff_group_read
#print axioms equal_fair_pair_laws_safe_group_quartet_read
#print axioms equal_fair_pair_laws_safe_original_quartet_witness
end GProgram.G5.AttainedChronology
