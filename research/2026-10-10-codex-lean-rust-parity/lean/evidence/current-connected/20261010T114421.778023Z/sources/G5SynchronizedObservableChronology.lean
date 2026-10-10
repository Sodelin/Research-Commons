import G5AncestralObservedPairGerm

/-!
# Observable chronology synchronizes across actual sources, including ancestry
Contributor: dot / OpenAI, 2026-10-03.
Positive ancestral rates close the root-terminal coefficient case. Equality of
fresh distinct-tip ordinary pair laws forces equality of first attained grouping
ages and simultaneous blocks on the full original source class. No hidden
vertex grid, desired source support or chronology is an observed input field.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.SafePast
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativePairCalendarObservation UnifiedLean.Source.NativeFairCurrentPosition
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma sharesPopulation_iff_coOccupy_below_root (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) {t : ℝ} (ht : t < C.age N.root) (x y : X) :
    SharesPopulation N R C t x y ↔ CoOccupy N R C t x y := by
  constructor
  · rintro ⟨p,hx,hy⟩
    cases p with
    | none => exact False.elim (not_le_of_gt ht hx)
    | some e => exact ⟨e,hx.1,hy.1,hx.2⟩
  · rintro ⟨e,hx,hy,ha⟩
    exact ⟨some e,⟨hx,ha⟩,⟨hy,ha⟩⟩

/-- Both extremes of the FULL intrinsic observed germ recover actual support,
including the ancestral population, without an original-root cutoff. -/
theorem observed_full_safe_pair_support (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (B : Finset X) {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ}
    (hlx : C.age (N.leaf x) ≤ t) (hly : C.age (N.leaf y) ≤ t) (hsafe : SafeAt N C B t) :
    (fullPairCalendarCoefficients N C H (fairParameters N) r common x y t 0 = 0 ↔
      ∀ R : RouteFamily N, SharesPopulation N R C t x y) ∧
    (fullPairCalendarCoefficients N C H (fairParameters N) r common x y t 0 = 1 ↔
      ∀ R : RouteFamily N, ¬SharesPopulation N R C t x y) := by
  by_cases ht : t < C.age N.root
  · simp only [fullPairCalendarCoefficients,if_pos ht,sharesPopulation_iff_coOccupy_below_root N C _ ht]
    exact observed_safe_pair_support N C hcut H r common B hx hy hne hlx hly ht hsafe
  · have hr := le_of_not_gt ht
    rw [full_pair_ancestral_zero_coefficient N C H (fairParameters N) r common x y hr]
    constructor
    · constructor
      · intro _ R; exact ⟨none,hr,hr⟩
      · intro _; rfl
    · constructor
      · intro h; norm_num at h
      · intro h
        obtain ⟨R⟩ := routeFamily_exists N
        exact False.elim (h R ⟨none,hr,hr⟩)

/-- Option-population support predicate for ALL original route families. -/
def FullPairSureBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) (t : ℝ) : Prop :=
  (∀ R : RouteFamily N, ∀ x ∈ D, ∀ y ∈ D, x ≠ y → SharesPopulation N R C t x y) ∧
  (∀ R : RouteFamily N, ∀ x ∈ D, ∀ y ∈ B, y ∉ D → ¬SharesPopulation N R C t x y)

lemma occupies_exists (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x : X) {t : ℝ} (hl : C.age (N.leaf x) ≤ t) :
    ∃ p : Option E, Occupies N R C t x p := by
  by_cases ht : C.age N.root ≤ t
  · exact ⟨none,ht⟩
  · obtain ⟨e,he,ha⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists C (R.valid x) hl (lt_of_not_ge ht)
    exact ⟨some e,he,ha⟩

theorem sureBlock_iff_full_pair_predicates (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) {t : ℝ} (hDB : D ⊆ B) (hD : D.Nonempty)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ t) :
    SureBlock N C B D t ↔ FullPairSureBlock N C B D t := by
  constructor
  · intro h
    constructor
    · intro R x hx y hy _
      obtain ⟨p,hp⟩ := h R
      have hxp : x ∈ populationBlock N R B C t p := by rw [hp]; exact hx
      have hyp : y ∈ populationBlock N R B C t p := by rw [hp]; exact hy
      exact ⟨p,(Finset.mem_filter.mp hxp).2,(Finset.mem_filter.mp hyp).2⟩
    · intro R x hx y hyB hyD hco
      obtain ⟨p,hp⟩ := h R
      have hxp : x ∈ populationBlock N R B C t p := by rw [hp]; exact hx
      obtain ⟨q,hxq,hyq⟩ := hco
      have he := occupies_unique N C R (Finset.mem_filter.mp hxp).2 hxq
      subst q
      have hyp : y ∈ populationBlock N R B C t p := Finset.mem_filter.mpr ⟨hyB,hyq⟩
      exact hyD (by rwa [hp] at hyp)
  · intro h R
    obtain ⟨x,hxD⟩ := hD
    obtain ⟨p,hxp⟩ := occupies_exists N C R x (hl x (hDB hxD))
    refine ⟨p,?_⟩
    ext y
    constructor
    · intro hy
      have hh := Finset.mem_filter.mp hy
      by_contra hyD
      exact h.2 R x hxD y hh.1 hyD ⟨p,hxp,hh.2⟩
    · intro hyD
      apply Finset.mem_filter.mpr
      refine ⟨hDB hyD,?_⟩
      by_cases hxy : x = y
      · exact hxy ▸ hxp
      · obtain ⟨q,hxq,hyq⟩ := h.1 R x hxD y hyD hxy
        have he := occupies_unique N C R hxp hxq
        exact he.symm ▸ hyq

def ObservedFullSureBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (B D : Finset X) (t : ℝ) : Prop :=
  (∀ x ∈ D, ∀ y ∈ D, x ≠ y → fullPairCalendarCoefficients N C H (fairParameters N) r common x y t 0 = 0) ∧
  (∀ x ∈ D, ∀ y ∈ B, y ∉ D → fullPairCalendarCoefficients N C H (fairParameters N) r common x y t 0 = 1)

theorem sureBlock_iff_observed_full_safe (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (B D : Finset X) {t : ℝ} (hDB : D ⊆ B) (hD : D.Nonempty)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ t) (hsafe : SafeAt N C B t) :
    SureBlock N C B D t ↔ ObservedFullSureBlock N C H r common B D t := by
  rw [sureBlock_iff_full_pair_predicates N C B D hDB hD hl]
  constructor
  · intro h
    constructor
    · intro x hx y hy hne
      exact (observed_full_safe_pair_support N C hcut H r common B (hDB hx) (hDB hy) hne
        (hl x (hDB hx)) (hl y (hDB hy)) hsafe).1.mpr (fun R => h.1 R x hx y hy hne)
    · intro x hx y hyB hyD
      have hne : x ≠ y := fun hxy => hyD (hxy ▸ hx)
      exact (observed_full_safe_pair_support N C hcut H r common B (hDB hx) hyB hne
        (hl x (hDB hx)) (hl y hyB) hsafe).2.mpr (fun R => h.2 R x hx y hyB hyD)
  · intro h
    constructor
    · intro R x hx y hy hne
      exact (observed_full_safe_pair_support N C hcut H r common B (hDB hx) (hDB hy) hne
        (hl x (hDB hx)) (hl y (hDB hy)) hsafe).1.mp (h.1 x hx y hy hne) R
    · intro R x hx y hyB hyD
      have hne : x ≠ y := fun hxy => hyD (hxy ▸ hx)
      exact (observed_full_safe_pair_support N C hcut H r common B (hDB hx) hyB hne
        (hl x (hDB hx)) (hl y hyB) hsafe).2.mp (h.2 x hx y hyB hyD) R

lemma safeAt_before_or_at_firstGroupingAge (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s : ℝ} (hs : s ≤ C.age N.root) (hc : 2 ≤ B.card)
    (hstart : SafeAt N C B s) {t : ℝ} (ht : t ≤ firstGroupingAge N C B hs hc) : SafeAt N C B t := by
  apply safeAt_of_no_earlier_sure_block N C hcut B hstart
  intro u hsu hut D hDB hD hblock
  exact no_sure_block_before_firstGroupingAge N C B hs hc hsu (hut.trans_le ht) hDB hD
    (sureExactBlock_implies_sureBlock N C B D u hblock)

section DifferentSources
variable {V₂ E₂ : Type*} [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]

theorem equal_fair_pair_laws_full_sure_block_equivalence
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    (B D : Finset X) {t : ℝ} (hDB : D ⊆ B) (hD : D.Nonempty)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ t) (hl₂ : ∀ x ∈ B, C₂.age (N₂.leaf x) ≤ t)
    (hsafe : SafeAt N C B t) (hsafe₂ : SafeAt N₂ C₂ B t)
    (heq : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    SureBlock N C B D t ↔ SureBlock N₂ C₂ B D t := by
  rw [sureBlock_iff_observed_full_safe N C hcut H r common B D hDB hD hl hsafe,
    sureBlock_iff_observed_full_safe N₂ C₂ hcut₂ H₂ r₂ common₂ B D hDB hD hl₂ hsafe₂]
  have hcoeff (x y : X) (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) :
      fullPairCalendarCoefficients N C H (fairParameters N) r common x y t 0 =
        fullPairCalendarCoefficients N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y t 0 :=
    congrArg (fun f : ℝ →₀ ℝ => f 0) (equal_pair_calendar_laws_identify_full_coefficients
      N C H (fairParameters N) r common N₂ C₂ H₂ (fairParameters N₂) r₂ common₂
      x y hne t (heq x hx y hy hne))
  constructor <;> intro h <;> constructor
  · intro x hx y hy hne
    rw [←hcoeff x y (hDB hx) (hDB hy) hne]
    exact h.1 x hx y hy hne
  · intro x hx y hyB hyD
    rw [←hcoeff x y (hDB hx) hyB (fun hxy => hyD (hxy ▸ hx))]
    exact h.2 x hx y hyB hyD
  · intro x hx y hy hne
    rw [hcoeff x y (hDB hx) (hDB hy) hne]
    exact h.1 x hx y hy hne
  · intro x hx y hyB hyD
    rw [hcoeff x y (hDB hx) hyB (fun hxy => hyD (hxy ▸ hx))]
    exact h.2 x hx y hyB hyD

/-- The first ACTUALLY ATTAINED grouping age is identified by ordinary pair
laws across arbitrary different fair sources and mechanisms, including a
root-terminal first age in either source. -/
theorem equal_fair_pair_laws_first_attained_age
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    (B : Finset X) {s : ℝ} (hs : s ≤ C.age N.root) (hs₂ : s ≤ C₂.age N₂.root) (hc : 2 ≤ B.card)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ s) (hl₂ : ∀ x ∈ B, C₂.age (N₂.leaf x) ≤ s)
    (hstart : SafeAt N C B s) (hstart₂ : SafeAt N₂ C₂ B s)
    (heq : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    firstGroupingAge N C B hs hc = firstGroupingAge N₂ C₂ B hs₂ hc := by
  let τ := firstGroupingAge N C B hs hc
  let σ := firstGroupingAge N₂ C₂ B hs₂ hc
  have hτ := firstGroupingAge_attained N C B hs hc
  have hσ := firstGroupingAge_attained N₂ C₂ B hs₂ hc
  apply le_antisymm
  · by_contra hn
    have hστ : σ < τ := lt_of_not_ge hn
    obtain ⟨D,hDB,hD,hblock⟩ := hσ.2.2.2
    have hsN := safeAt_before_or_at_firstGroupingAge N C hcut B hs hc hstart hστ.le
    have hsN₂ := safeAt_firstGroupingAge N₂ C₂ hcut₂ B hs₂ hc hstart₂
    have he := equal_fair_pair_laws_full_sure_block_equivalence N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂ B D
      hDB (Finset.card_pos.mp (by omega)) (fun x hx => (hl x hx).trans hσ.2.1)
      (fun x hx => (hl₂ x hx).trans hσ.2.1) hsN hsN₂ heq
    exact no_sure_block_before_firstGroupingAge N C B hs hc hσ.2.1 hστ hDB hD (he.mpr hblock)
  · by_contra hn
    have hτσ : τ < σ := lt_of_not_ge hn
    obtain ⟨D,hDB,hD,hblock⟩ := hτ.2.2.2
    have hsN := safeAt_firstGroupingAge N C hcut B hs hc hstart
    have hsN₂ := safeAt_before_or_at_firstGroupingAge N₂ C₂ hcut₂ B hs₂ hc hstart₂ hτσ.le
    have he := equal_fair_pair_laws_full_sure_block_equivalence N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂ B D
      hDB (Finset.card_pos.mp (by omega)) (fun x hx => (hl x hx).trans hτ.2.1)
      (fun x hx => (hl₂ x hx).trans hτ.2.1) hsN hsN₂ heq
    exact no_sure_block_before_firstGroupingAge N₂ C₂ B hs₂ hc hτ.2.1 hτσ hDB hD (he.mp hblock)
/-- Both the attained age and ALL simultaneous blocks agree. With one shared
original-label order, the next retained original-label set is identical. -/
theorem equal_fair_pair_laws_simultaneous_deletion [LinearOrder X]
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    (B : Finset X) {s : ℝ} (hs : s ≤ C.age N.root) (hs₂ : s ≤ C₂.age N₂.root) (hc : 2 ≤ B.card)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ s) (hl₂ : ∀ x ∈ B, C₂.age (N₂.leaf x) ≤ s)
    (hstart : SafeAt N C B s) (hstart₂ : SafeAt N₂ C₂ B s)
    (heq : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    firstGroupingAge N C B hs hc = firstGroupingAge N₂ C₂ B hs₂ hc ∧
    simultaneousBlocks N C B (firstGroupingAge N C B hs hc) =
      simultaneousBlocks N₂ C₂ B (firstGroupingAge N₂ C₂ B hs₂ hc) ∧
    survivors N C B (firstGroupingAge N C B hs hc) =
      survivors N₂ C₂ B (firstGroupingAge N₂ C₂ B hs₂ hc) := by
  have ha := equal_fair_pair_laws_first_attained_age N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂
    B hs hs₂ hc hl hl₂ hstart hstart₂ heq
  have hsa := safeAt_firstGroupingAge N C hcut B hs hc hstart
  have hsa₂ := safeAt_firstGroupingAge N₂ C₂ hcut₂ B hs₂ hc hstart₂
  rw [←ha] at hsa₂
  have hτ := (firstGroupingAge_attained N C B hs hc).2.1
  have hblocks : simultaneousBlocks N C B (firstGroupingAge N C B hs hc) =
      simultaneousBlocks N₂ C₂ B (firstGroupingAge N₂ C₂ B hs₂ hc) := by
    rw [←ha]
    ext D
    rw [mem_simultaneousBlocks,mem_simultaneousBlocks]
    constructor <;> rintro ⟨hDB,hD,hblock⟩
    · refine ⟨hDB,hD,?_⟩
      exact (equal_fair_pair_laws_full_sure_block_equivalence N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂ B D
        hDB (Finset.card_pos.mp (by omega)) (fun x hx => (hl x hx).trans hτ)
        (fun x hx => (hl₂ x hx).trans hτ) hsa hsa₂ heq).mp hblock
    · refine ⟨hDB,hD,?_⟩
      exact (equal_fair_pair_laws_full_sure_block_equivalence N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂ B D
        hDB (Finset.card_pos.mp (by omega)) (fun x hx => (hl x hx).trans hτ)
        (fun x hx => (hl₂ x hx).trans hτ) hsa hsa₂ heq).mpr hblock
  refine ⟨ha,hblocks,?_⟩
  unfold survivors
  apply Finset.filter_congr
  intro x _
  constructor <;> intro h D hD hxD
  · have hDN : D ∈ simultaneousBlocks N C B (firstGroupingAge N C B hs hc) := by rwa [hblocks]
    exact h D hDN hxD
  · have hDN₂ : D ∈ simultaneousBlocks N₂ C₂ B (firstGroupingAge N₂ C₂ B hs₂ hc) := by rwa [←hblocks]
    exact h D hDN₂ hxD

#print axioms equal_fair_pair_laws_simultaneous_deletion
end DifferentSources

#print axioms observed_full_safe_pair_support
#print axioms sureBlock_iff_observed_full_safe
#print axioms equal_fair_pair_laws_full_sure_block_equivalence
#print axioms equal_fair_pair_laws_first_attained_age
end GProgram.G5.AttainedChronology
