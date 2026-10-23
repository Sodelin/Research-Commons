import G5AllAgeSafeQuartetTransfer
import G5SharedObservableDeletionTrace

/-!
# Pair-equivalent sources have the same original quartet witnesses at all ages
Contributor: dot / OpenAI, 2026-10-03.
The current original group map is synchronized by actual simultaneous blocks.
Safe stage witness transfer is composed along the constructed finite trace.
Once one original representative remains, COMMON group persistence forbids all
future proper quartet-side witnesses. No final witness equivalence is assumed.
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

lemma stepRepresentative_eq_of_containing_sureBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) (t : ℝ) (hD : D ∈ simultaneousBlocks N C B t) {x : X} (hx : x ∈ D) :
    stepRepresentative N C B t x = originalRepresentative D ((mem_simultaneousBlocks N C B D t).mp hD).2.1 := by
  have h : ∃ F ∈ simultaneousBlocks N C B t, x ∈ F := ⟨D,hD,hx⟩
  unfold stepRepresentative
  rw [dif_pos h]
  have hF := (Classical.choose_spec h).1
  have hxF := (Classical.choose_spec h).2
  have heq := sureBlocks_eq_of_intersection N C B (Classical.choose h) D
    ((mem_simultaneousBlocks N C B (Classical.choose h) t).mp hF).2.2
    ((mem_simultaneousBlocks N C B D t).mp hD).2.2 hxF hx
  simp only [heq]

lemma stepRepresentative_eq_of_same_blocks
    (N : RootedBinary V E X) (C : Calendar N.graph) (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (B : Finset X) (t : ℝ) (hblocks : simultaneousBlocks N C B t = simultaneousBlocks N₂ C₂ B t) :
    ∀ x, stepRepresentative N C B t x = stepRepresentative N₂ C₂ B t x := by
  intro x
  by_cases h : ∃ D ∈ simultaneousBlocks N C B t, x ∈ D
  · obtain ⟨D,hD,hx⟩ := h
    have hD₂ : D ∈ simultaneousBlocks N₂ C₂ B t := by rwa [←hblocks]
    rw [stepRepresentative_eq_of_containing_sureBlock N C B D t hD hx,
      stepRepresentative_eq_of_containing_sureBlock N₂ C₂ B D t hD₂ hx]
  · have h₂ : ¬∃ D ∈ simultaneousBlocks N₂ C₂ B t, x ∈ D := by rwa [←hblocks]
    simp only [stepRepresentative,dif_neg h,dif_neg h₂]

lemma singleton_groups_no_future_quartet_witness (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (A B : Finset X) (g : X → X) {s t : ℝ}
    (hB : B.card = 1) (hgroups : GroupPathInvariant N C H A B g s) (hst : s ≤ t)
    (q : Fin 4 ↪ X) (hqA : ∀ i, q i ∈ A) :
    ¬∃ a : CommonSeed N, OriginalQuartetSideWitness N C H a t q := by
  rintro ⟨a,hw⟩
  have hg0 := hgroups (q 0) (hqA 0)
  have hg2 := hgroups (q 2) (hqA 2)
  have he : g (q 0) = g (q 2) := Finset.card_le_one.mp hB.le _ hg0.1 _ hg2.1
  have hp2 := hg2.2 t hst a
  rw [←he] at hp2
  have hmeet := sharesPopulation_trans N C _ (hg0.2 t hst a) (sharesPopulation_symm N C _ hp2)
  exact original_quartet_witness_cross_separate N C H a q hw hmeet

/-- Inductive composition over the actual attained original-tip trace. -/
theorem deletionTrace_transfers_all_future_quartet_witnesses
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    {B F : Finset X} {s u : ℝ} {n : Nat} (trace : DeletionTrace N C B s F u n)
    (A : Finset X) (q : Fin 4 ↪ X) (hqA : ∀ i, q i ∈ A) (g : X → X)
    (hs₂ : s ≤ C₂.age N₂.root)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ s) (hl₂ : ∀ x ∈ B, C₂.age (N₂.leaf x) ≤ s)
    (hstart : SafeAt N C B s) (hstart₂ : SafeAt N₂ C₂ B s)
    (hgroups : GroupPathInvariant N C H A B g s) (hgroups₂ : GroupPathInvariant N₂ C₂ H₂ A B g s)
    (heq : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    ∀ t : ℝ, s ≤ t →
      ((∃ a : CommonSeed N, OriginalQuartetSideWitness N C H a t q) ↔
        (∃ a : CommonSeed N₂, OriginalQuartetSideWitness N₂ C₂ H₂ a t q)) := by
  induction trace generalizing g with
  | terminal B s hB =>
    intro t hst
    exact iff_of_false (singleton_groups_no_future_quartet_witness N C H A B g hB hgroups hst q hqA)
      (singleton_groups_no_future_quartet_witness N₂ C₂ H₂ A B g hB hgroups₂ hst q hqA)
  | @step B s hs hc F u n rest ih =>
    have hsame := equal_fair_pair_laws_simultaneous_deletion N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂
      B hs hs₂ hc hl hl₂ hstart hstart₂ heq
    let τ := firstGroupingAge N C B hs hc
    have hτs := (firstGroupingAge_attained N C B hs hc).2.1
    have hτr₂ : τ ≤ C₂.age N₂.root := by
      dsimp [τ]; rw [hsame.1]
      exact (firstGroupingAge_attained N₂ C₂ B hs₂ hc).2.2.1
    intro t hst
    by_cases htτ : t ≤ τ
    · have hsN := safeAt_before_or_at_firstGroupingAge N C hcut B hs hc hstart htτ
      have hsN₂ := safeAt_before_or_at_firstGroupingAge N₂ C₂ hcut₂ B hs₂ hc hstart₂
        (show t ≤ firstGroupingAge N₂ C₂ B hs₂ hc from by rw [←hsame.1]; exact htτ)
      exact equal_fair_pair_laws_all_age_safe_original_quartet_witness N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂
        B (fun x hx => (hl x hx).trans hst) (fun x hx => (hl₂ x hx).trans hst) hsN hsN₂ q (fun i => g (q i))
        (fun i => (hgroups (q i) (hqA i)).1) (fun a i => (hgroups (q i) (hqA i)).2 t hst a)
        (fun a i => (hgroups₂ (q i) (hqA i)).2 t hst a) heq
    · have hsB := survivors_subset N C B τ
      have hsa := safeAt_firstGroupingAge N C hcut B hs hc hstart
      have hsa₂ := safeAt_firstGroupingAge N₂ C₂ hcut₂ B hs₂ hc hstart₂
      rw [←hsame.1] at hsa₂
      have hblocks : simultaneousBlocks N C B τ = simultaneousBlocks N₂ C₂ B τ := by
        simpa only [←hsame.1] using hsame.2.1
      have hsurv : survivors N C B τ = survivors N₂ C₂ B τ := by simpa only [←hsame.1] using hsame.2.2
      let g' : X → X := fun x => stepRepresentative N C B τ (g x)
      have hg' := group_paths_preserved_by_simultaneous_deletion N C H A B g hτs
        (fun x hx => (hl x hx).trans hτs) hgroups
      have hg'₂ : GroupPathInvariant N₂ C₂ H₂ A (survivors N C B τ) g' τ := by
        have hg := group_paths_preserved_by_simultaneous_deletion N₂ C₂ H₂ A B g hτs
          (fun x hx => (hl₂ x hx).trans hτs) hgroups₂
        have hgeq : g' = (fun x => stepRepresentative N₂ C₂ B τ (g x)) := by
          funext x; exact stepRepresentative_eq_of_same_blocks N C N₂ C₂ B τ hblocks (g x)
        rw [hsurv,hgeq]
        exact hg
      exact ih g' hτr₂ (fun x hx => (hl x (hsB hx)).trans hτs)
        (fun x hx => (hl₂ x (hsB hx)).trans hτs) (safeAt_subset N C hsB hsa)
        (safeAt_subset N₂ C₂ hsB hsa₂) hg' hg'₂
        (fun x hx y hy hne => heq x (hsB hx) y (hsB hy) hne) t (le_of_not_ge htτ)

/-- Ordinary fresh pair laws identify original quartet-edge witnesses at EVERY
age after actual contemporaneous sampling, under the full fair cut-child class. -/
theorem contemporaneous_pair_laws_identify_all_quartet_witness_ages
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    (A : Finset X) {s : ℝ} (q : Fin 4 ↪ X) (hqA : ∀ i, q i ∈ A)
    (htips : ∀ x ∈ A, C.age (N.leaf x) = s) (htips₂ : ∀ x ∈ A, C₂.age (N₂.leaf x) = s)
    (heq : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    ∀ t : ℝ, s ≤ t →
      ((∃ a : CommonSeed N, OriginalQuartetSideWitness N C H a t q) ↔
        (∃ a : CommonSeed N₂, OriginalQuartetSideWitness N₂ C₂ H₂ a t q)) := by
  have hA : A.Nonempty := ⟨q 0,hqA 0⟩
  obtain ⟨F,u,n,trace,_⟩ := contemporaneous_original_tip_chronology N C hcut A hA htips
  have hs₂ : s ≤ C₂.age N₂.root := by
    rw [←htips₂ (q 0) (hqA 0)]
    exact C₂.age_le_of_directed (N₂.rooted (N₂.leaf (q 0)))
  have hl := fun x hx => (htips x hx).le
  have hl₂ := fun x hx => (htips₂ x hx).le
  exact deletionTrace_transfers_all_future_quartet_witnesses N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂
    trace A q hqA id hs₂ hl hl₂ (safeAt_sampling_age N C A s htips) (safeAt_sampling_age N₂ C₂ A s htips₂)
    (initial_original_group_paths N C H A hl) (initial_original_group_paths N₂ C₂ H₂ A hl₂) heq

#print axioms deletionTrace_transfers_all_future_quartet_witnesses
#print axioms contemporaneous_pair_laws_identify_all_quartet_witness_ages
end GProgram.G5.AttainedChronology
