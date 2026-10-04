import G5SynchronizedObservableChronology
import G5OriginalGroupPathChronology

/-!
# One identical attained deletion trace for different observed-equivalent sources
Contributor: dot / OpenAI, 2026-10-03.
The original labels, fixed label order and ordinary fresh pair laws are retained
at every stage. The graph/calendar/rates/COMMON-I mode can differ. Entire-safe
past and singleton original group paths are derived, not source record fields.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.SafePast
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativePairCalendarObservation UnifiedLean.Source.NativeFairCurrentPosition
open scoped Classical
variable {V E X V₂ E₂ : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E] [LinearOrder X]
variable [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]

theorem deletionTrace_of_equal_fair_pair_laws
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    {B F : Finset X} {s u : ℝ} {n : Nat} (trace : DeletionTrace N C B s F u n)
    (hs₂ : s ≤ C₂.age N₂.root)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ s) (hl₂ : ∀ x ∈ B, C₂.age (N₂.leaf x) ≤ s)
    (hstart : SafeAt N C B s) (hstart₂ : SafeAt N₂ C₂ B s)
    (heq : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    DeletionTrace N₂ C₂ B s F u n := by
  induction trace with
  | terminal B s hB => exact DeletionTrace.terminal B s hB
  | @step B s hs hc F u n rest ih =>
    have hsame := equal_fair_pair_laws_simultaneous_deletion N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂
      B hs hs₂ hc hl hl₂ hstart hstart₂ heq
    let τ := firstGroupingAge N C B hs hc
    have hτs := (firstGroupingAge_attained N C B hs hc).2.1
    have hτr₂ : τ ≤ C₂.age N₂.root := by
      dsimp [τ]
      rw [hsame.1]
      exact (firstGroupingAge_attained N₂ C₂ B hs₂ hc).2.2.1
    have hsa := safeAt_firstGroupingAge N C hcut B hs hc hstart
    have hsa₂ := safeAt_firstGroupingAge N₂ C₂ hcut₂ B hs₂ hc hstart₂
    rw [←hsame.1] at hsa₂
    have hsB := survivors_subset N C B τ
    have hrest := ih hτr₂
      (fun x hx => (hl x (hsB hx)).trans hτs)
      (fun x hx => (hl₂ x (hsB hx)).trans hτs)
      (safeAt_subset N C hsB hsa) (safeAt_subset N₂ C₂ hsB hsa₂)
      (fun x hx y hy hne => heq x (hsB hx) y (hsB hy) hne)
    apply DeletionTrace.step B s hs₂ hc
    rwa [hsame.2.2,hsame.1] at hrest

/-- Actual observed-equivalent sources admit the SAME finite first-age /
simultaneous-block deletion trace to the SAME surviving original tip. -/
theorem contemporaneous_shared_observable_chronology
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    (A : Finset X) {s : ℝ} (hA : A.Nonempty)
    (htips : ∀ x ∈ A, C.age (N.leaf x) = s) (htips₂ : ∀ x ∈ A, C₂.age (N₂.leaf x) = s)
    (heq : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    ∃ F u n, DeletionTrace N C A s F u n ∧ DeletionTrace N₂ C₂ A s F u n ∧
      F.card = 1 ∧ F ⊆ A ∧ s ≤ u ∧ SafeAt N C F u ∧ n ≤ A.card-1 := by
  obtain ⟨F,u,n,ht,hF,hFA,hsu,hu,hFs,hbound⟩ := contemporaneous_original_tip_chronology N C hcut A hA htips
  have hs₂ : s ≤ C₂.age N₂.root := by
    obtain ⟨x,hx⟩ := hA
    rw [←htips₂ x hx]
    exact C₂.age_le_of_directed (N₂.rooted (N₂.leaf x))
  have hl := fun x hx => (htips x hx).le
  have hl₂ := fun x hx => (htips₂ x hx).le
  exact ⟨F,u,n,ht,deletionTrace_of_equal_fair_pair_laws N C hcut H r common N₂ C₂ hcut₂ H₂ r₂ common₂
    ht hs₂ hl hl₂ (safeAt_sampling_age N C A s htips) (safeAt_sampling_age N₂ C₂ A s htips₂) heq,
    hF,hFA,hsu,hFs,hbound⟩

#print axioms deletionTrace_of_equal_fair_pair_laws
#print axioms contemporaneous_shared_observable_chronology
end GProgram.G5.AttainedChronology
