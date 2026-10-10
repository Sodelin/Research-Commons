import G5ObservedExactBlockTransfer
import G5ChronologicalQuartetWitnessTransfer

/-!
# M3 exact blocks lifted through the actual full original-label chronology
Contributor: dot / OpenAI, 10 October 2026.
UNCOMPILED CANDIDATE. Reuses the accepted original group-path invariant and
cardinality-decreasing attained-age induction. The observable block transfer
is freshly derived at each safe stage. No posterior, common register or
independence assumption is transported between stages or rival sources.
-/
namespace GProgram.G5.ObservedLiftedBlocks
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.SafePast
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open GProgram.G5.AttainedChronology GProgram.G5.HiddenRegisterTimedProjectivity
open GProgram.G5.SafeExactBlockSupport GProgram.G5.ObservedExactBlockTransfer
open GProgram.G5.ObservedSureBlockChronology
open scoped Classical
variable {V E X V₂ E₂ : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E] [LinearOrder X]
variable [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]

lemma singleton_groups_possible_block_iff (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (A B D : Finset X) (g : X → X) {s t : ℝ}
    (hl : ∀ x, C.age (N.leaf x) ≤ t) (hB : B.card = 1)
    (hgroups : GroupPathInvariant N C H A B g s) (hst : s ≤ t)
    (hDA : D ⊆ A) (hD : D.Nonempty) :
    PossibleBlock N C H A D t ↔ D = A := by
  obtain ⟨c,hc⟩ := hD
  have hsame (a : CommonSeed N) (x : X) (hx : x ∈ A) :
      currentPopulation N C H t hl a x = currentPopulation N C H t hl a c := by
    have hgc := hgroups c (hDA hc)
    have hgx := hgroups x hx
    have he : g x = g c := Finset.card_le_one.mp hB.le _ hgx.1 _ hgc.1
    have hp := hgx.2 t hst a
    rw [he] at hp
    have hxc := sharesPopulation_trans N C (commonRoutes N C H a) hp
      (sharesPopulation_symm N C _ (hgc.2 t hst a))
    obtain ⟨pop,hxp,hcp⟩ := hxc
    exact ((occupies_iff_currentPopulation N C H t hl a x pop).mp hxp).trans
      ((occupies_iff_currentPopulation N C H t hl a c pop).mp hcp).symm
  rw [possibleBlock_iff_anchor N C H A D t hl hDA hc]
  constructor
  · rintro ⟨a,ha⟩
    exact Finset.Subset.antisymm hDA (fun x hx => (ha x hx).mpr (hsame a x hx))
  · intro he
    refine ⟨fun _ => false,?_⟩
    intro x hx
    exact iff_of_true (by rwa [he]) (hsame (fun _ => false) x hx)

/-- A representative exact block transfers and lifts to precisely the SAME
set of original labels through the shared group map. -/
theorem safe_lifted_block_transfer
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (hX : 3 ≤ Fintype.card X) (A B D : Finset X) (g : X → X) (a0 s t : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    (ht : a0 ≤ t) (hst : s ≤ t) (hsafe : SafeAt N C B t) (hsafe₂ : SafeAt N₂ C₂ B t)
    (hgroups : GroupPathInvariant N C H A B g s) (hgroups₂ : GroupPathInvariant N₂ C₂ H₂ A B g s)
    (hD : D.Nonempty)
    (heq : ∀ tip : Fin 3 ↪ X, naturalObservedFullLaw N C tip H p common r =
      naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    PossibleBlock N C H A D t → PossibleBlock N₂ C₂ H₂ A D t := by
  rintro ⟨a,pop,hblock⟩
  let F := populationBlock N (commonRoutes N C H a) B C t pop
  have hFB : F ⊆ B := Finset.filter_subset _ _
  have hlift : A.filter (fun x => g x ∈ F) = D :=
    (original_population_block_is_group_lift N C H A B g hgroups hst a pop).symm.trans hblock
  have hF : F.Nonempty := by
    obtain ⟨x,hx⟩ := hD
    rw [←hlift] at hx
    exact ⟨g x,(Finset.mem_filter.mp hx).2⟩
  obtain ⟨a₂,pop₂,hblock₂⟩ := (equal_m3_laws_safe_possible_blocks N C hcut H p common r
    N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ hX B F hFB hF a0 t htips htips₂ ht hsafe hsafe₂ heq).mp ⟨a,pop,rfl⟩
  refine ⟨a₂,pop₂,?_⟩
  rw [original_population_block_is_group_lift N₂ C₂ H₂ A B g hgroups₂ hst a₂ pop₂,hblock₂]
  exact hlift

/-- Actual attained-age induction transfers every nonempty original block at
all future ages, not only quartet-side witnesses. -/
theorem deletionTrace_transfers_all_future_blocks
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (hX : 3 ≤ Fintype.card X) (a0 : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    {B F : Finset X} {s u : ℝ} {n : Nat} (trace : DeletionTrace N C B s F u n)
    (A D : Finset X) (hDA : D ⊆ A) (hD : D.Nonempty) (g : X → X)
    (hstartAge : a0 ≤ s) (hs₂ : s ≤ C₂.age N₂.root)
    (hstart : SafeAt N C B s) (hstart₂ : SafeAt N₂ C₂ B s)
    (hgroups : GroupPathInvariant N C H A B g s) (hgroups₂ : GroupPathInvariant N₂ C₂ H₂ A B g s)
    (heq : ∀ tip : Fin 3 ↪ X, naturalObservedFullLaw N C tip H p common r =
      naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    ∀ t : ℝ, s ≤ t → (PossibleBlock N C H A D t ↔ PossibleBlock N₂ C₂ H₂ A D t) := by
  induction trace generalizing g with
  | terminal B s hB =>
    intro t hst
    rw [singleton_groups_possible_block_iff N C H A B D g
        (fun x => (htips x).le.trans (hstartAge.trans hst)) hB hgroups hst hDA hD,
      singleton_groups_possible_block_iff N₂ C₂ H₂ A B D g
        (fun x => (htips₂ x).le.trans (hstartAge.trans hst)) hB hgroups₂ hst hDA hD]
  | @step B s hs hc F u n rest ih =>
    have hsame := equal_m3_laws_simultaneous_deletion N C hcut H p common r
      N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ hX B a0 s htips htips₂ hstartAge hs hs₂ hc hstart hstart₂ heq
    let tau := firstGroupingAge N C B hs hc
    have hts := (firstGroupingAge_attained N C B hs hc).2.1
    have htr₂ : tau ≤ C₂.age N₂.root := by
      dsimp [tau]; rw [hsame.1]
      exact (firstGroupingAge_attained N₂ C₂ B hs₂ hc).2.2.1
    intro t hst
    by_cases htt : t ≤ tau
    · have hsN := safeAt_before_or_at_firstGroupingAge N C hcut B hs hc hstart htt
      have hsN₂ := safeAt_before_or_at_firstGroupingAge N₂ C₂ hcut₂ B hs₂ hc hstart₂
        (show t ≤ firstGroupingAge N₂ C₂ B hs₂ hc from by rw [←hsame.1]; exact htt)
      exact ⟨safe_lifted_block_transfer N C hcut H p common r N₂ C₂ hcut₂ H₂ p₂ common₂ r₂
          hX A B D g a0 s t htips htips₂ (hstartAge.trans hst) hst hsN hsN₂ hgroups hgroups₂ hD heq,
        safe_lifted_block_transfer N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ N C hcut H p common r
          hX A B D g a0 s t htips₂ htips (hstartAge.trans hst) hst hsN₂ hsN hgroups₂ hgroups hD
          (fun tip => (heq tip).symm)⟩
    · have hsB := survivors_subset N C B tau
      have hsa := safeAt_firstGroupingAge N C hcut B hs hc hstart
      have hsa₂ := safeAt_firstGroupingAge N₂ C₂ hcut₂ B hs₂ hc hstart₂
      rw [←hsame.1] at hsa₂
      have hblocks : simultaneousBlocks N C B tau = simultaneousBlocks N₂ C₂ B tau := by
        simpa only [←hsame.1] using hsame.2.1
      have hsurv : survivors N C B tau = survivors N₂ C₂ B tau := by
        simpa only [←hsame.1] using hsame.2.2
      let g' : X → X := fun x => stepRepresentative N C B tau (g x)
      have hg' := group_paths_preserved_by_simultaneous_deletion N C H A B g hts
        (fun x _ => (htips x).le.trans (hstartAge.trans hts)) hgroups
      have hg'₂ : GroupPathInvariant N₂ C₂ H₂ A (survivors N C B tau) g' tau := by
        have hg := group_paths_preserved_by_simultaneous_deletion N₂ C₂ H₂ A B g hts
          (fun x _ => (htips₂ x).le.trans (hstartAge.trans hts)) hgroups₂
        have hgeq : g' = (fun x => stepRepresentative N₂ C₂ B tau (g x)) := by
          funext x; exact stepRepresentative_eq_of_same_blocks N C N₂ C₂ B tau hblocks (g x)
        rw [hsurv,hgeq]
        exact hg
      exact ih g' (hstartAge.trans hts) htr₂
        (safeAt_subset N C hsB hsa) (safeAt_subset N₂ C₂ hsB hsa₂) hg' hg'₂ t (le_of_not_ge htt)

/-- The whole original-label possible-block family at every finite age follows
from ordinary M3 observation laws alone on the admitted binary source class. -/
theorem m3_identifies_all_original_possible_blocks
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (hX : 3 ≤ Fintype.card X) (a0 : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    (heq : ∀ tip : Fin 3 ↪ X, naturalObservedFullLaw N C tip H p common r =
      naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    ∀ D : Finset X, D.Nonempty → ∀ t : ℝ, a0 ≤ t →
      (PossibleBlock N C H Finset.univ D t ↔ PossibleBlock N₂ C₂ H₂ Finset.univ D t) := by
  intro D hD
  have hA : (Finset.univ : Finset X).Nonempty := hD.mono (Finset.subset_univ D)
  obtain ⟨F,u,n,trace,_⟩ := contemporaneous_original_tip_chronology N C hcut
    Finset.univ hA (fun x _ => htips x)
  have hs₂ : a0 ≤ C₂.age N₂.root := by
    obtain ⟨x,_⟩ := hD
    rw [←htips₂ x]
    exact C₂.age_le_of_directed (N₂.rooted (N₂.leaf x))
  exact deletionTrace_transfers_all_future_blocks N C hcut H p common r N₂ C₂ hcut₂ H₂ p₂ common₂ r₂
    hX a0 htips htips₂ trace Finset.univ D (Finset.subset_univ D) hD id le_rfl hs₂
    (safeAt_sampling_age N C Finset.univ a0 (fun x _ => htips x))
    (safeAt_sampling_age N₂ C₂ Finset.univ a0 (fun x _ => htips₂ x))
    (initial_original_group_paths N C H Finset.univ (fun x _ => (htips x).le))
    (initial_original_group_paths N₂ C₂ H₂ Finset.univ (fun x _ => (htips₂ x).le)) heq

#print axioms safe_lifted_block_transfer
#print axioms deletionTrace_transfers_all_future_blocks
#print axioms m3_identifies_all_original_possible_blocks
end GProgram.G5.ObservedLiftedBlocks
