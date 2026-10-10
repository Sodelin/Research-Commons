import G5SafeExactBlockSupport

/-!
# Ordinary M3 laws identify every safe possible exact block
Contributor: dot / OpenAI, 10 October 2026.
UNCOMPILED CANDIDATE. The accepted bounded-domain obstruction is applied to
actual source domains. Every small obstruction is read from a genuine fresh
three-taxon panel on the original labels, including deleted extra taxa.
-/
namespace GProgram.G5.ObservedExactBlockTransfer
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5 GProgram.G5.SafePast
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.NativeCurrentPortCompiler
open UnifiedLean.Source.NativeCommonPairGerm
open GProgram.G5.OriginalProgramSurvival GProgram.G5.OriginalSelectedPosterior
open GProgram.G5.EnumeratedPosteriorGerm GProgram.G5.ActualActivatedPrefix
open GProgram.G5.TriplePartitionReadout GProgram.G5.AllAgeObservedSupport
open GProgram.G5.HiddenRegisterTimedProjectivity GProgram.G5.AttainedChronology
open GProgram.G5.ObservedSureBlockChronology GProgram.G5.BoundedSupport
open GProgram.G5.SafeExactBlockSupport
open scoped Classical
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

lemma possibleBlock_iff_anchor (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (B D : Finset X) (t : ℝ)
    (hl : ∀ x, C.age (N.leaf x) ≤ t) (hDB : D ⊆ B) {c : X} (hc : c ∈ D) :
    PossibleBlock N C H B D t ↔ ∃ a : CommonSeed N, ∀ x ∈ B,
      (x ∈ D ↔ currentPopulation N C H t hl a x = currentPopulation N C H t hl a c) := by
  constructor
  · rintro ⟨a,pop,hp⟩
    have hmem (x : X) (hx : x ∈ B) :
        x ∈ D ↔ currentPopulation N C H t hl a x = pop := by
      rw [←hp]
      simp only [populationBlock,Finset.mem_filter,hx,true_and,occupies_iff_currentPopulation N C H t hl]
    refine ⟨a,?_⟩
    intro x hx
    rw [(hmem c (hDB hc)).mp hc]
    exact hmem x hx
  · rintro ⟨a,ha⟩
    refine ⟨a,currentPopulation N C H t hl a c,?_⟩
    ext x
    simp only [populationBlock,Finset.mem_filter,occupies_iff_currentPopulation N C H t hl]
    constructor
    · rintro ⟨hx,he⟩; exact (ha x hx).mpr he
    · intro hx; exact ⟨hDB hx,(ha x (hDB hx)).mp hx⟩

lemma exactBlock_inter {P : Type*} [DecidableEq P] (S : X → Finset P) (U D : Finset X) :
    ExactBlock S U D ↔ ExactBlock S U (U ∩ D) := by
  constructor <;> rintro ⟨a,ha⟩ <;> refine ⟨a,?_⟩ <;> intro x hx
  · simpa only [Finset.mem_inter,hx,true_and] using ha x hx
  · simpa only [Finset.mem_inter,hx,true_and] using ha x hx

section TwoSources
variable {V₂ E₂ : Type*} [DecidableEq V₂] [DecidableEq E₂] [Fintype V₂] [Fintype E₂]

/-- The source-independent five-state partition reader transfers an exact
block on any selected safe subset of one genuine original triple. -/
theorem observed_triple_transfers_selected_block
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (B U D : Finset X) (hUB : U ⊆ B) (hDU : D ⊆ U) (hD : D.Nonempty)
    (tip : Fin 3 ↪ X) (hcover : ∀ x ∈ U, ∃ i, tip i = x)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    (ht : a0 ≤ t) (hsafe : SafeAt N C B t) (hsafe₂ : SafeAt N₂ C₂ B t)
    (heq : naturalObservedFullLaw N C tip H p common r = naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    PossibleBlock N C H U D t → PossibleBlock N₂ C₂ H₂ U D t := by
  let hl : ∀ x, C.age (N.leaf x) ≤ t := fun x => (htips x).le.trans ht
  let hl₂ : ∀ x, C₂.age (N₂.leaf x) ≤ t := fun x => (htips₂ x).le.trans ht
  obtain ⟨c,hc⟩ := hD
  obtain ⟨ic,hic⟩ := hcover c (hDU hc)
  obtain ⟨past,epsilon,hread,hforward,_⟩ := actual_selected_safe_readout
    N C hcut H p common r B tip a0 t htips ht hsafe
  obtain ⟨past₂,epsilon₂,hread₂,_,hbackward₂⟩ := actual_selected_safe_readout
    N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ B tip a0 t htips₂ ht hsafe₂
  have hsupport := cut_readouts_identify_occupancy N C tip H p common r N₂ C₂ tip H₂ p₂ common₂ r₂
    t past past₂ epsilon epsilon₂ hread hread₂ heq
  intro hblock
  obtain ⟨a,ha⟩ := (possibleBlock_iff_anchor N C H U D t hl hDU hc).mp hblock
  obtain ⟨s,hs⟩ := hforward a
  obtain ⟨s₂,hpartition⟩ := (hsupport (ancestorPartition (codePopulation N s.val))).mp ⟨s,rfl⟩
  obtain ⟨a₂,ha₂⟩ := hbackward₂ s₂
  apply (possibleBlock_iff_anchor N₂ C₂ H₂ U D t hl₂ hDU hc).mpr
  refine ⟨a₂,?_⟩
  intro x hx
  obtain ⟨ix,hix⟩ := hcover x hx
  have hxB : tip ix ∈ B := by rw [hix]; exact hUB hx
  have hcB : tip ic ∈ B := by rw [hic]; exact hUB (hDU hc)
  have hrel := ancestorPartition_eq_rel (codePopulation N s.val) (codePopulation N₂ s₂.val)
    hpartition.symm ix ic
  rw [hs ix hxB,hs ic hcB,ha₂ ix hxB,ha₂ ic hcB,hix,hic] at hrel
  exact (ha x hx).trans hrel

/-- No compatibility of hidden registers, edge identities, rates, root ages,
conditioned weights or deletion schedules is included in this premise. -/
theorem equal_m3_laws_safe_possible_blocks
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (hX : 3 ≤ Fintype.card X) (B D : Finset X) (hDB : D ⊆ B) (hD : D.Nonempty)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    (ht : a0 ≤ t) (hsafe : SafeAt N C B t) (hsafe₂ : SafeAt N₂ C₂ B t)
    (heq : ∀ tip : Fin 3 ↪ X, naturalObservedFullLaw N C tip H p common r =
      naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    PossibleBlock N C H B D t ↔ PossibleBlock N₂ C₂ H₂ B D t := by
  let hl : ∀ x, C.age (N.leaf x) ≤ t := fun x => (htips x).le.trans ht
  let hl₂ : ∀ x, C₂.age (N₂.leaf x) ≤ t := fun x => (htips₂ x).le.trans ht
  rw [possible_block_iff_cartesian N C hcut H B D t hl hsafe hDB,
    possible_block_iff_cartesian N₂ C₂ hcut₂ H₂ B D t hl₂ hsafe₂ hDB,
    exact_block_iff_local _ B D hDB hD 2 (fun c _ => currentDomain_card_le_two N C hcut H t hl c),
    exact_block_iff_local _ B D hDB hD 2 (fun c _ => currentDomain_card_le_two N₂ C₂ hcut₂ H₂ t hl₂ c)]
  have hlocal (U : Finset X) (hUB : U ⊆ B) (hU : U.card ≤ 2+1) (hUD : (U ∩ D).Nonempty) :
      ExactBlock (currentDomain N C H t hl) U D ↔ ExactBlock (currentDomain N₂ C₂ H₂ t hl₂) U D := by
    obtain ⟨tip,hcover⟩ := triple_covering_small_set hX U hU
    have hsafeU : SafeAt N C U t ∧ SafeAt N₂ C₂ U t := by
      letI : LinearOrder X := LinearOrder.lift' (Fintype.equivFin X) (Fintype.equivFin X).injective
      exact ⟨safeAt_subset N C hUB hsafe,safeAt_subset N₂ C₂ hUB hsafe₂⟩
    rw [exactBlock_inter _ U D,exactBlock_inter _ U D,
      ←possible_block_iff_cartesian N C hcut H U (U ∩ D) t hl hsafeU.1 Finset.inter_subset_left,
      ←possible_block_iff_cartesian N₂ C₂ hcut₂ H₂ U (U ∩ D) t hl₂ hsafeU.2 Finset.inter_subset_left]
    exact ⟨observed_triple_transfers_selected_block N C hcut H p common r N₂ C₂ hcut₂ H₂ p₂ common₂ r₂
        B U (U ∩ D) hUB Finset.inter_subset_left hUD tip hcover a0 t htips htips₂ ht hsafe hsafe₂ (heq tip),
      observed_triple_transfers_selected_block N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ N C hcut H p common r
        B U (U ∩ D) hUB Finset.inter_subset_left hUD tip hcover a0 t htips₂ htips ht hsafe₂ hsafe (heq tip).symm⟩
  constructor
  · intro h U hUB hU hUD; exact (hlocal U hUB hU hUD).mp (h U hUB hU hUD)
  · intro h U hUB hU hUD; exact (hlocal U hUB hU hUD).mpr (h U hUB hU hUD)
end TwoSources

#print axioms observed_triple_transfers_selected_block
#print axioms equal_m3_laws_safe_possible_blocks
end GProgram.G5.ObservedExactBlockTransfer
