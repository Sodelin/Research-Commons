import UnifiedLean.Source.SourceWinningClockReset

/-!
# Actual merged CURRENT-pair catalogue inside the surviving clock coordinates

Contributor: dot, 2026-10-02. Original source merges erase only their second
live representative and retain every remaining live population. Consequently
EVERY pair in the actual coded destination is an injective, same-rate original
competitor of the winning clock. This supplies the concrete catalogue needed
to transport the proved residual product law, rather than an assumed reset.
-/
namespace UnifiedLean.Source.SourceMergerClockCatalogue
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceExponentialRace
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma merged_live (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    (state (stepDestination N s (some p))).live = (state s).live.erase p.2.val.2 := rfl

lemma merged_live_population (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) (x : Copy)
    (hx : x ∈ (state (stepDestination N s (some p))).live) :
    (state (stepDestination N s (some p))).location x = (state s).location x := by
  unfold state stepDestination admittedCode
  rw [decode_encode_live_population]
  rfl
  exact hx

/-- Actual finite coding does not invent or move a live population after a
merger. Its original-population root catalogue erases exactly the removed ID. -/
theorem merged_population_catalogue (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) (place : Location V E) :
    populationRoots (state (stepDestination N s (some p))) place =
      (populationRoots (state s) place).erase p.2.val.2 := by
  ext x
  simp only [populationRoots,Finset.mem_filter,Finset.mem_erase]
  have hl := merged_live N s p
  by_cases hx : x ∈ (state (stepDestination N s (some p))).live
  · rw [merged_live_population N s p x hx]
    rw [hl,Finset.mem_erase] at hx ⊢
    tauto
  · have hn : ¬(x ≠ p.2.val.2 ∧ x ∈ (state s).live) := by
      simpa only [hl,Finset.mem_erase] using hx
    tauto

lemma destination_pair_old (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s)
    (q : Choice N (stepDestination N s (some p))) :
    q.2.val ∈ (populationRoots (state s) (originalPlace N q.1)).offDiag := by
  have h := q.2.property
  simp only [merged_population_catalogue] at h
  rcases Finset.mem_offDiag.mp h with ⟨h1,h2,hne⟩
  exact Finset.mem_offDiag.mpr ⟨(Finset.mem_erase.mp h1).2,(Finset.mem_erase.mp h2).2,hne⟩

noncomputable def destinationChoiceOld (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s)
    (q : Choice N (stepDestination N s (some p))) : Choice N s :=
  ⟨q.1,⟨q.2.val,destination_pair_old N s p q⟩⟩

lemma destinationChoiceOld_injective (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    Function.Injective (destinationChoiceOld N s p) := by
  intro q q' h
  have hi : q.1 = q'.1 := congrArg (fun z : Choice N s => z.1) h
  have hp : q.2.val = q'.2.val := congrArg (fun z : Choice N s => z.2.val) h
  cases q with
  | mk i q =>
      cases q' with
      | mk i' q' =>
          cases hi
          exact congrArg (Sigma.mk i) (Subtype.ext hp)

lemma destinationChoiceOld_ne_winner (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s)
    (q : Choice N (stepDestination N s (some p))) : destinationChoiceOld N s p q ≠ p := by
  have h := q.2.property
  simp only [merged_population_catalogue] at h
  have hn := (Finset.mem_erase.mp (Finset.mem_offDiag.mp h).2.1).1
  intro heq
  exact hn (congrArg (fun z : Choice N s => z.2.val.2) heq)

/-- Every actual post-merger coordinate is a distinct genuine surviving
old coordinate. Both original graph/population and current representative IDs
are preserved by the embedding; all removed-ID clocks are discarded. -/
noncomputable def destinationClockEmbedding (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    Choice N (stepDestination N s (some p)) ↪ Other p where
  toFun q := ⟨destinationChoiceOld N s p q,destinationChoiceOld_ne_winner N s p q⟩
  inj' := by
    intro q q' h
    exact destinationChoiceOld_injective N s p (congrArg Subtype.val h)

theorem destination_clock_original_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Choice N s)
    (q : Choice N (stepDestination N s (some p))) :
    choiceRate N r s (destinationClockEmbedding N s p q).val =
      choiceRate N r (stepDestination N s (some p)) q := rfl

#print axioms merged_population_catalogue
#print axioms destinationClockEmbedding
#print axioms destination_clock_original_rate
end UnifiedLean.Source.SourceMergerClockCatalogue
