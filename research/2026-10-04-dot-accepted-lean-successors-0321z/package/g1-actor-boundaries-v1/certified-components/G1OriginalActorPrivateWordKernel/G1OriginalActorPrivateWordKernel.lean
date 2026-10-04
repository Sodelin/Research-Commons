import G1ActualOriginalUnrankedLocalKernel
import G1FinitePendingActorPromotion

/-! The actual source-defined unranked local kernels compose to the ORIGINAL
source program row on a common actor carrier. This supplies a genuine private
word to the inherited finite pending algebra, without a desired-word oracle. -/
namespace G1OriginalActorPrivateWordKernel
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open G1UnrankedSourceView G1UnrankedActualGenerator G1ActualOriginalUnrankedLocalKernel
open G1FinitePendingActorPromotion
open scoped Classical
variable {V E Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

lemma actual_original_local_nil (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (keep : Finset Copy) (value : UnrankedView V E Copy) :
    originalLocalRow N sample r keep [] value = PMF.pure value := by
  unfold originalLocalRow
  split_ifs with hw
  · simp only [G1UnrankedActualFuture.unrankedProgram,PMF.pure_map]
    rw [Classical.choose_spec hw]
  · rfl

/-- The harmless identity extension on unreachable interface values composes
as well. All reachable rows remain the exact actual original source law. -/
theorem actual_original_local_composition_all_values (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (keep : Finset Copy) (first last : List (ProgramStep N))
    (value : UnrankedView V E Copy) :
    originalLocalRow N sample r keep (first ++ last) value =
      (originalLocalRow N sample r keep first value).bind (originalLocalRow N sample r keep last) := by
  by_cases hw : ∃ v : UnrankedIndex N sample keep, v.val = value
  · obtain ⟨v,rfl⟩ := hw
    exact actual_original_local_word_composition N r keep first last v
  · simp only [originalLocalRow,dif_neg hw,PMF.pure_bind]

/-- The actual finite ORIGINAL operation word is an actual private actor
kernel, including whole unranked labels/populations/SAME register. -/
theorem actual_original_source_private_word (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N)) (value : UnrankedView V E Copy) :
    actorWordKernel (ops.map (fun op => originalLocalRow N sample r keep [op])) value =
      originalLocalRow N sample r keep ops value := by
  induction ops generalizing value with
  | nil => exact (actual_original_local_nil N sample r keep value).symm
  | cons op ops ih =>
    simp only [List.map_cons,actorWordKernel]
    have ht : actorWordKernel (ops.map (fun op => originalLocalRow N sample r keep [op])) =
        originalLocalRow N sample r keep ops := funext ih
    rw [ht,←actual_original_local_composition_all_values]
    rfl

#print axioms actual_original_source_private_word
end G1OriginalActorPrivateWordKernel
