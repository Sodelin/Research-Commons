import G5SourcePairPersistence
import UnifiedLean.Source.SourceCompletionHarmonic

namespace GProgram.G5.CompletionPairPersistence
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic UnifiedLean.G6.BinHistory
open UnifiedLean.Source.SourceEmbeddedJumpLaw
open CloudG3.LiteralSameBinTrace
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma jump_relation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample)
    (hd : d ∈ (sourceJumpStep N r s).support) : RelationMonotone N s d := by
  rcases source_jump_support_cases N r s hd with ⟨he,_⟩ | ⟨p,he⟩
  · subst d
    exact relation_monotone_refl N s
  · subst d
    exact actual_destination_relation_monotone N s p

lemma ancestral_completion_relation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : ℕ) (s d : Code N sample)
    (hd : d ∈ (ancestralCompletion N r n s).support) : RelationMonotone N s d := by
  induction n generalizing s with
  | zero =>
    have h : d = s := by simpa [ancestralCompletion] using hd
    subst d
    exact relation_monotone_refl N s
  | succ n ih =>
    obtain ⟨e,he,hd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    exact relation_monotone_trans N s e d (jump_relation N r s e he) (ih e hd)

lemma completion_relation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample)
    (hd : d ∈ (completionKernel N r s).support) : RelationMonotone N s d :=
  ancestral_completion_relation N r (Fintype.card Copy) s d hd

lemma completion_all_pairs (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) (hs : AncestralRoot N s)
    (hd : d ∈ (completionKernel N r s).support) (x y : Copy) :
    (state d).ancestor x = (state d).ancestor y := by
  have hc := (ancestral_completion_terminal_support N r (Fintype.card Copy) s hs
    (Finset.card_le_univ s.val.live) hd).2
  exact (Finset.card_le_one.mp hc) _ (d.property.forest.ancestor_live x) _
    (d.property.forest.ancestor_live y)

#print axioms completion_relation
#print axioms completion_all_pairs
end GProgram.G5.CompletionPairPersistence
