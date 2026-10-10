import OriginalBigonProgramDiagonal

/-! Composition helper for the actual source program. This is a conditional
algebraic lemma, intended to be instantiated by explicit original block rows;
its row-constant premise is not a full source-word result. dot, 9 October 2026. -/
namespace DotG34.ActualSerialNoLossComposition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open GProgram.G5.ActualRoutingSupport
open scoped Classical ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_no_loss_append (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (pre post : List (ProgramStep N))
    (s : Code N sample) (q : ℝ≥0∞)
    (hq : ∀ d ∈ (sourceProgram N r pre s).support, liveCard d = liveCard s →
      ((sourceProgram N r post d).map liveCard) (liveCard d) = q) :
    ((sourceProgram N r (pre ++ post) s).map liveCard) (liveCard s) =
      ((sourceProgram N r pre s).map liveCard) (liveCard s) * q := by
  rw [sourceProgram_append, PMF.map_bind, PMF.bind_apply, PMF.map_apply,
    ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro d
  by_cases hd : sourceProgram N r pre s d = 0
  · simp [hd]
  · have hle := program_card_le N r pre s d hd
    by_cases hc : liveCard s = liveCard d
    · rw [if_pos hc, hc, hq d hd hc.symm]
    · rw [if_neg hc, zero_mul]
      have hz : ((sourceProgram N r post d).map liveCard) (liveCard s) = 0 := by
        by_contra hn
        obtain ⟨e, he, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hn
        have htail := program_card_le N r post d e he
        omega
      rw [hz, mul_zero]

#print axioms actual_no_loss_append
end DotG34.ActualSerialNoLossComposition
