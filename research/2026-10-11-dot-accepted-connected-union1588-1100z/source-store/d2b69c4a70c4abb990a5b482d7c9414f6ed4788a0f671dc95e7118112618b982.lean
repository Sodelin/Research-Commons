import FiniteCutSourceWord
import ArbitraryCutSharedBankProxy

/-! Original finite-bin complete-law proxy with generated legal cut word.
Contributor: dot / OpenAI, 9 October 2026. Source comparison and finite-count
budgets remain explicit; no refinement/bin-contract oracle is supplied. -/
namespace DotG6.GeneratedCompleteBinProxy
open Nanuq.Source MeasureTheory GProgram.G5
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceEpochSemigroup
open UnifiedLean.Source.SourceCalendarPhysicalSupport UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.G6.AncestralRateFree UnifiedLean.G6.FiniteProbability
open GProgram.G2.SourceFiniteHistory GProgram.G2.ChronologicalPathReadout
open CloudG3.ActualCutJointLaw CloudG3.ActualCalendarCutContext
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualObservationCutRefinement
open CloudG3.CompleteCalendarJointLaw
open CloudG6.PrivateSeedFactorization CloudG6.NaturalCalendarPastAdmission
open CloudG6.NaturalPastCompleteObservation
open DotG6.UpperRateNaturalHistory DotG6.UpperRateProxySupport
open DotG6.OriginalInheritanceRetuning DotG6.SharedBankNaturalProxy
open DotG6.SharedBankCompleteProxy
open UnifiedLean.G6.NaturalAncestralCutExtension
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

open UnifiedLean.G6.FiniteCutSourceWord DotG6.ArbitraryCutSharedBankProxy

noncomputable def lastCut (qs : List ℝ) : ℝ := qs.foldr max 0

theorem le_lastCut (qs : List ℝ) (q : ℝ) (hq : q ∈ qs) : q ≤ lastCut qs := by
  induction qs with
  | nil => simp at hq
  | cons a qs ih =>
      rcases List.mem_cons.mp hq with h | h
      · subst q
        exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

noncomputable def extendedOriginalOps (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (qs : List ℝ) : List (ProgramStep N) :=
  let ops := compiledCalendarProgram N C H (originalGamma p) common
  ops ++ [.interval (Real.toNNReal (lastCut qs -
    (firstOriginalDate N C + (programDuration N ops : ℝ))))]

noncomputable def originalCutWord (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (qs : List ℝ) :
    List (ProgramStep N × Fin (qs.length+1)) :=
  rankedWord N qs (extendedOriginalOps N C H p common qs) (firstOriginalDate N C)

/-- Full original natural completed finite-bin law: calendar, register and
ancestral completion are unchanged. The legal cut word and its bin contract
are now constructed for every finite supplied cut list. -/
theorem actual_generated_complete_bin_proxy_tv {O : Type*} [Fintype O]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p phat : HybridProbabilities N)
    (common : Hybrid N → Bool) (r rhat rtail : PositivePairRates E)
    (b : ℝ≥0 → ℝ≥0) (K : ℕ) (hz : b 0 = 0) (ell u beta : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1) (hu1 : 1 ≤ u)
    (hlo : ∀ i : Option E, ell * pairRate r i ≤ pairRate rhat i)
    (hup : ∀ i : Option E, pairRate rhat i ≤ u * pairRate r i)
    (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (htrue : ∀ h, beta * p.gamma h ≤ phat.gamma h)
    (hfalse : ∀ h, beta * (1-p.gamma h) ≤ 1-phat.gamma h)
    (qs : List ℝ)
    (hb : ∀ op ∈ physicalOps N (originalCutWord N C H p common qs),
      Budget (Copy := Copy) N r b K op)
    (readout : TaggedEndpoint (Tag := Fin (qs.length+1)) N sample → O) :
    pmfTV ((naturalCompletedJoint N C sample p r (rankBin qs) (rank_bin_measurable qs)
        (compiledCalendarProgram N C H (originalGamma p) common)).map readout)
      (((allBankNaturalJoint N C sample phat rhat b K (rankBin qs)
        (originalCutWord N C H p common qs)).bind
        (jointTailKernel N rtail (Fin.last qs.length))).map readout) ≤
      1 - (initialMass N beta * ((physicalOps N (originalCutWord N C H p common qs)).map
        (allBankMass (Copy := Copy) N r b K ell u beta)).prod).toReal := by
  exact actual_arbitrary_cut_all_bank_proxy_tv N C sample H p phat common r rhat rtail
    b K hz ell u beta hell hell1 hu1 hlo hup hbeta hbeta1 htrue hfalse
    (rankBin qs) (rank_bin_measurable qs)
    (compiledCalendarProgram N C H (originalGamma p) common) rfl
    (lastCut qs) (originalCutWord N C H p common qs)
    (ranked_word_refines N qs (extendedOriginalOps N C H p common qs) (firstOriginalDate N C))
    (ranked_word_contract N qs (extendedOriginalOps N C H p common qs) (firstOriginalDate N C))
    hb (Fin.last qs.length) (fun x hx => rank_bin_tail qs (lastCut qs) x (le_lastCut qs) hx)
    readout

end DotG6.GeneratedCompleteBinProxy
