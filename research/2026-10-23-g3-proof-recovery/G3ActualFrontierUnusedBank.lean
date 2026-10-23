import ActualUnusedSeedConditioning
import G1InitializedFrontierPrefix

/-!
UNCOMPILED source candidate, existing G3 owner, 2026-10-22.
Derive whole-bank no-read/product law at the LITERAL before-node cut frontier.
The inherited guarded-calendar prefix processes the whole guard boundary;
this candidate instead binds actualFrontierProgram used by the node panel.
No arbitrary initial independence, refreshed bit or averaged target M is input.
-/
namespace G3ActualFrontierUnusedBank
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceForestPulseMeasure UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.G6.PrivateRegisterErasure UnifiedLean.G6.PrivateRegisterBoundary
open UnifiedLean.G6.PrivateRegisterProgram UnifiedLean.G6.PrivateRegisterHistory
open UnifiedLean.G6.PrivateRegisterCalendarPrefix
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open DotG34.ActualUnusedSeedConditioning G1InitializedFrontierPrefix
open G1NaturalCalendarNodes G1ActualEnteringFrontier G1NonrootBigonKernel
open GProgram.G2.SourceFiniteHistory
open scoped Classical NNReal

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

private theorem noRead_append (N : RootedBinary V E X) (P : Finset V)
    (a b : List (ProgramStep N)) (ha : NoPrivateWordRead N P a)
    (hb : NoPrivateWordRead N P b) : NoPrivateWordRead N P (a ++ b) := by
  intro op hop
  rcases List.mem_append.mp hop with hop | hop
  · exact ha op hop
  · exact hb op hop

theorem stopBeforeTail_noRead (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (P : Finset V) (stop a : ℝ) (dates : List ℝ)
    (hordered : dates.Pairwise (· < ·)) (hstop : stop ∈ dates)
    (hprivate : ∀ v ∈ P, stop < C.age v) :
    NoPrivateWordRead N P (stopBeforeTail N C H gamma common stop a dates) := by
  induction dates generalizing a with
  | nil => exact False.elim (List.not_mem_nil hstop)
  | cons b bs ih =>
      have hp := List.pairwise_cons.mp hordered
      by_cases hbstop : b = stop
      · subst stop
        intro op hop
        have he : op = .interval (Real.toNNReal (b-a)) := by
          simpa only [stopBeforeTail, if_pos rfl, List.mem_singleton] using hop
        subst op
        trivial
      · have hstop' : stop ∈ bs :=
          (List.mem_cons.mp hstop).resolve_left (Ne.symm hbstop)
        have hb := boundaryOperations_noPrivateWordRead_of_age_gt N C H gamma common
          P stop b hprivate (hp.1 stop hstop').le
        have ht := ih b hp.2 hstop'
        intro op hop
        have hm : op ∈ .interval (Real.toNNReal (b-a)) ::
            (boundaryOperations N C H gamma common b ++
              stopBeforeTail N C H gamma common stop b bs) := by
          simpa only [stopBeforeTail, if_neg hbstop] using hop
        rcases List.mem_cons.mp hm with hm | hm
        · subst op
          trivial
        · rcases List.mem_append.mp hm with hm | hm
          · exact hb op hm
          · exact ht op hm

theorem beforeBoundaryProgram_noRead (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (P : Finset V) (stop : ℝ)
    (hstop : stop ∈ sortedOriginalDates N C)
    (hprivate : ∀ v ∈ P, stop < C.age v) :
    NoPrivateWordRead N P (beforeBoundaryProgram N C H gamma common stop) := by
  have hne : sortedOriginalDates N C ≠ [] := by
    intro he
    rw [he] at hstop
    exact List.not_mem_nil hstop
  obtain ⟨a,dates,heq⟩ := List.exists_cons_of_ne_nil hne
  by_cases ha : a = stop
  · intro op hop
    have hf : False := by
      simpa only [beforeBoundaryProgram, heq, if_pos ha, List.not_mem_nil] using hop
    exact False.elim hf
  · have hmem : stop ∈ dates := by
      rw [heq] at hstop
      exact (List.mem_cons.mp hstop).resolve_left (Ne.symm ha)
    have hord := original_dates_strict N C
    rw [heq] at hord
    have hp := List.pairwise_cons.mp hord
    have hb := boundaryOperations_noPrivateWordRead_of_age_gt N C H gamma common
      P stop a hprivate (hp.1 stop hmem).le
    have ht := stopBeforeTail_noRead N C H gamma common P stop a dates hp.2 hmem hprivate
    simpa only [beforeBoundaryProgram, heq, if_neg ha] using
      noRead_append N P _ _ hb ht

/-- The actual frontier includes tied exits and stops BEFORE the node batch.
Every private original node is strictly above that physical cut date. -/
theorem actualFrontierProgram_noRead (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (P : Finset V) (v : V)
    (hprivate : ∀ w ∈ P, C.age v < C.age w) :
    NoPrivateWordRead N P (actualFrontierProgram N C H gamma common (C.age v)) := by
  apply noRead_append N P
    (beforeBoundaryProgram N C H gamma common (C.age v)) _
  · exact beforeBoundaryProgram_noRead N C H gamma common P (C.age v)
      (original_date_scheduled N C v) hprivate
  · intro op hop
    obtain ⟨e,_,he⟩ := List.mem_map.mp hop
    subst op
    trivial

/-- Whole original private bank, not a single-bit marginal. Natural initial
product and its exact erased endpoint history are inherited source results. -/
theorem actual_frontier_unused_bank_product (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (v : V)
    (hprivate : ∀ w ∈ P, C.age v < C.age w) :
    let ops := actualFrontierProgram N C H gamma common (C.age v)
    (initializedSourceHistory N r ops (naturalInitialJoint N P sample p)).map
      (fun a => (a.1,(erasePrivateCode N P a.2.1,
        historyProjection (erasePrivateCode N P) a.2.2))) =
      independentPMF (privateSeedPMF N P p)
        (initializedEndpointLaw N r ops (outsideInitialCodeLaw N P sample p)) := by
  dsimp only
  exact actual_private_seed_erased_history_product N P sample p r _
    (actualFrontierProgram_noRead N C H gamma common P v hprivate)

/-- One stochastic continuation of the SAME whole-bank/erased-history law.
Choosing K does not grant a new observation or reconstruct a future source. -/
theorem actual_frontier_unused_bank_continuation (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (v : V)
    (hprivate : ∀ w ∈ P, C.age v < C.age w) {Obs : Type*}
    (K : (PrivateHybrid N P → Bool) ×
      (Code N sample ×
        (Fin (actualFrontierProgram N C H gamma common (C.age v)).length → Code N sample)) →
      PMF Obs) :
    let ops := actualFrontierProgram N C H gamma common (C.age v)
    (initializedSourceHistory N r ops (naturalInitialJoint N P sample p)).bind
      (fun a => K (a.1,(erasePrivateCode N P a.2.1,
        historyProjection (erasePrivateCode N P) a.2.2))) =
      (independentPMF (privateSeedPMF N P p)
        (initializedEndpointLaw N r ops (outsideInitialCodeLaw N P sample p))).bind K := by
  dsimp only
  change (initializedSourceHistory N r _ (naturalInitialJoint N P sample p)).bind
    (K ∘ (fun a => (a.1,(erasePrivateCode N P a.2.1,
      historyProjection (erasePrivateCode N P) a.2.2)))) = _
  rw [← PMF.bind_map, actual_frontier_unused_bank_product N C H gamma common P sample p r v hprivate]

end G3ActualFrontierUnusedBank
