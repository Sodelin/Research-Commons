import ResearchCommons.MSCI.JC69SourceRootQuotient
import ResearchCommons.MSCI.JC69EndpointWeight

/-! Actual endpoint-weight quotient composition. UNCOMPILED, 31 October 2026.
Contributor: dot (OpenAI). Uses exact repaired root adapter32a09d45 and accepted
endpoint renewal f40648e8. No assumed sufficient statistic, changed source,
conditional final likelihood expansion, boundary admission or larger bound. -/
noncomputable section
namespace ResearchCommons.MSCI.JC69EndpointQuotient
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.MarkedTraceRenewal
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Occupation
open ResearchCommons.MSCI.JC69TraceOccupation ResearchCommons.MSCI.JC69WeightedTrace
open ResearchCommons.MSCI.JC69CurrentPartition ResearchCommons.MSCI.JC69EndpointWeight
open ResearchCommons.MSCI.JC69SourceRootQuotient
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

lemma actualChoiceEquiv_first_block (N : RootedBinary V E X) {sample : Copy → X}
    (s t : Code N sample) (hB : currentBlocks (state s) = currentBlocks (state t))
    (hLoc : ∀ x, copyLocation (state s) x = copyLocation (state t) x) (p : Choice N s) :
    ((state t).genealogy (actualChoiceEquiv N s t hB hLoc p).2.val.1).leaves =
      ((state s).genealogy p.2.val.1).leaves := by
  have ha := (Finset.mem_filter.mp (Finset.mem_offDiag.mp p.2.property).1).1
  change ((state t).genealogy (matchingRoot (state s) (state t) hB
    ⟨p.2.val.1,ha⟩).val).leaves = _
  exact matchingRoot_block (state s) (state t) hB ⟨p.2.val.1,ha⟩

lemma actualChoiceEquiv_second_block (N : RootedBinary V E X) {sample : Copy → X}
    (s t : Code N sample) (hB : currentBlocks (state s) = currentBlocks (state t))
    (hLoc : ∀ x, copyLocation (state s) x = copyLocation (state t) x) (p : Choice N s) :
    ((state t).genealogy (actualChoiceEquiv N s t hB hLoc p).2.val.2).leaves =
      ((state s).genealogy p.2.val.2).leaves := by
  have hb := (Finset.mem_filter.mp (Finset.mem_offDiag.mp p.2.property).2.1).1
  change ((state t).genealogy (matchingRoot (state s) (state t) hB
    ⟨p.2.val.2,hb⟩).val).leaves = _
  exact matchingRoot_block (state s) (state t) hB ⟨p.2.val.2,hb⟩

/-- Matching ACTUAL choices reach the same descendant-block observation
AFTER the original legal merge and the original finite snapshot re-encoding. -/
theorem actual_matched_destinations_blocks (N : RootedBinary V E X) {sample : Copy → X}
    (s t : Code N sample) (hB : currentBlocks (state s) = currentBlocks (state t))
    (hLoc : ∀ x, copyLocation (state s) x = copyLocation (state t) x) (p : Choice N s) :
    currentBlocks (state (stepDestination N t (some (actualChoiceEquiv N s t hB hLoc p)))) =
      currentBlocks (state (stepDestination N s (some p))) := by
  rw [actual_coded_merge_blocks,actual_coded_merge_blocks]
  rw [actual_merge_blocks (state t) t.property.forest,
    actual_merge_blocks (state s) s.property.forest]
  all_goals try exact (population_pair_is_source_legal _ _ (originalPlace_not_node N _) (actualChoiceEquiv N s t hB hLoc p).2.property)
  all_goals try exact (population_pair_is_source_legal _ _ (originalPlace_not_node N p.1) p.2.property)
  rw [actualChoiceEquiv_first_block,actualChoiceEquiv_second_block,← hB]

/-- Matching coded destinations also preserve the per-original-copy
population part of the same quotient relation; no register is equated. -/
theorem actual_matched_destinations_locations (N : RootedBinary V E X) {sample : Copy → X}
    (s t : Code N sample) (hB : currentBlocks (state s) = currentBlocks (state t))
    (hLoc : ∀ x, copyLocation (state s) x = copyLocation (state t) x)
    (p : Choice N s) (x : Copy) :
    copyLocation (state (stepDestination N t (some (actualChoiceEquiv N s t hB hLoc p)))) x =
      copyLocation (state (stepDestination N s (some p))) x := by
  rw [actual_coded_merge_copyLocation,actual_coded_merge_copyLocation]
  exact (hLoc x).symm

/-- Matched original choices preserve exactly the observation used by the
accepted endpoint-resolved weight, after actual source coding. -/
theorem actual_matched_destinations_observation (N : RootedBinary V E X)
    {sample : Copy → X} (s t : Code N sample)
    (hB : currentBlocks (state s) = currentBlocks (state t))
    (hLoc : ∀ x, copyLocation (state s) x = copyLocation (state t) x) (p : Choice N s) :
    observeCode N (stepDestination N s (some p)) =
      observeCode N (stepDestination N t (some (actualChoiceEquiv N s t hB hLoc p))) := by
  apply Prod.ext
  · exact (actual_matched_destinations_blocks N s t hB hLoc p).symm
  · funext x
    exact (actual_matched_destinations_locations N s t hB hLoc p x).symm

/-- The actual shared-locus killing coefficient, not a new fitted rate,
factors through the complete current descendant blocks. -/
theorem actual_locusKill_eq (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (s t : Code N sample)
    (hB : currentBlocks (state s) = currentBlocks (state t)) :
    locusKill N L q t = locusKill N L q s := by
  have hc (j : Fin L) : codeCharge N (q j) t = codeCharge N (q j) s := by
    have hn : activeChargeCount (state t) (fun x (_ : Unit) => q j x) =
        activeChargeCount (state s) (fun x (_ : Unit) => q j x) := by
      rw [active_charge_factors_through_partition (state t) t.property.forest,
        active_charge_factors_through_partition (state s) s.property.forest]
      change (∑ B ∈ currentBlocks (state t), ∑ k : Unit, nonzeroCharge (∑ x ∈ B, q j x)) =
        (∑ B ∈ currentBlocks (state s), ∑ k : Unit, nonzeroCharge (∑ x ∈ B, q j x))
      rw [hB]
    change (activeChargeCount (state t) (fun x (_ : Unit) => q j x) : ℝ) =
      (activeChargeCount (state s) (fun x (_ : Unit) => q j x) : ℝ)
    exact_mod_cast hn
  unfold locusKill
  congr 1
  exact Finset.sum_congr rfl (fun j _ => hc j)

/-- At fuel zero the original success flag is clock survival, not a
probability-one success assertion. Its exact no-event mass is retained. -/
theorem actual_resolved_weight_zero (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (s : Code N sample) (T : ℝ≥0) (target : BlockPopulationObservation Copy V E) :
    actualResolvedWeight N r L q 0 s T target =
      ENNReal.ofReal (Real.exp (-(totalRate N r s*(T : ℝ)))) *
        (ENNReal.ofReal (Real.exp (-(locusKill N L q s*(T : ℝ)))) *
          (if observeCode N s = target then 1 else 0)) := by
  let μ := actualMarkedTraceLaw N r 0 s (T : ℝ)
  letI : IsProbabilityMeasure μ := actual_marked_trace_probability N r 0 s T
  let A : Set (Bool × ClockTrace N sample 0) := {z | NoMarkedEvent N 0 z}
  let c : ENNReal := ENNReal.ofReal (Real.exp (-(locusKill N L q s*(T : ℝ)))) *
    (if observeCode N s = target then 1 else 0)
  have hA : MeasurableSet A := no_marked_event_measurable N 0
  have hf : (fun z => resolvedTraceWeight N L q 0 s (T : ℝ) target z) =
      A.indicator (fun _ => c) := by
    funext z
    rcases z with ⟨flag,z⟩
    have hz : z = emptyTrace N 0 s := by funext i; exact Fin.elim0 i
    rw [hz]
    cases flag with
    | false => simp [resolvedTraceWeight,locusTraceWeight,A,NoMarkedEvent]
    | true =>
        rw [resolved_weight_empty]
        simp [A,NoMarkedEvent,c]
  have hm : μ A = ENNReal.ofReal (Real.exp (-(totalRate N r s*(T : ℝ)))) := by
    rw [← actual_marked_no_event_mass N r 0 s T]
    exact (ENNReal.ofReal_toReal (measure_ne_top μ A)).symm
  change (∫⁻ z, resolvedTraceWeight N L q 0 s (T : ℝ) target z ∂μ) = _
  rw [hf,lintegral_indicator_const hA c,hm]
  exact mul_comm _ _

/-- Finite-fuel equality of ORIGINAL endpoint-resolved weighted laws.
All sites share one trace; the same final target remains attached to each
future branch. No full-mass conditioning or boundary factorization occurs. -/
theorem actual_resolved_weight_quotient (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base) (n : ℕ)
    (s t : Code N sample) (T : ℝ≥0) (target : BlockPopulationObservation Copy V E)
    (hobs : observeCode N s = observeCode N t) :
    actualResolvedWeight N r L q n s T target = actualResolvedWeight N r L q n t T target := by
  induction n generalizing s t T with
  | zero =>
      have hB : currentBlocks (state s) = currentBlocks (state t) := congrArg Prod.fst hobs
      have hLoc : ∀ x, copyLocation (state s) x = copyLocation (state t) x :=
        fun x => congrFun (congrArg Prod.snd hobs) x
      rw [actual_resolved_weight_zero,actual_resolved_weight_zero,
        actual_totalRate_eq N r s t hB hLoc,actual_locusKill_eq N L q s t hB,hobs]
  | succ n ih =>
      have hB : currentBlocks (state s) = currentBlocks (state t) := congrArg Prod.fst hobs
      have hLoc : ∀ x, copyLocation (state s) x = copyLocation (state t) x :=
        fun x => congrFun (congrArg Prod.snd hobs) x
      let e := actualChoiceEquiv N s t hB hLoc
      rw [actual_resolved_weight_renewal,actual_resolved_weight_renewal]
      have hC := actual_totalRate_eq N r s t hB hLoc
      have hK := actual_locusKill_eq N L q s t hB
      have hzero :
          ENNReal.ofReal (Real.exp (-(totalRate N r s*(T : ℝ)))) *
            (ENNReal.ofReal (Real.exp (-(locusKill N L q s*(T : ℝ)))) *
              (if observeCode N s = target then 1 else 0)) =
          ENNReal.ofReal (Real.exp (-(totalRate N r t*(T : ℝ)))) *
            (ENNReal.ofReal (Real.exp (-(locusKill N L q t*(T : ℝ)))) *
              (if observeCode N t = target then 1 else 0)) := by rw [hC,hK,hobs]
      rw [hzero]
      congr 1
      rw [← e.sum_comp (fun p : Choice N t =>
        ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (-(locusKill N L q t*u))) *
          actualResolvedWeight N r L q n (stepDestination N t (some p)) ((T : ℝ)-u) target
          ∂((ENNReal.ofReal (choiceRate N r t p/totalRate N r t) •
            expMeasure (totalRate N r t)).restrict (Iic (T : ℝ))))]
      apply Finset.sum_congr rfl
      intro p _
      have hR : choiceRate N r t (e p) = choiceRate N r s p :=
        actualChoiceEquiv_rate N r s t hB hLoc p
      rw [hR,hC,hK]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
      have htime : 0 ≤ (T : ℝ)-u := sub_nonneg.mpr hu
      have hd := actual_matched_destinations_observation N s t hB hLoc p
      have hfuture := ih (stepDestination N s (some p))
        (stepDestination N t (some (e p))) ⟨(T : ℝ)-u,htime⟩ hd
      exact congrArg (fun w => ENNReal.ofReal (Real.exp (-(locusKill N L q s*u))) * w) hfuture

#print axioms actual_matched_destinations_observation
#print axioms actual_locusKill_eq
#print axioms actual_resolved_weight_zero
#print axioms actual_resolved_weight_quotient
end ResearchCommons.MSCI.JC69EndpointQuotient
