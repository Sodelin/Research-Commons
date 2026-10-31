import ResearchCommons.MSCI.JC69SamplingReduction

/-! WORKING UNCOMPILED. Closed admitted active observation carriers through
an actual interval and WHOLE next-date boundary. Dot (OpenAI),31 October2026.
No representative reachability, bank averaging or global M/D/window claim. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69ActiveStage
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.NativeParentRouting
open GProgram.G2.ActualCalendarTrace GProgram.G2.CalendarDecoration
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69CurrentPartition
open ResearchCommons.MSCI.JC69EndpointWeight ResearchCommons.MSCI.JC69WeightedCalendar
open ResearchCommons.MSCI.JC69GuardedCalendarQuotient ResearchCommons.MSCI.JC69ActivatedPrefix
open ResearchCommons.MSCI.JC69SupportedStateBound ResearchCommons.MSCI.JC69SamplingReduction
open scoped Classical BigOperators ENNReal NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def ActiveCode (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    (a : ℝ) (s : Code N sample) : Prop :=
  ∀ x : Copy, copyLocation (state s) x ∈ activeLocations N C a

lemma active_after_nodes (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    (a : ℝ) (s : Code N sample) (hs : ActiveCode N C a s) : AfterNodes N C a (state s) := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro x
    obtain ⟨e,he,ha⟩ := (mem_activeLocations N C a _).mp (hs x)
    rw [he]
    exact ⟨ha.1,ha.2.le⟩
  · intro x e he
    obtain ⟨f,hf,ha⟩ := (mem_activeLocations N C a _).mp (hs x)
    have hef := Location.edge.inj (he.symm.trans hf)
    simpa only [hef] using ha.2
  · intro x v hv
    obtain ⟨e,he,_⟩ := (mem_activeLocations N C a _).mp (hs x)
    have hne : Location.node v = Location.edge e := hv.symm.trans he
    cases hne

lemma active_node_upper (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    (a : ℝ) (s : Code N sample) (hs : ActiveCode N C a s) : NodeUpper N C a s := by
  intro x v hv
  obtain ⟨e,he,_⟩ := (mem_activeLocations N C a _).mp (hs x)
  have hne : Location.node v = Location.edge e := hv.symm.trans he
  cases hne

def stageProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a b : ℝ) : List (ProgramStep N) :=
  .interval (Real.toNNReal (b-a)) :: boundaryOperations N C H gamma common b

/-- At the final original date only the actual root population is counted.
There is no extra root color appended to each P-sized active-edge carrier. -/
def stageLocations (N : RootedBinary V E X) (C : Calendar N.graph) (b : ℝ) :
    Finset (Location V E) :=
  if b < C.age N.root then activeLocations N C b else {.rootPopulation N.root}

lemma after_nodes_upper_locations (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (b : ℝ) (hb : b ≤ C.age N.root) (s : Code N sample)
    (hs : AfterNodes N C b (state s)) (hu : NodeUpper N C b s) :
    ∀ x : Copy, copyLocation (state s) x ∈ stageLocations N C b := by
  intro x
  have hn (v : V) : copyLocation (state s) x ≠ .node v :=
    fun h => (not_lt_of_ge (hu x v h)) (hs.2 x v h)
  have hr := hs.1.1 x
  by_cases hbefore : b < C.age N.root
  · rw [stageLocations,if_pos hbefore]
    apply (mem_activeLocations N C b _).mpr
    cases he : copyLocation (state s) x with
    | node v => exact False.elim (hn v he)
    | edge e =>
        rw [he] at hr
        exact ⟨e,rfl,hr.1,hs.1.2 x e he⟩
    | rootPopulation v =>
        rw [he] at hr
        exact False.elim ((not_le_of_gt hbefore) hr.2)
  · have heq : b = C.age N.root := le_antisymm hb (le_of_not_gt hbefore)
    rw [stageLocations,if_neg hbefore,Finset.mem_singleton]
    cases he : copyLocation (state s) x with
    | node v => exact False.elim (hn v he)
    | edge e =>
        have hlt := hs.1.2 x e he
        have hle := actual_root_latest N C (N.graph.source e)
        rw [← heq] at hle
        exact False.elim ((not_lt_of_ge hle) hlt)
    | rootPopulation v =>
        rw [he] at hr
        exact congrArg Location.rootPopulation hr.1

/-- Actual source closure for ANY admitted active representative, independent
of reachability/bank/counts. The gap is the original next-date condition. -/
theorem actual_stage_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a b : ℝ)
    (hab : a < b) (hb : b ≤ C.age N.root)
    (hgap : ∀ v : V, a < C.age v → b ≤ C.age v)
    (s : Code N sample) (hs : ActiveCode N C a s) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (stageProgram N C H gamma common a b) s).support) :
    ∀ x : Copy, copyLocation (state d) x ∈ stageLocations N C b := by
  have hafter := active_after_nodes N C a s hs
  have hupper := active_node_upper N C a s hs
  have hepoch := after_nodes_to_epoch N C hafter hgap
  obtain ⟨m,hm,hmd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hme := actual_source_time_epoch_support N C r (Real.toNNReal (b-a)) s hepoch hm
  have hmu := time_node_upper N C r (Real.toNNReal (b-a)) s m a hupper hm
  have hdb := actual_original_boundary_batch_support N C H gamma common r b m
    (epoch_to_next_ready N C hme hab.le) hmd
  have hdu := actual_boundary_node_upper N C H gamma common r b b le_rfl m
    (node_upper_mono N C hmu hab.le) hmd
  exact after_nodes_upper_locations N C b hb d hdb hdu

/-- A genuine remaining original agenda gives the gap and root upper bound;
these are derived source conditions, not an assumed quotient transition. -/
theorem actual_next_date_stage_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a b : ℝ) (dates : List ℝ)
    (haroot : a < C.age N.root) (hab : a < b)
    (hfuture : FutureComplete N C a (b::dates)) (ho : (b::dates).Pairwise (· < ·))
    (s : Code N sample) (hs : ActiveCode N C a s) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (stageProgram N C H gamma common a b) s).support) :
    ∀ x : Copy, copyLocation (state d) x ∈ stageLocations N C b := by
  have hgap : ∀ v : V, a < C.age v → b ≤ C.age v := by
    intro v hv
    rcases List.mem_cons.mp (hfuture v hv) with he | he
    · exact he.ge
    · exact (List.pairwise_cons.mp ho).1 _ he |>.le
  exact actual_stage_support N C H gamma common r a b hab (hgap N.root haroot) hgap s hs hd

theorem stage_supported_card (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (b : ℝ) (P : ℕ) (hroot : 1 ≤ P)
    (hP : (Finset.univ.filter (C.Active b)).card ≤ P) :
    Fintype.card (SupportedObservation N sample (stageLocations N C b)) ≤
      BellCount (Fintype.card Copy) * P ^ Fintype.card Copy := by
  apply supported_observation_card N sample _ P
  by_cases hb : b < C.age N.root
  · simpa only [stageLocations,if_pos hb,active_locations_card] using hP
  · simpa only [stageLocations,if_neg hb,Finset.card_singleton] using hroot

/-- Original whole-program weighted observation mass; no normalization. -/
def programObservationWeight (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (ops : List (ProgramStep N)) (s : Code N sample) (target : BlockPopulationObservation Copy V E) : ℝ≥0∞ :=
  ∫⁻ past, calendarWeight N L q ops s past *
    (if observeCode N (calendarEnd N ops s past) = target then 1 else 0)
    ∂actualCalendarTraceLaw N r ops s

lemma program_indicator_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (L : ℕ) (q : Fin L → Copy → Base) (ops : List (ProgramStep N)) (s : Code N sample)
    (target : BlockPopulationObservation Copy V E) :
    Measurable (fun past => calendarWeight N L q ops s past *
      (if observeCode N (calendarEnd N ops s past) = target then (1:ℝ≥0∞) else 0)) :=
  (calendar_weight_measurable N L q ops s).mul
    ((measurable_of_countable (fun d : Code N sample =>
      if observeCode N d = target then (1:ℝ≥0∞) else 0)).comp (calendar_end_measurable N ops s))

lemma program_supported_readout (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (ops : List (ProgramStep N)) (s : Code N sample) (A : Finset (Location V E))
    (hA : ∀ d ∈ (sourceProgram N r ops s).support, ∀ x : Copy, copyLocation (state d) x ∈ A)
    (F : BlockPopulationObservation Copy V E → ℝ≥0∞) :
    (∫⁻ past, calendarWeight N L q ops s past * F (observeCode N (calendarEnd N ops s past))
      ∂actualCalendarTraceLaw N r ops s) =
      ∑ o : SupportedObservation N sample A, programObservationWeight N r L q ops s o.val * F o.val := by
  let p := sourceProgram N r ops s
  have hs : ∀ᵐ d ∂p.toMeasure, d ∈ p.support := by
    rw [← p.restrict_toMeasure_support]
    exact ae_restrict_mem p.support_countable.measurableSet
  have ha : ∀ᵐ d ∂p.toMeasure, ∀ x : Copy, copyLocation (state d) x ∈ A := by
    filter_upwards [hs] with d hd
    exact hA d hd
  change ∀ᵐ d ∂(sourceProgram N r ops s).toMeasure, _ at ha
  rw [← actual_calendar_endpoint_law N r ops s] at ha
  have hend := ae_of_ae_map (calendar_end_measurable N ops s).aemeasurable ha
  calc
    _ = ∫⁻ past, ∑ o : SupportedObservation N sample A,
        F o.val * (calendarWeight N L q ops s past *
          (if observeCode N (calendarEnd N ops s past) = o.val then 1 else 0))
        ∂actualCalendarTraceLaw N r ops s := by
      apply lintegral_congr_ae
      filter_upwards [hend] with past hp
      let d := calendarEnd N ops s past
      let o0 : SupportedObservation N sample A := ⟨observeCode N d,⟨d,rfl⟩,hp⟩
      rw [Finset.sum_eq_single o0]
      · simp [o0,d,mul_comm]
      · intro o _ hne
        have hno : observeCode N d ≠ o.val := by
          intro he
          exact hne (Subtype.ext he.symm)
        exact (congrArg (fun z : ℝ≥0∞ => F o.val * (calendarWeight N L q ops s past * z))
          (if_neg hno)).trans
          ((congrArg (fun z : ℝ≥0∞ => F o.val * z) (mul_zero _)).trans (mul_zero _))
      · simp
    _ = ∑ o : SupportedObservation N sample A,
        ∫⁻ past, F o.val * (calendarWeight N L q ops s past *
          (if observeCode N (calendarEnd N ops s past) = o.val then 1 else 0))
          ∂actualCalendarTraceLaw N r ops s := by
      rw [lintegral_finset_sum]
      intro o _
      exact (program_indicator_measurable N L q ops s o.val).const_mul _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro o _
      rw [lintegral_const_mul _ (program_indicator_measurable N L q ops s o.val)]
      exact mul_comm _ _

/-- Derived actual finite weighted transfer on the closed next-stage carrier;
internal boundary states are inside one coefficient, not extra S choices. -/
theorem actual_stage_finite_readout (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (a b : ℝ) (hab : a < b) (hb : b ≤ C.age N.root)
    (hgap : ∀ v : V, a < C.age v → b ≤ C.age v)
    (s : Code N sample) (hs : ActiveCode N C a s)
    (F : BlockPopulationObservation Copy V E → ℝ≥0∞) :
    let ops := stageProgram N C H gamma common a b
    (∫⁻ past, calendarWeight N L q ops s past * F (observeCode N (calendarEnd N ops s past))
      ∂actualCalendarTraceLaw N r ops s) =
      ∑ o : SupportedObservation N sample (stageLocations N C b),
        programObservationWeight N r L q ops s o.val * F o.val := by
  exact program_supported_readout N r L q _ s (stageLocations N C b)
    (fun d hd => actual_stage_support N C H gamma common r a b hab hb hgap s hs hd) F

/-- The future readout is DERIVED from the accepted same-bank quotient.
No desired finite-state likelihood/continuation is supplied as a premise. -/
theorem actual_stage_guarded_transfer [Nonempty Copy] (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (a b : ℝ) (hab : a < b) (hb : b ≤ C.age N.root)
    (hgap : ∀ v : V, a < C.age v → b ≤ C.age v)
    (s : Code N sample) (hs : ActiveCode N C a s) (post : List (ProgramStep N)) :
    ∃ F : BlockPopulationObservation Copy V E → ℝ≥0∞,
      (∀ d : Code N sample, (state d).register = (state s).register →
        calendarValue N r L q (guardedRoot N r L q) post d = F (observeCode N d)) ∧
      calendarValue N r L q (guardedRoot N r L q) (stageProgram N C H gamma common a b ++ post) s =
        ∑ o : SupportedObservation N sample (stageLocations N C b),
          programObservationWeight N r L q (stageProgram N C H gamma common a b) s o.val * F o.val := by
  let ops := stageProgram N C H gamma common a b
  let future : Code N sample → ℝ≥0∞ := calendarValue N r L q (guardedRoot N r L q) post
  obtain ⟨F,hF⟩ := exists_bank_readout N future
    (fun u v ho hr => actual_guarded_calendar_quotient N r L q hbal post u v ho hr) ((state s).register)
  refine ⟨F,hF,?_⟩
  rw [calendar_value_append,← actual_calendar_weighted_recursion]
  let p := sourceProgram N r ops s
  have hsupp : ∀ᵐ d ∂p.toMeasure, d ∈ p.support := by
    rw [← p.restrict_toMeasure_support]
    exact ae_restrict_mem p.support_countable.measurableSet
  have hreg : ∀ᵐ d ∂p.toMeasure, (state d).register = (state s).register := by
    filter_upwards [hsupp] with d hd
    exact program_support_register N r ops s hd
  change ∀ᵐ d ∂(sourceProgram N r ops s).toMeasure, _ at hreg
  rw [← actual_calendar_endpoint_law N r ops s] at hreg
  have hre := ae_of_ae_map (calendar_end_measurable N ops s).aemeasurable hreg
  calc
    _ = ∫⁻ past, calendarWeight N L q ops s past * F (observeCode N (calendarEnd N ops s past))
        ∂actualCalendarTraceLaw N r ops s := by
      apply lintegral_congr_ae
      filter_upwards [hre] with past hp
      exact congrArg (fun z : ℝ≥0∞ => calendarWeight N L q ops s past * z) (hF _ hp)
    _ = _ := actual_stage_finite_readout N C H gamma common r L q a b hab hb hgap s hs F

#print axioms actual_stage_support
#print axioms actual_next_date_stage_support
#print axioms stage_supported_card
#print axioms actual_stage_finite_readout
#print axioms actual_stage_guarded_transfer
end ResearchCommons.MSCI.JC69ActiveStage
