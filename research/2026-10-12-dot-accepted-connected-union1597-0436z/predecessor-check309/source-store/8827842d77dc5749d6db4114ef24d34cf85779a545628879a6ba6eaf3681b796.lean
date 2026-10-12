import G2ActualCalendarTrace
import G2SourceFiniteHistory

/-!
The complete vector of actual calendar segment endpoints has the original
source programme history law. Contributor: dot (OpenAI), 6 October 2026.
This reads the literal records and derives their joint PMF by the original
terminal-fibre products. Internal interval paths are a separate binding.
-/
namespace GProgram.G2.CalendarHistoryBinding
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.SourceFiniteHistory
open scoped Classical ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

local instance joinedMeasurable (N : RootedBinary V E X) (sample : Copy → X)
    (keep : Finset Copy) : MeasurableSpace (JoinedIndex N sample keep) := ⊤

def calendarHistory (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (z : Fin ops.length → SegmentRecord N sample) :
    Fin ops.length → Code N sample := fun i => (z i).2

lemma calendar_history_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) : Measurable (calendarHistory N (sample := sample) ops) :=
  measurable_pi_lambda _ (fun i => (measurable_pi_apply i).snd)

lemma cons_code_history_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) : Measurable (fun z : Code N sample × (Fin n → Code N sample) =>
      (Fin.cons z.1 z.2 : Fin (n+1) → Code N sample)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

lemma fixed_cons_code_history_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (d : Code N sample) :
    Measurable (fun z : Fin n → Code N sample => (Fin.cons d z : Fin (n+1) → Code N sample)) :=
  (cons_code_history_measurable N n).comp (measurable_const.prodMk measurable_id)

lemma calendar_history_cons (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (ops : List (ProgramStep N))
    (z : SegmentRecord N sample × (Fin ops.length → SegmentRecord N sample)) :
    calendarHistory N (op::ops) (recordCons N ops.length z) =
      Fin.cons z.1.2 (calendarHistory N ops z.2) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Each branch retains its unnormalized first-endpoint mass and the entire
future vector, including a branch of zero mass. -/
theorem calendar_branch_history_map (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (ops : List (ProgramStep N))
    (s d : Code N sample) :
    (((((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
      (actualCalendarTraceLaw N r ops d)).map (recordCons N ops.length)).map
        (calendarHistory N (op::ops))) =
      sourceProgramStep N r op s d •
        (((actualCalendarTraceLaw N r ops d).map (calendarHistory N ops)).map (Fin.cons d)) := by
  letI := actual_segment_probability N r op s
  letI := actual_calendar_trace_probability N r ops d
  let F : SegmentRecord N sample × (Fin ops.length → SegmentRecord N sample) →
      Fin (ops.length+1) → Code N sample :=
    fun z => Fin.cons z.1.2 (calendarHistory N ops z.2)
  let G : SegmentRecord N sample × (Fin ops.length → SegmentRecord N sample) →
      Fin (ops.length+1) → Code N sample :=
    fun z => Fin.cons d (calendarHistory N ops z.2)
  have hF : Measurable F := (cons_code_history_measurable N _).comp
    (measurable_fst.snd.prodMk ((calendar_history_measurable N ops).comp measurable_snd))
  have hG : Measurable G := (fixed_cons_code_history_measurable N _ d).comp
    ((calendar_history_measurable N ops).comp measurable_snd)
  have hA : MeasurableSet {z : SegmentRecord N sample | z.2 = d} :=
    measurableSet_eq_fun measurable_snd measurable_const
  have he : F =ᵐ[((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
      (actualCalendarTraceLaw N r ops d)] G := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hF hG)).mpr
    filter_upwards [ae_restrict_mem hA] with z hz
    exact Filter.Eventually.of_forall (fun tail => by dsimp [F,G]; rw [hz])
  rw [Measure.map_map (calendar_history_measurable N _) (record_cons_measurable N _)]
  have hc : calendarHistory N (op::ops) ∘ recordCons N ops.length = F := by
    funext z
    exact calendar_history_cons N op ops z
  rw [hc,Measure.map_congr he]
  change ((((actualSegmentLaw N r op s).restrict {z | z.2 = d}).prod
    (actualCalendarTraceLaw N r ops d)).map
      (((fun z : Fin ops.length → Code N sample =>
        (Fin.cons d z : Fin (ops.length+1) → Code N sample)) ∘ calendarHistory N ops) ∘ Prod.snd)) = _
  rw [← Measure.map_map ((fixed_cons_code_history_measurable N _ d).comp
      (calendar_history_measurable N ops)) measurable_snd,
    Measure.map_snd_prod,Measure.map_smul,Measure.restrict_apply MeasurableSet.univ,
    univ_inter,segment_end_fibre_mass,
    ← Measure.map_map (fixed_cons_code_history_measurable N _ d) (calendar_history_measurable N ops)]

/-- The endpoint history is read directly from the actual successive segment
records; it is not defined by a separately sampled history PMF. -/
theorem actual_calendar_history_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    (actualCalendarTraceLaw N r ops s).map (calendarHistory N ops) =
      (sourceHistoryLaw N r ops s).toMeasure := by
  induction ops generalizing s with
  | nil =>
      rw [actualCalendarTraceLaw,Measure.map_dirac' (calendar_history_measurable N [])]
      simp only [sourceHistoryLaw,historyLaw,PMF.toMeasure_pure]
      congr 1
      funext i
      exact Fin.elim0 i
  | cons op ops ih =>
      simp only [List.length_cons] at *
      rw [actualCalendarTraceLaw,
        Measure.map_finset_sum' (calendar_history_measurable N (op::ops)).aemeasurable]
      simp_rw [calendar_branch_history_map,ih,
        PMF.toMeasure_map _ _ (fixed_cons_code_history_measurable N ops.length _)]
      apply Measure.ext
      intro A hA
      rw [Measure.finsetSum_apply Finset.univ _ A,sourceHistoryLaw,historyLaw,
        PMF.toMeasure_bind_apply _ _ A hA,tsum_fintype]
      simp only [Measure.smul_apply,smul_eq_mul,sourceHistoryLaw]
      rfl

lemma projected_calendar_history_measurable (N : RootedBinary V E X) {sample : Copy → X}
    {Q : Type*} [MeasurableSpace Q] (f : Code N sample → Q)
    (ops : List (ProgramStep N)) : Measurable (historyProjection f ∘ calendarHistory N ops) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_of_countable f).comp ((measurable_pi_apply i).snd)

/-- Full/small equality of the entire actual calendar endpoint vector. This
does not yet claim a law for the interior interval paths. -/
theorem actual_cross_carrier_calendar_history (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (ops : List (ProgramStep N)) (s : Code N sample)
    (d : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state d) Finset.univ)) :
    (actualCalendarTraceLaw N r ops s).map
      (historyProjection (fun z => joinedProjection N keep (.inl z)) ∘ calendarHistory N ops) =
    (actualCalendarTraceLaw N r ops d).map
      (historyProjection (fun z => joinedProjection N keep (.inr z)) ∘ calendarHistory N ops) := by
  have hf : Measurable (historyProjection (n := ops.length)
      (fun z : Code N sample => joinedProjection N keep (.inl z))) :=
    measurable_pi_lambda _ (fun i => (measurable_of_countable
      (fun z : Code N sample => joinedProjection N keep (.inl z))).comp (measurable_pi_apply i))
  have hg : Measurable (historyProjection (n := ops.length)
      (fun z : Code N (selectedSample sample keep) => joinedProjection N keep (.inr z))) :=
    measurable_pi_lambda _ (fun i => (measurable_of_countable
      (fun z : Code N (selectedSample sample keep) => joinedProjection N keep (.inr z))).comp (measurable_pi_apply i))
  rw [← Measure.map_map hf (calendar_history_measurable N ops),
    ← Measure.map_map hg (calendar_history_measurable N ops),
    actual_calendar_history_law,actual_calendar_history_law,
    PMF.toMeasure_map _ _ hf,PMF.toMeasure_map _ _ hg,
    actual_cross_carrier_source_history N r keep ops s d hs]

#print axioms calendar_history_measurable
#print axioms cons_code_history_measurable
#print axioms fixed_cons_code_history_measurable
#print axioms calendar_history_cons
#print axioms calendar_branch_history_map
#print axioms actual_calendar_history_law
#print axioms projected_calendar_history_measurable
#print axioms actual_cross_carrier_calendar_history
end GProgram.G2.CalendarHistoryBinding
