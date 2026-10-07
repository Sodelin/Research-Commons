import CompleteCalendarBinReadout
import ActualTailBinRow
import G2FiniteFibreTransport

/-!
Contributor: Codex, delegated G3/source bridge, 2026-10-07.
UNCHECKED separate principal-law author derivative; no compiler has run here.
The actual correlated calendar pushforward supplies Gamma; actual clock/tail
and raw completion laws derive its joint kernel. Desired law equality is
never an input. Standard finite measure algebra and Mathlib toPMF are prior.
The previously hand-reviewed ten-helper draft remains unchanged.
-/

namespace CloudG3.CompleteCalendarJointLaw

universe u v w x y

open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.CompleteDecoration
open GProgram.G2.FiniteAncestralTrace GProgram.G2.AncestralTraceSourceLaw
open GProgram.G2.FiniteFibreTransport
open UnifiedLean.G6.BinHistory
open CloudG3.CompleteCalendarBinReadout CloudG3.ActualTailBinRow
open scoped Classical NNReal ENNReal BigOperators

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Conversion occurs only after actual joint-map probability was proved. -/
noncomputable def calendarJointPMF (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) : PMF (Code N sample × (Copy → Copy → Tag)) := by
  letI := calendar_joint_probability N r bin hbin ops s offset M
  exact (calendarJointLaw N r bin ops s offset M).toPMF

theorem calendar_joint_pmf_toMeasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) :
    (calendarJointPMF N r bin hbin ops s offset M).toMeasure =
      calendarJointLaw N r bin ops s offset M := by
  unfold calendarJointPMF
  exact Measure.toPMF_toMeasure _

/-- Original completion Code and retained past tags remain in one joint row. -/
noncomputable def jointTailKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag)
    (q : Code N sample × (Copy → Copy → Tag)) :
    PMF (Code N sample × (Copy → Copy → Tag)) :=
  (completionKernel N r q.1).map (fun e => (e, tagUpdate N q.1 e tag q.2))

/-- An actual finite PMF's singleton restriction is its weighted point mass. -/
theorem pmf_singleton_restrict {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (p : PMF A) (a : A) :
    p.toMeasure.restrict {x | x = a} = p a • Measure.dirac a := by
  have hs : {x : A | x = a} = {a} := by ext x; simp
  rw [hs]
  apply Measure.ext
  intro S hS
  rw [Measure.restrict_apply hS, Measure.smul_apply, Measure.dirac_apply' a hS]
  by_cases ha : a ∈ S
  · have hi : S ∩ {a} = {a} := by
      ext x
      constructor
      · exact And.right
      · intro hx
        have he : x = a := by simpa using hx
        subst x
        exact ⟨ha, by simp⟩
    rw [hi, PMF.toMeasure_apply_singleton p a (measurableSet_singleton a)]
    simp [ha]
  · have hi : S ∩ {a} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have he : x = a := by simpa using hx.2
      exact ha (he ▸ hx.1)
    rw [hi]
    simp [ha]

/-- Generic finite measure regrouping, attributed standard algebra. The source
application below derives p from the actual calendar, never assumes its law. -/
theorem finite_joint_kernel_measure {A S B O : Type*}
    [Fintype A] [Fintype S] [Fintype B] [Fintype O]
    [MeasurableSpace A] [MeasurableSpace S] [MeasurableSpace B] [MeasurableSpace O]
    [MeasurableSingletonClass A] [MeasurableSingletonClass S]
    [MeasurableSingletonClass B] [MeasurableSingletonClass O]
    (p : PMF A) (k : A → S) (ν : S → PMF B) (g : A × B → O) :
    (∑ s : S, ((p.toMeasure.restrict {a | k a = s}).prod
      (ν s).toMeasure).map g) =
      (p.bind (fun a => (ν (k a)).map (fun b => g (a, b)))).toMeasure := by
  letI : ∀ s, SFinite (ν s).toMeasure := fun _ => inferInstance
  have hk : Measurable k := measurable_of_countable _
  have hg : Measurable g := measurable_of_countable _
  have hr := finite_endpoint_fibre_product_regroup_map p.toMeasure id id k k
    measurable_id measurable_id hk (fun _ => rfl)
    (fun s => (ν s).toMeasure) p.toMeasure Measure.map_id g hg
  have he (a : A) :
      ((p.toMeasure.restrict {x | x = a}).prod (ν (k a)).toMeasure).map g =
        p a • ((ν (k a)).map (fun b => g (a, b))).toMeasure := by
    rw [pmf_singleton_restrict, Measure.prod_smul_left, Measure.map_smul,
      Measure.dirac_prod, Measure.map_map hg measurable_prodMk_left]
    rw [PMF.toMeasure_map _ _ (measurable_of_countable _)]
    rfl
  calc
    _ = ∑ a : A, ((p.toMeasure.restrict {x | x = a}).prod
        (ν (k a)).toMeasure).map g := by
      simpa only [id_eq, Measure.map_id] using hr.symm
    _ = ∑ a : A, p a • ((ν (k a)).map (fun b => g (a, b))).toMeasure := by
      exact Finset.sum_congr rfl (fun a _ => he a)
    _ = _ := by
      apply Measure.ext
      intro S hS
      rw [Measure.finsetSum_apply,
        PMF.toMeasure_bind_apply _ _ _ hS, tsum_fintype]
      simp only [Measure.smul_apply, smul_eq_mul]

/-- One actual complete-calendar fibre retains its correlated past tags.
The SAME clock tail and raw completion law prove the source-connected row. -/
theorem complete_branch_joint_source_law (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) (ops : List (ProgramStep N)) (s d : Code N sample)
    (hd : AncestralRoot N d) (offset cut : ℝ) (tag : Tag)
    (hoff : cut ≤ offset + (programDuration N ops : ℝ))
    (htail : ∀ a : ℝ, cut < a → bin a = tag) (M : Copy → Copy → ℝ) :
    (((((actualCalendarTraceLaw N r ops s).restrict
        {past | calendarEnd N ops s past = d}).prod
      (completeAncestralTraceLaw N r d)).map (fun z => (d, z))).map
        (fun z => (completeEnd N ops z,
          completeTags N bin ops s offset (fun a b => bin (M a b)) z))) =
      ((((actualCalendarTraceLaw N r ops s).restrict
        {past | calendarEnd N ops s past = d}).map
          (fun past => (calendarEnd N ops s past,
            calendarTags N bin ops s offset (fun a b => bin (M a b)) past))).prod
        (completionKernel N r d).toMeasure).map
          (fun z => (z.2, tagUpdate N z.1.1 z.2 tag z.1.2)) := by
  letI := actual_calendar_trace_probability N r ops s
  letI := complete_ancestral_trace_probability N r d
  let C := (actualCalendarTraceLaw N r ops s).restrict
    {past | calendarEnd N ops s past = d}
  let ν := completeAncestralTraceLaw N r d
  let obs := fun past : Fin ops.length → SegmentRecord N sample =>
    (calendarEnd N ops s past,
      calendarTags N bin ops s offset (fun a b => bin (M a b)) past)
  let g := fun z : (Code N sample × (Copy → Copy → Tag)) × Code N sample =>
    (z.2, tagUpdate N z.1.1 z.2 tag z.1.2)
  let ep := fun z : Bool × ClockTrace N sample (Fintype.card Copy) =>
    traceEndpoint N (Fintype.card Copy) d z.2
  have hobs : Measurable obs := calendar_joint_bin_readout_measurable N bin hbin ops s offset M
  have hg : Measurable g := measurable_of_countable _
  have hep : Measurable ep := raw_tail_endpoint_measurable N d
  have hi : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d, z)) :=
    measurable_const.prodMk measurable_id
  have hout := complete_joint_bin_readout_measurable N bin hbin ops s offset M
  have hm : MeasurableSet {z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) |
      (completeEnd N ops (d, z), completeTags N bin ops s offset
        (fun a b => bin (M a b)) (d, z)) = g (Prod.map obs ep z)} :=
    measurableSet_eq_fun (hout.comp hi) (hg.comp (hobs.prodMap hep))
  have hae : (fun z => (completeEnd N ops (d, z),
      completeTags N bin ops s offset (fun a b => bin (M a b)) (d, z)))
        =ᵐ[C.prod ν] g ∘ Prod.map obs ep := by
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [ae_restrict_mem
      (measurableSet_eq_fun (calendar_end_measurable N ops s) measurable_const)] with past hp
    filter_upwards [actual_complete_tail_bin_fold N r d bin hbin tag cut
      (offset + (programDuration N ops : ℝ)) hoff htail] with z hz
    dsimp only [Function.comp_def, Prod.map, obs, g, ep, completeEnd, completeTags]
    rw [hp]
    exact Prod.ext rfl (hz _)
  rw [Measure.map_map hout hi, Measure.map_congr hae,
    ← Measure.map_map hg (hobs.prodMap hep), ← Measure.map_prod_map C ν hobs hep]
  rw [complete_ancestral_state_source_law N r d hd]

/-- Principal hand equality (A), now given a concrete source proof draft.
Gamma is the ACTUAL normalized correlated calendar PMF, not an input law. -/
theorem actual_complete_joint_source_law (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (hbin : Measurable bin) (ops : List (ProgramStep N)) (s : Code N sample)
    (hroot : ∀ d ∈ (sourceProgram N r ops s).support, AncestralRoot N d)
    (offset cut : ℝ) (tag : Tag)
    (hoff : cut ≤ offset + (programDuration N ops : ℝ))
    (htail : ∀ a : ℝ, cut < a → bin a = tag) (M : Copy → Copy → ℝ) :
    (completeCalendarTraceLaw N r ops s).map
        (fun z => (completeEnd N ops z,
          completeTags N bin ops s offset (fun a b => bin (M a b)) z)) =
      ((calendarJointPMF N r bin hbin ops s offset M).bind
        (jointTailKernel N r tag)).toMeasure := by
  letI := actual_calendar_trace_probability N r ops s
  letI : ∀ d, SFinite (completionKernel N r d).toMeasure := fun _ => inferInstance
  let obs := fun past : Fin ops.length → SegmentRecord N sample =>
    (calendarEnd N ops s past,
      calendarTags N bin ops s offset (fun a b => bin (M a b)) past)
  let g := fun z : (Code N sample × (Copy → Copy → Tag)) × Code N sample =>
    (z.2, tagUpdate N z.1.1 z.2 tag z.1.2)
  let Γ := calendarJointPMF N r bin hbin ops s offset M
  have hobs : Measurable obs := calendar_joint_bin_readout_measurable N bin hbin ops s offset M
  have hg : Measurable g := measurable_of_countable _
  have hΓ : (actualCalendarTraceLaw N r ops s).map obs = Γ.toMeasure := by
    exact (calendar_joint_pmf_toMeasure N r bin hbin ops s offset M).symm
  have hactual : (completeCalendarTraceLaw N r ops s).map
      (fun z => (completeEnd N ops z,
        completeTags N bin ops s offset (fun a b => bin (M a b)) z)) =
      ∑ d : Code N sample,
        ((((actualCalendarTraceLaw N r ops s).restrict
          {past | calendarEnd N ops s past = d}).map obs).prod
            (completionKernel N r d).toMeasure).map g := by
    rw [completeCalendarTraceLaw, Measure.map_finset_sum'
      (complete_joint_bin_readout_measurable N bin hbin ops s offset M).aemeasurable]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : sourceProgram N r ops s d = 0
    · have hz : (actualCalendarTraceLaw N r ops s).restrict
          {past | calendarEnd N ops s past = d} = 0 :=
        Measure.restrict_eq_zero.mpr ((calendar_end_fibre_mass N r ops s d).trans hd)
      simp [hz]
    · exact complete_branch_joint_source_law N r bin hbin ops s d
        (hroot d ((PMF.mem_support_iff _ _).mpr hd)) offset cut tag hoff htail M
  rw [hactual]
  have hr := finite_endpoint_fibre_product_regroup_map
    (actualCalendarTraceLaw N r ops s) (calendarEnd N ops s) obs id Prod.fst
    (calendar_end_measurable N ops s) hobs measurable_fst (fun _ => rfl)
    (fun d => (completionKernel N r d).toMeasure) Γ.toMeasure hΓ g hg
  rw [hr]
  have hk := finite_joint_kernel_measure Γ Prod.fst (completionKernel N r) g
  simpa only [Γ, g, jointTailKernel, id_eq] using hk

#print axioms calendar_joint_pmf_toMeasure
#print axioms pmf_singleton_restrict
#print axioms finite_joint_kernel_measure
#print axioms complete_branch_joint_source_law
#print axioms actual_complete_joint_source_law

end CloudG3.CompleteCalendarJointLaw
