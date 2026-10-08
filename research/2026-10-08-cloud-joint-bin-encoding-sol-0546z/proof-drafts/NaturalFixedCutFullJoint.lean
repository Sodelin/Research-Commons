import FullJointCoordinateEncoding
import NaturalGuardOneBinForest

/-!
Cloud Sol /root/source_backend_review_sol, 8 October 2026.
EXPERIMENTAL SOURCE/HAND; every new body compiler UNCHECKED/outside179.
Actual natural correlated entering law, actual retained-clock fixed-cut law,
unchanged original count kernels, and SAME all-Location forest/register reader.
No desired backend equality, serializer, sampled entering law or new register.
-/
namespace CloudG6.NaturalFixedCutFullJoint
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.G6.BinHistory
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CalendarDecoration GProgram.G2.ChronologicalPathReadout
open CloudG3.CompleteCalendarBinReadout CloudG3.CompleteCalendarJointLaw
open CloudG3.ActualCalendarCutContext CloudG3.ActualFiniteCutJointLaw
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualObservationCutRefinement
open CloudG6.TaggedSourceIteration CloudG6.NaturalCalendarPastAdmission
open CloudG6.NaturalGuardOneBinForest CloudG6.FullJointCoordinateEncoding
open scoped Classical NNReal
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

variable {V E Copy X Tag Label Bin Pop RegisterID : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]

noncomputable def encodedForestReadout (N : RootedBinary V E X) {sample : Copy → X}
    (place : Location V E ≃ Pop) (vertex : V ≃ RegisterID)
    (leaf : Copy ≃ Label) (tag : Tag ≃ Bin) (q : TaggedCode N sample Tag) :
    FullRecord Pop RegisterID Label Bin :=
  encodeFullRecord place vertex leaf tag (forestReadout N q)

/-- A derived source refinement law; CutRefines carries only deterministic
nonnegative subdivisions and never changes a boundary or register draw. -/
theorem actual_natural_past_refinement (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) {ops refined : List (ProgramStep N)}
    (href : CutRefines N ops refined) :
    naturalPastJoint N C sample p r bin hbin ops =
      naturalPastJoint N C sample p r bin hbin refined := by
  have hrow (steps : List (ProgramStep N)) (s : Code N sample) :
      calendarJointPMF N r bin hbin steps s (firstOriginalDate N C)
        (leafAgeMatrix N C sample) =
      calendarJoint N r bin hbin steps s (firstOriginalDate N C)
        (fun a b => bin (leafAgeMatrix N C sample a b)) := by
    apply PMF.toMeasure_injective
    rw [calendar_joint_pmf_toMeasure, calendar_joint_toMeasure]
    rfl
  unfold naturalPastJoint
  simp_rw [hrow]
  apply congrArg (PMF.bind (originalRegisterPMF N p))
  funext register
  exact cut_refines_actual_calendar_joint N r bin hbin href
    (initialCode N sample register) (firstOriginalDate N C)
    (fun a b => bin (leafAgeMatrix N C sample a b))

/-- Full coordinate encoding of the actual naturally initialized endpoint
history. One joint pushforward, no product of coordinate/panel marginals. -/
theorem actual_natural_refined_encoded_record (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word))
    (hword : wordBinContract N bin word (firstOriginalDate N C))
    (place : Location V E ≃ Pop) (vertex : V ≃ RegisterID)
    (leaf : Copy ≃ Label) (tag : Tag ≃ Bin) :
    (naturalPastJoint N C sample p r bin hbin ops).map
        (encodedForestReadout N place vertex leaf tag) =
      (initializedEndpointLaw N r (physicalOps N word)
        (naturalInitialCodeLaw N sample p)).map (fun a =>
          encodedForestReadout N place vertex leaf tag
            (endpointHistoryReadout N word a.1
              (fun x y => bin (leafAgeMatrix N C sample x y)) a.2)) := by
  rw [actual_natural_past_endpoint_history N C sample p r bin hbin ops word href hword,
    PMF.map_comp]
  rfl

/-- SAME actual countPMF and sourceIteration, retaining the joint old matrix. -/
noncomputable def oneBinJointCount (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) (h : ℝ≥0) (q : TaggedCode N sample Tag) :
    PMF (TaggedCode N sample Tag) :=
  (countPMF (globalClockRate (Copy := Copy) r * h)).bind (fun k =>
    (sourceIteration N r k q.1).map (fun d => (d, tagUpdate N q.1 d tag q.2)))

theorem source_time_joint_count (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) (h : ℝ≥0) (q : TaggedCode N sample Tag) :
    (sourceTimeKernel N r h q.1).map (fun d => (d, tagUpdate N q.1 d tag q.2)) =
      oneBinJointCount N r tag h q := by
  simp only [sourceTimeKernel, PMF.map_bind, oneBinJointCount]

theorem actual_interval_joint_count (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (offset : ℝ) (h : ℝ≥0) (tag : Tag) (B : Copy → Copy → Tag)
    (hconst : ∀ a : ℝ, offset < a → a < offset + (h : ℝ) → bin a = tag) :
    segmentJoint N r bin hbin (.interval h) s offset B =
      oneBinJointCount N r tag h (s, B) := by
  rw [actual_segment_endpoint_tag_row N r bin hbin (.interval h) tag s offset B hconst]
  change (sourceTimeKernel N r h s).map (fun d => (d, tagUpdate N s d tag B)) = _
  exact source_time_joint_count N r tag h (s, B)

/-- Genuine fixed-cut retained-clock joint law, not arbitrary count splitting
or an endpoint-only renewal premise. Zero left/right pieces are allowed. -/
theorem actual_two_bin_joint_count (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (offset : ℝ) (t v : ℝ≥0) (leftTag rightTag : Tag)
    (B : Copy → Copy → Tag)
    (hl : ∀ a : ℝ, offset < a → a < offset + (t : ℝ) → bin a = leftTag)
    (hr : ∀ a : ℝ, offset + (t : ℝ) < a →
      a < offset + (t : ℝ) + (v : ℝ) → bin a = rightTag) :
    segmentJoint N r bin hbin (.interval (t + v)) s offset B =
      (oneBinJointCount N r leftTag t (s, B)).bind
        (oneBinJointCount N r rightTag v) := by
  rw [interval_joint_cut_bind N r bin hbin s offset t v B,
    actual_interval_joint_count N r bin hbin s offset t leftTag B hl]
  apply congrArg (PMF.bind (oneBinJointCount N r leftTag t (s, B)))
  funext q
  exact actual_interval_joint_count N r bin hbin q.1 (offset + (t : ℝ)) v rightTag q.2 hr

theorem actual_cut_duration (guard cut next : ℝ) (hl : guard ≤ cut) (hr : cut ≤ next) :
    Real.toNNReal (cut - guard) + Real.toNNReal (next - cut) =
      Real.toNNReal (next - guard) ∧
    guard + (Real.toNNReal (cut - guard) : ℝ) = cut := by
  have ht := Real.coe_toNNReal (cut - guard) (sub_nonneg.mpr hl)
  have hv := Real.coe_toNNReal (next - cut) (sub_nonneg.mpr hr)
  have hw := Real.coe_toNNReal (next - guard) (sub_nonneg.mpr (hl.trans hr))
  constructor
  · apply NNReal.eq
    simp only [NNReal.coe_add, ht, hv, hw]
    ring
  · rw [ht]
    ring

noncomputable def twoBinEncodedRow (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (leftTag rightTag : Tag) (t v : ℝ≥0)
    (place : Location V E ≃ Pop) (vertex : V ≃ RegisterID)
    (leaf : Copy ≃ Label) (tag : Tag ≃ Bin) (q : TaggedCode N sample Tag) :
    PMF (FullRecord Pop RegisterID Label Bin) :=
  (oneBinJointCount N r leftTag t q).bind (fun d =>
    (oneBinJointCount N r rightTag v d).map
      (encodedForestReadout N place vertex leaf tag))

/-- Substantive physical-guard consumer: the actual UNSPLIT next-gap law is
the full joint encoded two-bin original count bind. Primitive coordinates,
actual sorted split and deterministic fixed-cut/bin grammar are its inputs.
The SAME original register and all Locations survive both pieces. -/
theorem actual_guard_two_bin_encoded_count [Nonempty Copy]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (guard cut next : ℝ) (pre post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (hleft : guard ≤ cut) (hright : cut ≤ next) (leftTag rightTag : Tag)
    (hl : ∀ a : ℝ, guard < a → a < cut → bin a = leftTag)
    (hr : ∀ a : ℝ, cut < a → a < next → bin a = rightTag)
    (place : Location V E ≃ Pop) (vertex : V ≃ RegisterID)
    (leaf : Copy ≃ Label) (tag : Tag ≃ Bin) :
    (naturalPastJoint N C sample p r bin hbin
      (guardPrefix N C H (originalGamma p) common guard pre ++
        [.interval (Real.toNNReal (next - guard))])).map
          (encodedForestReadout N place vertex leaf tag) =
      (naturalPastJoint N C sample p r bin hbin
        (guardPrefix N C H (originalGamma p) common guard pre)).bind
          (twoBinEncodedRow N r leftTag rightTag
            (Real.toNNReal (cut - guard)) (Real.toNNReal (next - cut))
            place vertex leaf tag) := by
  have hdate := actual_guard_prefix_date N C H (originalGamma p) common guard pre
    (next :: post) hsplit
  have hc := actual_cut_duration guard cut next hleft hright
  have hbl : ∀ a : ℝ, guard < a →
      a < guard + (Real.toNNReal (cut - guard) : ℝ) → bin a = leftTag := by
    simpa only [hc.2] using hl
  have hbr : ∀ a : ℝ, guard + (Real.toNNReal (cut - guard) : ℝ) < a →
      a < guard + (Real.toNNReal (cut - guard) : ℝ) +
        (Real.toNNReal (next - cut) : ℝ) → bin a = rightTag := by
    intro a ha hb
    rw [hc.2] at ha hb
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr hright)] at hb
    apply hr a ha
    linarith
  rw [actual_natural_past_append N C sample p r bin hbin
    (guardPrefix N C H (originalGamma p) common guard pre)
    [.interval (Real.toNNReal (next - guard))], PMF.map_bind]
  apply congrArg (PMF.bind (naturalPastJoint N C sample p r bin hbin
    (guardPrefix N C H (originalGamma p) common guard pre)))
  funext q
  rw [calendar_joint_single, hdate, ← hc.1,
    actual_two_bin_joint_count N r bin hbin q.1 guard
      (Real.toNNReal (cut - guard)) (Real.toNNReal (next - cut))
      leftTag rightTag q.2 hbl hbr, PMF.map_bind]
  rfl

end CloudG6.NaturalFixedCutFullJoint
