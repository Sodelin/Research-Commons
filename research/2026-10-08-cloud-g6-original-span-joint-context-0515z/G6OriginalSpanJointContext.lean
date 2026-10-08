import G6ProtectedChildCarrier
import CompleteCalendarBinReadout
import G1ContextualForestReplacement

/-!
Fixed original span's actual full-calendar conditional tagged continuation.
Cloud literature/organization structural lane, 8 October 2026, 05:15 UTC.
Original graph/calendar/clock/graft providers: Dot. Selected finite-bin reader:
Cloud G3/source bridge. Compiler UNCHECKED, outside proposed179.

The window includes ALL original dates and tied operations between the child's
lower interface and the entry's older interface. The entering full Code, its
current population/owner partition and entire register are retained. Tags and
endpoint are read from the SAME actual calendar record and old real matrix.
No desired source law, reduced graph Code, ordinary spine or positive-chain
replacement is a field. The endpoint phase is after exits / before node entry.
-/

namespace UnifiedLean.G6.OriginalSpanJointContext
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest GProgram.G5
open G1NaturalCalendarNodes G1InitializedFrontierPrefix G1ContextualForestReplacement
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceInitializedCalendar
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CalendarDecoration GProgram.G2.SourceGraftDecoration
open GProgram.G2.FaithfulPairAgeDecoration CloudG3.FiniteTagDecoder
open CloudG3.CompleteCalendarBinReadout
open UnifiedLean.G6.OriginalSpliceAdapter UnifiedLean.G6.SpineBoundaryCarrier
open scoped Classical

variable {V E X Copy Tag : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

private theorem filter_pairwise {A : Type*} (R : A → A → Prop) (p : A → Bool)
    (xs : List A) : xs.Pairwise R → (xs.filter p).Pairwise R := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      intro h
      have hh := List.pairwise_cons.mp h
      cases hp : p a with
      | false => simpa [List.filter_cons, hp] using ih hh.2
      | true =>
          have ht : (a :: xs.filter p).Pairwise R := List.pairwise_cons.mpr
            ⟨fun b hb => hh.1 b (List.mem_filter.mp hb).1, ih hh.2⟩
          simpa [List.filter_cons, hp] using ht

/-- The suffix is constructed from the SAME complete original date list. -/
noncomputable def datesAfter (N : RootedBinary V E X) (C : Calendar N.graph)
    (a : ℝ) : List ℝ := (sortedOriginalDates N C).filter (fun t => decide (a < t))

theorem actual_dates_after_constraints (N : RootedBinary V E X) (C : Calendar N.graph)
    (a : ℝ) : FutureComplete N C a (datesAfter N C a) ∧
    (datesAfter N C a).Pairwise (· < ·) ∧ (∀ t ∈ datesAfter N C a, a < t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    exact List.mem_filter.mpr ⟨original_date_scheduled N C v, by simpa using hv⟩
  · exact filter_pairwise (· < ·) _ _ (original_dates_strict N C)
  · intro t ht
    exact of_decide_eq_true (List.mem_filter.mp ht).2

/-- Original physical calendar window AFTER the complete child-date batch,
through every intermediate batch, ending AFTER all older-interface exits and
BEFORE its node batch. Outside operations at private/tied dates are retained. -/
noncomputable def spanWindowOps (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) : List (ProgramStep N) :=
  let A := derivedBigon N hcut b hb hp
  let a := C.age (N.graph.target A.child)
  let stop := C.age (N.graph.source A.entry)
  stopBeforeTail N C H gamma common stop a (datesAfter N C a) ++
    ((Finset.univ.filter (fun e : E => C.age (N.graph.source e) = stop)).toList.map
      (fun e => .boundary (.exit e)))

/-- The complete true original initialization/batch discharges entering
physical premises. Supported window endpoints inherit natural physical
frontier support and the SAME full entering register. No outside roots or
current locations are discarded to obtain this conclusion. -/
theorem actual_initialized_span_frontier_support (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) {d s w : Code N sample}
    (hd : d ∈ (sourceProgram N r
      (actualFrontierProgram N C H gamma common
        (C.age (N.graph.target (derivedBigon N hcut b hb hp).child)))
      (initialCode N sample register)).support)
    (hs : s ∈ (sourceProgram N r
      ((Finset.univ.filter (fun v : V =>
        C.age v = C.age (N.graph.target (derivedBigon N hcut b hb hp).child))).toList.map
        (fun v => .boundary (originalNodeOperation N H gamma common v))) d).support)
    (hw : w ∈ (sourceProgram N r (spanWindowOps N hcut b hb hp C H gamma common) s).support) :
    AfterExits N C (C.age (N.graph.source (derivedBigon N hcut b hb hp).entry)) (state w) ∧
    NaturalNodes N C sample (C.age (N.graph.source (derivedBigon N hcut b hb hp).entry)) (state w) ∧
    StrictEnteredEdges N C (C.age (N.graph.source (derivedBigon N hcut b hb hp).entry)) (state w) ∧
    (state w).register = (state s).register := by
  let A := derivedBigon N hcut b hb hp
  let a := C.age (N.graph.target A.child)
  let stop := C.age (N.graph.source A.entry)
  let vs := (Finset.univ.filter (fun v : V => C.age v = a)).toList
  have hreg := actual_program_register_support N r
    (spanWindowOps N hcut b hb hp C H gamma common) s hw
  have hfront := actual_initialized_frontier_support N C sample register H gamma common r
    (N.graph.target A.child) hd
  have hnd : NaturalState N C sample a (state d) :=
    ⟨hfront.2.1, fun x e he => (hfront.2.2 x e he).le⟩
  have hns := actual_node_list_natural N C H gamma common r vs a (by
    intro v hv; exact (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2) d hnd hs
  have has := actual_node_batch_support N C H gamma common r a d hfront.1 hs
  have hdates := actual_dates_after_constraints N C a
  have hage := boundary_original_private_age_order N hcut b hb hp C
  change a < C.age A.fragment.parents.hybrid ∧
    C.age A.fragment.parents.hybrid < C.age A.fragment.upper ∧
    C.age A.fragment.upper < stop at hage
  have hstop : stop ∈ datesAfter N C a :=
    hdates.1 (N.graph.source A.entry) ((hage.1.trans hage.2.1).trans hage.2.2)
  rw [spanWindowOps, sourceProgram_append] at hw
  obtain ⟨m, hm, hwm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hw
  have hbefore := actual_stop_tail_support N C H gamma common r (datesAfter N C a) a stop
    hdates.1 hdates.2.1 hdates.2.2 hstop s has hns hm
  have hphysical := actual_exit_batch_support N C r stop m hbefore.1 hwm
  have hnatural := actual_exit_list_natural N C r _ stop (by
    intro e he; exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2) m hbefore.2.1 hwm
  have hstrict := actual_exit_list_strict_entered N C r _ stop m hbefore.2.2 hwm
  exact ⟨hphysical, hnatural.1, hstrict, hreg⟩

variable [MeasurableSpace Tag]

/-- Conditional row from the actual ORIGINAL clock/boundary record. The full
endpoint Code and old/new tags remain JOINT. No desired law is a field. -/
noncomputable def spanJointTaggedLaw (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (s : Code N sample) (M : Copy → Copy → ℝ) :
    Measure (Code N sample × (Copy → Copy → Tag)) :=
  calendarJointLaw N r bin (spanWindowOps N hcut b hb hp C H gamma common) s
    (C.age (N.graph.target (derivedBigon N hcut b hb hp).child)) M

theorem span_joint_probability (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (M : Copy → Copy → ℝ) :
    IsProbabilityMeasure (spanJointTaggedLaw N hcut b hb hp C H gamma common r bin s M) :=
  calendar_joint_probability N r bin hbin _ _ _ _

/-- The endpoint marginal is the actual original word, not a replacement
kernel. It retains all current populations, outside forest and register. -/
theorem span_joint_endpoint_law (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (M : Copy → Copy → ℝ) :
    (spanJointTaggedLaw N hcut b hb hp C H gamma common r bin s M).map Prod.fst =
      (sourceProgram N r (spanWindowOps N hcut b hb hp C H gamma common) s).toMeasure := by
  unfold spanJointTaggedLaw calendarJointLaw
  rw [Measure.map_map measurable_fst (calendar_joint_bin_readout_measurable N bin hbin _ _ _ _)]
  exact actual_calendar_endpoint_law N r _ s

/-- Arbitrary SAME-history/full-endpoint/tag receiver is evaluated on the
same actual record. Correlated entering states use these identical rows;
neither their history nor register is replaced by an independent marginal. -/
theorem span_whole_outside_context_readout {History Obs : Type*} [MeasurableSpace Obs]
    (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (M : Copy → Copy → ℝ) (history : History)
    (receive : History → (Code N sample × (Copy → Copy → Tag)) → Obs)
    (hreceive : Measurable (receive history)) :
    (spanJointTaggedLaw N hcut b hb hp C H gamma common r bin s M).map (receive history) =
      (actualCalendarTraceLaw N r (spanWindowOps N hcut b hb hp C H gamma common) s).map
        (fun z => receive history
          (calendarEnd N (spanWindowOps N hcut b hb hp C H gamma common) s z,
            calendarTags N bin (spanWindowOps N hcut b hb hp C H gamma common) s
              (C.age (N.graph.target (derivedBigon N hcut b hb hp).child))
              (fun x y => bin (M x y)) z)) := by
  unfold spanJointTaggedLaw calendarJointLaw
  rw [Measure.map_map hreceive (calendar_joint_bin_readout_measurable N bin hbin _ _ _ _)]
  rfl

/-- The joint tags decode EVERY internal node of the SAME actual endpoint's
live forest under its physically carried old real decoration. This is not a
fresh compatible tree/time assignment or an assumed decoder law. -/
theorem span_actual_tagged_forest {V E X Copy Tag : Type*}
    [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
    [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
    (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag)
    (leafAge : Copy → ℝ) (s : Code N sample) (M : Copy → Copy → ℝ)
    (hM : ForestDecorates leafAge M (state s)) :
    let ops := spanWindowOps N hcut b hb hp C H gamma common
    let a := C.age (N.graph.target (derivedBigon N hcut b hb hp).child)
    ∀ᵐ z ∂actualCalendarTraceLaw N r ops s,
      ∀ l ∈ (state (calendarEnd N ops s z)).live,
        ∃ d : Decoration ((state (calendarEnd N ops s z)).genealogy l),
          (∀ x ∈ ((state (calendarEnd N ops s z)).genealogy l).leaves,
            ∀ y ∈ ((state (calendarEnd N ops s z)).genealogy l).leaves,
              calendarMatrix N ops s a M z x y =
                pairAge leafAge ((state (calendarEnd N ops s z)).genealogy l) d x y) ∧
          decodeTags (calendarTags N bin ops s a (fun x y => bin (M x y)) z)
              ((state (calendarEnd N ops s z)).genealogy l) =
            mapBinDecoration bin ((state (calendarEnd N ops s z)).genealogy l) d := by
  let ops := spanWindowOps N hcut b hb hp C H gamma common
  let a := C.age (N.graph.target (derivedBigon N hcut b hb hp).child)
  filter_upwards [actual_calendar_matrix_decorates N r leafAge ops s a M hM] with z hz
  intro l hl
  obtain ⟨d, hd⟩ := hz l hl
  refine ⟨d, hd, ?_⟩
  rw [← map_calendar_matrix N bin ops s a M z]
  exact decodeTags_bin_of_pair_agreement bin leafAge
    ((state (calendarEnd N ops s z)).genealogy l)
    ((calendarEnd N ops s z).property.forest.wellLabelled l hl) d
    (calendarMatrix N ops s a M z) hd

#print axioms actual_dates_after_constraints
#print axioms actual_initialized_span_frontier_support
#print axioms span_joint_probability
#print axioms span_joint_endpoint_law
#print axioms span_whole_outside_context_readout
#print axioms span_actual_tagged_forest

end UnifiedLean.G6.OriginalSpanJointContext
