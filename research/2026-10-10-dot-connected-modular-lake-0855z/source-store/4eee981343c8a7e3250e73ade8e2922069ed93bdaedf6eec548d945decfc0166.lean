import G5ObservedCutPosterior
import G1NonrootBigonKernel
import UnifiedLean.Source.SourceBoundaryLocations
import UnifiedLean.Source.SourceCalendarPhysicalSupport

/-! Actual contemporaneous-tip activation and original calendar prefix
population placement. Reuses the accepted G5 hand hypothesis. -/
namespace GProgram.G5.ActualActivatedPrefix
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceInitializedCalendar
open G1NonrootBigonKernel
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def NoPendingNodes (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) : Prop :=
  ∀ x v, copyLocation (state s) x ≠ .node v

def NodesAtDate (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    {sample : Copy → X} (a : ℝ) (s : Code N sample) : Prop :=
  ∀ x v, copyLocation (state s) x = .node v → C.age v = a

lemma exit_preserves_date_nodes (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) {sample : Copy → X} {a : ℝ}
    (s : Code N sample) (e : E) (he : C.age (N.graph.source e) = a)
    (hs : NodesAtDate N C a s) : NodesAtDate N C a (exitCode N s e) := by
  intro x v hv
  rw [exitCode_copyLocation] at hv
  unfold exitLocation at hv
  split_ifs at hv with h
  · cases hv
    exact he
  · exact hs x v hv

lemma exit_list_date_nodes (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) {sample : Copy → X} (r : PositivePairRates E)
    (a : ℝ) (es : List E) (he : ∀ e ∈ es, C.age (N.graph.source e) = a)
    (s d : Code N sample) (hs : NodesAtDate N C a s)
    (hd : d ∈ (sourceProgram N r (es.map (fun e => .boundary (.exit e))) s).support) :
    NodesAtDate N C a d := by
  induction es generalizing s with
  | nil =>
    have h : d = s := by simpa [sourceProgram] using hd
    subst d
    exact hs
  | cons e es ih =>
    have hd' : d ∈ (sourceProgram N r (es.map (fun e => .boundary (.exit e))) (exitCode N s e)).support := by
      simpa only [List.map_cons,sourceProgram,sourceProgramStep,boundaryKernel,PMF.pure_bind] using hd
    exact ih (fun f hf => he f (by simp [hf])) _
      (exit_preserves_date_nodes N C s e (he e (by simp)) hs) hd'

lemma node_list_eliminates (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (vs : List V)
    (s d : Code N sample)
    (hs : ∀ x v, copyLocation (state s) x = .node v → v ∈ vs)
    (hd : d ∈ (sourceProgram N r (vs.map (fun v =>
      .boundary (originalNodeOperation N H gamma common v))) s).support) :
    NoPendingNodes N d := by
  induction vs generalizing s with
  | nil =>
    have h : d = s := by simpa [sourceProgram] using hd
    subst d
    intro x v hv
    exact List.not_mem_nil (hs x v hv)
  | cons v vs ih =>
    change d ∈ ((boundaryKernel N (originalNodeOperation N H gamma common v) s).bind
      (sourceProgram N r (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v))))).support at hd
    obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    apply ih m ?_ hdm
    intro x u hu
    have move := actual_original_node_kernel_movement N H gamma common v s hm x
    have old : copyLocation (state s) x = .node u := by
      by_contra h
      exact node_move_never_creates_node N move h hu
    rcases List.mem_cons.mp (hs x u old) with huv | huv
    · subst u
      exact False.elim (node_move_removes_node N move hu)
    · exact huv

lemma actual_boundary_activates_date (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a : ℝ)
    (s d : Code N sample) (hs : NodesAtDate N C a s)
    (hd : d ∈ (sourceProgram N r (boundaryOperations N C H gamma common a) s).support) :
    NoPendingNodes N d := by
  unfold boundaryOperations at hd
  rw [sourceProgram_append] at hd
  obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hmdate := exit_list_date_nodes N C r a _ (by
    intro e he
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2) s m hs hm
  apply node_list_eliminates N H gamma common r _ m d ?_ hdm
  intro x v hv
  exact Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmdate x v hv⟩)

lemma actual_calendar_tail_no_pending (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a : ℝ) (dates : List ℝ)
    (s d : Code N sample) (hs : NoPendingNodes N s)
    (hd : d ∈ (sourceProgram N r (calendarTail N C H gamma common a dates) s).support) :
    NoPendingNodes N d := by
  induction dates generalizing a s with
  | nil =>
    have h : d = s := by simpa [calendarTail,sourceProgram] using hd
    subst d
    exact hs
  | cons b dates ih =>
    change d ∈ ((sourceTimeKernel N r (Real.toNNReal (b-a)) s).bind
      (sourceProgram N r (boundaryOperations N C H gamma common b ++
        calendarTail N C H gamma common b dates))).support at hd
    obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    rw [sourceProgram_append] at hdm
    obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdm
    apply ih b z ?_ hdz
    apply actual_boundary_activates_date N C H gamma common r b m z ?_ hz
    intro x v hv
    rw [actual_time_copy_population N r _ s hm x] at hv
    exact False.elim (hs x v hv)

lemma initial_nodes_at_tip_date (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (reg : V → Bool)
    (a : ℝ) (htips : ∀ x, C.age (N.leaf (sample x)) = a) :
    NodesAtDate N C a (initialCode N sample reg) := by
  intro x v hv
  unfold initialCode state admittedCode at hv
  rw [decode_encode_copyLocation] at hv
  change Location.node (N.leaf (sample x)) = .node v at hv
  cases hv
  exact htips x

/-- After the actual activation-date batch, every complete original date
batch and any ordinary partial epoch retain genuine edge/root populations.
The dates/operation-prefix identity is supplied by the actual calendar use site. -/
theorem actual_activated_prefix_no_pending (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (reg : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a : ℝ) (dates : List ℝ)
    (t : ℝ≥0) (htips : ∀ x, C.age (N.leaf (sample x)) = a) (d : Code N sample)
    (hd : d ∈ (sourceProgram N r
      (boundaryOperations N C H gamma common a ++
       calendarTail N C H gamma common a dates ++ [.interval t])
      (initialCode N sample reg)).support) : NoPendingNodes N d := by
  rw [List.append_assoc,sourceProgram_append] at hd
  obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  rw [sourceProgram_append] at hdm
  obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdm
  have hma := actual_boundary_activates_date N C H gamma common r a _ m
    (initial_nodes_at_tip_date N C sample reg a htips) hm
  have hzno := actual_calendar_tail_no_pending N C H gamma common r a dates m z hma hz
  have hdz' : d ∈ (sourceTimeKernel N r t z).support := by simpa [sourceProgram,sourceProgramStep] using hdz
  intro x v hv
  rw [actual_time_copy_population N r t z hdz' x] at hv
  exact hzno x v hv

noncomputable def codePopulation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (x : Copy) : Option E :=
  match copyLocation (state s) x with
  | .edge e => some e
  | _ => none

lemma codePopulation_actual (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : NoPendingNodes N s) (x : Copy) :
    copyLocation (state s) x = originalPlace N (codePopulation N s x) := by
  unfold codePopulation
  cases h : copyLocation (state s) x with
  | node v => exact False.elim (hs x v h)
  | edge e => rfl
  | rootPopulation v =>
    have hv := s.property.original_descendant x
    change DescendsTo N (copyLocation (state s) x) (sample x) at hv
    rw [h] at hv
    exact congrArg Location.rootPopulation hv.1

#print axioms actual_activated_prefix_no_pending
#print axioms codePopulation_actual
#print axioms actual_boundary_activates_date
#print axioms actual_time_copy_population
end GProgram.G5.ActualActivatedPrefix
