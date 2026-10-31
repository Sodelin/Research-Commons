import ResearchCommons.MSCI.JC69SourceRootQuotient
import UnifiedLean.Source.SourceInitializedCalendar

/-! Actual initialized calendar prefixes: no pending sample nodes after the
common sampling date. UNCOMPILED, dot (OpenAI), 31 October 2026.
Whole same-date batches are retained. No literal inactive Code identity,
small-state count or initial exposure cancellation is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69ActivatedPrefix
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.NativeParentRouting
open ResearchCommons.MSCI.JC69SourceRootQuotient
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def NodeUpper (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    (u : ℝ) (s : Code N sample) : Prop :=
  ∀ x : Copy, ∀ v : V, copyLocation (state s) x = .node v → C.age v ≤ u

lemma node_upper_mono (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    {u v : ℝ} {s : Code N sample} (hs : NodeUpper N C u s) (huv : u ≤ v) : NodeUpper N C v s :=
  fun x w hw => (hs x w hw).trans huv

lemma step_copy_location (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) (hd : d ∈ (sourceStep N r s).support)
    (x : Copy) : copyLocation (state d) x = copyLocation (state s) x := by
  obtain ⟨p,_,hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  rw [← hp]
  cases p with
  | none => rfl
  | some p => exact actual_coded_merge_copyLocation N s p x

lemma iteration_copy_location (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : ℕ) (s d : Code N sample)
    (hd : d ∈ (sourceIteration N r k s).support) (x : Copy) :
    copyLocation (state d) x = copyLocation (state s) x := by
  induction k generalizing s with
  | zero =>
      have he : d = s := by simpa only [sourceIteration,PMF.mem_support_pure_iff] using hd
      simp [he]
  | succ k ih =>
      obtain ⟨m,hm,hmd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact (ih m hmd).trans (step_copy_location N r s m hm x)

/-- Actual interval mergers preserve each original copy's population; no
new chronological support or normalization theorem is inserted. -/
theorem actual_time_copy_location (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (h : ℝ≥0) (s d : Code N sample)
    (hd : d ∈ (sourceTimeKernel N r h s).support) (x : Copy) :
    copyLocation (state d) x = copyLocation (state s) x := by
  obtain ⟨k,_,hk⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact iteration_copy_location N r k s d hk x

lemma time_node_upper (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    (r : PositivePairRates E) (h : ℝ≥0) (s d : Code N sample) (u : ℝ)
    (hs : NodeUpper N C u s) (hd : d ∈ (sourceTimeKernel N r h s).support) :
    NodeUpper N C u d := by
  intro x v hv
  exact hs x v ((actual_time_copy_location N r h s d hd x).symm.trans hv)

lemma exit_node_upper (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    (u : ℝ) (s : Code N sample) (e : E) (he : C.age (N.graph.source e) ≤ u)
    (hs : NodeUpper N C u s) : NodeUpper N C u (exitCode N s e) := by
  intro x v hv
  rw [exitCode_copyLocation] at hv
  unfold exitLocation at hv
  split_ifs at hv with hp
  · have hh := Location.node.inj hv
    simpa only [hh] using he
  · exact hs x v hv

lemma exit_list_node_upper (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    (r : PositivePairRates E) (u : ℝ) (es : List E)
    (he : ∀ e ∈ es, C.age (N.graph.source e) ≤ u) (s : Code N sample)
    (hs : NodeUpper N C u s) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (es.map (fun e => .boundary (.exit e))) s).support) :
    NodeUpper N C u d := by
  induction es generalizing s with
  | nil =>
      have hh : d = s := by simpa only [List.map_nil,sourceProgram,PMF.mem_support_pure_iff] using hd
      simpa only [hh] using hs
  | cons e es ih =>
      have ht : d ∈ (sourceProgram N r (es.map (fun e => .boundary (.exit e))) (exitCode N s e)).support := by
        simpa only [List.map_cons,sourceProgram,sourceProgramStep,boundaryKernel,PMF.pure_bind] using hd
      exact ih (fun f hf => he f (List.mem_cons_of_mem e hf)) (exitCode N s e)
        (exit_node_upper N C u s e (he e (by simp)) hs) ht

lemma node_operation_upper (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (u : ℝ) (v : V) (s d : Code N sample) (hs : NodeUpper N C u s)
    (hd : d ∈ (boundaryKernel N (originalNodeOperation N H gamma common v) s).support) :
    NodeUpper N C u d := by
  intro x w hw
  have hm := actual_original_node_kernel_movement N H gamma common v s hd x
  have ho : copyLocation (state s) x = .node w := by
    by_contra h
    exact node_move_never_creates_node N hm h hw
  exact hs x w ho

lemma node_list_upper (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (u : ℝ) (vs : List V) (s : Code N sample)
    (hs : NodeUpper N C u s) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (vs.map (fun v =>
      .boundary (originalNodeOperation N H gamma common v))) s).support) : NodeUpper N C u d := by
  induction vs generalizing s with
  | nil =>
      have hh : d = s := by simpa only [List.map_nil,sourceProgram,PMF.mem_support_pure_iff] using hd
      simpa only [hh] using hs
  | cons v vs ih =>
      change d ∈ ((boundaryKernel N (originalNodeOperation N H gamma common v) s).bind
        (sourceProgram N r (vs.map (fun w => .boundary (originalNodeOperation N H gamma common w))))).support at hd
      obtain ⟨m,hm,hmd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih m (node_operation_upper N C H gamma common u v s m hs hm) hmd

/-- A COMPLETE original date block creates nodes only at its own date;
node entries/pulses never create a future dormant node. -/
theorem actual_boundary_node_upper (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a u : ℝ) (hau : a ≤ u)
    (s : Code N sample) (hs : NodeUpper N C u s) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (boundaryOperations N C H gamma common a) s).support) :
    NodeUpper N C u d := by
  rw [boundaryOperations,sourceProgram_append] at hd
  obtain ⟨m,hm,hmd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have he := exit_list_node_upper N C r u
    (Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList
    (fun e he => (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2.le.trans hau) s hs hm
  exact node_list_upper N C H gamma common r u _ m he hmd

/-- Prefix form of the existing physical-calendar induction. FutureComplete
is retained for choosing the genuine next-date gap; it is not a new law field. -/
lemma actual_tail_prefix_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (dates : List ℝ) (a c : ℝ)
    (hfuture : FutureComplete N C a dates) (hordered : dates.Pairwise (· < ·))
    (hafter : ∀ b ∈ dates, a < b) (k : ℕ) (s : Code N sample)
    (hs : AfterNodes N C a (state s)) (hu : NodeUpper N C (max c a) s) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (calendarTail N C H gamma common a (dates.take k)) s).support) :
    AfterNodes N C (finalDate a (dates.take k)) (state d) ∧
      NodeUpper N C (max c (finalDate a (dates.take k))) d := by
  induction dates generalizing a s k with
  | nil =>
      have hh : d = s := by simpa only [List.take_nil,calendarTail,sourceProgram,PMF.mem_support_pure_iff] using hd
      simpa only [List.take_nil,finalDate,hh] using And.intro hs hu
  | cons b bs ih =>
      cases k with
      | zero =>
          have hh : d = s := by simpa only [List.take_zero,calendarTail,sourceProgram,PMF.mem_support_pure_iff] using hd
          simpa only [List.take_zero,finalDate,hh] using And.intro hs hu
      | succ k =>
          have hab : a < b := hafter b (by simp)
          have hbs := List.pairwise_cons.mp hordered
          have hgap : ∀ v : V, a < C.age v → b ≤ C.age v := by
            intro v hv
            rcases List.mem_cons.mp (hfuture v hv) with he | he
            · exact he.ge
            · exact (hbs.1 _ he).le
          have hepoch := after_nodes_to_epoch N C hs hgap
          change d ∈ ((sourceTimeKernel N r (Real.toNNReal (b-a)) s).bind
            (sourceProgram N r (boundaryOperations N C H gamma common b ++
              calendarTail N C H gamma common b (bs.take k)))).support at hd
          obtain ⟨m,hm,hmd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
          have hmepoch := actual_source_time_epoch_support N C r (Real.toNNReal (b-a)) s hepoch hm
          have hmupper := time_node_upper N C r (Real.toNNReal (b-a)) s m (max c a) hu hm
          rw [sourceProgram_append] at hmd
          obtain ⟨z,hz,hzd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hmd
          have hzphysical := actual_original_boundary_batch_support N C H gamma common r b m
            (epoch_to_next_ready N C hmepoch hab.le) hz
          have hzupper := actual_boundary_node_upper N C H gamma common r b (max c b)
            (le_max_right c b) m (node_upper_mono N C hmupper (max_le_max_left c hab.le)) hz
          have hnext : FutureComplete N C b bs := by
            intro v hv
            rcases List.mem_cons.mp (hfuture v (hab.trans hv)) with he | he
            · exact False.elim ((ne_of_gt hv) he)
            · exact he
          simpa only [List.take_succ_cons,finalDate] using
            ih b hnext hbs.2 hbs.1 k z hzphysical hzupper hzd

/-- Stop after the initial date block and k further COMPLETE date blocks. -/
def initializedPrefix (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (k : ℕ) : List (ProgramStep N) :=
  match sortedOriginalDates N C with
  | [] => []
  | a::dates => boundaryOperations N C H gamma common a ++ calendarTail N C H gamma common a (dates.take k)

def prefixDate (N : RootedBinary V E X) (C : Calendar N.graph) (k : ℕ) : ℝ :=
  match sortedOriginalDates N C with
  | [] => firstOriginalDate N C
  | a::dates => finalDate a (dates.take k)

/-- Actual initialized prefix support, deriving the no-future-node bound
from the original contemporaneous sampled leaf IDs and original operations. -/
theorem actual_initialized_prefix_support (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (c : ℝ) (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (k : ℕ) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (initializedPrefix N C H gamma common k)
      (initialCode N sample register)).support) :
    AfterNodes N C (prefixDate N C k) (state d) ∧
      NodeUpper N C (max c (prefixDate N C k)) d := by
  have hne : sortedOriginalDates N C ≠ [] := by
    intro h
    have hm := original_date_scheduled N C N.root
    rw [h] at hm
    exact List.not_mem_nil hm
  obtain ⟨a,dates,heq⟩ := List.exists_cons_of_ne_nil hne
  have hfirst : a = firstOriginalDate N C := by
    have h := first_compiled_date_is_initial_boundary N C
    simpa only [heq,List.getElem_cons_zero] using h
  have hordered := original_dates_strict N C
  rw [heq] at hordered
  have hp := List.pairwise_cons.mp hordered
  have hfuture : FutureComplete N C a dates := by
    intro v hv
    have hm := original_date_scheduled N C v
    rw [heq] at hm
    rcases List.mem_cons.mp hm with he | he
    · exact False.elim ((ne_of_gt hv) he)
    · exact he
  have hready : BoundaryReady N C a (state (initialCode N sample register)) := by
    rw [hfirst]
    exact actual_initial_calendar_boundary N C sample register
  have hi : NodeUpper N C c (initialCode N sample register) := by
    intro x v hv
    have hl : copyLocation (state (initialCode N sample register)) x = .node (N.leaf (sample x)) := by
      unfold initialCode state admittedCode
      rw [decode_encode_copyLocation]
      rfl
    have he := Location.node.inj (hl.symm.trans hv)
    simpa only [he] using (hc x).le
  rw [initializedPrefix,heq,sourceProgram_append] at hd
  obtain ⟨s,hs,hsd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hstart := actual_original_boundary_batch_support N C H gamma common r a _ hready hs
  have hupper := actual_boundary_node_upper N C H gamma common r a (max c a) (le_max_right c a)
    (initialCode N sample register) (node_upper_mono N C hi (le_max_left c a)) hs
  simpa only [prefixDate,heq] using
    actual_tail_prefix_support N C H gamma common r dates a c hfuture hp.2 hp.1 k s hstart hupper hsd

/-- No dormant sample node remains after the common sample date, on the
ACTUAL prefix support. Whole same-date batches, not elementary operations. -/
theorem actual_initialized_prefix_no_nodes (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (c : ℝ) (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (k : ℕ)
    (hactivated : c ≤ prefixDate N C k) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (initializedPrefix N C H gamma common k)
      (initialCode N sample register)).support) :
    ∀ x : Copy, ∀ v : V, copyLocation (state d) x ≠ .node v := by
  have h := actual_initialized_prefix_support N C sample register H gamma common r c hc k hd
  intro x v hv
  have hu := h.2 x v hv
  rw [max_eq_right hactivated] at hu
  exact (not_lt_of_ge hu) (h.1.2 x v hv)

#print axioms actual_time_copy_location
#print axioms actual_boundary_node_upper
#print axioms actual_initialized_prefix_support
#print axioms actual_initialized_prefix_no_nodes
end ResearchCommons.MSCI.JC69ActivatedPrefix
