import G4PartialExitSeparation

/-!
Actual initialized support below a supplied calibrated meeting geometry.
Contributor: dot (OpenAI), 2026-10-11. UNCOMPILED SOURCE DRAFT.

Ports the reviewed hand composition 0b6fecb7. The exact RouteMeetingGeometry
record remains an explicit geometric premise: its derivation from the original
COMMON calibration is accepted by hand but is not implemented in this module.
No physical support, desired probability identity or independence is a field.
Original source parameters, current-root ancestry and every supported prefix
are retained. The terminal cut precedes all later tied-date operations.
-/
namespace DotG4.ActualBelowMeetingSupport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.FiniteSourceSnapshot
open G1InitializedFrontierPrefix G1NonrootBigonKernel
open G1ActualJointProgram G1JointSeparatedSourceGeometry
open G4LiteralLastChildExitCutDraft G4PartialExitSeparationNextDraft
open scoped Classical NNReal

variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- Syntactic earlier-date steps of the unchanged compiler, not a source-law guard. -/
inductive EarlierOperation (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) : ProgramStep N → Prop
  | interval (dt : ℝ≥0) : EarlierOperation N C H gamma common v (.interval dt)
  | exit (e : E) (h : C.age (N.graph.source e) < C.age v) :
      EarlierOperation N C H gamma common v (.boundary (.exit e))
  | node (w : V) (h : C.age w < C.age v) :
      EarlierOperation N C H gamma common v
        (.boundary (originalNodeOperation N H gamma common w))

lemma boundary_operation_earlier (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) {a : ℝ} (ha : a < C.age v)
    {op : ProgramStep N} (hop : op ∈ boundaryOperations N C H gamma common a) :
    EarlierOperation N C H gamma common v op := by
  rw [boundaryOperations, List.mem_append] at hop
  rcases hop with hop | hop
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hop
    have heq := (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
    exact .exit e (by simpa only [heq] using ha)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hop
    have heq := (Finset.mem_filter.mp (Finset.mem_toList.mp hw)).2
    exact .node w (by simpa only [heq] using ha)

lemma stop_tail_operation_earlier (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (dates : List ℝ)
    (horder : dates.Pairwise (· < ·)) (hstop : C.age v ∈ dates) (a : ℝ)
    {op : ProgramStep N}
    (hop : op ∈ stopBeforeTail N C H gamma common (C.age v) a dates) :
    EarlierOperation N C H gamma common v op := by
  induction dates generalizing a with
  | nil => exact False.elim (List.not_mem_nil hstop)
  | cons b bs ih =>
      have hp := List.pairwise_cons.mp horder
      by_cases hb : b = C.age v
      · simp only [stopBeforeTail, if_pos hb, List.mem_singleton] at hop
        subst op
        exact .interval _
      · have hs : C.age v ∈ bs := (List.mem_cons.mp hstop).resolve_left (Ne.symm hb)
        have hbt : b < C.age v := hp.1 _ hs
        simp only [stopBeforeTail, if_neg hb, List.mem_cons, List.mem_append] at hop
        rcases hop with hop | hop | hop
        · subst op
          exact .interval _
        · exact boundary_operation_earlier N C H gamma common v hbt hop
        · exact ih hp.2 hs b hop

lemma before_boundary_operation_earlier (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) {op : ProgramStep N}
    (hop : op ∈ beforeBoundaryProgram N C H gamma common (C.age v)) :
    EarlierOperation N C H gamma common v op := by
  have hs := original_date_scheduled N C v
  have ho := original_dates_strict N C
  cases hd : sortedOriginalDates N C with
  | nil => rw [hd] at hs; exact False.elim (List.not_mem_nil hs)
  | cons a dates =>
      rw [hd] at hs ho
      have hp := List.pairwise_cons.mp ho
      by_cases ha : a = C.age v
      · simp only [beforeBoundaryProgram, hd, if_pos ha, List.not_mem_nil] at hop
      · have htail : C.age v ∈ dates := (List.mem_cons.mp hs).resolve_left (Ne.symm ha)
        simp only [beforeBoundaryProgram, hd, if_neg ha, List.mem_append] at hop
        rcases hop with hop | hop
        · exact boundary_operation_earlier N C H gamma common v (hp.1 _ htail) hop
        · exact stop_tail_operation_earlier N C H gamma common v dates hp.2 htail a hop

lemma actual_earlier_step_below (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) {sample : Copy → X}
    (r : PositivePairRates E) {op : ProgramStep N}
    (hop : EarlierOperation N C H gamma common v op) (s d : Code N sample) (x : Copy)
    (hs : BelowMeeting N C v (copyLocation (state s) x))
    (hd : d ∈ (sourceProgramStep N r op s).support) :
    BelowMeeting N C v (copyLocation (state d) x) := by
  cases hop with
  | interval dt =>
      have ht : d ∈ (sourceTimeKernel N r dt s).support := hd
      rw [actual_time_copy_population N r dt s ht x]
      exact hs
  | exit e he =>
      change d ∈ (PMF.pure (exitCode N s e)).support at hd
      obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd
      rw [exitCode_copyLocation]
      unfold exitLocation
      by_cases hx : copyLocation (state s) x = .edge e
      · simpa only [if_pos hx, BelowMeeting] using he
      · simpa only [if_neg hx] using hs
  | node w hw =>
      have hn : d ∈ (boundaryKernel N (originalNodeOperation N H gamma common w) s).support := hd
      have hm := actual_original_node_kernel_movement N H gamma common w s hn x
      unfold NodeMovement at hm
      by_cases hx : copyLocation (state s) x = .node w
      · rw [if_pos hx] at hm
        by_cases hr : w = N.root
        · rw [if_pos hr] at hm
          rw [hm]
          change C.age N.root < C.age v
          simpa only [hr] using hw
        · rw [if_neg hr] at hm
          obtain ⟨e, he, hloc⟩ := hm
          rw [hloc]
          change C.age (N.graph.target e) < C.age v
          simpa only [he] using hw
      · rw [if_neg hx] at hm
        rw [hm]
        exact hs

lemma actual_earlier_program_below (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hops : ∀ op ∈ ops, EarlierOperation N C H gamma common v op)
    (s d : Code N sample) (x : Copy)
    (hs : BelowMeeting N C v (copyLocation (state s) x))
    (hd : d ∈ (sourceProgram N r ops s).support) :
    BelowMeeting N C v (copyLocation (state d) x) := by
  induction ops generalizing s d with
  | nil =>
      have heq : d = s := by simpa only [sourceProgram, PMF.mem_support_pure_iff] using hd
      simpa only [heq] using hs
  | cons op ops ih =>
      change d ∈ ((sourceProgramStep N r op s).bind (sourceProgram N r ops)).support at hd
      obtain ⟨z, hz, hzd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih (fun q hq => hops q (List.mem_cons_of_mem op hq)) z d
        (actual_earlier_step_below N C H gamma common v r
          (hops op (by simp)) s z x hs hz) hzd

theorem actual_initialized_take_below (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (sample : Copy → X) (register : V → Bool)
    (r : PositivePairRates E) (x : Copy) (hy : C.age (N.leaf (sample x)) < C.age v)
    (k : Nat) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      ((beforeBoundaryProgram N C H gamma common (C.age v)).take k)
      (initialCode N sample register)).support) :
    BelowMeeting N C v (copyLocation (state d) x) := by
  have hinit : copyLocation (state (initialCode N sample register)) x = .node (N.leaf (sample x)) := by
    exact decode_encode_copyLocation N.root _ (initial_source_valid N sample register).forest x
  apply actual_earlier_program_below N C H gamma common v r _
    (fun op hop => before_boundary_operation_earlier N C H gamma common v
      (List.mem_of_mem_take hop)) (initialCode N sample register) d x _ hd
  rw [hinit]
  exact hy

lemma mandatory_child_tip_younger (N : RootedBinary V E X) (C : Calendar N.graph)
    (i : X) (v : V) (e : E) (he : N.graph.source e = v)
    (hp : ∀ es, EdgePath N.graph N.root (N.leaf i) es → e ∈ es) :
    C.age (N.leaf i) < C.age v := by
  obtain ⟨es, hs⟩ := original_tip_route_exists N i
  have hdesc := hs.target_reaches_end_of_mem (hp es hs)
  have hle := C.age_le_of_directed hdesc
  have hlt := C.edge_older e
  rw [he] at hlt
  exact hle.trans_lt hlt

theorem actual_initialized_before_agenda (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (sample : Copy → X) (register : V → Bool)
    (r : PositivePairRates E) {i j : X} {v : V} {ei ej : E}
    (hg : RouteMeetingGeometry N i j v ei ej) (inside outside : Finset Copy)
    (hi : ∀ x ∈ inside, sample x = i) (hj : ∀ y ∈ outside, sample y = j) :
    SeparatedAgenda N r inside outside
      (beforeBoundaryProgram N C H gamma common (C.age v)) (initialCode N sample register) := by
  apply agenda_of_supported_prefixes
  intro k hk d hd
  apply source_separated_of_below_meeting N C hg inside outside hi hj d
  intro x hx
  apply actual_initialized_take_below N C H gamma common v sample register r x _ k hd
  rw [hi x hx]
  exact mandatory_child_tip_younger N C i v ei hg.leftSource hg.leftOnEveryPath

lemma mandatory_child_of_ready_below (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (s : Code N sample) (x : Copy) (v : V) (e : E)
    (he : N.graph.source e = v)
    (hp : ∀ es, EdgePath N.graph N.root (N.leaf (sample x)) es → e ∈ es)
    (hr : BoundaryReady N C (C.age v) (state s))
    (hb : BelowMeeting N C v (copyLocation (state s) x)) :
    copyLocation (state s) x = .edge e := by
  have ht := hr x
  have hdesc : DescendsTo N (copyLocation (state s) x) (sample x) := by
    simpa only [state] using s.property.original_descendant x
  cases hloc : copyLocation (state s) x with
  | node w =>
      rw [hloc] at ht hb
      change C.age v ≤ C.age w at ht
      change C.age w < C.age v at hb
      exact False.elim (not_lt_of_ge ht hb)
  | rootPopulation w =>
      rw [hloc] at ht hb
      change w = N.root ∧ C.age N.root ≤ C.age v at ht
      change C.age w < C.age v at hb
      rw [ht.1] at hb
      exact False.elim (not_lt_of_ge (original_root_latest N C v) hb)
  | edge f =>
      rw [hloc] at ht hb hdesc
      change C.age (N.graph.target f) ≤ C.age v ∧ C.age v ≤ C.age (N.graph.source f) at ht
      change C.age (N.graph.target f) < C.age v at hb
      change N.graph.DReach (N.graph.target f) (N.leaf (sample x)) at hdesc
      obtain ⟨es, hes⟩ := exists_edgePath_of_directed (N.rooted (N.graph.source f))
      obtain ⟨fs, hfs⟩ := exists_edgePath_of_directed hdesc
      have path : EdgePath N.graph N.root (N.leaf (sample x)) (es ++ f :: fs) :=
        hes.append (.cons rfl hfs)
      have hem : e ∈ es ++ f :: fs := hp _ path
      have hfm : f ∈ es ++ f :: fs := by simp
      have hey : C.age (N.graph.target e) < C.age v := by simpa only [he] using C.edge_older e
      let u : ℝ := (max (C.age (N.graph.target f)) (C.age (N.graph.target e)) + C.age v) / 2
      have hm : max (C.age (N.graph.target f)) (C.age (N.graph.target e)) < C.age v :=
        max_lt_iff.mpr ⟨hb, hey⟩
      have hu : max (C.age (N.graph.target f)) (C.age (N.graph.target e)) ≤ u ∧ u < C.age v := by
        dsimp only [u]
        constructor <;> linarith
      have haf : C.Active u f := ⟨(le_max_left _ _).trans hu.1, hu.2.trans_le ht.2⟩
      have hae : C.Active u e := ⟨(le_max_right _ _).trans hu.1, by simpa only [he] using hu.2⟩
      have hfe : f = e := path.active_unique C hfm hem haf hae
      exact congrArg Location.edge hfe

theorem actual_initialized_before_children (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (sample : Copy → X) (register : V → Bool)
    (r : PositivePairRates E) {i j : X} {v : V} {ei ej : E}
    (hg : RouteMeetingGeometry N i j v ei ej) (inside outside : Finset Copy)
    (hi : ∀ x ∈ inside, sample x = i) (hj : ∀ y ∈ outside, sample y = j)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (beforeBoundaryProgram N C H gamma common (C.age v))
      (initialCode N sample register)).support) :
    (∀ x ∈ inside, copyLocation (state d) x = .edge ei) ∧
    (∀ y ∈ outside, copyLocation (state d) y = .edge ej) := by
  have hready := actual_initialized_before_boundary_support N C sample register H gamma common r
    (C.age v) (original_date_scheduled N C v) hd
  have below (x : Copy) (hy : C.age (N.leaf (sample x)) < C.age v) :
      BelowMeeting N C v (copyLocation (state d) x) := by
    apply actual_initialized_take_below N C H gamma common v sample register r x hy
      (beforeBoundaryProgram N C H gamma common (C.age v)).length
    simpa only [List.take_length] using hd
  constructor
  · intro x hx
    apply mandatory_child_of_ready_below N C d x v ei hg.leftSource
      (by simpa only [hi x hx] using hg.leftOnEveryPath) hready.1
    apply below
    rw [hi x hx]
    exact mandatory_child_tip_younger N C i v ei hg.leftSource hg.leftOnEveryPath
  · intro y hy
    apply mandatory_child_of_ready_below N C d y v ej hg.rightSource
      (by simpa only [hj y hy] using hg.rightOnEveryPath) hready.1
    apply below
    rw [hj y hy]
    exact mandatory_child_tip_younger N C j v ej hg.rightSource hg.rightOnEveryPath

/-- The former two physical premises are now derived from the actual initializer. -/
theorem actual_initialized_literal_agenda (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (sample : Copy → X) (register : V → Bool)
    (r : PositivePairRates E) {i j : X} {v : V} {ei ej : E}
    (hg : RouteMeetingGeometry N i j v ei ej) (inside outside : Finset Copy)
    (hi : ∀ x ∈ inside, sample x = i) (hj : ∀ y ∈ outside, sample y = j) :
    SeparatedAgenda N r inside outside (literalPrefix N C H gamma common v ei ej)
      (initialCode N sample register) := by
  apply literal_agenda_of_before_boundary_inputs N C H gamma common r v ei ej
    inside outside (initialCode N sample register) hg.childDistinct
  · exact actual_initialized_before_agenda N C H gamma common sample register r hg inside outside hi hj
  · intro d hd
    exact actual_initialized_before_children N C H gamma common sample register r hg inside outside hi hj hd

theorem actual_initialized_literal_colocates (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (sample : Copy → X) (register : V → Bool)
    (r : PositivePairRates E) {i j : X} {v : V} {ei ej : E}
    (hg : RouteMeetingGeometry N i j v ei ej) (inside outside : Finset Copy)
    (hi : ∀ x ∈ inside, sample x = i) (hj : ∀ y ∈ outside, sample y = j)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (literalPrefix N C H gamma common v ei ej)
      (initialCode N sample register)).support) :
    ∀ x ∈ inside ∪ outside, copyLocation (state d) x = .node v := by
  rw [literalPrefix, sourceProgram_append] at hd
  obtain ⟨z, hz, hzd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hc := actual_initialized_before_children N C H gamma common sample register r hg inside outside hi hj hz
  exact last_child_exit_colocates N C r v ei ej hg.leftSource hg.rightSource inside outside z d hc.1 hc.2 hzd

#print axioms actual_initialized_take_below
#print axioms actual_initialized_before_agenda
#print axioms actual_initialized_before_children
#print axioms actual_initialized_literal_agenda
#print axioms actual_initialized_literal_colocates
end DotG4.ActualBelowMeetingSupport
