import G4LiteralLastChildExitCut

/-! SOURCE-ONLY, UNCOMPILED. Lean reuse consumer, 2026-10-11.
No compiler/parser/target process has checked this draft. The original
calendar/date/program and actual location laws are unchanged. This module
only supplies strict younger-location support at every literal earlier
prefix, then applies the existing conditional source separator. Graph meeting
geometry/calibration, child-edge endpoint binding, and native refinement are
separate. No contemporary/zero-tip-age, nonempty-cohort or nonroot premise. -/
namespace G4InitializedBeforeBoundaryPrefixes
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceInitializedCalendar
open G1InitializedFrontierPrefix G1NonrootBigonKernel G1ActualJointProgram
open G1JointSeparatedSourceGeometry G4LiteralLastChildExitCutDraft
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- A witness extracted from the actual original earlier-date word. Intervals
may have any duration: their actual copy populations are invariant. -/
def EarlierCalendarStep (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (op : ProgramStep N) : Prop :=
  (∃ t : ℝ≥0, op = .interval t) ∨
  (∃ e : E, C.age (N.graph.source e) < C.age v ∧ op = .boundary (.exit e)) ∨
  (∃ w : V, C.age w < C.age v ∧
    op = .boundary (originalNodeOperation N H gamma common w))

lemma earlier_boundary_operations (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (a : ℝ) (ha : a < C.age v) :
    ∀ op ∈ boundaryOperations N C H gamma common a,
      EarlierCalendarStep N C H gamma common v op := by
  intro op hop
  rw [boundaryOperations] at hop
  rcases List.mem_append.mp hop with hexit | hnode
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hexit
    have hage : C.age (N.graph.source e) = a :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
    exact Or.inr (Or.inl ⟨e, by rw [hage]; exact ha, rfl⟩)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hnode
    have hage : C.age w = a :=
      (Finset.mem_filter.mp (Finset.mem_toList.mp hw)).2
    exact Or.inr (Or.inr ⟨w, by rw [hage]; exact ha, rfl⟩)

/-- No earlier-date batch is reconstructed: membership is read from the
unchanged stopBeforeTail recursion and strict original date list. -/
lemma earlier_stop_before_tail (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (dates : List ℝ)
    (horder : dates.Pairwise (· < ·)) (hstop : C.age v ∈ dates) (a : ℝ) :
    ∀ op ∈ stopBeforeTail N C H gamma common (C.age v) a dates,
      EarlierCalendarStep N C H gamma common v op := by
  induction dates generalizing a with
  | nil => exact False.elim (List.not_mem_nil hstop)
  | cons b bs ih =>
      have hp := List.pairwise_cons.mp horder
      intro op hop
      by_cases hb : b = C.age v
      · have heq : op = .interval (Real.toNNReal (b-a)) := by
          simpa only [stopBeforeTail, if_pos hb, List.mem_singleton] using hop
        exact Or.inl ⟨_, heq⟩
      · have hstop' : C.age v ∈ bs :=
          (List.mem_cons.mp hstop).resolve_left (Ne.symm hb)
        have hbstop : b < C.age v := hp.1 _ hstop'
        have hop' : op = .interval (Real.toNNReal (b-a)) ∨
            op ∈ boundaryOperations N C H gamma common b ++
              stopBeforeTail N C H gamma common (C.age v) b bs := by
          simpa only [stopBeforeTail, if_neg hb, List.mem_cons] using hop
        rcases hop' with hinterval | hrest
        · exact Or.inl ⟨_, hinterval⟩
        · rcases List.mem_append.mp hrest with hbatch | htail
          · exact earlier_boundary_operations N C H gamma common v b hbstop op hbatch
          · exact ih hp.2 hstop' b op htail

/-- Pure original-list chronology, including a stop at the earliest date. -/
theorem earlier_before_boundary_operations (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (v : V) :
    ∀ op ∈ beforeBoundaryProgram N C H gamma common (C.age v),
      EarlierCalendarStep N C H gamma common v op := by
  have hstop := original_date_scheduled N C v
  have hne : sortedOriginalDates N C ≠ [] := by
    intro hnil
    rw [hnil] at hstop
    exact List.not_mem_nil hstop
  obtain ⟨a, dates, hdates⟩ := List.exists_cons_of_ne_nil hne
  have horder := original_dates_strict N C
  rw [hdates] at hstop horder
  have hp := List.pairwise_cons.mp horder
  intro op hop
  by_cases ha : a = C.age v
  · have hempty : beforeBoundaryProgram N C H gamma common (C.age v) = [] := by
      simp only [beforeBoundaryProgram, hdates, if_pos ha]
    rw [hempty] at hop
    exact False.elim (List.not_mem_nil hop)
  · have hstop' : C.age v ∈ dates :=
      (List.mem_cons.mp hstop).resolve_left (Ne.symm ha)
    have hastop : a < C.age v := hp.1 _ hstop'
    have hop' : op ∈ boundaryOperations N C H gamma common a ++
        stopBeforeTail N C H gamma common (C.age v) a dates := by
      simpa only [beforeBoundaryProgram, hdates, if_neg ha] using hop
    rcases List.mem_append.mp hop' with hbatch | htail
    · exact earlier_boundary_operations N C H gamma common v a hastop op hbatch
    · exact earlier_stop_before_tail N C H gamma common v dates hp.2 hstop' a op htail

/-- An actual original node operation at a strictly younger date preserves
BelowMeeting for this copy. Root movement is covered at its ACTUAL node age. -/
lemma node_movement_below_meeting (N : RootedBinary V E X) (C : Calendar N.graph)
    (v w : V) {old new : Location V E} (hw : C.age w < C.age v)
    (hold : BelowMeeting N C v old) (hm : NodeMovement N w old new) :
    BelowMeeting N C v new := by
  unfold NodeMovement at hm
  by_cases hn : old = .node w
  · rw [if_pos hn] at hm
    by_cases hr : w = N.root
    · rw [if_pos hr] at hm
      rw [hm]
      change C.age N.root < C.age v
      simpa only [hr] using hw
    · rw [if_neg hr] at hm
      obtain ⟨e, htarget, hnew⟩ := hm
      rw [hnew]
      change C.age (N.graph.target e) < C.age v
      rw [htarget]
      exact hw
  · rw [if_neg hn] at hm
    rw [hm]
    exact hold

/-- Reuses actual continuous-time population invariance and original boundary
movement; no new generator, routed path family or count conditioning. -/
lemma actual_earlier_step_below_meeting (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (v : V) (op : ProgramStep N)
    (hop : EarlierCalendarStep N C H gamma common v op) (s : Code N sample)
    (x : Copy) (hs : BelowMeeting N C v (copyLocation (state s) x))
    {d : Code N sample} (hd : d ∈ (sourceProgramStep N r op s).support) :
    BelowMeeting N C v (copyLocation (state d) x) := by
  rcases hop with ⟨t, rfl⟩ | ⟨e, he, rfl⟩ | ⟨w, hw, rfl⟩
  · have htime : d ∈ (sourceTimeKernel N r t s).support := by
      simpa only [sourceProgramStep] using hd
    rw [actual_time_copy_population N r t s htime x]
    exact hs
  · have hds : d = exitCode N s e := by
      simpa only [sourceProgramStep, boundaryKernel, PMF.mem_support_pure_iff] using hd
    subst d
    rw [exitCode_copyLocation]
    unfold exitLocation
    by_cases hp : copyLocation (state s) x = .edge e
    · rw [if_pos hp]
      change C.age (N.graph.source e) < C.age v
      exact he
    · rw [if_neg hp]
      exact hs
  · have hnode : d ∈ (boundaryKernel N (originalNodeOperation N H gamma common w) s).support := by
      simpa only [sourceProgramStep] using hd
    exact node_movement_below_meeting N C v w hw hs
      (actual_original_node_kernel_movement N H gamma common w s hnode x)

/-- Finite bind-support induction on ACTUAL source steps only. -/
lemma actual_earlier_program_below_meeting (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (v : V) (ops : List (ProgramStep N))
    (hops : ∀ op ∈ ops, EarlierCalendarStep N C H gamma common v op)
    (s : Code N sample) (x : Copy)
    (hs : BelowMeeting N C v (copyLocation (state s) x)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r ops s).support) :
    BelowMeeting N C v (copyLocation (state d) x) := by
  induction ops generalizing s with
  | nil =>
      have hds : d = s := by
        simpa only [sourceProgram, PMF.mem_support_pure_iff] using hd
      rw [hds]
      exact hs
  | cons op ops ih =>
      change d ∈ ((sourceProgramStep N r op s).bind (sourceProgram N r ops)).support at hd
      obtain ⟨m, hm, hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih (fun q hq => hops q (List.mem_cons_of_mem op hq)) m
        (actual_earlier_step_below_meeting N C H gamma common r v op
          (hops op (by simp)) s x hs hm) hdm

/-- EVERY literal take-prefix, including n=length and n>length. Samples retain
all original ages and carried genealogy; no phase permutation is used. -/
theorem actual_initialized_before_boundary_prefix_below (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (v : V) (sample : Copy → X) (register : V → Bool)
    (keep : Finset Copy) (hleaf : ∀ x ∈ keep, C.age (N.leaf (sample x)) < C.age v)
    (n : Nat) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      ((beforeBoundaryProgram N C H gamma common (C.age v)).take n)
      (initialCode N sample register)).support) :
    ∀ x ∈ keep, BelowMeeting N C v (copyLocation (state d) x) := by
  intro x hx
  have hops : ∀ op ∈ (beforeBoundaryProgram N C H gamma common (C.age v)).take n,
      EarlierCalendarStep N C H gamma common v op := by
    intro op hop
    exact earlier_before_boundary_operations N C H gamma common v op
      (List.mem_of_mem_take hop)
  have hinitial : BelowMeeting N C v
      (copyLocation (state (initialCode N sample register)) x) := by
    have hpop : copyLocation (state (initialCode N sample register)) x =
        .node (N.leaf (sample x)) :=
      decode_encode_copyLocation N.root _ (initial_source_valid N sample register).forest x
    rw [hpop]
    exact hleaf x hx
  exact actual_earlier_program_below_meeting N C H gamma common r v _ hops
    (initialCode N sample register) x hinitial hd

/-- All-path child membership implies younger tips from the existing rooted
path and strict original edge calendar, not a tip-age convention. -/
lemma meeting_sample_age_lt (N : RootedBinary V E X) (C : Calendar N.graph)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej) :
    C.age (N.leaf i) < C.age v ∧ C.age (N.leaf j) < C.age v := by
  constructor
  · obtain ⟨es, hp⟩ := original_tip_route_exists N i
    have hd := hp.target_reaches_end_of_mem (hg.leftOnEveryPath es hp)
    have hage := (C.age_le_of_directed hd).trans_lt (C.edge_older ei)
    simpa only [hg.leftSource] using hage
  · obtain ⟨es, hp⟩ := original_tip_route_exists N j
    have hd := hp.target_reaches_end_of_mem (hg.rightOnEveryPath es hp)
    have hage := (C.age_le_of_directed hd).trans_lt (C.edge_older ej)
    simpa only [hg.rightSource] using hage

/-- Discharges the strict support-prefix separator from natural original
sample initialization and supplied graph meeting geometry. Empty cohorts work. -/
theorem actual_initialized_before_boundary_separated_prefixes
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (sample : Copy → X) (register : V → Bool)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (inside outside : Finset Copy)
    (hinside : ∀ x ∈ inside, sample x = i)
    (houtside : ∀ y ∈ outside, sample y = j) :
    SupportedSeparatedPrefixes N r inside outside
      (beforeBoundaryProgram N C H gamma common (C.age v))
      (initialCode N sample register) := by
  intro n hn d hd
  apply source_separated_of_below_meeting N C hg inside outside hinside houtside d
  apply actual_initialized_before_boundary_prefix_below N C H gamma common r v
    sample register inside _ n hd
  intro x hx
  rw [hinside x hx]
  exact (meeting_sample_age_lt N C hg).1

/-- The exact hbefore interface of G4PartialExitSeparation, with no input
separation/desired-law premise. It uses the existing support-to-agenda bridge. -/
theorem actual_initialized_before_boundary_separated_agenda
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (sample : Copy → X) (register : V → Bool)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (inside outside : Finset Copy)
    (hinside : ∀ x ∈ inside, sample x = i)
    (houtside : ∀ y ∈ outside, sample y = j) :
    SeparatedAgenda N r inside outside
      (beforeBoundaryProgram N C H gamma common (C.age v))
      (initialCode N sample register) := by
  exact agenda_of_supported_prefixes N r inside outside _ _
    (actual_initialized_before_boundary_separated_prefixes N C H gamma common r
      sample register hg inside outside hinside houtside)
end G4InitializedBeforeBoundaryPrefixes
