import G1ActualEnteringFrontier

/-! The exact naturally initialized original-calendar prefix at a cut-child
interface. Contributor: dot, 2026-10-03. Programs stop BEFORE a specified
original node batch, after all its original exits. Physical ready/natural node
and strict edge-entry invariants are derived from actual initialization and
sorted original dates, never supplied as stochastic admission fields. -/
namespace G1InitializedFrontierPrefix
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarTiming UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceProgramTransport
open G1NaturalCalendarNodes G1ActualEnteringFrontier G1NonrootBigonKernel
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

noncomputable def stopBeforeTail (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (stop : ℝ) : ℝ → List ℝ → List (ProgramStep N)
  | _,[] => []
  | a,b::bs => if b = stop then [.interval (Real.toNNReal (b-a))]
      else .interval (Real.toNNReal (b-a)) ::
        (boundaryOperations N C H gamma common b ++ stopBeforeTail N C H gamma common stop b bs)

noncomputable def beforeBoundaryProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (stop : ℝ) : List (ProgramStep N) :=
  match sortedOriginalDates N C with
  | [] => []
  | a::as => if a = stop then [] else
      boundaryOperations N C H gamma common a ++ stopBeforeTail N C H gamma common stop a as

noncomputable def actualFrontierProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (stop : ℝ) : List (ProgramStep N) := beforeBoundaryProgram N C H gamma common stop ++
      ((Finset.univ.filter (fun e : E => C.age (N.graph.source e) = stop)).toList.map
        (fun e => .boundary (.exit e)))

def StrictEnteredEdges (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ)
    (s : State V E Copy) : Prop :=
  ∀ x : Copy, ∀ e : E, copyLocation s x = .edge e → C.age (N.graph.target e) < a

def BeforeReady (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (a : ℝ) (s : State V E Copy) : Prop :=
  BoundaryReady N C a s ∧ NaturalState N C sample a s ∧ StrictEnteredEdges N C a s

/-- All invariants BEFORE the selected original date's node batch are derived
from genuine actual earlier batches and intervals in the original chronology. -/
theorem actual_stop_tail_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (dates : List ℝ) (a stop : ℝ)
    (hfuture : FutureComplete N C a dates) (hordered : dates.Pairwise (· < ·))
    (hafter : ∀ b ∈ dates, a < b) (hstop : stop ∈ dates) (s : Code N sample)
    (hs : AfterNodes N C a (state s)) (hn : NaturalState N C sample a (state s))
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (stopBeforeTail N C H gamma common stop a dates) s).support) :
    BeforeReady N C sample stop (state d) := by
  induction dates generalizing a s with
  | nil => exact False.elim (List.not_mem_nil hstop)
  | cons b bs ih =>
      have hab : a < b := hafter b (by simp)
      have hp := List.pairwise_cons.mp hordered
      have hgap : ∀ v : V, a < C.age v → b ≤ C.age v := by
        intro v hv
        rcases List.mem_cons.mp (hfuture v hv) with hv | hv
        · exact hv.ge
        · exact (hp.1 _ hv).le
      have hepoch := after_nodes_to_epoch N C hs hgap
      by_cases hbstop : b = stop
      · subst stop
        have hdtime : d ∈ (sourceTimeKernel N r (Real.toNNReal (b-a)) s).support := by
          simpa [stopBeforeTail,sourceProgram,sourceProgramStep] using hd
        have hc := actual_source_time_epoch_support N C r _ s hepoch hdtime
        have hnat := actual_time_natural N C r _ s a hn hdtime
        exact ⟨epoch_to_next_ready N C hc hab.le,natural_state_mono N C sample hab.le hnat,
          fun x e he => (hnat.2 x e he).trans_lt hab⟩
      · have hstop' : stop ∈ bs := (List.mem_cons.mp hstop).resolve_left (Ne.symm hbstop)
        have hnext : FutureComplete N C b bs := by
          intro v hv
          rcases List.mem_cons.mp (hfuture v (hab.trans hv)) with heq | hmem
          · exact False.elim ((ne_of_gt hv) heq)
          · exact hmem
        have hdstep : d ∈ ((sourceTimeKernel N r (Real.toNNReal (b-a)) s).bind
            (sourceProgram N r (boundaryOperations N C H gamma common b ++
              stopBeforeTail N C H gamma common stop b bs))).support := by
          simpa [stopBeforeTail,hbstop,sourceProgram,sourceProgramStep] using hd
        obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdstep
        have hc := actual_source_time_epoch_support N C r _ s hepoch hm
        have hnat := natural_state_mono N C sample hab.le (actual_time_natural N C r _ s a hn hm)
        rw [sourceProgram_append] at hdm
        obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdm
        have hzphysical := actual_original_boundary_batch_support N C H gamma common r b m
          (epoch_to_next_ready N C hc hab.le) hz
        have hznatural := actual_boundary_batch_natural N C H gamma common r b m hnat hz
        exact ih b hnext hp.2 hp.1 hstop' z hzphysical hznatural hdz

/-- The BEFORE-node prefix is generated from the complete original date list
and real original sample initialization, so its ready/natural/strict-entry
properties are conclusions rather than admission fields. -/
theorem actual_initialized_before_boundary_support (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (stop : ℝ) (hstop : stop ∈ sortedOriginalDates N C)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (beforeBoundaryProgram N C H gamma common stop)
      (initialCode N sample register)).support) : BeforeReady N C sample stop (state d) := by
  have hne : sortedOriginalDates N C ≠ [] := by
    intro heq; rw [heq] at hstop; exact List.not_mem_nil hstop
  obtain ⟨a,dates,heq⟩ := List.exists_cons_of_ne_nil hne
  have hfirst : a = firstOriginalDate N C := by
    have h := first_compiled_date_is_initial_boundary N C
    simpa only [heq,List.getElem_cons_zero] using h
  have hready : BoundaryReady N C a (state (initialCode N sample register)) := by
    rw [hfirst]
    exact actual_initial_calendar_boundary N C sample register
  have hnat := actual_initial_natural N C sample register a
  by_cases ha : a = stop
  · have hdinit : d = initialCode N sample register := by
      simpa [beforeBoundaryProgram,heq,ha,sourceProgram] using hd
    subst d
    subst stop
    refine ⟨hready,hnat,?_⟩
    intro x e he
    have hp : copyLocation (state (initialCode N sample register)) x = .node (N.leaf (sample x)) :=
      decode_encode_copyLocation N.root _ (initial_source_valid N sample register).forest x
    rw [hp] at he
    cases he
  · have hm : stop ∈ dates := by
      rw [heq] at hstop
      exact (List.mem_cons.mp hstop).resolve_left (Ne.symm ha)
    have hord := original_dates_strict N C
    rw [heq] at hord
    have hp := List.pairwise_cons.mp hord
    have hfuture : FutureComplete N C a dates := by
      intro v hv
      have hm := original_date_scheduled N C v
      rw [heq] at hm
      rcases List.mem_cons.mp hm with he | he
      · exact False.elim ((ne_of_gt hv) he)
      · exact he
    have hdappend : d ∈ (sourceProgram N r
        (boundaryOperations N C H gamma common a ++ stopBeforeTail N C H gamma common stop a dates)
          (initialCode N sample register)).support := by
      simpa [beforeBoundaryProgram,heq,ha] using hd
    rw [sourceProgram_append] at hdappend
    obtain ⟨s,hs,hds⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdappend
    have hphysical := actual_original_boundary_batch_support N C H gamma common r a _ hready hs
    have hnatural := actual_boundary_batch_natural N C H gamma common r a _ hnat hs
    exact actual_stop_tail_support N C H gamma common r dates a stop hfuture hp.2 hp.1 hm
      s hphysical hnatural hds

lemma actual_exit_list_strict_entered (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) (es : List E) (a : ℝ) (s : Code N sample)
    (hs : StrictEnteredEdges N C a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (es.map (fun e => .boundary (.exit e))) s).support) :
    StrictEnteredEdges N C a (state d) := by
  induction es generalizing s with
  | nil =>
      have h : d = s := by simpa [sourceProgram] using hd
      exact h ▸ hs
  | cons e es ih =>
      have hdest : d ∈ (sourceProgram N r (es.map (fun e => .boundary (.exit e))) (exitCode N s e)).support := by
        simpa [sourceProgram,sourceProgramStep,boundaryKernel] using hd
      apply ih (exitCode N s e) _ hdest
      intro x f hf
      apply hs x f
      by_contra hn
      exact exit_never_creates_edge N s e f x hn hf

/-- Actual original initialization plus original generated exits place every
supported state at the exact physical current-root interface BEFORE node entry. -/
theorem actual_initialized_frontier_support (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (D : V) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (actualFrontierProgram N C H gamma common (C.age D))
      (initialCode N sample register)).support) :
    AfterExits N C (C.age D) (state d) ∧ NaturalNodes N C sample (C.age D) (state d) ∧
      StrictEnteredEdges N C (C.age D) (state d) := by
  rw [actualFrontierProgram,sourceProgram_append] at hd
  obtain ⟨s,hs,hds⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hbefore := actual_initialized_before_boundary_support N C sample register H gamma common r
    (C.age D) (original_date_scheduled N C D) hs
  have hphysical := actual_exit_batch_support N C r (C.age D) s hbefore.1 hds
  have hnatural := actual_exit_list_natural N C r _ (C.age D) (by
    intro e he; exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2) s hbefore.2.1 hds
  have hstrict := actual_exit_list_strict_entered N C r _ (C.age D) s hbefore.2.2 hds
  exact ⟨hphysical,hnatural.1,hstrict⟩

/-- Full original descendant-labelled frontier identity is now supplied by the
ACTUAL initialized graph/calendar prefix, with no abstract frontier assumptions. -/
theorem actual_initialized_cut_frontier (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (e : E) (he : N.graph.IsBridge e) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (actualFrontierProgram N C H gamma common (C.age (N.graph.target e)))
      (initialCode N sample register)).support) :
    (∀ x : Copy, N.graph.DReach (N.graph.target e) (N.leaf (sample x)) ↔
      copyLocation (state d) x = .node (N.graph.target e)) ∧
    (∀ x ∈ enteringRoots N d (N.graph.target e), copyLocation (state d) x = .node (N.graph.target e)) ∧
    (∀ y ∈ exteriorRoots N d (N.graph.target e),
      ¬ N.graph.DReach (N.graph.target e) (N.leaf (sample y))) := by
  obtain ⟨hphysical,hnatural,hstrict⟩ := actual_initialized_frontier_support N C sample register H gamma common r _ hd
  exact ⟨actual_descendant_interface_location N C e he d hphysical hnatural hstrict,
    actual_current_frontier_owner_binding N C e he d hphysical hnatural hstrict⟩

end G1InitializedFrontierPrefix
