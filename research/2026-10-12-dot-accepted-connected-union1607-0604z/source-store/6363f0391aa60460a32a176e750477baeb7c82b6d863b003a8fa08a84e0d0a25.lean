import G5SafePrefixRouteBridge
import G1NonrootBigonKernel
import ActualStoredRegister

/-!
Actual COMMON prefix support follows its original retained selector.
Contributor: dot (OpenAI), 11 October 2026. UNCOMPILED SOURCE DRAFT.

The existing fixedRegisterPrefix is a no-merger support witness. This module
derives the same selector-location invariant for EVERY supported state of the
actual all-COMMON source prefix, including states with mergers. It assumes no
calibrated meeting geometry, no desired moment identity, and no observed route.
The entering original bank is fixed for this conditional theorem. Averaging
over that bank is not an assertion of independent mixture factors.
-/

namespace DotG4.ActualCommonPrefixSelector

open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization
open GProgram.G5.SafePrefixRouteBridge
open DotG34.ActualStoredRegister
open scoped Classical NNReal

variable {V E Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

def CommonBoundary (N : RootedBinary V E X) : BoundaryOperation N → Prop
  | .independent _ _ => False
  | _ => True

def CommonStep (N : RootedBinary V E X) : ProgramStep N → Prop
  | .interval _ => True
  | .boundary b => CommonBoundary N b

def CommonOnly (N : RootedBinary V E X) (ops : List (ProgramStep N)) : Prop :=
  ∀ op ∈ ops, CommonStep N op

lemma commonOnly_append (N : RootedBinary V E X) (xs ys : List (ProgramStep N)) :
    CommonOnly N (xs ++ ys) ↔ CommonOnly N xs ∧ CommonOnly N ys := by
  constructor
  · intro h
    exact ⟨fun op hop => h op (List.mem_append_left _ hop),
      fun op hop => h op (List.mem_append_right _ hop)⟩
  · rintro ⟨hx, hy⟩ op hop
    rcases List.mem_append.mp hop with hop | hop
    · exact hx op hop
    · exact hy op hop

lemma actual_common_node (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (v : V) :
    CommonBoundary N (originalNodeOperation N H gamma (fun _ => true) v) := by
  by_cases hr : v = N.root
  · simp [originalNodeOperation, hr, CommonBoundary]
  · by_cases hh : N.graph.IsHybrid v
    · simp [originalNodeOperation, hr, hh, CommonBoundary]
    · simp [originalNodeOperation, hr, hh, CommonBoundary]

lemma actual_common_batch (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (a : ℝ) :
    CommonOnly N (boundaryOperations N C H gamma (fun _ => true) a) := by
  intro op hop
  rcases List.mem_append.mp hop with hop | hop
  · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hop
    trivial
  · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hop
    exact actual_common_node N H gamma v

lemma actual_common_tail (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (a : ℝ) (dates : List ℝ) :
    CommonOnly N (calendarTail N C H gamma (fun _ => true) a dates) := by
  induction dates generalizing a with
  | nil => intro op hop; simp only [calendarTail, List.not_mem_nil] at hop
  | cons b dates ih =>
      intro op hop
      rcases List.mem_cons.mp hop with he | hop
      · subst op; trivial
      · exact ((commonOnly_append N _ _).mpr
          ⟨actual_common_batch N C H gamma b, ih b⟩) op hop

theorem actual_common_calendar (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) :
    CommonOnly N (compiledCalendarProgram N C H gamma (fun _ => true)) := by
  unfold compiledCalendarProgram
  cases sortedOriginalDates N C with
  | nil => intro op hop; exact False.elim (List.not_mem_nil hop)
  | cons a dates =>
      exact (commonOnly_append N _ _).mpr
        ⟨actual_common_batch N C H gamma a, actual_common_tail N C H gamma a dates⟩

lemma common_boundary_kernel (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (hb : CommonBoundary N b) (s : Code N sample) :
    boundaryKernel N b s = PMF.pure (fixedRegisterBoundary N b s) := by
  cases b <;> simp_all only [CommonBoundary, boundaryKernel, fixedRegisterBoundary]

lemma actual_step_register_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s d : Code N sample)
    (hd : d ∈ (sourceProgramStep N r op s).support) :
    (state d).register = (state s).register := by
  apply actual_program_register_support N r [op] s d
  simpa only [sourceProgram, PMF.bind_pure] using hd

/-- All mergers are allowed. Only actual current-copy locations and the
retained entering register are used in the induction. -/
theorem actual_common_program_preserves_selector
    (N : RootedBinary V E X) {sample : Copy → X}
    (P : IncomingSelector N) (reg : V → Bool) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (hc : CommonOnly N ops)
    (ha : WordAgrees N P reg ops) (s : Code N sample)
    (hr : (state s).register = reg)
    (hl : ∀ x, SelectorLocation N P (sample x) (copyLocation (state s) x))
    {d : Code N sample} (hd : d ∈ (sourceProgram N r ops s).support) :
    ∀ x, SelectorLocation N P (sample x) (copyLocation (state d) x) := by
  induction ops generalizing s with
  | nil =>
      have he : d = s := by
        simpa only [sourceProgram, PMF.mem_support_pure_iff] using hd
      subst d
      exact hl
  | cons op ops ih =>
      obtain ⟨z, hz, hzd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have htail : CommonOnly N ops :=
        fun q hq => hc q (List.mem_cons_of_mem op hq)
      have hrz : (state z).register = reg :=
        (actual_step_register_support N r op s z hz).trans hr
      cases op with
      | interval t =>
          apply ih htail ha z hrz ?_ hzd
          intro x
          rw [G1NonrootBigonKernel.actual_time_copy_population N r t s hz x]
          exact hl x
      | boundary b =>
          have hb : CommonBoundary N b := hc _ List.mem_cons_self
          have he : z = fixedRegisterBoundary N b s := by
            rw [sourceProgramStep, common_boundary_kernel N b hb s] at hz
            simpa only [PMF.mem_support_pure_iff] using hz
          apply ih htail ha.2 z hrz ?_ hzd
          intro x
          rw [he, fixedRegisterBoundary_copyLocation, hr]
          exact fixedBoundaryLocation_preserves_selector N P reg b ha.1 (sample x) _ (hl x)

/-- The physical initialized COMMON prefix, for every supported state and
every original copy. No meeting record or no-merger event is assumed. -/
theorem actual_common_prefix_follows_original_selector
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool)
    (past future : List (ProgramStep N))
    (hp : compiledCalendarProgram N C H gamma (fun _ => true) = past ++ future)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r past
      (initialCode N sample (originalRegister N coin))).support) :
    ∀ x, SelectorLocation N (coinSelector N H coin) (sample x)
      (copyLocation (state d) x) := by
  have hc : CommonOnly N (past ++ future) := by
    rw [← hp]
    exact actual_common_calendar N C H gamma
  have ha : WordAgrees N (coinSelector N H coin) (originalRegister N coin)
      (past ++ future) := by
    rw [← hp]
    exact actual_compiled_word_agrees N C H gamma (fun _ => true) coin
  apply actual_common_program_preserves_selector N (coinSelector N H coin)
    (originalRegister N coin) r past ((commonOnly_append N past future).mp hc).1
    ((wordAgrees_append N _ _ past future).mp ha).1 _ rfl ?_ hd
  intro x
  have hloc : copyLocation (state (initialCode N sample (originalRegister N coin))) x =
      .node (N.leaf (sample x)) := by
    exact UnifiedLean.Source.FiniteSourceSnapshot.decode_encode_copyLocation N.root
      (initial N sample (originalRegister N coin))
      (initial_source_valid N sample (originalRegister N coin)).forest x
  rw [hloc]
  exact selected_suffix_tip N (coinSelector N H coin) (sample x)

/-- The conclusion also identifies the actual original edge occurrence in
the compiled source route whenever a supported copy is on an edge. -/
theorem actual_common_prefix_edge_on_original_route
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool)
    (past future : List (ProgramStep N))
    (hp : compiledCalendarProgram N C H gamma (fun _ => true) = past ++ future)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r past
      (initialCode N sample (originalRegister N coin))).support)
    (x : Copy) (e : E) (he : copyLocation (state d) x = .edge e) :
    e ∈ compiledRoute N C (coinSelector N H coin) (N.leaf (sample x)) := by
  apply selectorLocation_edge_mem_compiled N C (coinSelector N H coin) (sample x) e
  rw [← he]
  exact actual_common_prefix_follows_original_selector N C sample H gamma r coin
    past future hp hd x

#print axioms actual_common_calendar
#print axioms actual_common_program_preserves_selector
#print axioms actual_common_prefix_follows_original_selector
#print axioms actual_common_prefix_edge_on_original_route

end DotG4.ActualCommonPrefixSelector
