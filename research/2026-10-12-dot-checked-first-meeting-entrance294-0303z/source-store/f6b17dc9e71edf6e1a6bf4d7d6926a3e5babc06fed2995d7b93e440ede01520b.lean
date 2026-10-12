import G5SafePrefixRouteBridge
import G1NonrootBigonKernel

/-!
# Every supported fixed-bank COMMON prefix follows its original selector

Source-only composition proposal, 11 October 2026. No compiler was invoked.
The definitions of selector suffix/location, boundary agreement, and compiled
calendar agreement are reused verbatim from G5SafePrefixRouteBridge (46a8a090).
The new induction uses G1NonrootBigonKernel.actual_time_copy_population and
G1ContextualForestReplacement.actual_time_register_support for EVERY supported
epoch endpoint. It does not restrict the source to its chosen no-merger witness.
The second source version first derives equality of every copy's actual location
with the old deterministic reference prefix, then reuses its selector theorem.
The full first version (16d191dd) is retained separately and was never compiled.

No calibrated RouteMeetingGeometry, fixed meeting across banks, topology moment,
private-cell law, root-completion transport, or new transition kernel is assumed
or proved. The small syntactic COMMON-only guard excludes independent pulses.
The original finite Code, carried ordered trees, register, graph, parent edge
occurrences, and literal program remain the actual source's own objects.

The independently mentioned draft6363f039 has not yet been supplied in full.
This separately attributed proposal must be compared with that original before
choosing any target; neither original draft nor this proposal is accepted here.
-/

namespace GProgram.G4.ActualCommonSelectorSupport
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceInitializedCalendar
open GProgram.G5.SafePrefixRouteBridge
open G1ContextualForestReplacement
open scoped Classical NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- A structural operation guard, not an assumed destination or probability law. -/
def CommonOnlyBoundary (N : RootedBinary V E X) : BoundaryOperation N → Prop
  | .independent _ _ => False
  | _ => True

def CommonOnlyWord (N : RootedBinary V E X) : List (ProgramStep N) → Prop
  | [] => True
  | .interval _ :: ops => CommonOnlyWord N ops
  | .boundary b :: ops => CommonOnlyBoundary N b ∧ CommonOnlyWord N ops

lemma commonOnlyWord_append (N : RootedBinary V E X)
    (xs ys : List (ProgramStep N)) :
    CommonOnlyWord N (xs ++ ys) ↔ CommonOnlyWord N xs ∧ CommonOnlyWord N ys := by
  induction xs with
  | nil => simp [CommonOnlyWord]
  | cons op ops ih => cases op <;> simp [CommonOnlyWord, ih, and_assoc]

/-- In a COMMON-only boundary, all supported destinations are the original
deterministic Code operation, including the stored-bit COMMON pulse. -/
lemma actual_common_boundary_destination (N : RootedBinary V E X)
    {sample : Copy → X} (b : BoundaryOperation N)
    (hb : CommonOnlyBoundary N b) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N b s).support) :
    d = fixedRegisterBoundary N b s := by
  cases b with
  | exit e => simpa only [boundaryKernel, fixedRegisterBoundary,
      PMF.mem_support_pure_iff] using hd
  | ordinary e degree => simpa only [boundaryKernel, fixedRegisterBoundary,
      PMF.mem_support_pure_iff] using hd
  | root => simpa only [boundaryKernel, fixedRegisterBoundary,
      PMF.mem_support_pure_iff] using hd
  | common H => simpa only [boundaryKernel, fixedRegisterBoundary,
      PMF.mem_support_pure_iff] using hd
  | independent H gamma => exact False.elim hb

/-- The inherited deterministic boundary reads only the original bank and the
copy's population for its location update, not the carried genealogy shape. -/
lemma fixedRegisterBoundary_copyLocation_congr (N : RootedBinary V E X)
    {sample : Copy → X} (b : BoundaryOperation N) (s t : Code N sample)
    (hreg : (state s).register = (state t).register)
    (hloc : ∀ x, copyLocation (state s) x = copyLocation (state t) x) :
    ∀ x, copyLocation (state (fixedRegisterBoundary N b s)) x =
      copyLocation (state (fixedRegisterBoundary N b t)) x := by
  intro x
  rw [fixedRegisterBoundary_copyLocation, fixedRegisterBoundary_copyLocation,
    hreg, hloc x]

/-- Value congruence of the already defined reference prefix. No new route or
kernel recurrence is introduced. -/
lemma fixedRegisterPrefix_copyLocation_congr (N : RootedBinary V E X)
    {sample : Copy → X} (ops : List (ProgramStep N)) (s t : Code N sample)
    (hreg : (state s).register = (state t).register)
    (hloc : ∀ x, copyLocation (state s) x = copyLocation (state t) x) :
    ∀ x, copyLocation (state (fixedRegisterPrefix N ops s)) x =
      copyLocation (state (fixedRegisterPrefix N ops t)) x := by
  induction ops generalizing s t with
  | nil => exact hloc
  | cons op ops ih =>
      cases op with
      | interval duration => exact ih s t hreg hloc
      | boundary b =>
          exact ih (fixedRegisterBoundary N b s) (fixedRegisterBoundary N b t)
            ((fixedRegisterBoundary_register N b s).trans
              (hreg.trans (fixedRegisterBoundary_register N b t).symm))
            (fixedRegisterBoundary_copyLocation_congr N b s t hreg hloc)

/-- Actual COMMON locations are deterministic conditional on the entering
original bank, despite all the mergers in the supported full-Code law.
Neither genealogy equality nor a no-merger condition is asserted. -/
theorem actual_common_program_copy_locations (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hcommon : CommonOnlyWord N ops) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r ops s).support) :
    ∀ x, copyLocation (state d) x =
      copyLocation (state (fixedRegisterPrefix N ops s)) x := by
  induction ops generalizing s with
  | nil =>
      have he : d = s := by
        simpa only [sourceProgram, PMF.mem_support_pure_iff] using hd
      subst d
      exact fun _ => rfl
  | cons op ops ih =>
      obtain ⟨z, hz, hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      cases op with
      | interval duration =>
          have htail := ih hcommon z hdz
          have href := fixedRegisterPrefix_copyLocation_congr N ops z s
            (actual_time_register_support N r duration s hz)
            (fun x => G1NonrootBigonKernel.actual_time_copy_population
              N r duration s hz x)
          exact fun x => (htail x).trans (href x)
      | boundary b =>
          have he := actual_common_boundary_destination N b hcommon.1 s hz
          subst z
          exact ih hcommon.2 (fixedRegisterBoundary N b s) hdz

/-- If two original labels share a population, the inherited reference word
keeps them together. The statement is about labels in carried roots, not only
the current surviving representative IDs. -/
lemma fixedRegisterPrefix_cooccupancy (N : RootedBinary V E X)
    {sample : Copy → X} (ops : List (ProgramStep N)) (s : Code N sample)
    (x y : Copy) (hxy : copyLocation (state s) x = copyLocation (state s) y) :
    copyLocation (state (fixedRegisterPrefix N ops s)) x =
      copyLocation (state (fixedRegisterPrefix N ops s)) y := by
  induction ops generalizing s with
  | nil => exact hxy
  | cons op ops ih =>
      cases op with
      | interval duration => exact ih s hxy
      | boundary b =>
          apply ih (fixedRegisterBoundary N b s)
          rw [fixedRegisterBoundary_copyLocation, fixedRegisterBoundary_copyLocation, hxy]

/-- At this bank's own meeting, shared occupancy persists in EVERY supported
COMMON future. This does not relocate the state to the ancestral root or supply
a completed topology probability. -/
theorem actual_common_program_cooccupancy (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hcommon : CommonOnlyWord N ops) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r ops s).support) (x y : Copy)
    (hxy : copyLocation (state s) x = copyLocation (state s) y) :
    copyLocation (state d) x = copyLocation (state d) y := by
  rw [actual_common_program_copy_locations N r ops hcommon s hd x,
    actual_common_program_copy_locations N r ops hcommon s hd y]
  exact fixedRegisterPrefix_cooccupancy N ops s x y hxy

/-- The missing quantifier relative to the older fixedRegisterPrefix witness:
EVERY supported actual endpoint obeys the same original selector, with arbitrary
mergers and arbitrary carried entering genealogy. -/
theorem actual_common_program_selector_support (N : RootedBinary V E X)
    {sample : Copy → X} (P : IncomingSelector N) (reg : V → Bool)
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hagrees : WordAgrees N P reg ops) (hcommon : CommonOnlyWord N ops)
    (s : Code N sample) (hreg : (state s).register = reg)
    (hloc : ∀ x, SelectorLocation N P (sample x) (copyLocation (state s) x))
    {d : Code N sample} (hd : d ∈ (sourceProgram N r ops s).support) :
    ∀ x, SelectorLocation N P (sample x) (copyLocation (state d) x) := by
  intro x
  rw [actual_common_program_copy_locations N r ops hcommon s hd x]
  exact fixedRegisterPrefix_preserves_selector N P reg ops hagrees s hreg hloc x

lemma actual_common_node_only (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (v : V) :
    CommonOnlyBoundary N (originalNodeOperation N H gamma (fun _ => true) v) := by
  by_cases hr : v = N.root
  · simp [originalNodeOperation, hr, CommonOnlyBoundary]
  · by_cases hh : N.graph.IsHybrid v <;>
      simp [originalNodeOperation, hr, hh, CommonOnlyBoundary]

lemma commonOnlyWord_boundary_map (N : RootedBinary V E X)
    {A : Type*} (f : A → BoundaryOperation N)
    (hf : ∀ a, CommonOnlyBoundary N (f a)) (xs : List A) :
    CommonOnlyWord N (xs.map (fun a => ProgramStep.boundary (f a))) := by
  induction xs with
  | nil => trivial
  | cons a xs ih => exact ⟨hf a, ih⟩

lemma actual_common_batch_only (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (a : ℝ) :
    CommonOnlyWord N (boundaryOperations N C H gamma (fun _ => true) a) := by
  unfold boundaryOperations
  apply (commonOnlyWord_append N _ _).mpr
  exact ⟨commonOnlyWord_boundary_map N (fun e => .exit e) (fun _ => trivial) _,
    commonOnlyWord_boundary_map N _ (actual_common_node_only N H gamma) _⟩

lemma actual_common_calendar_tail_only (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (a : ℝ) (dates : List ℝ) :
    CommonOnlyWord N (calendarTail N C H gamma (fun _ => true) a dates) := by
  induction dates generalizing a with
  | nil => trivial
  | cons b dates ih =>
      change CommonOnlyWord N
        (boundaryOperations N C H gamma (fun _ => true) b ++
          calendarTail N C H gamma (fun _ => true) b dates)
      exact (commonOnlyWord_append N _ _).mpr
        ⟨actual_common_batch_only N C H gamma b, ih b⟩

lemma actual_common_compiled_word_only (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) :
    CommonOnlyWord N (compiledCalendarProgram N C H gamma (fun _ => true)) := by
  unfold compiledCalendarProgram
  cases sortedOriginalDates N C with
  | nil => trivial
  | cons a dates =>
      exact (commonOnlyWord_append N _ _).mpr
        ⟨actual_common_batch_only N C H gamma a,
          actual_common_calendar_tail_only N C H gamma a dates⟩

/-- Fixed before all operations: the bank is the source's original once-stored
bank. Every actual supported literal prefix endpoint retains it and follows it.
Serial/negative tip ages, unrelated date ties, mergers, and arbitrary Copy size
require no contemporaneous-tip or no-merger guard. -/
theorem actual_fixed_bank_common_prefix_support (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool)
    (past future : List (ProgramStep N))
    (hprefix : compiledCalendarProgram N C H gamma (fun _ => true) = past ++ future)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r past
      (initialCode N sample (originalRegister N coin))).support) :
    (state d).register = originalRegister N coin ∧
      ∀ x, SelectorLocation N (coinSelector N H coin) (sample x)
        (copyLocation (state d) x) := by
  have hword : WordAgrees N (coinSelector N H coin) (originalRegister N coin)
      (past ++ future) := by
    rw [← hprefix]
    exact actual_compiled_word_agrees N C H gamma (fun _ => true) coin
  have hcommon : CommonOnlyWord N (past ++ future) := by
    rw [← hprefix]
    exact actual_common_compiled_word_only N C H gamma
  refine ⟨actual_program_register_support N r past _ hd, ?_⟩
  apply actual_common_program_selector_support N (coinSelector N H coin)
    (originalRegister N coin) r past ((wordAgrees_append N _ _ _ _).mp hword).1
    ((commonOnlyWord_append N past future).mp hcommon).1 _ rfl _ hd
  intro x
  have hx : copyLocation (state (initialCode N sample (originalRegister N coin))) x =
      .node (N.leaf (sample x)) :=
    UnifiedLean.Source.FiniteSourceSnapshot.decode_encode_copyLocation N.root
      (initial N sample (originalRegister N coin))
      (initial_source_valid N sample (originalRegister N coin)).forest x
  rw [hx]
  exact selected_suffix_tip N (coinSelector N H coin) (sample x)

/-- The occupied occurrence belongs to this SAME bank's compiled original route;
the older per-copy route-existence theorem alone did not fix a common bank. -/
theorem actual_fixed_bank_occupied_edge_on_route (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool)
    (past future : List (ProgramStep N))
    (hprefix : compiledCalendarProgram N C H gamma (fun _ => true) = past ++ future)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r past
      (initialCode N sample (originalRegister N coin))).support)
    (x : Copy) (e : E) (he : copyLocation (state d) x = .edge e) :
    e ∈ compiledRoute N C (coinSelector N H coin) (N.leaf (sample x)) := by
  have hx := (actual_fixed_bank_common_prefix_support N C sample H gamma r coin
    past future hprefix hd).2 x
  rw [he] at hx
  exact selectorLocation_edge_mem_compiled N C (coinSelector N H coin) (sample x) e hx

/-- Actual natural initialization is disintegrated once, not replaced by a fresh
bank at each operation. This existential is only the supported endpoint's bank;
the conditional theorem above applies universally to every supplied fixed bank. -/
theorem actual_natural_common_prefix_support (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (past future : List (ProgramStep N))
    (hprefix : compiledCalendarProgram N C H (originalGamma p) (fun _ => true) =
      past ++ future) {d : Code N sample}
    (hd : d ∈ ((originalRegisterPMF N p).bind (fun reg =>
      sourceProgram N r past (initialCode N sample reg))).support) :
    ∃ coin : Hybrid N → Bool,
      (state d).register = originalRegister N coin ∧
        ∀ x, SelectorLocation N (coinSelector N H coin) (sample x)
          (copyLocation (state d) x) := by
  obtain ⟨reg, hreg, hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  change reg ∈ (((originalRegisterMeasure N p).toPMF).map
    (originalRegister N)).support at hreg
  obtain ⟨coin, _, hcoin⟩ := (PMF.mem_support_map_iff _ _ _).mp hreg
  rw [← hcoin] at hdr
  exact ⟨coin, actual_fixed_bank_common_prefix_support N C sample H (originalGamma p)
    r coin past future hprefix hdr⟩

end GProgram.G4.ActualCommonSelectorSupport
