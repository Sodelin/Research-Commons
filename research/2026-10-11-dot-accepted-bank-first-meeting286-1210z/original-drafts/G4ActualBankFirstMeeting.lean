import G4ActualCommonNoLossRoute
import G4ActualColocatedCompletion
import Mathlib.Data.Nat.Find

/-!
# Actual fixed-bank first-meeting cut and its three-copy no-loss exposure

Contributor: dot (OpenAI), 11 October 2026. UNCOMPILED source draft.
This ports the first-meeting portion of the inherited arbitrary-k COMMON
caterpillar proof, not a new theorem of probability or a new observation.

The first cut is constructed from the actual deterministic reference prefix
for one original copy at each of two taxa. Its existence is derived from
actual initialized ancestral support. Every supported larger two-taxon
carrier is then proved co-located at that SAME cut. No calibrated all-bank
RouteMeetingGeometry or desired topology law is an input.

Receiver-owned G4ActualCommonSelectorSupport / G4ActualCommonNoLossRoute
remain statically reviewed, uncompiled dependencies. Their original author
and source semantics are retained. The completed three-copy no-loss weight
below uses the old actual weightedRoute/holding theorem. Identifying general
k exposure with choose(k,2) times this exposure, proving its strict positivity
for distinct taxa, and evaluating the forbidden-clade/completion topology
event remain later bindings; none is inserted as a premise here.
-/

namespace DotG4.ActualBankFirstMeeting
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.FiniteSourceSnapshot
open GProgram.G5.SafePrefixRouteBridge
open GProgram.G4.ActualCommonSelectorSupport
open GProgram.G4.ActualCommonNoLossRoute
open DotG34.ActualSerialSurvival
open DotG4.ActualColocatedCompletion
open scoped Classical NNReal ENNReal

variable {V E X Copy Other Obs : Type*}
variable [DecidableEq V] [DecidableEq E]
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [DecidableEq Other] [Fintype Other]

/-- Deterministic original locations depend on the entering bank and the
original copy's position, independently of the size of its finite carrier. -/
lemma reference_location_cross_carrier (N : RootedBinary V E X)
    {sample : Copy → X} {sample' : Other → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (z : Code N sample')
    (x : Copy) (y : Other)
    (hr : (state s).register = (state z).register)
    (hl : copyLocation (state s) x = copyLocation (state z) y) :
    copyLocation (state (fixedRegisterPrefix N ops s)) x =
      copyLocation (state (fixedRegisterPrefix N ops z)) y := by
  induction ops generalizing s z with
  | nil => exact hl
  | cons op ops ih =>
    cases op with
    | interval t => exact ih s z hr hl
    | boundary b =>
      apply ih (fixedRegisterBoundary N b s) (fixedRegisterBoundary N b z)
      · exact (fixedRegisterBoundary_register N b s).trans
          (hr.trans (fixedRegisterBoundary_register N b z).symm)
      · rw [fixedRegisterBoundary_copyLocation, fixedRegisterBoundary_copyLocation, hr, hl]

lemma initial_copy_location (N : RootedBinary V E X)
    (sample : Copy → X) (reg : V → Bool) (x : Copy) :
    copyLocation (state (initialCode N sample reg)) x = .node (N.leaf (sample x)) :=
  decode_encode_copyLocation N.root (initial N sample reg)
    (initial_source_valid N sample reg).forest x

lemma initial_reference_location_cross_carrier (N : RootedBinary V E X)
    (sample : Copy → X) (sample' : Other → X) (reg : V → Bool)
    (ops : List (ProgramStep N)) (x : Copy) (y : Other)
    (hxy : sample x = sample' y) :
    copyLocation (state (fixedRegisterPrefix N ops (initialCode N sample reg))) x =
      copyLocation (state (fixedRegisterPrefix N ops (initialCode N sample' reg))) y := by
  apply reference_location_cross_carrier N ops _ _ x y rfl
  rw [initial_copy_location, initial_copy_location, hxy]

def pairSample (i j : X) : Bool → X := fun b => if b then i else j

def repeatedSample (k : Nat) (i j : X) : Fin k ⊕ Unit → X :=
  Sum.elim (fun _ => i) (fun _ => j)

noncomputable def pairReference (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (coin : Hybrid N → Bool) (i j : X) (m : Nat) :
    Code N (pairSample i j) :=
  fixedRegisterPrefix N
    ((compiledCalendarProgram N C H gamma (fun _ => true)).take m)
    (initialCode N (pairSample i j) (originalRegister N coin))

/-- A common location exists on the literal finite calendar. The original
ancestral-support theorem and actual PMF support prove this; no geometric
meeting or target-calibration premise is supplied. -/
theorem pair_meeting_exists (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X) :
    ∃ m, m ≤ (compiledCalendarProgram N C H gamma (fun _ => true)).length ∧
      copyLocation (state (pairReference N C H gamma coin i j m)) true =
        copyLocation (state (pairReference N C H gamma coin i j m)) false := by
  let P := compiledCalendarProgram N C H gamma (fun _ => true)
  let s := initialCode N (pairSample i j) (originalRegister N coin)
  obtain ⟨d, hd⟩ := (sourceProgram N r P s).support_nonempty
  have ha := initialized_original_calendar_ancestral_support N C
    (pairSample i j) (originalRegister N coin) H gamma (fun _ => true) r hd
  have hl := actual_common_program_copy_locations N r P
    (actual_common_compiled_word_only N C H gamma) s hd
  refine ⟨P.length, le_rfl, ?_⟩
  change copyLocation (state (fixedRegisterPrefix N (P.take P.length) s)) true =
    copyLocation (state (fixedRegisterPrefix N (P.take P.length) s)) false
  rw [List.take_length, ← hl true, ← hl false]
  exact (ha true).trans (ha false).symm

noncomputable def bankFirstMeetingIndex (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X) : Nat :=
  Nat.find (pair_meeting_exists N C H gamma r coin i j)

theorem bankFirstMeeting_spec (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X) :
    let m := bankFirstMeetingIndex N C H gamma r coin i j
    m ≤ (compiledCalendarProgram N C H gamma (fun _ => true)).length ∧
      copyLocation (state (pairReference N C H gamma coin i j m)) true =
        copyLocation (state (pairReference N C H gamma coin i j m)) false :=
  Nat.find_spec (pair_meeting_exists N C H gamma r coin i j)

/-- This minimality is at literal operation indices, including intermediate
states inside a tied-date exit/node batch. -/
theorem before_bankFirstMeeting_separated (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X)
    (q : Nat) (hq : q < bankFirstMeetingIndex N C H gamma r coin i j) :
    copyLocation (state (pairReference N C H gamma coin i j q)) true ≠
      copyLocation (state (pairReference N C H gamma coin i j q)) false := by
  intro he
  have hbound := (bankFirstMeeting_spec N C H gamma r coin i j).1
  exact Nat.find_min (pair_meeting_exists N C H gamma r coin i j) hq
    ⟨Nat.le_trans (Nat.le_of_lt hq) hbound, he⟩

/-- Every supported larger two-taxon carrier is physically co-located at this
bank's own constructed cut. Mergers are allowed; no genealogy equality is
asserted. The cut does not depend on k. -/
theorem actual_bank_first_meeting_colocated (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X) (k : Nat)
    {s : Code N (repeatedSample k i j)}
    (hs : s ∈ (sourceProgram N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take
        (bankFirstMeetingIndex N C H gamma r coin i j))
      (initialCode N (repeatedSample k i j) (originalRegister N coin))).support) :
    SharedLocation N s := by
  let P := compiledCalendarProgram N C H gamma (fun _ => true)
  let m := bankFirstMeetingIndex N C H gamma r coin i j
  have hc : CommonOnlyWord N (P.take m) := by
    have hfull := actual_common_compiled_word_only N C H gamma
    have happ : P = P.take m ++ P.drop m := (List.take_append_drop m P).symm
    rw [happ] at hfull
    exact ((commonOnlyWord_append N _ _).mp hfull).1
  have hl := actual_common_program_copy_locations N r (P.take m) hc
    (initialCode N (repeatedSample k i j) (originalRegister N coin)) hs
  have hm := (bankFirstMeeting_spec N C H gamma r coin i j).2
  refine ⟨copyLocation (state (pairReference N C H gamma coin i j m)) true, ?_⟩
  intro x
  rw [hl x]
  cases x with
  | inl a =>
    exact initial_reference_location_cross_carrier N (repeatedSample k i j)
      (pairSample i j) (originalRegister N coin) (P.take m) (.inl a) true rfl
  | inr u =>
    have he := initial_reference_location_cross_carrier N (repeatedSample k i j)
      (pairSample i j) (originalRegister N coin) (P.take m) (.inr u) false rfl
    exact he.trans hm.symm

/-- Direct use of the accepted actual completion theorem, with its co-location
premise now discharged at a source-constructed first cut. The original future
and actual ancestral completion remain the unchanged source operations. -/
theorem actual_bank_first_meeting_completion (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X) (k : Nat)
    (keep : Finset (Fin k ⊕ Unit))
    (readout : UnrankedView V E (Fin k ⊕ Unit) → Obs)
    {s : Code N (repeatedSample k i j)}
    (hs : s ∈ (sourceProgram N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take
        (bankFirstMeetingIndex N C H gamma r coin i j))
      (initialCode N (repeatedSample k i j) (originalRegister N coin))).support) :
    ((sourceProgram N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).drop
        (bankFirstMeetingIndex N C H gamma r coin i j)) s).bind
      (completionKernel N r)).map
        (fun d => readout (unrankedView (selectedView (state d) keep))) =
      completionReader N r keep readout s := by
  apply actual_initialized_common_suffix_completion N C (repeatedSample k i j)
    H gamma r coin keep readout _ _
    (List.take_append_drop _ _).symm s hs
  exact actual_bank_first_meeting_colocated N C H gamma r coin i j k hs

/-- A cost read directly from the old fixed-register source prefix: each
actual interval contributes its original total pair rate times duration.
This is not a replacement transition kernel or an observed hidden clock. -/
noncomputable def referenceExposure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : List (ProgramStep N) → Code N sample → ℝ
  | [], _ => 0
  | .interval t :: ops, s => totalRate N r s * (t : ℝ) + referenceExposure N r ops s
  | .boundary b :: ops, s => referenceExposure N r ops (fixedRegisterBoundary N b s)

lemma weighted_reference_exposure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hc : CommonOnlyWord N ops) (s : Code N sample) :
    weightedRoute N r ops s (fixedRegisterPrefix N ops s) =
      ENNReal.ofReal (Real.exp (-referenceExposure N r ops s)) := by
  induction ops generalizing s with
  | nil => simp [weightedRoute, fixedRegisterPrefix, referenceExposure]
  | cons op ops ih =>
    cases op with
    | interval t =>
      change sourceTimeKernel N r t s s *
        weightedRoute N r ops s (fixedRegisterPrefix N ops s) = _
      rw [actual_holding_weight, ih hc s]
      simp only [referenceExposure, neg_add, Real.exp_add,
        ENNReal.ofReal_mul (Real.exp_nonneg _)]
    | boundary b =>
      change (∑' z, boundaryKernel N b s z *
        weightedRoute N r ops z (fixedRegisterPrefix N ops (fixedRegisterBoundary N b s))) =
          ENNReal.ofReal (Real.exp (-referenceExposure N r ops (fixedRegisterBoundary N b s)))
      rw [actual_common_boundary_kernel N b hc.1 s,
        tsum_eq_single (fixedRegisterBoundary N b s)]
      · simpa only [PMF.pure_apply, if_pos rfl, one_mul] using
          ih hc.2 (fixedRegisterBoundary N b s)
      · intro z hz
        simp only [PMF.pure_apply, if_neg hz, if_neg (Ne.symm hz), zero_mul]

theorem actual_common_no_loss_exposure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hc : CommonOnlyWord N ops) (s : Code N sample) :
    ((sourceProgram N r ops s).map liveCard) (liveCard s) =
      ENNReal.ofReal (Real.exp (-referenceExposure N r ops s)) := by
  rw [actual_common_word_no_loss_mass N r ops hc s]
  exact weighted_reference_exposure N r ops hc s

noncomputable def bankExclusiveExposure (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X) : ℝ :=
  referenceExposure N r
    ((compiledCalendarProgram N C H gamma (fun _ => true)).take
      (bankFirstMeetingIndex N C H gamma r coin i j))
    (initialCode N (repeatedSample 2 i j) (originalRegister N coin))

/-- The exact actual three-copy no-loss weight at the constructed cut. It
uses one fixed entering bank and the original complete three-copy carrier.
No source-independent exponential law is assumed. -/
theorem actual_bank_three_copy_no_loss (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X) :
    ((sourceProgram N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take
        (bankFirstMeetingIndex N C H gamma r coin i j))
      (initialCode N (repeatedSample 2 i j) (originalRegister N coin))).map liveCard) 3 =
      ENNReal.ofReal (Real.exp (-bankExclusiveExposure N C H gamma r coin i j)) := by
  let P := compiledCalendarProgram N C H gamma (fun _ => true)
  let m := bankFirstMeetingIndex N C H gamma r coin i j
  have hc : CommonOnlyWord N (P.take m) := by
    have hfull := actual_common_compiled_word_only N C H gamma
    rw [show P = P.take m ++ P.drop m from (List.take_append_drop m P).symm] at hfull
    exact ((commonOnlyWord_append N _ _).mp hfull).1
  have hcard : liveCard (initialCode N (repeatedSample 2 i j) (originalRegister N coin)) = 3 := by
    change (Finset.univ : Finset (Fin 2 ⊕ Unit)).card = 3
    simp
  rw [← hcard]
  exact actual_common_no_loss_exposure N r (P.take m) hc _

#print axioms pair_meeting_exists
#print axioms actual_bank_first_meeting_colocated
#print axioms actual_bank_first_meeting_completion
#print axioms actual_bank_three_copy_no_loss

end DotG4.ActualBankFirstMeeting
