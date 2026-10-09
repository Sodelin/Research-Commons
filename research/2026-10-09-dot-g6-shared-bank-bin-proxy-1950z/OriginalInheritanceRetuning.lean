import UpperRateProxySupport
import UnifiedLean.G6.InheritanceBankCommon

/-! dot (OpenAI), 9 October 2026. Work toward the full shared-bank source/proxy
bound. Original hybrid IDs, stored COMMON bits and calendar tie order remain
fixed. Only the one original-site inheritance bank is changed. -/
namespace DotG6.OriginalInheritanceRetuning
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.G6.InheritanceBankCommon
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def tuneBoundary (N : RootedBinary V E X) (phat : HybridProbabilities N) :
    BoundaryOperation N → BoundaryOperation N
  | .independent H _ => .independent H (originalGamma phat ⟨H.hybrid,H.isHybrid⟩)
  | q => q

noncomputable def tuneStep (N : RootedBinary V E X) (phat : HybridProbabilities N) :
    ProgramStep N → ProgramStep N
  | .boundary q => .boundary (tuneBoundary N phat q)
  | q => q

/-- The generated original hybrid occurrence reads its one shared bank entry. -/
theorem tune_original_node (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (p phat : HybridProbabilities N) (common : Hybrid N → Bool) (v : V) :
    tuneBoundary N phat (originalNodeOperation N H (originalGamma p) common v) =
      originalNodeOperation N H (originalGamma phat) common v := by
  unfold originalNodeOperation
  split
  · rfl
  · split
    · rename_i hh
      split
      · rfl
      · simp only [tuneBoundary]
        congr 2
        exact Subtype.ext (H.original_site _)
    · rfl

theorem tune_boundary_operations (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p phat : HybridProbabilities N)
    (common : Hybrid N → Bool) (a : ℝ) :
    (boundaryOperations N C H (originalGamma p) common a).map (tuneStep N phat) =
      boundaryOperations N C H (originalGamma phat) common a := by
  simp only [boundaryOperations, List.map_append, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro v _
  change ProgramStep.boundary (tuneBoundary N phat
    (originalNodeOperation N H (originalGamma p) common v)) = _
  rw [tune_original_node]

theorem tune_calendar_tail (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p phat : HybridProbabilities N)
    (common : Hybrid N → Bool) (a : ℝ) (dates : List ℝ) :
    (calendarTail N C H (originalGamma p) common a dates).map (tuneStep N phat) =
      calendarTail N C H (originalGamma phat) common a dates := by
  induction dates generalizing a with
  | nil => rfl
  | cons b bs ih =>
      simp only [calendarTail, List.map_cons, List.map_append]
      rw [tune_boundary_operations, ih]
      rfl

/-- Actual full calendar compiler commutes with one shared inheritance retuning;
all tied-boundary list order, original edge IDs and ordinary durations are fixed. -/
theorem tune_compiled_calendar (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p phat : HybridProbabilities N)
    (common : Hybrid N → Bool) :
    (compiledCalendarProgram N C H (originalGamma p) common).map (tuneStep N phat) =
      compiledCalendarProgram N C H (originalGamma phat) common := by
  unfold compiledCalendarProgram
  split
  · rfl
  · rw [List.map_append, tune_boundary_operations, tune_calendar_tail]

noncomputable def aligned (N : RootedBinary V E X) (p : HybridProbabilities N) :
    ProgramStep N → Prop
  | .boundary (.independent H gamma) => gamma = originalGamma p ⟨H.hybrid,H.isHybrid⟩
  | _ => True

noncomputable def inheritanceMass (N : RootedBinary V E X) (beta : ℝ) :
    ProgramStep N → ℝ≥0∞
  | .boundary (.independent _ _) => (ENNReal.ofReal beta)^Fintype.card Copy
  | _ => 1

theorem tuned_boundary_lower (N : RootedBinary V E X) {sample : Copy → X}
    (p phat : HybridProbabilities N) (beta : ℝ)
    (hbeta : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (htrue : ∀ h, beta * p.gamma h ≤ phat.gamma h)
    (hfalse : ∀ h, beta * (1-p.gamma h) ≤ 1-phat.gamma h)
    (k : BoundaryOperation N) (ha : aligned N p (.boundary k))
    (s d : Code N sample) :
    inheritanceMass (Copy := Copy) N beta (.boundary k) * boundaryKernel N k s d ≤
      boundaryKernel N (tuneBoundary N phat k) s d := by
  cases k with
  | exit e => simp only [inheritanceMass, one_mul, tuneBoundary]; exact le_rfl
  | ordinary e h => simp only [inheritanceMass, one_mul, tuneBoundary]; exact le_rfl
  | root => simp only [inheritanceMass, one_mul, tuneBoundary]; exact le_rfl
  | common H => simp only [inheritanceMass, one_mul, tuneBoundary]; exact le_rfl
  | independent H gamma =>
      change gamma = originalGamma p ⟨H.hybrid,H.isHybrid⟩ at ha
      subst gamma
      exact actual_independent_pulse_bank_lower_uniform N H s d
        (originalGamma p ⟨H.hybrid,H.isHybrid⟩) (originalGamma phat ⟨H.hybrid,H.isHybrid⟩)
        beta hbeta hbeta1 (htrue _) (hfalse _)

theorem original_node_aligned (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (v : V) :
    aligned N p (.boundary (originalNodeOperation N H (originalGamma p) common v)) := by
  unfold originalNodeOperation
  split
  · trivial
  · split
    · split
      · trivial
      · change originalGamma p _ = originalGamma p _
        congr 1
        exact Subtype.ext (H.original_site _).symm
    · trivial

theorem boundary_operations_aligned (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (a : ℝ) :
    ∀ op ∈ boundaryOperations N C H (originalGamma p) common a, aligned N p op := by
  intro op hop
  rcases List.mem_append.mp hop with he | hv
  · rcases List.mem_map.mp he with ⟨e,_,rfl⟩
    trivial
  · rcases List.mem_map.mp hv with ⟨v,_,rfl⟩
    exact original_node_aligned N H p common v

theorem calendar_tail_aligned (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (a : ℝ) (dates : List ℝ) :
    ∀ op ∈ calendarTail N C H (originalGamma p) common a dates, aligned N p op := by
  induction dates generalizing a with
  | nil => simp [calendarTail]
  | cons b bs ih =>
      intro op hop
      rcases List.mem_cons.mp hop with rfl | hop
      · trivial
      · rcases List.mem_append.mp hop with hb | ht
        · exact boundary_operations_aligned N C H p common b op hb
        · exact ih b op ht

theorem compiled_calendar_aligned (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) :
    ∀ op ∈ compiledCalendarProgram N C H (originalGamma p) common, aligned N p op := by
  unfold compiledCalendarProgram
  split
  · simp
  · intro op hop
    rcases List.mem_append.mp hop with hb | ht
    · exact boundary_operations_aligned N C H p common _ op hb
    · exact calendar_tail_aligned N C H p common _ _ op ht

open CloudG3.ActualObservationCutRefinement

theorem tune_cut_refines (N : RootedBinary V E X) (phat : HybridProbabilities N)
    {a b : List (ProgramStep N)} (href : CutRefines N a b) :
    CutRefines N (a.map (tuneStep N phat)) (b.map (tuneStep N phat)) := by
  induction href with
  | refl ops => exact CutRefines.refl _
  | split pre suf t v =>
      simpa only [List.map_append,List.map_cons,tuneStep] using
        CutRefines.split (pre.map (tuneStep N phat)) (suf.map (tuneStep N phat)) t v
  | trans h1 h2 ih1 ih2 => exact CutRefines.trans ih1 ih2

theorem refinement_aligned (N : RootedBinary V E X) (p : HybridProbabilities N)
    {a b : List (ProgramStep N)} (href : CutRefines N a b)
    (ha : ∀ op ∈ a, aligned N p op) : ∀ op ∈ b, aligned N p op := by
  induction href with
  | refl ops => exact ha
  | split pre suf t v =>
      intro op hop
      rcases List.mem_append.mp hop with hp | hs
      · exact ha op (List.mem_append_left _ hp)
      · rcases List.mem_cons.mp hs with rfl | hs
        · trivial
        · rcases List.mem_cons.mp hs with rfl | hs
          · trivial
          · exact ha op (List.mem_append_right _ (List.mem_cons_of_mem _ hs))
  | trans h1 h2 ih1 ih2 => exact ih2 (ih1 ha)

#print axioms tune_compiled_calendar
#print axioms tuned_boundary_lower
#print axioms compiled_calendar_aligned
#print axioms tune_cut_refines
#print axioms refinement_aligned
end DotG6.OriginalInheritanceRetuning
