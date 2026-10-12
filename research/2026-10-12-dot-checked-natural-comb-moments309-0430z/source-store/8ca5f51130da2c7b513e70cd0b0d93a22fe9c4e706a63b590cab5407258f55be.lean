import G2SourceGraftDecoration
import G2LiteralMarkedClockTrace

/-!
# Actual decoration fold on the original marked clock records

Contributor: dot (OpenAI), 6 October 2026. New reconstruction of a missing
deterministic interface. The original clock trace, destination states and
graft update are unchanged. Inactive records retain the carried state and
matrix. Arbitrary active records have a total update interpretation, but are
not thereby certified as legal source histories.
-/

namespace GProgram.G2.ActualDecorationFold
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.SourceGraftDecoration
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceRaceWinnerSelection
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Read the original records in order. An active record performs the exact
old/destination ancestor update at its absolute age; an inactive record
changes neither the carried source state nor the current matrix. -/
noncomputable def foldMatrix (N : RootedBinary V E X) {sample : Copy → X} :
    (n : Nat) → Code N sample → ℝ → (Copy → Copy → ℝ) →
      ClockTrace N sample n → (Copy → Copy → ℝ)
  | 0,_,_,M,_ => M
  | n+1,s,offset,M,z =>
      if (z 0).1 = true then
        foldMatrix N n (z 0).2.2 offset
          (codedAgeUpdate N s (z 0).2.2 (offset+(z 0).2.1) M)
          (fun i => z i.succ)
      else foldMatrix N n s offset M (fun i => z i.succ)

/-- The same age translation used on every tail coordinate by prependTrace.
The Bool flag and destination are retained, including on inactive padding. -/
def shiftTraceAges (N : RootedBinary V E X) {sample : Copy → X} {n : Nat}
    (age : ℝ) (z : ClockTrace N sample n) : ClockTrace N sample n :=
  fun i => ((z i).1,age+(z i).2.1,(z i).2.2)

theorem fold_shift_ages (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (age : ℝ) (z : ClockTrace N sample n) :
    foldMatrix N n s offset M (shiftTraceAges N age z) =
      foldMatrix N n s (offset+age) M z := by
  induction n generalizing s offset M with
  | zero => rfl
  | succ n ih =>
      by_cases h : (z 0).1 = true
      · simp only [foldMatrix,shiftTraceAges,if_pos h]
        change foldMatrix N n (z 0).2.2 offset
            (codedAgeUpdate N s (z 0).2.2 (offset+(age+(z 0).2.1)) M)
            (shiftTraceAges N age (fun i => z i.succ)) =
          foldMatrix N n (z 0).2.2 (offset+age)
            (codedAgeUpdate N s (z 0).2.2 ((offset+age)+(z 0).2.1) M)
            (fun i => z i.succ)
        rw [ih]
        simp only [add_assoc]
      · simp only [foldMatrix,shiftTraceAges,if_neg h]
        change foldMatrix N n s offset M (shiftTraceAges N age (fun i => z i.succ)) =
          foldMatrix N n s (offset+age) M (fun i => z i.succ)
        apply ih

theorem fold_empty (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) :
    foldMatrix N n s offset M (emptyTrace N n s) = M := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change foldMatrix N n s offset M (emptyTrace N n s) = M
      exact ih

/-- Exact legacy prepend equation: the shifted tail is folded with the
increased offset and the matrix produced by the actual first record. -/
theorem fold_prepend (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (age : ℝ) (d : Code N sample) (z : ClockTrace N sample n) :
    foldMatrix N (n+1) s offset M (prependTrace N age d z) =
      foldMatrix N n d (offset+age) (codedAgeUpdate N s d (offset+age) M) z := by
  change foldMatrix N n d offset (codedAgeUpdate N s d (offset+age) M)
      (shiftTraceAges N age z) = _
  exact fold_shift_ages N n d offset (codedAgeUpdate N s d (offset+age) M) age z

/-- Every active step of the literal compiler is a genuine current legal
merger. This invariant holds on all original clock vectors and budgets,
including failed/incomplete prefixes; no success or chronology premise is
needed. Padding never manufactures a graft. -/
theorem actual_literal_fold_decorates (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (H offset : ℝ) (c : Choice N s → ℝ)
    (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (hM : ForestDecorates leafAge M (state s)) :
    ForestDecorates leafAge (foldMatrix N n s offset M (literalMarkedTrace N n H s c).2)
      (state (traceEndpoint N n s (literalMarkedTrace N n H s c).2)) := by
  induction n generalizing s H offset M with
  | zero => exact hM
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, H < c p
      · simpa only [literalMarkedTrace,if_pos hstop,fold_empty,empty_trace_endpoint] using hM
      · simp only [literalMarkedTrace,if_neg hstop]
        cases hw : selectedWinner c with
        | none => simpa only [fold_empty,empty_trace_endpoint] using hM
        | some p =>
            by_cases hp : c p ≤ H
            · simp only [if_pos hp,fold_prepend,prepend_trace_endpoint]
              exact ih (stepDestination N s (some p)) (H-c p) (offset+c p)
                (fun q => c (destinationClockEmbedding N s p q).val-c p) _
                (coded_graft_decorates N leafAge M s p (offset+c p) hM)
            · simpa only [if_neg hp,fold_empty,empty_trace_endpoint] using hM

#print axioms fold_shift_ages
#print axioms fold_empty
#print axioms fold_prepend
#print axioms actual_literal_fold_decorates

end GProgram.G2.ActualDecorationFold
