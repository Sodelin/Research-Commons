import G2LiteralMarkedClockTrace
import G2MarkedTraceCuts

/-!
# Active-record stability under a larger successful trace budget

Contributor: dot (OpenAI), 2026-10-06. New disjoint phase06 source, importing
only the frozen literal trace and active-cut modules. The source state, copy
carrier, original clock vector and destination-clock embedding are unchanged.
Only the recursion budget changes; inactive padded vectors are not equated.
-/

namespace GProgram.G2.MarkedTraceBudgetStability
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceRaceWinnerSelection
open UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G2.LiteralMarkedClockTrace
open GProgram.G2.MarkedTraceCuts
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem activeTrace_of_no_jump (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (hstop : ∀ p : Choice N s, t < c p) :
    activeTrace N n t s c = [] := by
  cases n with
  | zero => exact activeTrace_zero N t s c
  | succ n => simp [activeTrace,literalMarkedTrace,hstop]

/-- Successful completion at n means that a larger budget cannot add an
active event. The clock catalogue is Choice N s, independent of both n and k;
the recursive residual vector is literally the same on both sides. -/
theorem activeTrace_budget_add_of_success (N : RootedBinary V E X)
    {sample : Copy → X} (n k : Nat) (t : ℝ) (s : Code N sample)
    (c : Choice N s → ℝ)
    (hsuccess : (literalMarkedTrace N n t s c).1 = true) :
    activeTrace N (n+k) t s c = activeTrace N n t s c := by
  induction n generalizing s t with
  | zero =>
      have hstop : ∀ p : Choice N s, t < c p := by
        simpa [literalMarkedTrace] using hsuccess
      simpa only [Nat.zero_add,activeTrace_zero] using
        activeTrace_of_no_jump N k t s c hstop
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, t < c p
      · rw [activeTrace_of_no_jump N ((n+1)+k) t s c hstop,
          activeTrace_of_no_jump N (n+1) t s c hstop]
      · cases hp : selectedWinner c with
        | none =>
            have hfalse : False := by
              simpa [literalMarkedTrace,hstop,hp] using hsuccess
            exact hfalse.elim
        | some p =>
            by_cases hpt : c p ≤ t
            · have htail :
                  (literalMarkedTrace N n (t-c p) (stepDestination N s (some p))
                    (fun q => c (destinationClockEmbedding N s p q).val-c p)).1 = true := by
                simpa only [literalMarkedTrace,if_neg hstop,hp,if_pos hpt] using hsuccess
              rw [Nat.succ_add,activeTrace_succ,activeTrace_succ]
              simp only [hp,if_pos hpt]
              rw [ih (t := t-c p) (s := stepDestination N s (some p))
                (c := fun q => c (destinationClockEmbedding N s p q).val-c p) htail]
            · have hfalse : False := by
                simpa [literalMarkedTrace,hstop,hp,hpt] using hsuccess
              exact hfalse.elim

theorem activeTrace_budget_succ_of_success (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (t : ℝ) (s : Code N sample)
    (c : Choice N s → ℝ)
    (hsuccess : (literalMarkedTrace N n t s c).1 = true) :
    activeTrace N (n+1) t s c = activeTrace N n t s c :=
  activeTrace_budget_add_of_success N n 1 t s c hsuccess

/-- Compare through one common enlarged budget. No independent clock draw,
changed copy carrier, or padding-vector identification occurs. -/
theorem activeTrace_eq_of_success (N : RootedBinary V E X) {sample : Copy → X}
    (n m : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (hn : (literalMarkedTrace N n t s c).1 = true)
    (hm : (literalMarkedTrace N m t s c).1 = true) :
    activeTrace N n t s c = activeTrace N m t s c := by
  calc
    activeTrace N n t s c = activeTrace N (n+m) t s c :=
      (activeTrace_budget_add_of_success N n m t s c hn).symm
    _ = activeTrace N (m+n) t s c := by rw [Nat.add_comm n m]
    _ = activeTrace N m t s c :=
      activeTrace_budget_add_of_success N m n t s c hm

/-- The actual phase01 success theorem discharges the two success premises
for every pair of budgets covering the same live carrier. -/
theorem regular_active_records_budget_eq (N : RootedBinary V E X)
    {sample : Copy → X} (n m : Nat) (t : ℝ) (s : Code N sample)
    (c : Choice N s → ℝ) (hc : ClockRegular c)
    (hn : liveCard s ≤ n) (hm : liveCard s ≤ m) (_ht : 0 ≤ t) :
    activeRecords (literalMarkedTrace N n t s c).2 =
      activeRecords (literalMarkedTrace N m t s c).2 := by
  simpa only [activeTrace] using activeTrace_eq_of_success N n m t s c
    (marked_trace_success_on_regular N n s t c hn hc)
    (marked_trace_success_on_regular N m s t c hm hc)

#print axioms activeTrace_of_no_jump
#print axioms activeTrace_budget_add_of_success
#print axioms activeTrace_budget_succ_of_success
#print axioms activeTrace_eq_of_success
#print axioms regular_active_records_budget_eq

end GProgram.G2.MarkedTraceBudgetStability
