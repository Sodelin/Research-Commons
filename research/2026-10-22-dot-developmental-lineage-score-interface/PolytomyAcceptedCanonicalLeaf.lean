/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual accepted-leaf body: original incremental comb cost, exact original
leaf token and physical accepted-count increment. A fixed finite slot
injection makes every nonaliasing assumption explicit.
-/
import PolytomyIncrementalCombCost

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

inductive CanonicalLeafSlot where
  | remaining | count | temp | cost | block | value | output
  deriving DecidableEq, Fintype

variable {K F : Type} [DecidableEq K]

structure CanonicalLeafLayout (K : Type) where
  port : CanonicalLeafSlot → K
  injective : Function.Injective port

theorem CanonicalLeafLayout.ne (p : CanonicalLeafLayout K) {a b : CanonicalLeafSlot} (h : a ≠ b) :
    p.port a ≠ p.port b := fun he => h (p.injective he)

def acceptedCanonicalLeafRoutine (p : CanonicalLeafLayout K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (combCostStepRoutine (p.port .remaining) (p.port .count) (p.port .temp) (p.port .cost))
    (RoutineComposition.seq (canonicalLeafRoutine (p.port .block) (p.port .value) (p.port .temp) (p.port .output))
      (Atom.routine (prependBitOp (p.port .count) true)))

def acceptedCanonicalLeafEval (p : CanonicalLeafLayout K) (s : CountdownStore K F) :=
  (prependBitOp (p.port .count) true).apply
    (canonicalLeafEval (p.port .block) (p.port .value) (p.port .output)
      (combCostStepEval (p.port .remaining) (p.port .count) (p.port .cost) s))

theorem acceptedCanonicalLeaf_executes (p : CanonicalLeafLayout K) (s : CountdownStore K F)
    (ht : s.stk (p.port .temp) = []) :
    ∃ n ≤ 3 * (s.stk (p.port .remaining)).length + 3 * (s.stk (p.port .value)).length +
      3 * (s.stk (p.port .block)).length + 16,
      (acceptedCanonicalLeafRoutine p).Executes s (acceptedCanonicalLeafEval p s) n := by
  let u := combCostStepEval (p.port .remaining) (p.port .count) (p.port .cost) s
  let v := canonicalLeafEval (p.port .block) (p.port .value) (p.port .output) u
  obtain ⟨n, hn, hcost⟩ := combCostStep_executes (p.port .remaining) (p.port .count) (p.port .temp) (p.port .cost)
    (p.ne (by decide)) (p.ne (by decide)) (p.ne (by decide)) s ht
  have huTemp : u.stk (p.port .temp) = [] :=
    (combCostStep_extra _ _ _ _ (p.ne (by decide)) (p.ne (by decide)) s).trans ht
  have hvalue : u.stk (p.port .value) = s.stk (p.port .value) :=
    combCostStep_extra _ _ _ _ (p.ne (by decide)) (p.ne (by decide)) s
  have hblock : u.stk (p.port .block) = s.stk (p.port .block) :=
    combCostStep_extra _ _ _ _ (p.ne (by decide)) (p.ne (by decide)) s
  have hleaf := canonicalLeaf_executes (p.port .block) (p.port .value) (p.port .temp) (p.port .output)
    (p.ne (by decide)) (p.ne (by decide)) (p.ne (by decide)) (p.ne (by decide)) (p.ne (by decide)) u huTemp
  rw [hvalue, hblock] at hleaf
  have hcount := Atom.executes (prependBitOp (p.port .count) true) v
  have htail := RoutineComposition.seq_executes
    (canonicalLeafRoutine (p.port .block) (p.port .value) (p.port .temp) (p.port .output))
    (Atom.routine (prependBitOp (p.port .count) true)) hleaf hcount
  have hall := RoutineComposition.seq_executes
    (combCostStepRoutine (p.port .remaining) (p.port .count) (p.port .temp) (p.port .cost))
    (RoutineComposition.seq (canonicalLeafRoutine (p.port .block) (p.port .value) (p.port .temp) (p.port .output))
      (Atom.routine (prependBitOp (p.port .count) true))) hcost htail
  exact ⟨n + ((3 * (s.stk (p.port .value)).length + 3 * (s.stk (p.port .block)).length + 9) + 1), by omega, hall⟩

theorem acceptedCanonicalLeaf_count (p : CanonicalLeafLayout K) (s : CountdownStore K F) :
    (acceptedCanonicalLeafEval p s).stk (p.port .count) = true :: s.stk (p.port .count) := by
  simp only [acceptedCanonicalLeafEval, prependBitOp, Op.apply, Function.update_same]
  rw [canonicalLeaf_extra _ _ _ _ (p.ne (by decide)),
    combCostStep_extra _ _ _ _ (p.ne (by decide)) (p.ne (by decide))]

theorem acceptedCanonicalLeaf_remaining (p : CanonicalLeafLayout K) (s : CountdownStore K F) :
    (acceptedCanonicalLeafEval p s).stk (p.port .remaining) = (s.stk (p.port .remaining)).tail := by
  simp only [acceptedCanonicalLeafEval, prependBitOp, Op.apply,
    Function.update_of_ne (p.ne (by decide : CanonicalLeafSlot.remaining ≠ .count))]
  rw [canonicalLeaf_extra _ _ _ _ (p.ne (by decide)),
    combCostStep_remaining _ _ _ (p.ne (by decide))]

theorem acceptedCanonicalLeaf_cost (p : CanonicalLeafLayout K) (s : CountdownStore K F) :
    (acceptedCanonicalLeafEval p s).stk (p.port .cost) =
      if (s.stk (p.port .count)).head?.isSome then
        (s.stk (p.port .remaining)).tail ++ s.stk (p.port .cost) else s.stk (p.port .cost) := by
  simp only [acceptedCanonicalLeafEval, prependBitOp, Op.apply,
    Function.update_of_ne (p.ne (by decide : CanonicalLeafSlot.cost ≠ .count))]
  rw [canonicalLeaf_extra _ _ _ _ (p.ne (by decide)),
    combCostStep_cost _ _ _ (p.ne (by decide)) (p.ne (by decide))]

theorem acceptedCanonicalLeaf_bytes (p : CanonicalLeafLayout K) (s : CountdownStore K F)
    (hb : IsUnaryWord (s.stk (p.port .block))) (hv : IsUnaryWord (s.stk (p.port .value))) :
    (acceptedCanonicalLeafEval p s).stk (p.port .output) =
      true :: (unaryFrame (s.stk (p.port .block)).length ++ unaryFrame (s.stk (p.port .value)).length ++ s.stk (p.port .output)) := by
  let u := combCostStepEval (p.port .remaining) (p.port .count) (p.port .cost) s
  have hblock : u.stk (p.port .block) = s.stk (p.port .block) :=
    combCostStep_extra _ _ _ _ (p.ne (by decide)) (p.ne (by decide)) s
  have hvalue : u.stk (p.port .value) = s.stk (p.port .value) :=
    combCostStep_extra _ _ _ _ (p.ne (by decide)) (p.ne (by decide)) s
  have hout : u.stk (p.port .output) = s.stk (p.port .output) :=
    combCostStep_extra _ _ _ _ (p.ne (by decide)) (p.ne (by decide)) s
  have h := canonicalLeaf_bytes (p.port .block) (p.port .value) (p.port .output)
    (p.ne (by decide)) u (by simpa [hblock] using hb) (by simpa [hvalue] using hv)
  simpa [acceptedCanonicalLeafEval, prependBitOp, Op.apply,
    p.ne (by decide : CanonicalLeafSlot.output ≠ .count), ← u, hblock, hvalue, hout] using h

theorem acceptedCanonicalLeaf_extra (p : CanonicalLeafLayout K) (s : CountdownStore K F) (k : K)
    (hkr : k ≠ p.port .remaining) (hkc : k ≠ p.port .count)
    (hkcost : k ≠ p.port .cost) (hko : k ≠ p.port .output) :
    (acceptedCanonicalLeafEval p s).stk k = s.stk k := by
  simp only [acceptedCanonicalLeafEval, prependBitOp, Op.apply, Function.update_of_ne hkc]
  rw [canonicalLeaf_extra _ _ _ _ hko, combCostStep_extra _ _ _ _ hkr hkcost]

theorem acceptedCanonicalLeaf_frame (p : CanonicalLeafLayout K) (s : CountdownStore K F) :
    (acceptedCanonicalLeafEval p s).state.1.1 = s.state.1.1 ∧
      (acceptedCanonicalLeafEval p s).state.2 = s.state.2 := by
  simpa only [acceptedCanonicalLeafEval, canonicalLeafEval, unaryPrependEval, prependBitOp, Op.apply] using
    combCostStep_frame (p.port .remaining) (p.port .count) (p.port .cost) s

theorem acceptedCanonicalLeaf_comb_invariant (p : CanonicalLeafLayout K) (s : CountdownStore K F)
    (S q acc : ℕ)
    (hr : s.stk (p.port .remaining) = List.replicate (S - q) true)
    (hc : s.stk (p.port .count) = List.replicate q true)
    (hcost : s.stk (p.port .cost) = List.replicate (acc + combTailCost S 1 (q - 1)) true) :
    (acceptedCanonicalLeafEval p s).stk (p.port .remaining) = List.replicate (S - (q + 1)) true ∧
      (acceptedCanonicalLeafEval p s).stk (p.port .count) = List.replicate (q + 1) true ∧
      (acceptedCanonicalLeafEval p s).stk (p.port .cost) = List.replicate (acc + combTailCost S 1 q) true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [acceptedCanonicalLeaf_remaining, hr, List.tail_replicate]
    have h : S - q - 1 = S - (q + 1) := by omega
    rw [h]
  · rw [acceptedCanonicalLeaf_count, hc]
    simp [List.replicate_succ]
  · rw [acceptedCanonicalLeaf_cost, hc, hr, hcost]
    cases q with
    | zero => simp [combTailCost]
    | succ q =>
        simp only [List.replicate_succ, List.head?_cons, Option.isSome_some, ↓reduceIte,
          Nat.succ_sub_one, List.tail_replicate]
        rw [capReplicate_append, combTailCost_snoc]
        congr 1
        have h : S - (q + 1) - 1 = S - (1 + q + 1) := by omega
        omega

/- The body is for ACCEPTED leaves only; actual membership gating and
descending type enumeration remain separate. It does not charge a skipped
type or use a membership oracle. Its semantic count/remaining/cost laws
support the full original comb invariant, while complete block prefixes,
canonical controller/target serialization and kernel checks stay open.
-/

end PolytomyReductionModel
