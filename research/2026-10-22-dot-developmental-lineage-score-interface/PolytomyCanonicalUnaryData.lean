/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Operational unary-data and count-growth invariants for EVERY actual
type-loop body, independent of whether the row selector is in range.
Original block semantics remain separate and exact; these facts let the
outer contract quantify over all its operational invariant states.
-/
import PolytomyActualCanonicalInitialization

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem canonical_unary_cons (xs : List Bool) (h : IsUnaryWord xs) : IsUnaryWord (true :: xs) := by
  unfold IsUnaryWord at *
  simpa [List.replicate_succ] using congrArg (List.cons true) h

theorem canonical_unary_append (xs ys : List Bool) (hx : IsUnaryWord xs) (hy : IsUnaryWord ys) :
    IsUnaryWord (xs ++ ys) := by
  unfold IsUnaryWord at *
  rw [List.length_append, ← capReplicate_append, ← hx, ← hy]

variable {K F : Type} [DecidableEq K]

def CanonicalUnaryData (p : CanonicalLeafLayout K) (s : CountdownStore K F) : Prop :=
  IsUnaryWord (s.stk (p.port .remaining)) ∧
  IsUnaryWord (s.stk (p.port .count)) ∧ IsUnaryWord (s.stk (p.port .cost))

theorem acceptedCanonicalLeaf_unary (p : CanonicalLeafLayout K) (s : CountdownStore K F)
    (h : CanonicalUnaryData p s) : CanonicalUnaryData p (acceptedCanonicalLeafEval p s) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [acceptedCanonicalLeaf_remaining]; exact unaryWord_tail _ h.1
  · rw [acceptedCanonicalLeaf_count]; exact canonical_unary_cons _ h.2.1
  · rw [acceptedCanonicalLeaf_cost]
    split
    · exact canonical_unary_append _ _ (unaryWord_tail _ h.1) h.2.2
    · exact h.2.2

theorem canonicalLeafGate_unary (p : CanonicalLeafLayout K) (s : CountdownStore K F)
    (h : CanonicalUnaryData p s) : CanonicalUnaryData p (canonicalLeafGateEval p s) := by
  cases hf : s.state.2 with
  | false => simpa [CanonicalUnaryData, canonicalLeafGateEval, canonicalContinueOp, Op.apply, hf] using h
  | true =>
      simpa [CanonicalUnaryData, canonicalLeafGateEval, canonicalContinueOp, Op.apply, hf]
        using acceptedCanonicalLeaf_unary p s h

theorem canonicalLeafGate_count_le (p : CanonicalLeafLayout K) (s : CountdownStore K F) :
    ((canonicalLeafGateEval p s).stk (p.port .count)).length ≤ (s.stk (p.port .count)).length + 1 := by
  rw [canonicalLeafGate_data]
  cases hf : s.state.2 <;> simp [hf, acceptedCanonicalLeaf_count]

abbrev RealTypeUnaryData (s : CanonicalFilterStore) :=
  CanonicalUnaryData (callerLeafLayout canonicalFilterLayout) s

theorem realTypeBody_unary (T : ℕ) (s : CanonicalFilterStore) (h : RealTypeUnaryData s) :
    RealTypeUnaryData (realTypeBodyEval T s) :=
  canonicalLeafGate_unary (callerLeafLayout canonicalFilterLayout) _ h

theorem realTypeBody_count_le (T : ℕ) (s : CanonicalFilterStore) :
    ((realTypeBodyEval T s).stk (.inr .count)).length ≤ (s.stk (.inr .count)).length + 1 :=
  canonicalLeafGate_count_le (callerLeafLayout canonicalFilterLayout) _

def RealTypeUnaryInv (L S I T B : ℕ) (s : CanonicalFilterStore) : Prop :=
  RealTypeLoopInv L S I T B s ∧ RealTypeUnaryData s

def realTypeUnaryContract (L S I T B : ℕ) :
    CountdownContract (.inr CanonicalFilterPort.typeIndex) realTypeBodyRoutine (realTypeBodyEval T)
      (RealTypeUnaryInv L S I T B) (realTypeBodyBound L S I T B) where
  peek_closed s hs := ⟨RealTypeLoopInv_of_stacks L S I T B s _ hs.1 (fun _ => rfl), hs.2⟩
  pop_closed s hs hg := by
    refine ⟨realTypeLoop_pop_invariant L S I T B s hs.1, ?_⟩
    simpa [RealTypeUnaryData, CanonicalUnaryData, callerLeafLayout, canonicalFilterLayout,
      countdownPop, countdownPopOp, Op.apply] using hs.2
  body_closed s hs := ⟨realTypeBody_invariant L S I T B s hs.1, realTypeBody_unary T s hs.2⟩
  reset_closed s hs := ⟨RealTypeLoopInv_of_stacks L S I T B s _ hs.1 (fun _ => rfl), hs.2⟩
  counter_preserved s hs := realTypeBody_counter T s
  body_executes s hs := realTypeBody_executes L S I T B s hs.1

theorem realTypeLoop_unary (L S I T B : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeLoopInv L S I T B s) (hu : RealTypeUnaryData s) :
    RealTypeUnaryData (realTypeLoopEval T s) := by
  obtain ⟨n, hn, he, hi, hg, hc⟩ := countdownRoutine_executes (.inr .typeIndex) realTypeBodyRoutine
    (realTypeBodyEval T) (RealTypeUnaryInv L S I T B) (realTypeBodyBound L S I T B)
    (realTypeUnaryContract L S I T B) s ⟨hs, hu⟩
  exact hi.2

theorem realTypeLoop_count_fuel (T n : ℕ) : ∀ s : CanonicalFilterStore,
    ((countdownLoopEval (.inr .typeIndex) (realTypeBodyEval T) n s).stk (.inr .count)).length ≤
      (s.stk (.inr .count)).length + n := by
  induction n with
  | zero => intro s; simp [countdownLoopEval]
  | succ n ih =>
      intro s
      cases hg : countdownGuard s.state with
      | false => simp [countdownLoopEval, hg]
      | true =>
          let p := countdownPop (.inr CanonicalFilterPort.typeIndex) s
          have hp : p.stk (.inr .count) = s.stk (.inr .count) := by
            simp [p, countdownPop, countdownPopOp, Op.apply]
          have hb := realTypeBody_count_le T p
          rw [hp] at hb
          have hi := ih (countdownPeek (.inr .typeIndex) (realTypeBodyEval T p))
          change ((countdownLoopEval (.inr .typeIndex) (realTypeBodyEval T) n
            (countdownPeek (.inr .typeIndex) (realTypeBodyEval T p))).stk (.inr .count)).length ≤
            ((realTypeBodyEval T p).stk (.inr .count)).length + n at hi
          rw [countdownLoopEval, hg]
          simp only [↓reduceIte]
          change ((countdownLoopEval (.inr .typeIndex) (realTypeBodyEval T) n
            (countdownPeek (.inr .typeIndex) (realTypeBodyEval T p))).stk (.inr .count)).length ≤ _
          omega

theorem realTypeLoop_count_bound (T : ℕ) (s : CanonicalFilterStore) :
    ((realTypeLoopEval T s).stk (.inr .count)).length ≤
      (s.stk (.inr .count)).length + (s.stk (.inr .typeIndex)).length :=
  realTypeLoop_count_fuel T _ (countdownPeek (.inr .typeIndex) s)

/- The operational data invariant holds even for an out-of-range row
selector and arbitrary query outcomes. The exact original block theorem
is still used once the ACTUAL outer pop proves i<m. This avoids silently
adding an in-range hypothesis to every generic countdown body call.
-/

end PolytomyReductionModel
