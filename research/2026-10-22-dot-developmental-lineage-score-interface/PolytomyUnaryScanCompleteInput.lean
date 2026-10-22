/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual complete-input suffix checking after concrete replay/header/rows,
with exact original readNormalizedSource observation. This establishes
syntax plus predicate folds, not declared-m equality or full coverage.
-/
import PolytomyConcreteUnaryScan

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {F : Type}

def readTaggedUnaryPrefix : List Bool → Option (RawMSSCRecord × List Bool)
  | true :: bits => parseUnaryRawPrefix bits
  | _ => none

theorem unaryScanReadFold_tagged (mode : UnaryVisitMode) (bump : F → Bool → F)
    (C : ℕ) (acc : F) (bits : List Bool) :
    unaryScanReadFold mode bump C acc bits = (readTaggedUnaryPrefix bits).map
      (fun z => (z.2, z.1.rows.foldl (fun a row => row.foldl (unaryVisitStep mode bump C) a) acc)) := by
  cases bits with
  | nil => rfl
  | cons tag bits =>
      cases tag with
      | false => rfl
      | true =>
          cases h1 : readUnaryFrame bits with
          | none => simp [unaryScanReadFold, readTaggedUnaryPrefix, readInternalHeaderPrefix, parseUnaryRawPrefix, h1]
          | some z1 =>
              rcases z1 with ⟨N, r1⟩
              cases h2 : readUnaryFrame r1 with
              | none => simp [unaryScanReadFold, readTaggedUnaryPrefix, readInternalHeaderPrefix, parseUnaryRawPrefix, h1, h2]
              | some z2 =>
                  rcases z2 with ⟨m, r2⟩
                  cases h3 : readUnaryFrame r2 with
                  | none => simp [unaryScanReadFold, readTaggedUnaryPrefix, readInternalHeaderPrefix, parseUnaryRawPrefix, h1, h2, h3]
                  | some z3 =>
                      rcases z3 with ⟨K, rest⟩
                      cases hrows : readFramedList (readFramedList readUnaryFrame) rest with
                      | none => simp [unaryScanReadFold, readTaggedUnaryPrefix, readInternalHeaderPrefix, parseUnaryRawPrefix, h1, h2, h3, hrows]
                      | some z4 => rcases z4 with ⟨rows, suffix⟩; simp [unaryScanReadFold,
                          readTaggedUnaryPrefix, readInternalHeaderPrefix, parseUnaryRawPrefix, h1, h2, h3, hrows]

theorem readNormalizedSource_tagged (bits : List Bool) :
    readNormalizedSource bits = match readTaggedUnaryPrefix bits with
      | some (R, []) => some R
      | _ => none := by
  cases bits with
  | nil => rfl
  | cons tag bits => cases tag <;> rfl

def unaryScanCompleteRoutine (mode : UnaryVisitMode) (bump : F → Bool → F) :
    Routine (fun _ : NumericStack UnaryScanPort => Bool) (CountdownState F) :=
  RoutineComposition.seq (unaryScanPrefixRoutine mode bump) (Atom.routine suffixCheckOp)

def unaryScanCompleteEval (mode : UnaryVisitMode) (bump : F → Bool → F) (C : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) :=
  suffixChecked (unaryScanPrefixEval mode bump C s)

def unaryScanCompleteObservation (s : CountdownStore (NumericStack UnaryScanPort) F) : Option F :=
  if s.state.2 then some s.state.1.1 else none

theorem unaryScanComplete_executes (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) (hs : UnaryScanReady C L s) :
    ∃ n ≤ unaryScanPrefixBound C L + 1,
      (unaryScanCompleteRoutine mode bump).Executes s (unaryScanCompleteEval mode bump C s) n := by
  obtain ⟨n, hn, he, hi⟩ := unaryScanPrefix_executes mode bump C L s hs
  exact ⟨n + 1, by omega, RoutineComposition.seq_executes (unaryScanPrefixRoutine mode bump)
    (Atom.routine suffixCheckOp) he (Atom.executes suffixCheckOp _)⟩

theorem unaryScanComplete_observation (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F) (hs : UnaryScanReady C L s) :
    unaryScanCompleteObservation (unaryScanCompleteEval mode bump C s) =
      (readNormalizedSource (s.stk (.inr .original))).map
        (fun R => R.rows.foldl (fun a row => row.foldl (unaryVisitStep mode bump C) a) s.state.1.1) := by
  have ho := unaryScanPrefix_observation mode bump C L s hs
  rw [unaryScanReadFold_tagged] at ho
  rw [readNormalizedSource_tagged]
  cases hp : readTaggedUnaryPrefix (s.stk (.inr .original)) with
  | none =>
      have hn : unaryVisitObservation (unaryScanPrefixEval mode bump C s) = none := by simpa [hp] using ho
      have hf := (unaryVisitObservation_none _).mp hn
      simp [unaryScanCompleteObservation, unaryScanCompleteEval, suffixChecked, suffixCheckOp, Op.apply, hf, hp]
  | some z =>
      rcases z with ⟨R, suffix⟩
      have hsome : unaryVisitObservation (unaryScanPrefixEval mode bump C s) =
          some (suffix, R.rows.foldl (fun a row => row.foldl (unaryVisitStep mode bump C) a) s.state.1.1) := by
        simpa [hp] using ho
      obtain ⟨hf, hsource, hacc⟩ := (unaryVisitObservation_some _ _ _).mp hsome
      cases suffix <;> simp [unaryScanCompleteObservation, unaryScanCompleteEval,
        suffixChecked, suffixCheckOp, Op.apply, hf, hsource, hacc, hp]

theorem unaryScanComplete_membership (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady C L s) :
    unaryScanCompleteObservation (unaryScanCompleteEval .equal (fun a b => a || b) C s) =
      (readNormalizedSource (s.stk (.inr .original))).map
        (fun R => s.state.1.1 || decide (C ∈ R.rows.flatten)) := by
  rw [unaryScanComplete_observation .equal (fun a b => a || b) C L s hs]
  apply congrArg
  funext R
  rw [visitFold_rows, visitFold_or]

theorem unaryScanComplete_range (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) Bool) (hs : UnaryScanReady C L s) :
    unaryScanCompleteObservation (unaryScanCompleteEval .less (fun a b => a && b) C s) =
      (readNormalizedSource (s.stk (.inr .original))).map
        (fun R => s.state.1.1 && R.rows.flatten.all (fun a => decide (a < C))) := by
  rw [unaryScanComplete_observation .less (fun a b => a && b) C L s hs]
  apply congrArg
  funext R
  rw [visitFold_rows, visitFold_and]

/- The whole original input is physically copied and read, including
header tag/scalars and all count delimiters; trailing suffixes are actually
rejected. The cap C is still an explicit physical query supplied at entry.
Declared-m consistency, coverage enumeration, cleanup and full downstream
construction remain separate, as do the independent verifier and hardness.
-/

end PolytomyReductionModel
