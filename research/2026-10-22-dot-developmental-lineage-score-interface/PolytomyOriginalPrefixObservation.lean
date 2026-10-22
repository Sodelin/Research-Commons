/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Exact observation of the actual provided-cap spine as the ORIGINAL
three-header/nested-rows prefix parser, on arbitrary input words. No
complete-input or valid-instance assumption is substituted.
-/
import PolytomyProvidedCapPrefix

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def loggedRead {A : Type} (read : List Bool → Option (A × List Bool))
    (encode : A → List Bool) (obs : Option (List Bool × List Bool)) :
    Option (List Bool × List Bool) :=
  obs.bind fun q => (read q.1).map (fun p => (p.2, (encode p.1).reverse ++ q.2))

theorem guardedNumeric_logged (r : K) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    numericListObservation r (guardedNumericEval r C s) =
      loggedRead (readSaturatedBinaryNatFrame C) unaryFrame (numericListObservation r s) := by
  rw [guardedNumeric_observation]
  cases hf : s.state.2 <;> simp [numericListObservation, loggedRead, hf]

theorem capSwitchedHeader_logged (r b t : K) (hrb : r ≠ b) (hrt : r ≠ t)
    (D : ℕ) (s : CountdownStore (NumericStack K) F) :
    numericListObservation r (capSwitchedHeaderEval r b t D s) =
      loggedRead (readSaturatedBinaryNatFrame D) unaryFrame (numericListObservation r s) := by
  rw [capSwitchedHeader_observation r b t hrb hrt]
  cases hf : s.state.2 <;> simp [numericListObservation, loggedRead, hf]

theorem guardedRows_logged (r c d : K) (hrc : r ≠ c) (hrd : r ≠ d) (hcd : c ≠ d)
    (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    numericListObservation r (guardedRowsEval r c d C s) =
      loggedRead (readFramedList (readFramedList (readSaturatedBinaryNatFrame C)))
        (encodeFramedList (encodeFramedList unaryFrame)) (numericListObservation r s) := by
  rw [guardedRows_observation r c d hrc hrd hcd]
  cases hf : s.state.2 <;> simp [numericListObservation, loggedRead, hf]

theorem providedCapPrefix_logged (p : PrefixPorts K) (C D : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    numericListObservation p.r (providedCapPrefixEval p C D s) =
      loggedRead (readFramedList (readFramedList (readSaturatedBinaryNatFrame C)))
        (encodeFramedList (encodeFramedList unaryFrame))
        (loggedRead (readSaturatedBinaryNatFrame D) unaryFrame
          (loggedRead (readSaturatedBinaryNatFrame C) unaryFrame
            (loggedRead (readSaturatedBinaryNatFrame C) unaryFrame (numericListObservation p.r s)))) := by
  unfold providedCapPrefixEval
  rw [guardedRows_logged p.r p.c p.d p.hrc p.hrd p.hcd,
    capSwitchedHeader_logged p.r p.b p.t p.hrb p.hrt,
    guardedNumeric_logged, guardedNumeric_logged]

theorem originalLoggedPrefix_exact (L : ℕ) (bits record : List Bool) :
    loggedRead (readFramedList (readFramedList (readSaturatedBinaryNatFrame (L + 1))))
      (encodeFramedList (encodeFramedList unaryFrame))
      (loggedRead (readSaturatedBinaryNatFrame ((L + 1) ^ 2)) unaryFrame
        (loggedRead (readSaturatedBinaryNatFrame (L + 1)) unaryFrame
          (loggedRead (readSaturatedBinaryNatFrame (L + 1)) unaryFrame (some (bits, record))))) =
    (parseSaturatedSourcePrefix L bits).map (fun p => (p.2, (encodeUnaryRaw p.1).reverse ++ record)) := by
  cases h1 : readSaturatedBinaryNatFrame (L + 1) bits with
  | none => simp [loggedRead, h1, parseSaturatedSourcePrefix]
  | some q1 =>
      rcases q1 with ⟨N, r1⟩
      cases h2 : readSaturatedBinaryNatFrame (L + 1) r1 with
      | none => simp [loggedRead, h1, h2, parseSaturatedSourcePrefix]
      | some q2 =>
          rcases q2 with ⟨m, r2⟩
          cases h3 : readSaturatedBinaryNatFrame ((L + 1) ^ 2) r2 with
          | none => simp [loggedRead, h1, h2, h3, parseSaturatedSourcePrefix]
          | some q3 =>
              rcases q3 with ⟨budget, r3⟩
              cases h4 : readFramedList (readFramedList (readSaturatedBinaryNatFrame (L + 1))) r3 with
              | none => simp [loggedRead, h1, h2, h3, h4, parseSaturatedSourcePrefix]
              | some q4 =>
                  rcases q4 with ⟨rows, rest⟩
                  simp [loggedRead, h1, h2, h3, h4, parseSaturatedSourcePrefix,
                    encodeUnaryRaw, List.reverse_append, List.append_assoc]

theorem providedCapPrefix_original_observation (p : PrefixPorts K) (L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hf : s.state.2 = true) :
    numericListObservation p.r (providedCapPrefixEval p (L + 1) ((L + 1) ^ 2) s) =
      (parseSaturatedSourcePrefix L (s.stk (.inl .source))).map
        (fun q => (q.2, (encodeUnaryRaw q.1).reverse ++ s.stk (.inr p.r))) := by
  rw [providedCapPrefix_logged]
  simpa only [numericListObservation, hf, ↓reduceIte] using
    originalLoggedPrefix_exact L (s.stk (.inl .source)) (s.stk (.inr p.r))

theorem providedCapPrefix_failure_absorbing (p : PrefixPorts K) (C D : ℕ)
    (s : CountdownStore (NumericStack K) F) (hf : s.state.2 = false) :
    numericListObservation p.r (providedCapPrefixEval p C D s) = none := by
  rw [providedCapPrefix_logged]
  simp [numericListObservation, hf, loggedRead]

theorem originalPrefixStepBound_expansion (L : ℕ) :
    providedCapPrefixStepBound L (L + 1) ((L + 1) ^ 2) =
      6 * L ^ 4 + 28 * L ^ 3 + 67 * L ^ 2 + 105 * L + 93 := by
  unfold providedCapPrefixStepBound framedRowsStepBound framedNumericRowStepBound numericRecordStepBound
  ring

theorem originalPrefixRecordBound_expansion (L : ℕ) :
    L ^ 2 * (L + 3) + 2 * L + 2 * (L + 1) + (L + 1) ^ 2 + 4 =
      L ^ 3 + 4 * L ^ 2 + 6 * L + 7 := by ring

/-- Actual provided-cap execution, original-prefix observation and all-path
    record bound in a single interface. This does NOT accept a nonempty
    final suffix as a complete input, or construct the supplied caps. -/
theorem providedCapPrefix_original_executes (p : PrefixPorts K) (L : ℕ)
    (s : CountdownStore (NumericStack K) F)
    (hs : PrefixReady p (L + 1) ((L + 1) ^ 2) L s) (hf : s.state.2 = true) :
    ∃ n ≤ providedCapPrefixStepBound L (L + 1) ((L + 1) ^ 2),
      (providedCapPrefixRoutine p).Executes s (providedCapPrefixEval p (L + 1) ((L + 1) ^ 2) s) n ∧
      numericListObservation p.r (providedCapPrefixEval p (L + 1) ((L + 1) ^ 2) s) =
        (parseSaturatedSourcePrefix L (s.stk (.inl .source))).map
          (fun q => (q.2, (encodeUnaryRaw q.1).reverse ++ s.stk (.inr p.r))) ∧
      PrefixReturned p (L + 1) ((L + 1) ^ 2) L
        (providedCapPrefixEval p (L + 1) ((L + 1) ^ 2) s) ∧
      ((providedCapPrefixEval p (L + 1) ((L + 1) ^ 2) s).stk (.inr p.r)).length ≤
        (s.stk (.inr p.r)).length + L ^ 2 * (L + 3) + 2 * L + 2 * (L + 1) + (L + 1) ^ 2 + 4 := by
  obtain ⟨n, hn, he, hi⟩ := providedCapPrefix_executes p (L + 1) ((L + 1) ^ 2) L s hs
  exact ⟨n, hn, he, providedCapPrefix_original_observation p L s hf, hi,
    providedCapPrefix_record_bound p (L + 1) ((L + 1) ^ 2) L s hs⟩

/- Exact prefix semantics now joins the actual full header/rows routine.
No cap-creation, trailing-suffix check, successful reversal/tag, failure
cleanup, standalone normalizer/constructor/checker, formal source hardness
or kernel evidence is inferred. Original actual-D_lambda endpoint and
original biological/general-DAG obligations are retained, not replaced.
-/

end PolytomyReductionModel
