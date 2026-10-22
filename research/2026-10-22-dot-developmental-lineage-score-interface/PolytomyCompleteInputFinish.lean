/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual full-input suffix check, reversal/tagging and unconditional cleanup.
Output is separate from all ten owned prefix ports. Failure does not skip
cleanup, and a successful prefix with trailing bits is rejected.
-/
import PolytomyOwnedStackCleanup

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def suffixCheckOp : Op (NumericStack K) Bool (CountdownState F) :=
  .peek (.inl .source) (fun s h => (s.1, s.2 && h.isNone))

def suffixChecked (s : CountdownStore (NumericStack K) F) : CountdownStore (NumericStack K) F :=
  suffixCheckOp.apply s

def finishTagOp (o : K) (b : Bool) : Op (NumericStack K) Bool (CountdownState F) :=
  .push (.inr o) (fun _ => b)

def emitFinishedRoutine (r o : K) : Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineControl.branch Prod.snd
    (RoutineComposition.seq (frameReverseRoutine (.inr r) (.inr o)) (Atom.routine (finishTagOp o true)))
    (Atom.routine (finishTagOp o false))

def emitFinishedEval (r o : K) (s : CountdownStore (NumericStack K) F) : CountdownStore (NumericStack K) F :=
  if s.state.2 then (finishTagOp o true).apply (reverseMoveEval (.inr r) (.inr o) s)
  else (finishTagOp o false).apply s

theorem emitFinished_executes (r o : K) (hro : r ≠ o) (s : CountdownStore (NumericStack K) F) :
    ∃ n ≤ (s.stk (.inr r)).length + 3,
      (emitFinishedRoutine r o).Executes s (emitFinishedEval r o s) n := by
  cases hf : s.state.2 with
  | false =>
      refine ⟨2, by omega, ?_⟩
      have h := RoutineControl.branch_false Prod.snd
        (RoutineComposition.seq (frameReverseRoutine (.inr r) (.inr o)) (Atom.routine (finishTagOp o true)))
        (Atom.routine (finishTagOp o false)) hf (Atom.executes (finishTagOp o false) s)
      simpa only [emitFinishedRoutine, emitFinishedEval, hf, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
      have h1 := reverseMove_executes (.inr r : NumericStack K) (.inr o) (by simpa using hro) s
      have h2 := Atom.executes (finishTagOp o true) (reverseMoveEval (.inr r) (.inr o) s)
      have h12 := RoutineComposition.seq_executes (frameReverseRoutine (.inr r) (.inr o))
        (Atom.routine (finishTagOp o true)) h1 h2
      have h := RoutineControl.branch_true Prod.snd
        (RoutineComposition.seq (frameReverseRoutine (.inr r) (.inr o)) (Atom.routine (finishTagOp o true)))
        (Atom.routine (finishTagOp o false)) hf h12
      refine ⟨(s.stk (.inr r)).length + 3, le_refl _, ?_⟩
      simpa only [emitFinishedRoutine, emitFinishedEval, hf, ↓reduceIte, Nat.add_assoc] using h

theorem emitFinished_output (r o : K) (s : CountdownStore (NumericStack K) F)
    (ho : s.stk (.inr o) = []) :
    (emitFinishedEval r o s).stk (.inr o) =
      if s.state.2 then true :: (s.stk (.inr r)).reverse else [false] := by
  cases hf : s.state.2 <;>
    simp [emitFinishedEval, hf, finishTagOp, Op.apply, reverseMoveEval, ho]

theorem emitFinished_length_le (r o : K) (k : NumericStack K) (hko : k ≠ .inr o)
    (s : CountdownStore (NumericStack K) F) :
    ((emitFinishedEval r o s).stk k).length ≤ (s.stk k).length := by
  cases hf : s.state.2 with
  | false => simp [emitFinishedEval, hf, finishTagOp, Op.apply, hko]
  | true =>
      by_cases hkr : k = .inr r
      · simp [emitFinishedEval, hf, finishTagOp, Op.apply, reverseMoveEval, hko, hkr]
      · simp [emitFinishedEval, hf, finishTagOp, Op.apply, reverseMoveEval, hko, hkr]

def prefixOwned (p : PrefixPorts K) : List (NumericStack K) :=
  [.inl .source, .inl .payload, .inl .cap, .inl .work, .inl .output,
    .inr p.r, .inr p.c, .inr p.d, .inr p.b, .inr p.t]

theorem prefixOwned_length (p : PrefixPorts K) : (prefixOwned p).length = 10 := rfl

def finishRoutine (p : PrefixPorts K) (o : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine suffixCheckOp)
    (RoutineComposition.seq (emitFinishedRoutine p.r o) (clearManyRoutine (prefixOwned p)))

def finishEval (p : PrefixPorts K) (o : K) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  clearManyEval (prefixOwned p) (emitFinishedEval p.r o (suffixChecked s))

theorem emitFinished_mass_le (p : PrefixPorts K) (o : K) (ho : .inr o ∉ prefixOwned p)
    (s : CountdownStore (NumericStack K) F) :
    cleanupMass (prefixOwned p) (emitFinishedEval p.r o s) ≤ cleanupMass (prefixOwned p) s := by
  have hlist : ∀ ks : List (NumericStack K), .inr o ∉ ks →
      cleanupMass ks (emitFinishedEval p.r o s) ≤ cleanupMass ks s := by
    intro ks
    induction ks with
    | nil => intro _; simp [cleanupMass]
    | cons k ks ih =>
        intro hnot
        simp only [List.mem_cons, not_or] at hnot
        have hk := emitFinished_length_le p.r o k (Ne.symm hnot.1) s
        have ht := ih hnot.2
        simp only [cleanupMass, List.map_cons, List.sum_cons] at *
        omega
  exact hlist (prefixOwned p) ho

theorem finish_executes (p : PrefixPorts K) (o : K) (hro : p.r ≠ o)
    (ho : .inr o ∉ prefixOwned p) (s : CountdownStore (NumericStack K) F) :
    ∃ n ≤ (s.stk (.inr p.r)).length + cleanupMass (prefixOwned p) s + 15,
      (finishRoutine p o).Executes s (finishEval p o s) n := by
  let u := suffixChecked s
  let v := emitFinishedEval p.r o u
  have h1 := Atom.executes (suffixCheckOp (K := K) (F := F)) s
  obtain ⟨n2, hn2, h2⟩ := emitFinished_executes p.r o hro u
  obtain ⟨n3, hn3, h3⟩ := clearMany_executes (prefixOwned p) v
  have hm := emitFinished_mass_le p o ho u
  have h23 := RoutineComposition.seq_executes (emitFinishedRoutine p.r o) (clearManyRoutine (prefixOwned p)) h2 h3
  have hall := RoutineComposition.seq_executes (Atom.routine suffixCheckOp)
    (RoutineComposition.seq (emitFinishedRoutine p.r o) (clearManyRoutine (prefixOwned p))) h1 h23
  refine ⟨1 + (n2 + n3), ?_, hall⟩
  have hstk : u.stk = s.stk := rfl
  have hmass : cleanupMass (prefixOwned p) u = cleanupMass (prefixOwned p) s := rfl
  rw [hstk] at hn2
  rw [hmass] at hm
  rw [prefixOwned_length] at hn3
  omega

def completedLog : Option (List Bool × List Bool) → List Bool
  | none => [false]
  | some ([], record) => true :: record.reverse
  | some (_ :: _, _) => [false]

theorem finish_output (p : PrefixPorts K) (o : K) (ho : .inr o ∉ prefixOwned p)
    (s : CountdownStore (NumericStack K) F) (hempty : s.stk (.inr o) = []) :
    (finishEval p o s).stk (.inr o) = completedLog (numericListObservation p.r s) := by
  unfold finishEval
  rw [clearMany_outside (prefixOwned p) (.inr o) ho]
  rw [emitFinished_output p.r o (suffixChecked s) hempty]
  cases hf : s.state.2 <;> cases hx : s.stk (.inl .source) <;>
    simp [suffixChecked, suffixCheckOp, Op.apply, hf, hx, numericListObservation, completedLog]

theorem finish_owned_clear (p : PrefixPorts K) (o : K) (k : NumericStack K)
    (hk : k ∈ prefixOwned p) (s : CountdownStore (NumericStack K) F) :
    (finishEval p o s).stk k = [] :=
  clearMany_member (prefixOwned p) k hk (emitFinishedEval p.r o (suffixChecked s))

theorem finish_frame (p : PrefixPorts K) (o : K) (s : CountdownStore (NumericStack K) F) :
    (finishEval p o s).state.1.1 = s.state.1.1 := by
  unfold finishEval
  rw [clearMany_state]
  cases hf : (suffixChecked s).state.2 <;>
    simp [emitFinishedEval, hf, finishTagOp, Op.apply, reverseMoveEval, suffixChecked, suffixCheckOp]

theorem finish_outside (p : PrefixPorts K) (o : K) (k : NumericStack K)
    (hk : k ∉ prefixOwned p) (hko : k ≠ .inr o) (s : CountdownStore (NumericStack K) F) :
    (finishEval p o s).stk k = s.stk k := by
  have hkr : k ≠ .inr p.r := by intro h; apply hk; simp [prefixOwned, h]
  unfold finishEval
  rw [clearMany_outside (prefixOwned p) k hk]
  cases hf : (suffixChecked s).state.2 <;>
    simp [emitFinishedEval, hf, finishTagOp, Op.apply, reverseMoveEval, suffixChecked, suffixCheckOp, hkr, hko]

theorem completedLog_original (bits : List Bool) :
    completedLog ((parseSaturatedSourcePrefix bits.length bits).map
      (fun q => (q.2, (encodeUnaryRaw q.1).reverse))) = normalizedSource bits := by
  cases hp : parseSaturatedSourcePrefix bits.length bits with
  | none => simp [hp, completedLog, normalizedSource, parseSaturatedSource]
  | some q =>
      rcases q with ⟨R, rest⟩
      cases rest <;> simp [hp, completedLog, normalizedSource, parseSaturatedSource]

/- The actual finish now computes exact complete-input output and clears
every owned prefix stack on BOTH flags. Its time is stated in actual
entry record length and owned-stack mass, not yet only original input
length. The all-path counter/mass bound and full standalone normalizer
composition are still required, along with original downstream machinery,
closed compatible hardness and every kernel/dependency check.
-/

end PolytomyReductionModel
