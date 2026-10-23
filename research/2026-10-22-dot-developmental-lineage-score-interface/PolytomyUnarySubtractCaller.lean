/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual finite unary subtraction/comparison for the original downstream
constructor. Consume the right operand, return saturated left difference
and the exact no-underflow bit. Underflow still clears the right suffix.
-/
import PolytomyUnaryProductCaller

namespace PolytomyReductionModel

open Turing StateTransition Lax218471.Subroutine Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def unarySubtractRoutine («left» «right» : K) : Routine (fun _ : K => Bool) (F × Bool) where
  W := Empty
  Δ _ := Bool
  τ := Option Bool
  initial := none
  Label := Bool
  entry := false
  code
    | false => .pop (.inl «right») (fun v h => ((v.1.1, false), h))
        (.branch (fun v => v.2.isSome)
          (.pop (.inl «left») (fun v h => (v.1, h))
            (.branch (fun v => v.2.isSome) (.goto (fun _ => false)) (.goto (fun _ => true))))
          (.load (fun v => ((v.1.1, true), none)) .halt))
    | true => .pop (.inl «right») (fun v h => ((v.1.1, false), h))
        (.branch (fun v => v.2.isSome) (.goto (fun _ => true))
          (.load (fun v => ((v.1.1, false), none)) .halt))

def subtractCallerCfg («left» «right» : K) (l : Option Bool) (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ys : List Bool) :
    TM2.Cfg (Sum.elim (fun _ : K => Bool) (fun _ : Empty => Bool)) Bool ((F × Bool) × Option Bool) :=
  ⟨l, ((frame, flag), o), unaryCallerStacks «left» «right» base xs ys⟩

theorem subtractCaller_boundary («left» «right» : K) (l : Option Bool)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ys : List Bool) :
    subtractCallerCfg «left» «right» l none base frame flag xs ys =
      (unarySubtractRoutine «left» «right»).boundary l (frameCallerStore «left» «right» base frame flag xs ys) := by
  apply RoutineComposition.cfg_ext
  · rfl
  · rfl
  · funext k; cases k with
    | inl k => rfl
    | inr e => nomatch e

theorem subtract_done («left» «right» : K) (hne : «left» ≠ «right») (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs : List Bool) :
    TM2.step (unarySubtractRoutine «left» «right»).code
      (subtractCallerCfg «left» «right» (some false) o base frame flag xs []) =
      some (subtractCallerCfg «left» «right» none none base frame true xs []) := by
  simp [unarySubtractRoutine, subtractCallerCfg, TM2.step, TM2.stepAux,
    unaryCallerStacks_output, unaryCallerStacks, hne]

theorem subtract_pair («left» «right» : K) (hne : «left» ≠ «right») (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag a b : Bool) (xs ys : List Bool) :
    TM2.step (unarySubtractRoutine «left» «right»).code
      (subtractCallerCfg «left» «right» (some false) o base frame flag (a :: xs) (b :: ys)) =
      some (subtractCallerCfg «left» «right» (some false) (some a) base frame false xs ys) := by
  simp [unarySubtractRoutine, subtractCallerCfg, TM2.step, TM2.stepAux,
    unaryCallerStacks_output, unaryCallerStacks_source, unaryCallerStacks, hne]

theorem subtract_underflow («left» «right» : K) (hne : «left» ≠ «right») (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag b : Bool) (ys : List Bool) :
    TM2.step (unarySubtractRoutine «left» «right»).code
      (subtractCallerCfg «left» «right» (some false) o base frame flag [] (b :: ys)) =
      some (subtractCallerCfg «left» «right» (some true) none base frame false [] ys) := by
  simp [unarySubtractRoutine, subtractCallerCfg, TM2.step, TM2.stepAux,
    unaryCallerStacks_output, unaryCallerStacks_source, unaryCallerStacks, hne]

theorem subtract_clear_nil («left» «right» : K) (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs : List Bool) :
    TM2.step (unarySubtractRoutine «left» «right»).code
      (subtractCallerCfg «left» «right» (some true) o base frame flag xs []) =
      some (subtractCallerCfg «left» «right» none none base frame false xs []) := by
  simp [unarySubtractRoutine, subtractCallerCfg, TM2.step, TM2.stepAux,
    unaryCallerStacks_output, unaryCallerStacks]

theorem subtract_clear_cons («left» «right» : K) (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag b : Bool) (xs ys : List Bool) :
    TM2.step (unarySubtractRoutine «left» «right»).code
      (subtractCallerCfg «left» «right» (some true) o base frame flag xs (b :: ys)) =
      some (subtractCallerCfg «left» «right» (some true) (some b) base frame false xs ys) := by
  simp [unarySubtractRoutine, subtractCallerCfg, TM2.step, TM2.stepAux,
    unaryCallerStacks_output, unaryCallerStacks]

theorem subtractClearRun («left» «right» : K) (base : K → List Bool) (frame : F)
    (xs ys : List Bool) : ∀ o flag,
    Runs (TM2.step (unarySubtractRoutine «left» «right»).code)
      (subtractCallerCfg «left» «right» (some true) o base frame flag xs ys)
      (subtractCallerCfg «left» «right» none none base frame false xs []) (ys.length + 1) := by
  induction ys with
  | nil => intro o flag; exact Runs.one (subtract_clear_nil «left» «right» o base frame flag xs)
  | cons b ys ih =>
      intro o flag
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Runs.cons (subtract_clear_cons «left» «right» o base frame flag b xs ys) (ih (some b) false)

theorem unarySubtractRun («left» «right» : K) (hne : «left» ≠ «right»)
    (base : K → List Bool) (frame : F) (D : ℕ) : ∀ C o flag,
    Runs (TM2.step (unarySubtractRoutine «left» «right»).code)
      (subtractCallerCfg «left» «right» (some false) o base frame flag
        (List.replicate C true) (List.replicate D true))
      (subtractCallerCfg «left» «right» none none base frame (decide (D ≤ C))
        (List.replicate (C - D) true) []) (D + 1) := by
  induction D with
  | zero =>
      intro C o flag
      simpa using Runs.one (subtract_done «left» «right» hne o base frame flag (List.replicate C true))
  | succ D ih =>
      intro C o flag
      cases C with
      | zero =>
          have r := Runs.cons (subtract_underflow «left» «right» hne o base frame flag true (List.replicate D true))
            (subtractClearRun «left» «right» base frame [] (List.replicate D true) none false)
          simpa [List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r
      | succ C =>
          have r := Runs.cons (subtract_pair «left» «right» hne o base frame flag true true
            (List.replicate C true) (List.replicate D true)) (ih C (some true) false)
          simpa [List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

/-- Exact no-underflow flag and saturated difference; right operand is
    consumed even if it exceeds left. All other caller data/F survives. -/
theorem unarySubtract_executes («left» «right» : K) (hne : «left» ≠ «right»)
    (base : K → List Bool) (frame : F) (flag : Bool) (C D : ℕ) :
    (unarySubtractRoutine «left» «right»).Executes
      (frameCallerStore «left» «right» base frame flag (List.replicate C true) (List.replicate D true))
      (frameCallerStore «left» «right» base frame (decide (D ≤ C)) (List.replicate (C - D) true) [])
      (D + 1) := by
  have r := unarySubtractRun «left» «right» hne base frame D C none flag
  rw [subtractCaller_boundary, subtractCaller_boundary] at r
  exact r.iterate

/- This NEW arithmetic attempt overwrites its result flag deliberately;
it is not a failure-absorbing parser. A caller must explicitly guard it or
save other flags in F. Original operands that must survive require actual
copies. The result bit distinguishes equality/success from underflow even
when both differences are zero. Whole original downstream constructor,
independent checker, hardness and kernel obligations remain open.
-/

end PolytomyReductionModel
