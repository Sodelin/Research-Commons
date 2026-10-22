/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual cleanup independent of the parser success flag. A failed parser
must still drain partial counters/records; a failure-guarded countdown
would not do that. Every outside stack and public state are preserved.
-/
import PolytomyOriginalCapPreparation

namespace PolytomyReductionModel

open Turing StateTransition Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def clearStackRoutine (k : K) : Routine (fun _ : K => Bool) (CountdownState F) where
  W := Empty
  Δ _ := Bool
  τ := Option Bool
  initial := none
  Label := Unit
  entry := ()
  code _ := .pop (.inl k) (fun v h => (v.1, h))
    (.branch (fun v => v.2.isSome) (.goto (fun _ => ()))
      (.load (fun v => (v.1, none)) .halt))

def clearStackEval (k : K) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨s.state, Function.update s.stk k []⟩

def clearCallerStacks (k : K) (base : K → List Bool) (xs : List Bool) :
    ∀ j : K ⊕ Empty, List ((Sum.elim (fun _ : K => Bool) (fun _ : Empty => Bool)) j)
  | .inl j => Function.update base k xs j
  | .inr e => nomatch e

theorem clearCallerStacks_update (k : K) (base : K → List Bool) (xs ys : List Bool) :
    Function.update (clearCallerStacks k base xs) (.inl k) ys = clearCallerStacks k base ys := by
  funext j
  cases j with
  | inl j => by_cases hj : j = k <;> simp [clearCallerStacks, hj]
  | inr e => nomatch e

def clearCallerCfg (k : K) (l : Option Unit) (o : Option Bool)
    (base : K → List Bool) (state : CountdownState F) (xs : List Bool) :
    TM2.Cfg (Sum.elim (fun _ : K => Bool) (fun _ : Empty => Bool))
      Unit (CountdownState F × Option Bool) :=
  ⟨l, (state, o), clearCallerStacks k base xs⟩

theorem clearCaller_boundary (k : K) (l : Option Unit) (base : K → List Bool)
    (state : CountdownState F) (xs : List Bool) :
    clearCallerCfg k l none base state xs =
      (clearStackRoutine k).boundary l ⟨state, Function.update base k xs⟩ := by
  apply RoutineComposition.cfg_ext
  · rfl
  · rfl
  · funext j; cases j with
    | inl j => rfl
    | inr e => nomatch e

theorem clearStack_nil (k : K) (o : Option Bool) (base : K → List Bool) (state : CountdownState F) :
    TM2.step (clearStackRoutine (F := F) k).code (clearCallerCfg k (some ()) o base state []) =
      some (clearCallerCfg k none none base state []) := by
  simp [clearStackRoutine, clearCallerCfg, TM2.step, TM2.stepAux, clearCallerStacks_update, clearCallerStacks]

theorem clearStack_cons (k : K) (o : Option Bool) (base : K → List Bool)
    (state : CountdownState F) (b : Bool) (xs : List Bool) :
    TM2.step (clearStackRoutine (F := F) k).code (clearCallerCfg k (some ()) o base state (b :: xs)) =
      some (clearCallerCfg k (some ()) (some b) base state xs) := by
  simp [clearStackRoutine, clearCallerCfg, TM2.step, TM2.stepAux, clearCallerStacks_update, clearCallerStacks]

theorem clearStackRun (k : K) (base : K → List Bool) (state : CountdownState F)
    (xs : List Bool) : ∀ o,
    Runs (TM2.step (clearStackRoutine (F := F) k).code)
      (clearCallerCfg k (some ()) o base state xs) (clearCallerCfg k none none base state []) (xs.length + 1) := by
  induction xs with
  | nil => intro o; exact Runs.one (clearStack_nil k o base state)
  | cons b xs ih =>
      intro o
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Runs.cons (clearStack_cons k o base state b xs) (ih (some b))

theorem clearStack_executes (k : K) (s : CountdownStore K F) :
    (clearStackRoutine k).Executes s (clearStackEval k s) ((s.stk k).length + 1) := by
  have r := clearStackRun k s.stk s.state (s.stk k) none
  rw [clearCaller_boundary, clearCaller_boundary] at r
  have hs : (⟨s.state, Function.update s.stk k (s.stk k)⟩ : CountdownStore K F) = s := by
    apply countdownStore_ext
    · rfl
    · funext j; by_cases hj : j = k <;> simp [hj]
  rw [hs] at r
  exact r.iterate

def cleanupNoop : Op K Bool (CountdownState F) := .load id

def clearManyRoutine : List K → Routine (fun _ : K => Bool) (CountdownState F)
  | [] => Atom.routine cleanupNoop
  | k :: ks => RoutineComposition.seq (clearStackRoutine k) (clearManyRoutine ks)

def clearManyEval : List K → CountdownStore K F → CountdownStore K F
  | [], s => s
  | k :: ks, s => clearManyEval ks (clearStackEval k s)

def cleanupMass (ks : List K) (s : CountdownStore K F) : ℕ :=
  (ks.map (fun k => (s.stk k).length)).sum

theorem clearStack_mass_le (k : K) (ks : List K) (s : CountdownStore K F) :
    cleanupMass ks (clearStackEval k s) ≤ cleanupMass ks s := by
  induction ks with
  | nil => simp [cleanupMass]
  | cons j ks ih =>
      have hlen : ((clearStackEval k s).stk j).length ≤ (s.stk j).length := by
        by_cases hj : j = k <;> simp [clearStackEval, hj]
      simp only [cleanupMass, List.map_cons, List.sum_cons] at *
      omega

theorem clearMany_executes (ks : List K) (s : CountdownStore K F) :
    ∃ n ≤ cleanupMass ks s + ks.length + 1,
      (clearManyRoutine ks).Executes s (clearManyEval ks s) n := by
  induction ks generalizing s with
  | nil => exact ⟨1, by simp [cleanupMass], Atom.executes cleanupNoop s⟩
  | cons k ks ih =>
      obtain ⟨n, hn, he⟩ := ih (clearStackEval k s)
      have hm := clearStack_mass_le k ks s
      have hall := RoutineComposition.seq_executes (clearStackRoutine k) (clearManyRoutine ks)
        (clearStack_executes k s) he
      refine ⟨(s.stk k).length + 1 + n, ?_, hall⟩
      simp only [cleanupMass, List.map_cons, List.sum_cons, List.length_cons] at *
      omega

theorem clearMany_state (ks : List K) (s : CountdownStore K F) :
    (clearManyEval ks s).state = s.state := by
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih => exact ih (clearStackEval k s)

theorem clearMany_outside (ks : List K) (k : K) (hk : k ∉ ks) (s : CountdownStore K F) :
    (clearManyEval ks s).stk k = s.stk k := by
  induction ks generalizing s with
  | nil => rfl
  | cons j ks ih =>
      simp only [List.mem_cons, not_or] at hk
      rw [clearManyEval, ih hk.2]
      simp [clearStackEval, hk.1]

theorem clearMany_member (ks : List K) (k : K) (hk : k ∈ ks) (s : CountdownStore K F) :
    (clearManyEval ks s).stk k = [] := by
  induction ks generalizing s with
  | nil => simp at hk
  | cons j ks ih =>
      rw [clearManyEval]
      by_cases htail : k ∈ ks
      · exact ih htail (clearStackEval j s)
      · rw [clearMany_outside ks k htail]
        have hkj : k = j := by simpa [htail] using hk
        simp [clearStackEval, hkj]

/- Cleanup is total for both success flags and arbitrary bit words. List
duplicates are allowed and do not increase the stated initial-mass upper
bound; output/foreign ports are preserved only when absent from the list.
Actual whole-parser finish and all-path mass bounds are still to be joined.
-/

end PolytomyReductionModel
