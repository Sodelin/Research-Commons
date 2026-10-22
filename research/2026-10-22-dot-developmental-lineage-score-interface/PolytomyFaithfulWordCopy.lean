/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual faithful arbitrary-bit copy for repeated ORIGINAL record scans.
The source and all caller state survive. Unlike a unary tally copy, false
bits are not replaced by true. Private restore work is emptied on return.
-/
import PolytomyUnaryDownstreamValidation

namespace PolytomyReductionModel

open Turing StateTransition Lax218471.Subroutine Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def wordCopyStacks (source target : K) (base : K → List Bool) (xs ys zs : List Bool) :
    ∀ j : K ⊕ Unit, List ((Sum.elim (fun _ : K => Bool) (fun _ : Unit => Bool)) j)
  | .inl k => Function.update (Function.update base source xs) target ys k
  | .inr _ => zs

theorem wordCopyStacks_source (source target : K) (hne : source ≠ target)
    (base : K → List Bool) (xs ys zs ws : List Bool) :
    Function.update (wordCopyStacks source target base xs ys zs) (.inl source) ws =
      wordCopyStacks source target base ws ys zs := by
  funext j; cases j with
  | inr u => cases u; simp [wordCopyStacks]
  | inl k => by_cases hkt : k = target <;> by_cases hks : k = source <;>
      simp_all [wordCopyStacks]

theorem wordCopyStacks_target (source target : K) (base : K → List Bool) (xs ys zs ws : List Bool) :
    Function.update (wordCopyStacks source target base xs ys zs) (.inl target) ws =
      wordCopyStacks source target base xs ws zs := by
  funext j; cases j with
  | inr u => cases u; simp [wordCopyStacks]
  | inl k => by_cases hkt : k = target <;> simp [wordCopyStacks, hkt]

theorem wordCopyStacks_restore (source target : K) (base : K → List Bool) (xs ys zs ws : List Bool) :
    Function.update (wordCopyStacks source target base xs ys zs) (.inr ()) ws =
      wordCopyStacks source target base xs ys ws := by
  funext j; cases j with
  | inr u => cases u; simp [wordCopyStacks]
  | inl k => simp [wordCopyStacks]

def wordCopyRoutine (source target : K) : Routine (fun _ : K => Bool) (F × Bool) where
  W := Unit
  Δ _ := Bool
  τ := Option Bool
  initial := none
  Label := Bool
  entry := false
  code
    | false => .pop (.inl source) (fun v h => (v.1, h))
        (.branch (fun v => v.2.isSome)
          (.push (.inl target) (fun v => v.2.getD false)
            (.push (.inr ()) (fun v => v.2.getD false) (.goto (fun _ => false))))
          (.goto (fun _ => true)))
    | true => .pop (.inr ()) (fun v h => (v.1, h))
        (.branch (fun v => v.2.isSome)
          (.push (.inl source) (fun v => v.2.getD false) (.goto (fun _ => true)))
          (.load (fun v => (v.1, none)) .halt))

def wordCopyCfg (source target : K) (l : Option Bool) (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ys zs : List Bool) :
    TM2.Cfg (Sum.elim (fun _ : K => Bool) (fun _ : Unit => Bool)) Bool ((F × Bool) × Option Bool) :=
  ⟨l, ((frame, flag), o), wordCopyStacks source target base xs ys zs⟩

theorem wordCopy_boundary (source target : K) (l : Option Bool)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ys : List Bool) :
    wordCopyCfg source target l none base frame flag xs ys [] =
      (wordCopyRoutine source target).boundary l (frameCallerStore source target base frame flag xs ys) := by
  apply RoutineComposition.cfg_ext
  · rfl
  · rfl
  · funext j; cases j <;> rfl

theorem wordCopy_copy_nil (source target : K) (hne : source ≠ target) (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag : Bool) (ys zs : List Bool) :
    TM2.step (wordCopyRoutine source target).code
      (wordCopyCfg source target (some false) o base frame flag [] ys zs) =
      some (wordCopyCfg source target (some true) none base frame flag [] ys zs) := by
  simp [wordCopyRoutine, wordCopyCfg, TM2.step, TM2.stepAux, wordCopyStacks_source, wordCopyStacks, hne]

theorem wordCopy_copy_cons (source target : K) (hne : source ≠ target) (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag b : Bool) (xs ys zs : List Bool) :
    TM2.step (wordCopyRoutine source target).code
      (wordCopyCfg source target (some false) o base frame flag (b :: xs) ys zs) =
      some (wordCopyCfg source target (some false) (some b) base frame flag xs (b :: ys) (b :: zs)) := by
  simp [wordCopyRoutine, wordCopyCfg, TM2.step, TM2.stepAux, wordCopyStacks_source,
    wordCopyStacks_target, wordCopyStacks_restore, wordCopyStacks, hne]

theorem wordCopy_restore_nil (source target : K) (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ys : List Bool) :
    TM2.step (wordCopyRoutine source target).code
      (wordCopyCfg source target (some true) o base frame flag xs ys []) =
      some (wordCopyCfg source target none none base frame flag xs ys []) := by
  simp [wordCopyRoutine, wordCopyCfg, TM2.step, TM2.stepAux, wordCopyStacks_restore, wordCopyStacks]

theorem wordCopy_restore_cons (source target : K) (hne : source ≠ target) (o : Option Bool)
    (base : K → List Bool) (frame : F) (flag b : Bool) (xs ys zs : List Bool) :
    TM2.step (wordCopyRoutine source target).code
      (wordCopyCfg source target (some true) o base frame flag xs ys (b :: zs)) =
      some (wordCopyCfg source target (some true) (some b) base frame flag (b :: xs) ys zs) := by
  simp [wordCopyRoutine, wordCopyCfg, TM2.step, TM2.stepAux, wordCopyStacks_restore,
    wordCopyStacks_source, wordCopyStacks, hne]

theorem wordCopyRestoreRun (source target : K) (hne : source ≠ target)
    (base : K → List Bool) (frame : F) (flag : Bool) (zs ys : List Bool) : ∀ xs o,
    Runs (TM2.step (wordCopyRoutine source target).code)
      (wordCopyCfg source target (some true) o base frame flag xs ys zs)
      (wordCopyCfg source target none none base frame flag (zs.reverse ++ xs) ys []) (zs.length + 1) := by
  induction zs with
  | nil => intro xs o; simpa using Runs.one (wordCopy_restore_nil source target o base frame flag xs ys)
  | cons b zs ih =>
      intro xs o
      have r := Runs.cons (wordCopy_restore_cons source target hne o base frame flag b xs ys zs)
        (ih (b :: xs) (some b))
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

theorem wordCopyRun (source target : K) (hne : source ≠ target)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs : List Bool) : ∀ ys zs o,
    Runs (TM2.step (wordCopyRoutine source target).code)
      (wordCopyCfg source target (some false) o base frame flag xs ys zs)
      (wordCopyCfg source target none none base frame flag (zs.reverse ++ xs) (xs.reverse ++ ys) [])
      (2 * xs.length + zs.length + 2) := by
  induction xs with
  | nil =>
      intro ys zs o
      have r := Runs.cons (wordCopy_copy_nil source target hne o base frame flag ys zs)
        (wordCopyRestoreRun source target hne base frame flag zs ys [] none)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r
  | cons b xs ih =>
      intro ys zs o
      have r := Runs.cons (wordCopy_copy_cons source target hne o base frame flag b xs ys zs)
        (ih (b :: ys) (b :: zs) (some b))
      simpa [List.reverse_cons, List.append_assoc, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using r

theorem wordCopy_executes (source target : K) (hne : source ≠ target)
    (base : K → List Bool) (frame : F) (flag : Bool) (xs ys : List Bool) :
    (wordCopyRoutine source target).Executes (frameCallerStore source target base frame flag xs ys)
      (frameCallerStore source target base frame flag xs (xs.reverse ++ ys)) (2 * xs.length + 2) := by
  have r := wordCopyRun source target hne base frame flag xs ys [] none
  simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero] at r
  rw [wordCopy_boundary, wordCopy_boundary] at r
  exact r.iterate

def wordDuplicateRoutine (source temp target : K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (wordCopyRoutine (F := F × Bool) source temp) (frameReverseRoutine temp target)

def wordDuplicateEval (source target : K) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨s.state, Function.update s.stk target (s.stk source ++ s.stk target)⟩

theorem wordDuplicate_executes (source temp target : K)
    (hst : source ≠ temp) (hso : source ≠ target) (hto : temp ≠ target)
    (s : CountdownStore K F) (ht : s.stk temp = []) :
    (wordDuplicateRoutine source temp target).Executes s (wordDuplicateEval source target s)
      (3 * (s.stk source).length + 3) := by
  let u := frameCallerStore source temp s.stk s.state.1 s.state.2 (s.stk source) (s.stk source).reverse
  have h1 := wordCopy_executes source temp hst s.stk s.state.1 s.state.2 (s.stk source) (s.stk temp)
  rw [frameCallerStore_self, ht, List.append_nil] at h1
  have h2 := reverseMove_executes temp target hto u
  have he : reverseMoveEval temp target u = wordDuplicateEval source target s := by
    apply countdownStore_ext
    · rfl
    · funext k
      by_cases hko : k = target
      · subst k; simp [u, reverseMoveEval, wordDuplicateEval, frameCallerStore, hst, hso, hto, Ne.symm hso, Ne.symm hto]
      · by_cases hkt : k = temp
        · subst k; simp [u, reverseMoveEval, wordDuplicateEval, frameCallerStore, ht, hko]
        · by_cases hks : k = source
          · subst k; simp [u, reverseMoveEval, wordDuplicateEval, frameCallerStore, hst, hso]
          · simp [u, reverseMoveEval, wordDuplicateEval, frameCallerStore, hko, hkt, hks]
  rw [he] at h2
  have hall := RoutineComposition.seq_executes (wordCopyRoutine (F := F × Bool) source temp)
    (frameReverseRoutine temp target) h1 h2
  convert hall using 1 <;> simp [wordDuplicateRoutine, u, frameCallerStore] <;> omega

/- The source, whole public state, and every port except target are
preserved; initially empty temp returns empty. Target receives original
source in FORWARD order, prepended to any previous target content. For a
fresh scan, target must explicitly start empty. Cost 3L+3 includes source
restoration and final reversal; private work/control are clean. Actual
structured unary-record scans and bounded coverage-loop composition
remain next, with the whole original constructor/checker/hardness/kernel
obligations unchanged. No unary-only copy is used on record bits.
-/

end PolytomyReductionModel
