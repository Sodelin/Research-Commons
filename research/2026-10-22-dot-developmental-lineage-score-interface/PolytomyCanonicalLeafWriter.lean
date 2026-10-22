/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual original canonical leaf-token writer. Both physical unary values
survive, target may already contain output, and the temporary returns empty.
The byte order is original true :: (U block ++ U type), not a new encoding.
-/
import PolytomyAdditionalCallerPorts

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def prependBitOp (target : K) (bit : Bool) : Op K Bool (CountdownState F) :=
  .push target (fun _ => bit)

def unaryPrependRoutine (value temp target : K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (prependBitOp target false)) (wordDuplicateRoutine value temp target)

def unaryPrependEval (value target : K) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨s.state, Function.update s.stk target (s.stk value ++ false :: s.stk target)⟩

theorem unaryPrepend_executes (value temp target : K)
    (hvt : value ≠ temp) (hvo : value ≠ target) (hto : temp ≠ target)
    (s : CountdownStore K F) (ht : s.stk temp = []) :
    (unaryPrependRoutine value temp target).Executes s (unaryPrependEval value target s)
      (3 * (s.stk value).length + 4) := by
  let u := (prependBitOp target false).apply s
  have hu : u.stk temp = [] := by simp [u, prependBitOp, Op.apply, hto, ht]
  have hcopy := wordDuplicate_executes value temp target hvt hvo hto u hu
  have he : wordDuplicateEval value target u = unaryPrependEval value target s := by
    apply countdownStore_ext
    · rfl
    · funext k; by_cases hk : k = target <;>
        simp [wordDuplicateEval, unaryPrependEval, u, prependBitOp, Op.apply, hk, hvo]
  have hlen : (u.stk value).length = (s.stk value).length := by simp [u, prependBitOp, Op.apply, hvo]
  rw [he, hlen] at hcopy
  have hall := RoutineComposition.seq_executes (Atom.routine (prependBitOp target false))
    (wordDuplicateRoutine value temp target) (Atom.executes (prependBitOp target false) s) hcopy
  simpa only [unaryPrependRoutine, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hall

theorem unaryPrepend_bytes (value target : K) (s : CountdownStore K F) (hv : IsUnaryWord (s.stk value)) :
    (unaryPrependEval value target s).stk target = unaryFrame (s.stk value).length ++ s.stk target := by
  simp only [unaryPrependEval, Function.update_same, hv, unaryFrame, List.append_assoc, List.singleton_append]

theorem unaryPrepend_extra (value target k : K) (hk : k ≠ target) (s : CountdownStore K F) :
    (unaryPrependEval value target s).stk k = s.stk k := by simp [unaryPrependEval, hk]

def canonicalLeafRoutine (block value temp target : K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (unaryPrependRoutine value temp target)
    (RoutineComposition.seq (unaryPrependRoutine block temp target) (Atom.routine (prependBitOp target true)))

def canonicalLeafEval (block value target : K) (s : CountdownStore K F) :=
  (prependBitOp target true).apply (unaryPrependEval block target (unaryPrependEval value target s))

theorem canonicalLeaf_executes (block value temp target : K)
    (hbt : block ≠ temp) (hbo : block ≠ target) (hvt : value ≠ temp) (hvo : value ≠ target)
    (hto : temp ≠ target) (s : CountdownStore K F) (ht : s.stk temp = []) :
    (canonicalLeafRoutine block value temp target).Executes s (canonicalLeafEval block value target s)
      (3 * (s.stk value).length + 3 * (s.stk block).length + 9) := by
  let u := unaryPrependEval value target s
  let v := unaryPrependEval block target u
  have h1 := unaryPrepend_executes value temp target hvt hvo hto s ht
  have hu : u.stk temp = [] := (unaryPrepend_extra value target temp hto s).trans ht
  have h2 := unaryPrepend_executes block temp target hbt hbo hto u hu
  have hlen : (u.stk block).length = (s.stk block).length := by rw [unaryPrepend_extra value target block hbo]
  rw [hlen] at h2
  have h3 := Atom.executes (prependBitOp target true) v
  have h23 := RoutineComposition.seq_executes (unaryPrependRoutine block temp target)
    (Atom.routine (prependBitOp target true)) h2 h3
  have hall := RoutineComposition.seq_executes (unaryPrependRoutine value temp target)
    (RoutineComposition.seq (unaryPrependRoutine block temp target) (Atom.routine (prependBitOp target true))) h1 h23
  convert hall using 1 <;> omega

theorem canonicalLeaf_bytes (block value target : K) (hbo : block ≠ target)
    (s : CountdownStore K F) (hb : IsUnaryWord (s.stk block)) (hv : IsUnaryWord (s.stk value)) :
    (canonicalLeafEval block value target s).stk target =
      true :: (unaryFrame (s.stk block).length ++ unaryFrame (s.stk value).length ++ s.stk target) := by
  have hblock : (unaryPrependEval value target s).stk block = s.stk block := unaryPrepend_extra value target block hbo s
  simp only [canonicalLeafEval, prependBitOp, Op.apply, Function.update_same]
  rw [unaryPrepend_bytes block target _ (by simpa [hblock] using hb), hblock, unaryPrepend_bytes value target s hv]
  simp only [List.append_assoc]

theorem canonicalLeaf_extra (block value target k : K) (hk : k ≠ target) (s : CountdownStore K F) :
    (canonicalLeafEval block value target s).stk k = s.stk k := by
  simp [canonicalLeafEval, prependBitOp, Op.apply, unaryPrependEval, hk]

/- Descending type enumeration can prepend accepted leaf tokens to obtain
the original ascending code order. The enumeration/membership controller,
comb-node prefixes, cost accumulation and target header serializer still
need actual composition. This writer alone is not a canonical constructor.
-/

end PolytomyReductionModel
