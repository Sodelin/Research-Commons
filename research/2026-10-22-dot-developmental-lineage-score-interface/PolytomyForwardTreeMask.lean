/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual forward-order legal-node mask. The logger's reversed physical word
is transferred through the inspected instruction-level reverse routine;
there is no assumed reversal oracle or uncharged traversal.
-/
import PolytomyTreeMaskCaller

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471Proofs

variable {K F : Type} [DecidableEq K]

theorem treeMask_reverse_rotate (p : TreeMaskPorts K) (base : K → List Bool)
    (frame : F) (flag : Bool) (xs rev out : List Bool) :
    treeMaskCallerStore p (Function.update base p.output out) frame flag xs [] rev =
      frameCallerStore p.reverse p.output
        (Function.update (Function.update base p.source xs) p.pending []) frame flag rev out := by
  unfold treeMaskCallerStore frameCallerStore
  congr 1
  funext k
  by_cases ho : k = p.output <;> by_cases hr : k = p.reverse <;>
    by_cases hp : k = p.pending <;> by_cases hs : k = p.source <;>
    simp_all [p.hsp, p.hsr, p.hso, p.hpr, p.hpo, p.hro,
      Ne.symm p.hsp, Ne.symm p.hsr, Ne.symm p.hso,
      Ne.symm p.hpr, Ne.symm p.hpo, Ne.symm p.hro]

def treeMaskForwardRoutine (p : TreeMaskPorts K) : Routine (fun _ : K => Bool) (F × Bool) :=
  RoutineComposition.seq (treeMaskCallerRoutine p .start) (frameReverseRoutine p.reverse p.output)

def treeMaskForwardResult (p : TreeMaskPorts K) (base : K → List Bool) (frame : F) :
    Option (List Bool × List Bool) → Store (fun _ : K => Bool) (F × Bool)
  | none => treeMaskCallerStore p (Function.update base p.output []) frame false [] [] []
  | some (rest, mask) => treeMaskCallerStore p (Function.update base p.output mask) frame true rest [] []

/-- Every original raw input word, exact suffix and forward mask, both
    scratch ports clean, and an actual time bound including reversal. -/
theorem treeMaskForward_executes (p : TreeMaskPorts K) (base : K → List Bool)
    (frame : F) (flag : Bool) (bits : List Bool) :
    ∃ n ≤ 4 * bits.length + 6,
      (treeMaskForwardRoutine p).Executes
        (treeMaskCallerStore p (Function.update base p.output []) frame flag bits [] [])
        (treeMaskForwardResult p base frame (rawForestMaskParse bits.length 1 bits)) n := by
  obtain ⟨n, hn, hparse⟩ := treeMaskCaller_prefix_executes p
    (Function.update base p.output []) frame flag bits
  cases hp : rawForestMaskParse bits.length 1 bits with
  | none =>
      have hreverse := frameReverse_executes p.reverse p.output p.hro
        (Function.update (Function.update base p.source []) p.pending []) frame false [] []
      have hparse' : (treeMaskCallerRoutine p .start).Executes
          (treeMaskCallerStore p (Function.update base p.output []) frame flag bits [] [])
          (frameCallerStore p.reverse p.output
            (Function.update (Function.update base p.source []) p.pending []) frame false [] []) n := by
        simpa only [hp, treeMaskCallerResult, treeMask_reverse_rotate] using hparse
      have hjoin := RoutineComposition.seq_executes (treeMaskCallerRoutine p .start)
        (frameReverseRoutine p.reverse p.output) hparse' hreverse
      have hfinish := treeMask_reverse_rotate p base frame false [] [] []
      rw [← hfinish] at hjoin
      refine ⟨n + 1, by omega, ?_⟩
      simpa only [treeMaskForwardRoutine, treeMaskForwardResult, hp, List.length_nil,
        List.reverse_nil, List.nil_append] using hjoin
  | some result =>
      rcases result with ⟨rest, mask⟩
      have hlen := rawForestMaskParse_consumption bits rest mask 1 hp
      have hreverse := frameReverse_executes p.reverse p.output p.hro
        (Function.update (Function.update base p.source rest) p.pending []) frame true mask.reverse []
      have hparse' : (treeMaskCallerRoutine p .start).Executes
          (treeMaskCallerStore p (Function.update base p.output []) frame flag bits [] [])
          (frameCallerStore p.reverse p.output
            (Function.update (Function.update base p.source rest) p.pending [])
            frame true mask.reverse []) n := by
        simpa only [hp, treeMaskCallerResult, List.append_nil, treeMask_reverse_rotate] using hparse
      have hjoin := RoutineComposition.seq_executes (treeMaskCallerRoutine p .start)
        (frameReverseRoutine p.reverse p.output) hparse' hreverse
      have hfinish := treeMask_reverse_rotate p base frame true rest [] mask
      simp only [List.reverse_reverse, List.append_nil] at hjoin
      rw [← hfinish] at hjoin
      refine ⟨n + (mask.length + 1), by omega, ?_⟩
      simpa only [treeMaskForwardRoutine, treeMaskForwardResult, hp, List.length_reverse] using hjoin

theorem treeMaskForward_observation (p : TreeMaskPorts K) (base : K → List Bool)
    (frame : F) (result : Option (List Bool × List Bool)) :
    (if (treeMaskForwardResult p base frame result).state.2 then
      some ((treeMaskForwardResult p base frame result).stk p.source,
        (treeMaskForwardResult p base frame result).stk p.output) else none) = result := by
  cases result with
  | none => rfl
  | some v =>
      rcases v with ⟨rest, mask⟩
      simp [treeMaskForwardResult, treeMaskCallerStore, frameCallerStore,
        p.hsp, p.hsr, p.hso, Ne.symm p.hpo, Ne.symm p.hro]

theorem treeMaskForward_preserves (p : TreeMaskPorts K) (k : K)
    (hs : k ≠ p.source) (hp : k ≠ p.pending) (hr : k ≠ p.reverse) (ho : k ≠ p.output)
    (base : K → List Bool) (frame : F) (result : Option (List Bool × List Bool)) :
    (treeMaskForwardResult p base frame result).state.1 = frame ∧
      (treeMaskForwardResult p base frame result).stk p.pending = [] ∧
      (treeMaskForwardResult p base frame result).stk p.reverse = [] ∧
      (treeMaskForwardResult p base frame result).stk k = base k := by
  cases result <;> simp [treeMaskForwardResult, treeMaskCallerStore, frameCallerStore,
    p.hpr, hs, hp, hr, ho]

/- Token-position correctness is supplied by rawForestMaskParse_all_words
   and rawMarkedSuffixes_tree. Physical bounded-index replay and all typed
   target/clade/score predicates still need their full emitted composition. -/

end PolytomyReductionModel
