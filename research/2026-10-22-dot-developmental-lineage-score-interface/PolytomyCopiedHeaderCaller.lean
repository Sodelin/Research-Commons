/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual faithful record copy followed by tagged physical header extraction.
The original record remains available for repeated ORIGINAL validator
scans; header success does not imply valid rows or complete input.
-/
import PolytomyInternalHeaderCaller

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def copiedHeaderRoutine (original temp : K) (p : InternalHeaderPorts K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (wordDuplicateRoutine original temp p.source) (internalHeaderRoutine p)

def copiedHeaderEval (original : K) (p : InternalHeaderPorts K) (s : CountdownStore K F) :
    CountdownStore K F := internalHeaderEval p (wordDuplicateEval original p.source s)

theorem copiedHeader_executes (original temp : K) (p : InternalHeaderPorts K)
    (hot : original ≠ temp) (hos : original ≠ p.source) (hts : temp ≠ p.source)
    (s : CountdownStore K F) (ht : s.stk temp = []) (hs : s.stk p.source = [])
    (hn : s.stk p.n = []) (hm : s.stk p.m = []) (hk : s.stk p.k = []) :
    ∃ steps ≤ 9 * (s.stk original).length + 16,
      (copiedHeaderRoutine original temp p).Executes s (copiedHeaderEval original p s) steps ∧
      internalHeaderObservation p (copiedHeaderEval original p s) = readInternalHeaderPrefix (s.stk original) ∧
      ((copiedHeaderEval original p s).stk p.source).length ≤ (s.stk original).length ∧
      ((copiedHeaderEval original p s).stk p.n).length ≤ (s.stk original).length ∧
      ((copiedHeaderEval original p s).stk p.m).length ≤ (s.stk original).length ∧
      ((copiedHeaderEval original p s).stk p.k).length ≤ (s.stk original).length := by
  let u := wordDuplicateEval original p.source s
  have hsource : u.stk p.source = s.stk original := by simp [u, wordDuplicateEval, hs]
  have hn' : u.stk p.n = [] := by simp [u, wordDuplicateEval, Ne.symm p.hsn, hn]
  have hm' : u.stk p.m = [] := by simp [u, wordDuplicateEval, Ne.symm p.hsm, hm]
  have hk' : u.stk p.k = [] := by simp [u, wordDuplicateEval, Ne.symm p.hsk, hk]
  have hL : (u.stk p.source).length ≤ (s.stk original).length := by rw [hsource]
  have h1 := wordDuplicate_executes original temp p.source hot hos hts s ht
  obtain ⟨n, hnTime, h2⟩ := internalHeader_executes p (s.stk original).length u hL hn' hm' hk'
  have hall := RoutineComposition.seq_executes (wordDuplicateRoutine original temp p.source) (internalHeaderRoutine p) h1 h2
  have hobs := internalHeader_observation p u
  rw [hsource] at hobs
  exact ⟨(3 * (s.stk original).length + 3) + n, by omega, hall, hobs,
    internalHeader_bounds p (s.stk original).length u hL hn' hm' hk'⟩

theorem copiedHeader_original_preserved (original : K) (p : InternalHeaderPorts K)
    (hos : original ≠ p.source) (hon : original ≠ p.n) (hom : original ≠ p.m) (hok : original ≠ p.k)
    (s : CountdownStore K F) : (copiedHeaderEval original p s).stk original = s.stk original := by
  unfold copiedHeaderEval
  rw [internalHeader_extra p original hos hon hom hok]
  simp [wordDuplicateEval, hos]

theorem copiedHeader_extra (original : K) (p : InternalHeaderPorts K) (j : K)
    (hjs : j ≠ p.source) (hjn : j ≠ p.n) (hjm : j ≠ p.m) (hjk : j ≠ p.k)
    (s : CountdownStore K F) : (copiedHeaderEval original p s).stk j = s.stk j := by
  unfold copiedHeaderEval
  rw [internalHeader_extra p j hjs hjn hjm hjk]
  simp [wordDuplicateEval, hjs]

theorem copiedHeader_frame (original : K) (p : InternalHeaderPorts K) (s : CountdownStore K F) :
    (copiedHeaderEval original p s).state.1 = s.state.1 := by
  unfold copiedHeaderEval
  rw [internalHeader_frame]
  rfl

/- To preserve the original record, its port must also differ from all
three scalar outputs; the separate preservation theorem makes that
condition explicit rather than silently deriving it from copy safety.
Likewise temp stays empty after header extraction only if absent from
the header outputs. A concrete caller allocates these ports distinctly.
Next: actual nested unary rows visitor with physical counters, exact row
count/range/membership observations and finite found/error flags. A false
comparison must NOT become a parser failure. Whole downstream constructor,
independent checker, closed hardness and all kernel checks remain open.
-/

end PolytomyReductionModel
