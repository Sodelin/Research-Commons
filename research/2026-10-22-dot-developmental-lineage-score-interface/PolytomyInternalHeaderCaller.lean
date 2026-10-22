/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual tagged INTERNAL unary header reader. N,m,K are stored as separate
physical scalar words for the ORIGINAL downstream constructor; row bits
remain on the source. This is not complete row validation or construction.
-/
import PolytomyGuardedUnaryField

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

structure InternalHeaderPorts (K : Type) where
  source : K
  n : K
  m : K
  k : K
  hsn : source ≠ n
  hsm : source ≠ m
  hsk : source ≠ k
  hnm : n ≠ m
  hnk : n ≠ k
  hmk : m ≠ k

def internalTagOp (source : K) : Op K Bool (CountdownState F) :=
  .pop source (fun s h => (s.1, h == some true))

def internalTagEval (source : K) (s : CountdownStore K F) : CountdownStore K F :=
  (internalTagOp source).apply s

theorem internalTag_extra (source k : K) (hk : k ≠ source) (s : CountdownStore K F) :
    (internalTagEval source s).stk k = s.stk k := by
  simp [internalTagEval, internalTagOp, Op.apply, hk]

theorem internalTag_source_bound (source : K) (s : CountdownStore K F) :
    ((internalTagEval source s).stk source).length ≤ (s.stk source).length := by
  simp only [internalTagEval, internalTagOp, Op.apply, Function.update_same]
  cases s.stk source <;> simp

def internalHeaderRoutine (p : InternalHeaderPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (internalTagOp p.source))
    (RoutineComposition.seq (guardedUnaryFieldRoutine p.source p.n)
      (RoutineComposition.seq (guardedUnaryFieldRoutine p.source p.m) (guardedUnaryFieldRoutine p.source p.k)))

def internalHeaderEval (p : InternalHeaderPorts K) (s : CountdownStore K F) : CountdownStore K F :=
  guardedUnaryFieldEval p.source p.k (guardedUnaryFieldEval p.source p.m
    (guardedUnaryFieldEval p.source p.n (internalTagEval p.source s)))

def readInternalHeaderPrefix : List Bool → Option ((ℕ × ℕ × ℕ) × List Bool)
  | true :: bits =>
      match readUnaryFrame bits with
      | none => none
      | some (n, r1) =>
          match readUnaryFrame r1 with
          | none => none
          | some (m, r2) =>
              match readUnaryFrame r2 with
              | none => none
              | some (k, rest) => some ((n, m, k), rest)
  | _ => none

def internalHeaderObservation (p : InternalHeaderPorts K) (s : CountdownStore K F) :
    Option ((ℕ × ℕ × ℕ) × List Bool) :=
  if s.state.2 then some (((s.stk p.n).length, (s.stk p.m).length, (s.stk p.k).length), s.stk p.source)
  else none

theorem internalHeader_executes (p : InternalHeaderPorts K) (L : ℕ)
    (s : CountdownStore K F) (hL : (s.stk p.source).length ≤ L)
    (hn : s.stk p.n = []) (hm : s.stk p.m = []) (hk : s.stk p.k = []) :
    ∃ steps ≤ 6 * L + 13,
      (internalHeaderRoutine p).Executes s (internalHeaderEval p s) steps := by
  let s0 := internalTagEval p.source s
  let s1 := guardedUnaryFieldEval p.source p.n s0
  let s2 := guardedUnaryFieldEval p.source p.m s1
  have hL0 := (internalTag_source_bound p.source s).trans hL
  have hL1 := (guardedUnaryField_source_bound p.source p.n p.hsn s0).trans hL0
  have hL2 := (guardedUnaryField_source_bound p.source p.m p.hsm s1).trans hL1
  have hn0 : s0.stk p.n = [] := (internalTag_extra p.source p.n (Ne.symm p.hsn) s).trans hn
  have hm0 : s0.stk p.m = [] := (internalTag_extra p.source p.m (Ne.symm p.hsm) s).trans hm
  have hk0 : s0.stk p.k = [] := (internalTag_extra p.source p.k (Ne.symm p.hsk) s).trans hk
  have hm1 : s1.stk p.m = [] :=
    (guardedUnaryField_extra p.source p.n p.m (Ne.symm p.hsm) (Ne.symm p.hnm) s0).trans hm0
  have hk1 : s1.stk p.k = [] :=
    (guardedUnaryField_extra p.source p.n p.k (Ne.symm p.hsk) (Ne.symm p.hnk) s0).trans hk0
  have hk2 : s2.stk p.k = [] :=
    (guardedUnaryField_extra p.source p.m p.k (Ne.symm p.hsk) (Ne.symm p.hmk) s1).trans hk1
  obtain ⟨a, ha, h1⟩ := guardedUnaryField_executes p.source p.n p.hsn s0 hn0 L hL0
  obtain ⟨b, hb, h2⟩ := guardedUnaryField_executes p.source p.m p.hsm s1 hm1 L hL1
  obtain ⟨c, hc, h3⟩ := guardedUnaryField_executes p.source p.k p.hsk s2 hk2 L hL2
  have h23 := RoutineComposition.seq_executes (guardedUnaryFieldRoutine p.source p.m)
    (guardedUnaryFieldRoutine p.source p.k) h2 h3
  have h123 := RoutineComposition.seq_executes (guardedUnaryFieldRoutine p.source p.n)
    (RoutineComposition.seq (guardedUnaryFieldRoutine p.source p.m) (guardedUnaryFieldRoutine p.source p.k)) h1 h23
  have hall := RoutineComposition.seq_executes (Atom.routine (internalTagOp p.source))
    (RoutineComposition.seq (guardedUnaryFieldRoutine p.source p.n)
      (RoutineComposition.seq (guardedUnaryFieldRoutine p.source p.m) (guardedUnaryFieldRoutine p.source p.k)))
    (Atom.executes (internalTagOp p.source) s) h123
  exact ⟨1 + (a + (b + c)), by omega, hall⟩

theorem internalHeader_extra (p : InternalHeaderPorts K) (j : K)
    (hjs : j ≠ p.source) (hjn : j ≠ p.n) (hjm : j ≠ p.m) (hjk : j ≠ p.k)
    (s : CountdownStore K F) : (internalHeaderEval p s).stk j = s.stk j := by
  unfold internalHeaderEval
  rw [guardedUnaryField_extra p.source p.k j hjs hjk,
    guardedUnaryField_extra p.source p.m j hjs hjm,
    guardedUnaryField_extra p.source p.n j hjs hjn, internalTag_extra p.source j hjs]

theorem internalHeader_bounds (p : InternalHeaderPorts K) (L : ℕ)
    (s : CountdownStore K F) (hL : (s.stk p.source).length ≤ L)
    (hn : s.stk p.n = []) (hm : s.stk p.m = []) (hk : s.stk p.k = []) :
    ((internalHeaderEval p s).stk p.source).length ≤ L ∧
      ((internalHeaderEval p s).stk p.n).length ≤ L ∧
      ((internalHeaderEval p s).stk p.m).length ≤ L ∧
      ((internalHeaderEval p s).stk p.k).length ≤ L := by
  let s0 := internalTagEval p.source s
  let s1 := guardedUnaryFieldEval p.source p.n s0
  let s2 := guardedUnaryFieldEval p.source p.m s1
  have hL0 := (internalTag_source_bound p.source s).trans hL
  have hL1 := (guardedUnaryField_source_bound p.source p.n p.hsn s0).trans hL0
  have hL2 := (guardedUnaryField_source_bound p.source p.m p.hsm s1).trans hL1
  have hn0 : s0.stk p.n = [] := (internalTag_extra p.source p.n (Ne.symm p.hsn) s).trans hn
  have hm0 : s0.stk p.m = [] := (internalTag_extra p.source p.m (Ne.symm p.hsm) s).trans hm
  have hk0 : s0.stk p.k = [] := (internalTag_extra p.source p.k (Ne.symm p.hsk) s).trans hk
  have hm1 : s1.stk p.m = [] :=
    (guardedUnaryField_extra p.source p.n p.m (Ne.symm p.hsm) (Ne.symm p.hnm) s0).trans hm0
  have hk1 : s1.stk p.k = [] :=
    (guardedUnaryField_extra p.source p.n p.k (Ne.symm p.hsk) (Ne.symm p.hnk) s0).trans hk0
  have hk2 : s2.stk p.k = [] :=
    (guardedUnaryField_extra p.source p.m p.k (Ne.symm p.hsk) (Ne.symm p.hmk) s1).trans hk1
  refine ⟨(guardedUnaryField_source_bound p.source p.k p.hsk s2).trans hL2, ?_, ?_, ?_⟩
  · change ((guardedUnaryFieldEval p.source p.k s2).stk p.n).length ≤ L
    rw [guardedUnaryField_extra p.source p.k p.n (Ne.symm p.hsn) p.hnk,
      guardedUnaryField_extra p.source p.m p.n (Ne.symm p.hsn) p.hnm]
    exact (guardedUnaryField_output_bound p.source p.n s0 hn0).trans hL0
  · change ((guardedUnaryFieldEval p.source p.k s2).stk p.m).length ≤ L
    rw [guardedUnaryField_extra p.source p.k p.m (Ne.symm p.hsm) p.hmk]
    exact (guardedUnaryField_output_bound p.source p.m s1 hm1).trans hL1
  · exact (guardedUnaryField_output_bound p.source p.k s2 hk2).trans hL2

theorem internalHeader_frame (p : InternalHeaderPorts K) (s : CountdownStore K F) :
    (internalHeaderEval p s).state.1 = s.state.1 := by
  unfold internalHeaderEval
  rw [guardedUnaryField_frame, guardedUnaryField_frame, guardedUnaryField_frame]
  rfl

theorem internalHeader_unary_scalars (p : InternalHeaderPorts K) (s : CountdownStore K F)
    (hn : s.stk p.n = []) (hm : s.stk p.m = []) (hk : s.stk p.k = []) :
    IsUnaryWord ((internalHeaderEval p s).stk p.n) ∧
      IsUnaryWord ((internalHeaderEval p s).stk p.m) ∧ IsUnaryWord ((internalHeaderEval p s).stk p.k) := by
  let s0 := internalTagEval p.source s
  let s1 := guardedUnaryFieldEval p.source p.n s0
  let s2 := guardedUnaryFieldEval p.source p.m s1
  have hn0 : s0.stk p.n = [] := (internalTag_extra p.source p.n (Ne.symm p.hsn) s).trans hn
  have hm0 : s0.stk p.m = [] := (internalTag_extra p.source p.m (Ne.symm p.hsm) s).trans hm
  have hk0 : s0.stk p.k = [] := (internalTag_extra p.source p.k (Ne.symm p.hsk) s).trans hk
  have hm1 : s1.stk p.m = [] :=
    (guardedUnaryField_extra p.source p.n p.m (Ne.symm p.hsm) (Ne.symm p.hnm) s0).trans hm0
  have hk1 : s1.stk p.k = [] :=
    (guardedUnaryField_extra p.source p.n p.k (Ne.symm p.hsk) (Ne.symm p.hnk) s0).trans hk0
  have hk2 : s2.stk p.k = [] :=
    (guardedUnaryField_extra p.source p.m p.k (Ne.symm p.hsk) (Ne.symm p.hmk) s1).trans hk1
  refine ⟨?_, ?_, guardedUnaryField_output_unary p.source p.k s2 hk2⟩
  · change IsUnaryWord ((guardedUnaryFieldEval p.source p.k s2).stk p.n)
    rw [guardedUnaryField_extra p.source p.k p.n (Ne.symm p.hsn) p.hnk,
      guardedUnaryField_extra p.source p.m p.n (Ne.symm p.hsn) p.hnm]
    exact guardedUnaryField_output_unary p.source p.n s0 hn0
  · change IsUnaryWord ((guardedUnaryFieldEval p.source p.k s2).stk p.m)
    rw [guardedUnaryField_extra p.source p.k p.m (Ne.symm p.hsm) p.hmk]
    exact guardedUnaryField_output_unary p.source p.m s1 hm1

theorem internalHeader_observation (p : InternalHeaderPorts K) (s : CountdownStore K F) :
    internalHeaderObservation p (internalHeaderEval p s) = readInternalHeaderPrefix (s.stk p.source) := by
  cases hx : s.stk p.source with
  | nil => simp [internalHeaderObservation, internalHeaderEval, internalTagEval, internalTagOp,
      guardedUnaryFieldEval, Op.apply, hx, readInternalHeaderPrefix]
  | cons tag bits =>
      cases tag with
      | false => simp [internalHeaderObservation, internalHeaderEval, internalTagEval, internalTagOp,
          guardedUnaryFieldEval, Op.apply, hx, readInternalHeaderPrefix]
      | true =>
          cases h1 : readUnaryFrame bits with
          | none => simp [internalHeaderObservation, internalHeaderEval, internalTagEval, internalTagOp,
              guardedUnaryFieldEval, unaryCallerResult, frameCallerStore, Op.apply, hx, h1,
              readInternalHeaderPrefix, p.hsn]
          | some q1 =>
              rcases q1 with ⟨n, r1⟩
              cases h2 : readUnaryFrame r1 with
              | none => simp [internalHeaderObservation, internalHeaderEval, internalTagEval, internalTagOp,
                  guardedUnaryFieldEval, unaryCallerResult, frameCallerStore, Op.apply, hx, h1, h2,
                  readInternalHeaderPrefix, p.hsn, p.hsm]
              | some q2 =>
                  rcases q2 with ⟨m, r2⟩
                  cases h3 : readUnaryFrame r2 with
                  | none => simp [internalHeaderObservation, internalHeaderEval, internalTagEval, internalTagOp,
                      guardedUnaryFieldEval, unaryCallerResult, frameCallerStore, Op.apply, hx, h1, h2, h3,
                      readInternalHeaderPrefix, p.hsn, p.hsm, p.hsk]
                  | some q3 =>
                      rcases q3 with ⟨k, rest⟩
                      simp [internalHeaderObservation, internalHeaderEval, internalTagEval, internalTagOp,
                        guardedUnaryFieldEval, unaryCallerResult, frameCallerStore, Op.apply, hx, h1, h2, h3,
                        readInternalHeaderPrefix, p.hsn, p.hsm, p.hsk, p.hnm, p.hnk, p.hmk,
                        Ne.symm p.hsn, Ne.symm p.hsm, Ne.symm p.hsk]

theorem internalHeader_success_values (p : InternalHeaderPorts K) (s : CountdownStore K F)
    (hn : s.stk p.n = []) (hm : s.stk p.m = []) (hk : s.stk p.k = [])
    (N M B : ℕ) (rest : List Bool)
    (hp : readInternalHeaderPrefix (s.stk p.source) = some ((N, M, B), rest)) :
    (internalHeaderEval p s).state.2 = true ∧ (internalHeaderEval p s).stk p.source = rest ∧
      (internalHeaderEval p s).stk p.n = List.replicate N true ∧
      (internalHeaderEval p s).stk p.m = List.replicate M true ∧
      (internalHeaderEval p s).stk p.k = List.replicate B true := by
  have ho := (internalHeader_observation p s).trans hp
  have hu := internalHeader_unary_scalars p s hn hm hk
  cases hf : (internalHeaderEval p s).state.2 with
  | false => simp [internalHeaderObservation, hf] at ho
  | true =>
      simp only [internalHeaderObservation, hf, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at ho
      unfold IsUnaryWord at hu
      rw [ho.1.1] at hu
      rw [ho.1.2.1, ho.1.2.2] at hu
      exact ⟨hf, ho.2, hu.1, hu.2.1, hu.2.2⟩

theorem readInternalHeader_complete_record (bits : List Bool) (R : RawMSSCRecord)
    (h : readNormalizedSource bits = some R) :
    readInternalHeaderPrefix bits =
      some ((R.N, R.declaredM, R.K), encodeFramedList (encodeFramedList unaryFrame) R.rows) := by
  rw [readNormalizedSource_sound bits R h]
  simp only [readInternalHeaderPrefix, encodeUnaryRaw, List.append_assoc, readUnaryFrame_encode]

theorem internalHeader_complete_record_values (p : InternalHeaderPorts K) (s : CountdownStore K F)
    (hn : s.stk p.n = []) (hm : s.stk p.m = []) (hk : s.stk p.k = [])
    (R : RawMSSCRecord) (h : readNormalizedSource (s.stk p.source) = some R) :
    (internalHeaderEval p s).state.2 = true ∧
      (internalHeaderEval p s).stk p.source = encodeFramedList (encodeFramedList unaryFrame) R.rows ∧
      (internalHeaderEval p s).stk p.n = List.replicate R.N true ∧
      (internalHeaderEval p s).stk p.m = List.replicate R.declaredM true ∧
      (internalHeaderEval p s).stk p.k = List.replicate R.K true :=
  internalHeader_success_values p s hn hm hk R.N R.declaredM R.K _
    (readInternalHeader_complete_record (s.stk p.source) R h)

/- Actual source and scalar all-path bounds follow from the three guarded
field bounds and outside-field preservation. Full row syntax, declared
row count, identifier bounds/coverage and complete suffix validation are
NOT inferred from successful headers. The next row visitor must preserve
these physical scalars and distinguish comparison-false from parse failure.
The original whole downstream constructor/checker/hardness/kernel remain.
-/

end PolytomyReductionModel
