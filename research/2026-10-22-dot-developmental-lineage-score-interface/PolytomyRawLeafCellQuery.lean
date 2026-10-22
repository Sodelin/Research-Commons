/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual original LEAF token and its two unary cell fields. No enclosing-row
index restriction is added. Range validation remains explicit downstream.
Failure may retain the first bounded scalar; complete cleanup is not faked.
-/
import PolytomyInternalHeaderCaller

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

structure RawCellPorts (K : Type) where
  source : K
  block : K
  kind : K
  hsb : source ≠ block
  hsk : source ≠ kind
  hbk : block ≠ kind

def rawLeafCellRoutine (p : RawCellPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (internalTagOp p.source))
    (RoutineComposition.seq (guardedUnaryFieldRoutine p.source p.block)
      (guardedUnaryFieldRoutine p.source p.kind))

def rawLeafCellEval (p : RawCellPorts K) (s : CountdownStore K F) : CountdownStore K F :=
  guardedUnaryFieldEval p.source p.kind
    (guardedUnaryFieldEval p.source p.block (internalTagEval p.source s))

def readRawLeafCell : List Bool → Option ((ℕ × ℕ) × List Bool)
  | true :: bits =>
      match readUnaryFrame bits with
      | none => none
      | some (b, r1) =>
          match readUnaryFrame r1 with
          | none => none
          | some (t, rest) => some ((b, t), rest)
  | _ => none

def rawLeafCellObservation (p : RawCellPorts K) (s : CountdownStore K F) :
    Option ((ℕ × ℕ) × List Bool) :=
  if s.state.2 then some (((s.stk p.block).length, (s.stk p.kind).length), s.stk p.source) else none

theorem rawLeafCell_executes (p : RawCellPorts K) (L : ℕ) (s : CountdownStore K F)
    (hL : (s.stk p.source).length ≤ L) (hb : s.stk p.block = []) (hk : s.stk p.kind = []) :
    ∃ n ≤ 4 * L + 9, (rawLeafCellRoutine p).Executes s (rawLeafCellEval p s) n := by
  let s0 := internalTagEval p.source s
  let s1 := guardedUnaryFieldEval p.source p.block s0
  have hL0 := (internalTag_source_bound p.source s).trans hL
  have hL1 := (guardedUnaryField_source_bound p.source p.block p.hsb s0).trans hL0
  have hb0 : s0.stk p.block = [] := (internalTag_extra p.source p.block (Ne.symm p.hsb) s).trans hb
  have hk0 : s0.stk p.kind = [] := (internalTag_extra p.source p.kind (Ne.symm p.hsk) s).trans hk
  have hk1 : s1.stk p.kind = [] :=
    (guardedUnaryField_extra p.source p.block p.kind (Ne.symm p.hsk) (Ne.symm p.hbk) s0).trans hk0
  obtain ⟨a, ha, h1⟩ := guardedUnaryField_executes p.source p.block p.hsb s0 hb0 L hL0
  obtain ⟨b, hbTime, h2⟩ := guardedUnaryField_executes p.source p.kind p.hsk s1 hk1 L hL1
  have h12 := RoutineComposition.seq_executes (guardedUnaryFieldRoutine p.source p.block)
    (guardedUnaryFieldRoutine p.source p.kind) h1 h2
  have hall := RoutineComposition.seq_executes (Atom.routine (internalTagOp p.source))
    (RoutineComposition.seq (guardedUnaryFieldRoutine p.source p.block)
      (guardedUnaryFieldRoutine p.source p.kind)) (Atom.executes (internalTagOp p.source) s) h12
  exact ⟨1 + (a + b), by omega, hall⟩

theorem rawLeafCell_extra (p : RawCellPorts K) (j : K)
    (hjs : j ≠ p.source) (hjb : j ≠ p.block) (hjk : j ≠ p.kind)
    (s : CountdownStore K F) : (rawLeafCellEval p s).stk j = s.stk j := by
  unfold rawLeafCellEval
  rw [guardedUnaryField_extra p.source p.kind j hjs hjk,
    guardedUnaryField_extra p.source p.block j hjs hjb, internalTag_extra p.source j hjs]

theorem rawLeafCell_frame (p : RawCellPorts K) (s : CountdownStore K F) :
    (rawLeafCellEval p s).state.1 = s.state.1 := by
  unfold rawLeafCellEval
  rw [guardedUnaryField_frame, guardedUnaryField_frame]
  rfl

theorem rawLeafCell_bounds (p : RawCellPorts K) (L : ℕ) (s : CountdownStore K F)
    (hL : (s.stk p.source).length ≤ L) (hb : s.stk p.block = []) (hk : s.stk p.kind = []) :
    ((rawLeafCellEval p s).stk p.source).length ≤ L ∧
      ((rawLeafCellEval p s).stk p.block).length ≤ L ∧
      ((rawLeafCellEval p s).stk p.kind).length ≤ L := by
  let s0 := internalTagEval p.source s
  let s1 := guardedUnaryFieldEval p.source p.block s0
  have hL0 := (internalTag_source_bound p.source s).trans hL
  have hL1 := (guardedUnaryField_source_bound p.source p.block p.hsb s0).trans hL0
  have hb0 : s0.stk p.block = [] := (internalTag_extra p.source p.block (Ne.symm p.hsb) s).trans hb
  have hk0 : s0.stk p.kind = [] := (internalTag_extra p.source p.kind (Ne.symm p.hsk) s).trans hk
  have hk1 : s1.stk p.kind = [] :=
    (guardedUnaryField_extra p.source p.block p.kind (Ne.symm p.hsk) (Ne.symm p.hbk) s0).trans hk0
  refine ⟨(guardedUnaryField_source_bound p.source p.kind p.hsk s1).trans hL1, ?_, ?_⟩
  · change ((guardedUnaryFieldEval p.source p.kind s1).stk p.block).length ≤ L
    rw [guardedUnaryField_extra p.source p.kind p.block (Ne.symm p.hsb) p.hbk]
    exact (guardedUnaryField_output_bound p.source p.block s0 hb0).trans hL0
  · exact (guardedUnaryField_output_bound p.source p.kind s1 hk1).trans hL1

theorem rawLeafCell_unary (p : RawCellPorts K) (s : CountdownStore K F)
    (hb : s.stk p.block = []) (hk : s.stk p.kind = []) :
    IsUnaryWord ((rawLeafCellEval p s).stk p.block) ∧
      IsUnaryWord ((rawLeafCellEval p s).stk p.kind) := by
  let s0 := internalTagEval p.source s
  let s1 := guardedUnaryFieldEval p.source p.block s0
  have hb0 : s0.stk p.block = [] := (internalTag_extra p.source p.block (Ne.symm p.hsb) s).trans hb
  have hk0 : s0.stk p.kind = [] := (internalTag_extra p.source p.kind (Ne.symm p.hsk) s).trans hk
  have hk1 : s1.stk p.kind = [] :=
    (guardedUnaryField_extra p.source p.block p.kind (Ne.symm p.hsk) (Ne.symm p.hbk) s0).trans hk0
  refine ⟨?_, guardedUnaryField_output_unary p.source p.kind s1 hk1⟩
  change IsUnaryWord ((guardedUnaryFieldEval p.source p.kind s1).stk p.block)
  rw [guardedUnaryField_extra p.source p.kind p.block (Ne.symm p.hsb) p.hbk]
  exact guardedUnaryField_output_unary p.source p.block s0 hb0

theorem rawLeafCell_observation (p : RawCellPorts K) (s : CountdownStore K F) :
    rawLeafCellObservation p (rawLeafCellEval p s) = readRawLeafCell (s.stk p.source) := by
  cases hx : s.stk p.source with
  | nil => simp [rawLeafCellObservation, rawLeafCellEval, internalTagEval, internalTagOp,
      guardedUnaryFieldEval, Op.apply, hx, readRawLeafCell]
  | cons tag bits =>
      cases tag with
      | false => simp [rawLeafCellObservation, rawLeafCellEval, internalTagEval, internalTagOp,
          guardedUnaryFieldEval, Op.apply, hx, readRawLeafCell]
      | true =>
          cases h1 : readUnaryFrame bits with
          | none => simp [rawLeafCellObservation, rawLeafCellEval, internalTagEval, internalTagOp,
              guardedUnaryFieldEval, unaryCallerResult, frameCallerStore, Op.apply, hx, h1,
              readRawLeafCell, p.hsb]
          | some q1 =>
              rcases q1 with ⟨b, r1⟩
              cases h2 : readUnaryFrame r1 with
              | none => simp [rawLeafCellObservation, rawLeafCellEval, internalTagEval, internalTagOp,
                  guardedUnaryFieldEval, unaryCallerResult, frameCallerStore, Op.apply, hx, h1, h2,
                  readRawLeafCell, p.hsb, p.hsk]
              | some q2 =>
                  rcases q2 with ⟨t, rest⟩
                  simp [rawLeafCellObservation, rawLeafCellEval, internalTagEval, internalTagOp,
                    guardedUnaryFieldEval, unaryCallerResult, frameCallerStore, Op.apply, hx, h1, h2,
                    readRawLeafCell, p.hsb, p.hsk, p.hbk, Ne.symm p.hsb, Ne.symm p.hsk]

theorem rawLeafCell_success_values (p : RawCellPorts K) (s : CountdownStore K F)
    (hb : s.stk p.block = []) (hk : s.stk p.kind = []) (B T : ℕ) (rest : List Bool)
    (hp : readRawLeafCell (s.stk p.source) = some ((B, T), rest)) :
    (rawLeafCellEval p s).state.2 = true ∧ (rawLeafCellEval p s).stk p.source = rest ∧
      (rawLeafCellEval p s).stk p.block = List.replicate B true ∧
      (rawLeafCellEval p s).stk p.kind = List.replicate T true := by
  have ho := (rawLeafCell_observation p s).trans hp
  have hu := rawLeafCell_unary p s hb hk
  cases hf : (rawLeafCellEval p s).state.2 with
  | false => simp [rawLeafCellObservation, hf] at ho
  | true =>
      simp only [rawLeafCellObservation, hf, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at ho
      unfold IsUnaryWord at hu
      rw [ho.1.1, ho.1.2] at hu
      exact ⟨hf, ho.2, hu.1, hu.2⟩

def readOriginalLeafCell (N m : ℕ) : List Bool → Option (Cell N m × List Bool)
  | true :: bits => readCellBits N m bits
  | _ => none

theorem readOriginalLeafCell_raw (N m : ℕ) (bits : List Bool) :
    readOriginalLeafCell N m bits = (readRawLeafCell bits).bind (fun p =>
      (decodeBlock m p.1.1).bind (fun b =>
        (decodeTerminal N m p.1.2).map (fun t => ((b, t), p.2)))) := by
  cases bits with
  | nil => rfl
  | cons tag bits =>
      cases tag with
      | false => rfl
      | true =>
          cases h1 : readUnaryFrame bits with
          | none => simp [readOriginalLeafCell, readRawLeafCell, readCellBits, h1]
          | some p1 =>
              rcases p1 with ⟨b, rest⟩
              cases h2 : readUnaryFrame rest with
              | none => simp [readOriginalLeafCell, readRawLeafCell, readCellBits, h1, h2]
              | some p2 =>
                  rcases p2 with ⟨t, after⟩
                  cases hb : decodeBlock m b <;> cases ht : decodeTerminal N m t <;>
                    simp [readOriginalLeafCell, readRawLeafCell, readCellBits, h1, h2, hb, ht]

theorem decodeBlock_isSome_iff (m b : ℕ) : (decodeBlock m b).isSome = true ↔ b ≤ m := by
  by_cases h0 : b = 0 <;> by_cases hb : b - 1 < m <;> simp [decodeBlock, h0, hb] <;> omega

theorem decodeTerminal_isSome_iff (N m t : ℕ) :
    (decodeTerminal N m t).isSome = true ↔ t < N + m * N + 3 := by
  by_cases hx : t < N <;> by_cases hz : t - N < privateCount N m <;>
    by_cases hk : t - N - privateCount N m < 2 <;>
    simp [decodeTerminal, hx, hz, hk] <;> unfold privateCount at * <;> omega

theorem blockCode_of_decode {m b : ℕ} {a : Block m} (h : decodeBlock m b = some a) :
    blockCode a = b := by
  unfold decodeBlock at h
  split_ifs at h with h0 hi
  · simp only [Option.some.injEq] at h
    subst a
    simp [blockCode]
    omega
  · simp only [Option.some.injEq] at h
    subst a
    simp [blockCode]
    omega
  · simp at h

theorem terminalCode_of_decode {N m t : ℕ} {a : Terminal N m}
    (h : decodeTerminal N m t = some a) : terminalCode N m a = t := by
  unfold decodeTerminal at h
  split_ifs at h with hx hz hk
  · simp only [Option.some.injEq] at h
    subst a
    rfl
  · simp only [Option.some.injEq] at h
    subst a
    simp [terminalCode]
    omega
  · simp only [Option.some.injEq] at h
    subst a
    simp [terminalCode]
    omega
  · simp at h

def cellNatCode {N m : ℕ} (a : Cell N m) : ℕ × ℕ :=
  (blockCode a.1, terminalCode N m a.2)

theorem cellNatCode_injective (N m : ℕ) : Function.Injective (@cellNatCode N m) := by
  intro a b h
  have hb := congrArg (decodeBlock m) (congrArg Prod.fst h)
  have ht := congrArg (decodeTerminal N m) (congrArg Prod.snd h)
  simp only [cellNatCode, decodeBlock_code] at hb
  simp only [cellNatCode, decodeTerminal_code] at ht
  exact Prod.ext (Option.some.inj hb) (Option.some.inj ht)

/- Raw success does not validate b<=m or t<N+m*N+3. The next actual
   operand-preserving comparisons must enforce exactly those inequalities,
   not equate a leaf block tag with its enclosing row index. -/

end PolytomyReductionModel
