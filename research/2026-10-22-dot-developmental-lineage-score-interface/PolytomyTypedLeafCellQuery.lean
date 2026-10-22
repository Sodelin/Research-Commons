/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Original two-field cell query with ACTUAL finite-port range checks. Rows
and type counts are physical unary operands, never unbounded control.
Accepts precisely raw block<=m and raw type<N+m*N+3. The block is NOT
identified with the enclosing fixed-child row. All source words allowed.
-/
import PolytomyRawLeafCellQuery
import PolytomyPhysicalCellCompare

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

inductive TypedCellPort where
  | source | block | kind | rows | types | temp | residue | subtrahend
  deriving DecidableEq, Fintype

abbrev TypedCellPorts (K : Type) := TypedCellPort ↪ K

variable {K F : Type} [DecidableEq K]

@[simp] theorem typedCellPorts_eq (p : TypedCellPorts K) (a b : TypedCellPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def typedRawCellPorts (p : TypedCellPorts K) : RawCellPorts K where
  source := p .source
  block := p .block
  kind := p .kind
  hsb := by simp
  hsk := by simp
  hbk := by simp

def typedBlockCompare (p : TypedCellPorts K) : CellComparePorts K where
  toFun := fun
    | .left => p .rows
    | .right => p .block
    | .temp => p .temp
    | .residue => p .residue
    | .subtrahend => p .subtrahend
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def typedKindCompare (p : TypedCellPorts K) : CellComparePorts K where
  toFun := fun
    | .left => p .types
    | .right => p .kind
    | .temp => p .temp
    | .residue => p .residue
    | .subtrahend => p .subtrahend
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def typedLeafCellRoutine (p : TypedCellPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (rawLeafCellRoutine (typedRawCellPorts p))
    (RoutineComposition.seq (guardedCellCompareRoutine (typedBlockCompare p) .le)
      (guardedCellCompareRoutine (typedKindCompare p) .lt))

def typedLeafCellEval (p : TypedCellPorts K) (m A : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  let u := rawLeafCellEval (typedRawCellPorts p) s
  guardedCellCompareEval .lt A (u.stk (p .kind)).length
    (guardedCellCompareEval .le m (u.stk (p .block)).length u)

theorem typedLeafCell_executes (p : TypedCellPorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hL : (s.stk (p .source)).length ≤ L)
    (hm : s.stk (p .rows) = List.replicate m true) (hA : s.stk (p .types) = List.replicate A true)
    (hb : s.stk (p .block) = []) (hk : s.stk (p .kind) = [])
    (ht : s.stk (p .temp) = []) (hr : s.stk (p .residue) = []) (hd : s.stk (p .subtrahend) = []) :
    ∃ n ≤ 12 * L + 4 * m + 4 * A + 29,
      (typedLeafCellRoutine p).Executes s (typedLeafCellEval p m A s) n := by
  let u := rawLeafCellEval (typedRawCellPorts p) s
  let B := (u.stk (p .block)).length
  let T := (u.stk (p .kind)).length
  let v := guardedCellCompareEval .le m B u
  have hbounds := rawLeafCell_bounds (typedRawCellPorts p) L s hL hb hk
  have hunary := rawLeafCell_unary (typedRawCellPorts p) s hb hk
  have hB : B ≤ L := hbounds.2.1
  have hT : T ≤ L := hbounds.2.2
  have hext (j : TypedCellPort) (hjs : j ≠ .source) (hjb : j ≠ .block) (hjk : j ≠ .kind) :
      u.stk (p j) = s.stk (p j) :=
    rawLeafCell_extra (typedRawCellPorts p) (p j)
      (by simpa [typedRawCellPorts] using hjs)
      (by simpa [typedRawCellPorts] using hjb)
      (by simpa [typedRawCellPorts] using hjk) s
  have hmU := (hext .rows (by decide) (by decide) (by decide)).trans hm
  have hAU := (hext .types (by decide) (by decide) (by decide)).trans hA
  have htU := (hext .temp (by decide) (by decide) (by decide)).trans ht
  have hrU := (hext .residue (by decide) (by decide) (by decide)).trans hr
  have hdU := (hext .subtrahend (by decide) (by decide) (by decide)).trans hd
  have hBU : u.stk (p .block) = List.replicate B true := hunary.1
  have hTU : u.stk (p .kind) = List.replicate T true := hunary.2
  have hv : v.stk = u.stk := guardedCellCompare_stacks .le m B u
  obtain ⟨n1, hn1, h1⟩ := rawLeafCell_executes (typedRawCellPorts p) L s hL hb hk
  obtain ⟨n2, hn2, h2⟩ := guardedCellCompare_executes (typedBlockCompare p) .le m B u
    (by simpa [typedBlockCompare] using hmU) (by simpa [typedBlockCompare] using hBU)
    (by simpa [typedBlockCompare] using hrU) (by simpa [typedBlockCompare] using hdU)
    (by simpa [typedBlockCompare] using htU)
  obtain ⟨n3, hn3, h3⟩ := guardedCellCompare_executes (typedKindCompare p) .lt A T v
    (by simpa [typedKindCompare, hv] using hAU) (by simpa [typedKindCompare, hv] using hTU)
    (by simpa [typedKindCompare, hv] using hrU) (by simpa [typedKindCompare, hv] using hdU)
    (by simpa [typedKindCompare, hv] using htU)
  have hall := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3)
  exact ⟨n1 + (n2 + n3), by omega, hall⟩

def filterRawLeafCell (m A : ℕ) (result : Option ((ℕ × ℕ) × List Bool)) :=
  result.bind (fun p => if p.1.1 ≤ m ∧ p.1.2 < A then some p else none)

theorem typedLeafCell_observation (p : TypedCellPorts K) (m A : ℕ) (s : CountdownStore K F) :
    rawLeafCellObservation (typedRawCellPorts p) (typedLeafCellEval p m A s) =
      filterRawLeafCell m A (readRawLeafCell (s.stk (p .source))) := by
  rw [← rawLeafCell_observation (typedRawCellPorts p) s]
  let u := rawLeafCellEval (typedRawCellPorts p) s
  change rawLeafCellObservation (typedRawCellPorts p)
    (guardedCellCompareEval .lt A (u.stk (p .kind)).length
      (guardedCellCompareEval .le m (u.stk (p .block)).length u)) =
    filterRawLeafCell m A (rawLeafCellObservation (typedRawCellPorts p) u)
  cases hf : u.state.2 <;> by_cases hb : (u.stk (p .block)).length ≤ m <;>
    by_cases hk : (u.stk (p .kind)).length < A <;>
    simp [rawLeafCellObservation, typedRawCellPorts, guardedCellCompareEval,
      cellCompareFlagStore, cellCompareAnswer, filterRawLeafCell, hf, hb, hk]

theorem typedLeafCell_stacks (p : TypedCellPorts K) (m A : ℕ) (s : CountdownStore K F) :
    (typedLeafCellEval p m A s).stk = (rawLeafCellEval (typedRawCellPorts p) s).stk := by
  unfold typedLeafCellEval
  rw [guardedCellCompare_stacks, guardedCellCompare_stacks]

theorem typedLeafCell_frame (p : TypedCellPorts K) (m A : ℕ) (s : CountdownStore K F) :
    (typedLeafCellEval p m A s).state.1 = s.state.1 := by
  unfold typedLeafCellEval
  rw [guardedCellCompare_frame, guardedCellCompare_frame, rawLeafCell_frame]

theorem readOriginalLeafCell_filtered (N m : ℕ) (bits : List Bool) :
    (readOriginalLeafCell N m bits).map (fun p => (cellNatCode p.1, p.2)) =
      filterRawLeafCell m (N + m * N + 3) (readRawLeafCell bits) := by
  rw [readOriginalLeafCell_raw]
  cases hp : readRawLeafCell bits with
  | none => simp [filterRawLeafCell]
  | some pair =>
      rcases pair with ⟨⟨B, T⟩, rest⟩
      cases hb : decodeBlock m B with
      | none =>
          have hnot : ¬ B ≤ m := by
            intro hle
            have hs := (decodeBlock_isSome_iff m B).mpr hle
            simp [hb] at hs
          simp [filterRawLeafCell, hb, hnot]
      | some b =>
          have hB : B ≤ m := (decodeBlock_isSome_iff m B).mp (by simp [hb])
          have hbc := blockCode_of_decode hb
          cases ht : decodeTerminal N m T with
          | none =>
              have hnot : ¬ T < N + m * N + 3 := by
                intro hlt
                have hs := (decodeTerminal_isSome_iff N m T).mpr hlt
                simp [ht] at hs
              simp [filterRawLeafCell, hb, ht, hnot]
          | some t =>
              have hT : T < N + m * N + 3 := (decodeTerminal_isSome_iff N m T).mp (by simp [ht])
              have htc := terminalCode_of_decode ht
              simp [filterRawLeafCell, hb, ht, hB, hT, cellNatCode, hbc, htc]

theorem typedLeafCell_original_observation (p : TypedCellPorts K) (N m : ℕ) (s : CountdownStore K F) :
    rawLeafCellObservation (typedRawCellPorts p) (typedLeafCellEval p m (N + m * N + 3) s) =
      (readOriginalLeafCell N m (s.stk (p .source))).map (fun q => (cellNatCode q.1, q.2)) := by
  rw [typedLeafCell_observation, readOriginalLeafCell_filtered]

/- These are actual parser/comparison routines, not a complete target or
certificate verifier. Valid finite cell codes do not establish syntax of
an entire tree, legal node starts, unique cells, required fixed clades,
mixed target nodes, marker/type coverage, score or clean final halt.
The source remains unelaborated and the whole independent verifier open.
-/

end PolytomyReductionModel
