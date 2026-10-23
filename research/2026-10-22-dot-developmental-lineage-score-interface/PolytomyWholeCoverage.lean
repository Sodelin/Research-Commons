/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Original whole-forest terminal coverage, NOT cell-set equality: tally
distinct terminal types, physically compare the unary tally with A, and
clear the tally. No alphabet enumeration is used. This is one remaining
target guard inside the same restricted marked-star verifier.
-/
import PolytomyWholeMixedness

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def coverageComparePorts (p : InclusionPorts K) (out : K)
    (hout : ∀ j : InclusionPort, out ≠ p j) : CellComparePorts K where
  toFun := fun
    | .left => p (.outer .types)
    | .right => out
    | .temp => p (.outer .temp)
    | .residue => p (.outer .residue)
    | .subtrahend => p (.outer .subtrahend)
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all [hout]

def coverageRoutine (p : InclusionPorts K) (out : K)
    (hout : ∀ j : InclusionPort, out ≠ p j) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (typeCountRoutine p out)
    (RoutineComposition.seq (guardedCellCompareRoutine (coverageComparePorts p out hout) .eq)
      (clearManyRoutine [out]))

def coverageAnswer (m A : ℕ) (word mask : List Bool) : Bool :=
  decide (typeCountAnswer m A word mask = A)

def coverageResult (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨((s.state.1.1, false), coverageAnswer m A (s.stk (p (.outer .originalWord)))
    (s.stk (p (.outer .originalMask)))), s.stk⟩

def coverageBound (m A L : ℕ) : ℕ := typeCountBound m A L + 4 * A + 5 * L + 12

theorem coverage_executes (p : InclusionPorts K) (out : K)
    (hout : ∀ j : InclusionPort, out ≠ p j) (m A L : ℕ)
    (s : CountdownStore K F) (hs : UniqueEntry p m A L s) (ho : s.stk out = []) :
    ∃ n ≤ coverageBound m A L,
      (coverageRoutine p out hout).Executes s (coverageResult p m A s) n := by
  let C := typeCountAnswer m A (s.stk (p (.outer .originalWord))) (s.stk (p (.outer .originalMask)))
  let u := typeCountResult p out m A s
  let v := guardedCellCompareEval .eq A C u
  let o := inclusionOuterPorts p
  have huout : u.stk out = List.replicate C true := by simp [u, C, typeCountResult, ho]
  have hux (j : InclusionPort) : u.stk (p j) = s.stk (p j) := by
    simp [u, typeCountResult, (hout j).symm]
  have hf (j : RangeCursorPort) (hj : o j ∈ rangeAllWork o) : s.stk (o j) = [] := hs.1.2.2.2.2 _ hj
  have hA : s.stk (p (.outer .types)) = List.replicate A true := hs.1.2.2.2.1
  obtain ⟨a, ha, h1⟩ := typeCount_executes p out hout m A L s hs
  obtain ⟨b, hb, h2⟩ := guardedCellCompare_executes (coverageComparePorts p out hout) .eq A C u
    (by simpa [coverageComparePorts, hux] using hA)
    (by simpa [coverageComparePorts] using huout)
    (by simpa [coverageComparePorts, hux] using hf .residue (by simp [rangeAllWork]))
    (by simpa [coverageComparePorts, hux] using hf .subtrahend (by simp [rangeAllWork]))
    (by simpa [coverageComparePorts, hux] using hf .temp (by simp [rangeAllWork]))
  obtain ⟨d, hd, h3⟩ := clearMany_executes [out] v
  have hresult : clearManyEval [out] v = coverageResult p m A s := by
    apply countdownStore_ext
    · rw [clearMany_state]
      apply Prod.ext
      · exact guardedCellCompare_frame .eq A C u
      · rw [guardedCellCompare_flag]
        simp [u, typeCountResult, coverageResult, coverageAnswer, C, cellCompareAnswer, eq_comm]
    · funext j
      by_cases hj : j = out
      · subst j
        rw [clearMany_member _ _ (by simp)]
        exact ho.symm
      · rw [clearMany_outside _ _ (by simp [hj]), guardedCellCompare_stacks]
        simp [u, typeCountResult, hj]
  have hmass : cleanupMass [out] v = C := by
    simp [cleanupMass, v, guardedCellCompare_stacks, huout]
  have hC : C ≤ L := (typeCountAnswer_le m A _ _).trans (hs.1.2.1.trans hs.1.1)
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3)
  rw [hresult] at he
  refine ⟨a + (b + d), ?_, he⟩
  simp only [List.length_cons, List.length_nil, hmass] at hd
  unfold coverageBound
  omega

theorem coverageAnswer_observed_typed (N m q : ℕ) (word mask rest : List Bool)
    (hparse : rawForestMaskParse word.length q word = some (rest, mask))
    (hcheck : forestMaskCellCheck N m word mask = true) :
    ∃ Ts : List (BTree (Cell N m)), Ts.length = q ∧ word = Ts.flatMap treeBits ++ rest ∧
      coverageAnswer m (N + m * N + 3) word mask =
        decide (scanDistinctCount ((Ts.flatMap scanLeaves).map Prod.snd) = N + m * N + 3) := by
  obtain ⟨Ts, hq, hw, hc⟩ := typeCountAnswer_observed_typed N m q word mask rest hparse hcheck
  exact ⟨Ts, hq, hw, by rw [coverageAnswer, hc]⟩

theorem coverage_executes_observed_typed (p : InclusionPorts K) (out : K)
    (hout : ∀ j : InclusionPort, out ≠ p j) (N m q L : ℕ)
    (s : CountdownStore K F) (rest : List Bool)
    (hs : UniqueEntry p m (N + m * N + 3) L s) (ho : s.stk out = [])
    (hparse : rawForestMaskParse (s.stk (p (.outer .originalWord))).length q
      (s.stk (p (.outer .originalWord))) = some (rest, s.stk (p (.outer .originalMask))))
    (hcheck : forestMaskCellCheck N m (s.stk (p (.outer .originalWord)))
      (s.stk (p (.outer .originalMask))) = true) :
    ∃ Ts : List (BTree (Cell N m)), ∃ n : ℕ, Ts.length = q ∧
      s.stk (p (.outer .originalWord)) = Ts.flatMap treeBits ++ rest ∧
      n ≤ coverageBound m (N + m * N + 3) L ∧
      (coverageRoutine p out hout).Executes s
        ⟨((s.state.1.1, false),
          decide (scanDistinctCount ((Ts.flatMap scanLeaves).map Prod.snd) = N + m * N + 3)), s.stk⟩ n := by
  obtain ⟨Ts, hq, hw, hans⟩ := coverageAnswer_observed_typed N m q
    (s.stk (p (.outer .originalWord))) (s.stk (p (.outer .originalMask))) rest hparse hcheck
  obtain ⟨n, hn, he⟩ := coverage_executes p out hout m (N + m * N + 3) L s hs ho
  refine ⟨Ts, n, hq, hw, hn, ?_⟩
  simpa only [coverageResult, hans] using he

/- Bounds remain parameterized in physical m,A,L. The binary N,m guards
and paid cap/product sequence must precede these routines. Coverage alone
does not ensure per-row markers, mixedness, or identical cell sets. The
final all-word verifier and compatible encoded hardness remain open. -/

end PolytomyReductionModel.WholeVerifierController
