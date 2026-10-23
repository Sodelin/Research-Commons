/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

WORK IN PROGRESS: actual bounded headers for the SAME original verifier.
N and m must be range-rejected while still capped at target-length+1,
before A=N+mN+3 is materialized. Budget is saturated, not range-rejected.
The current definitions are intended for ONE pair/header/guard controller;
they do not supply its initial cap construction or final machine witness.
-/
import PolytomyWholeScoreController
import PolytomyPreservingProductStore

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

inductive HeaderScratchPort where
  | temp | residue | subtrahend
  deriving DecidableEq, Fintype

abbrev HeaderScratchPorts (K : Type) := HeaderScratchPort ↪ K

@[simp] theorem headerScratchPorts_eq (p : HeaderScratchPorts K) (a b : HeaderScratchPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def headerScalarComparePorts (p : HeaderScratchPorts K) (dest : K)
    (hdest : ∀ j : HeaderScratchPort, dest ≠ p j) : CellComparePorts (NumericStack K) where
  toFun := fun
    | .left => .inl .cap
    | .right => .inr dest
    | .temp => .inr (p .temp)
    | .residue => .inr (p .residue)
    | .subtrahend => .inr (p .subtrahend)
  inj' := by intro a b h; cases a <;> cases b <;> simp_all [hdest]

def headerScalarMode (strict : Bool) : CellCompareMode := if strict then .lt else .le

def headerScalarRead (strict : Bool) (C : ℕ) (bits : List Bool) : Option (ℕ × List Bool) :=
  (readSaturatedBinaryNatFrame C bits).bind (fun q =>
    if cellCompareAnswer (headerScalarMode strict) C q.1 then some q else none)

theorem headerScalarRead_bounded (L : ℕ) (bits : List Bool) :
    headerScalarRead true (L + 1) bits = readBoundedNatFrame L bits := by
  unfold headerScalarRead readBoundedNatFrame
  cases hp : readSaturatedBinaryNatFrame (L + 1) bits with
  | none => simp [hp]
  | some q =>
      rcases q with ⟨n, rest⟩
      have he : (n < L + 1) ↔ n ≤ L := by omega
      simp [hp, headerScalarMode, cellCompareAnswer, he]

theorem headerScalarRead_saturated (C : ℕ) (bits : List Bool) :
    headerScalarRead false C bits = readSaturatedBinaryNatFrame C bits := by
  unfold headerScalarRead
  cases hp : readSaturatedBinaryNatFrame C bits with
  | none => simp [hp]
  | some q =>
      rcases q with ⟨n, rest⟩
      have hn := readSaturated_value_le C bits n rest hp
      simp [hp, headerScalarMode, cellCompareAnswer, hn]

def headerScalarFinishRoutine (p : HeaderScratchPorts K) (dest : K)
    (hdest : ∀ j : HeaderScratchPort, dest ≠ p j) (strict : Bool) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (countdownPopOp (.inr dest)))
    (RoutineComposition.seq
      (guardedCellCompareRoutine (headerScalarComparePorts p dest hdest) (headerScalarMode strict))
      (RoutineComposition.seq
        (RoutineControl.branch Prod.snd (Atom.routine cleanupNoop) (clearManyRoutine [.inr dest]))
        (Atom.routine countdownResetOp)))

def headerScalarRoutine (p : HeaderScratchPorts K) (dest counter : K)
    (hdest : ∀ j : HeaderScratchPort, dest ≠ p j) (strict : Bool) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (guardedNumericRoutine dest counter)
    (headerScalarFinishRoutine p dest hdest strict)

def headerScalarFinishResult (dest : K) (strict : Bool) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) : CountdownStore (NumericStack K) F :=
  let u := countdownPop (.inr dest) s
  let flag := s.state.2 && cellCompareAnswer (headerScalarMode strict) C (u.stk (.inr dest)).length
  ⟨((s.state.1.1, false), flag), if flag then u.stk else Function.update u.stk (.inr dest) []⟩

/-- Entry to this finish is the ACTUAL reversed unary record emitted by
the original capped reader, or an empty record on failure. One physical
pop removes its false delimiter; no unary framing is guessed or ignored. -/
theorem headerScalarFinish_executes (p : HeaderScratchPorts K) (dest : K)
    (hdest : ∀ j : HeaderScratchPort, dest ≠ p j) (strict : Bool) (C n : ℕ)
    (s : CountdownStore (NumericStack K) F)
    (hC : s.stk (.inl .cap) = List.replicate C true)
    (hout : (s.stk (.inr dest)).tail = List.replicate n true)
    (hfresh : ∀ j : HeaderScratchPort, s.stk (.inr (p j)) = []) :
    ∃ steps ≤ 4 * C + 5 * n + 15,
      (headerScalarFinishRoutine p dest hdest strict).Executes s
        (headerScalarFinishResult dest strict C s) steps := by
  let u := countdownPop (.inr dest) s
  let v := guardedCellCompareEval (headerScalarMode strict) C n u
  have h1 := Atom.executes (countdownPopOp (.inr dest)) s
  have huout : u.stk (.inr dest) = List.replicate n true := by
    simpa only [u, countdownPop_counter] using hout
  have huC : u.stk (.inl .cap) = List.replicate C true := by
    simpa [u, countdownPop, countdownPopOp, Op.apply] using hC
  have hux (j : HeaderScratchPort) : u.stk (.inr (p j)) = [] := by
    simpa [u, countdownPop, countdownPopOp, Op.apply, (hdest j).symm] using hfresh j
  obtain ⟨a, ha, h2⟩ := guardedCellCompare_executes (headerScalarComparePorts p dest hdest)
    (headerScalarMode strict) C n u huC huout (hux .residue) (hux .subtrahend) (hux .temp)
  have hvstk : v.stk = u.stk := guardedCellCompare_stacks _ _ _ _
  have hvstate : v.state.1 = u.state.1 := guardedCellCompare_frame _ _ _ _
  have hvflag : v.state.2 = s.state.2 && cellCompareAnswer (headerScalarMode strict) C n :=
    guardedCellCompare_flag _ _ _ _
  cases hg : v.state.2 with
  | false =>
      obtain ⟨d, hd, h3⟩ := clearMany_executes [.inr dest] v
      have h4 := RoutineControl.branch_false Prod.snd (Atom.routine cleanupNoop)
        (clearManyRoutine [.inr dest]) hg h3
      have h5 := Atom.executes (countdownResetOp (K := NumericStack K) (F := F))
        (clearManyEval [.inr dest] v)
      have hr : countdownReset (clearManyEval [.inr dest] v) = headerScalarFinishResult dest strict C s := by
        apply countdownStore_ext
        · simp [headerScalarFinishResult, ← hvflag, ← huout, hg, countdownReset,
            countdownResetOp, Op.apply, clearMany_state, hvstate, u]
        · simp [headerScalarFinishResult, ← hvflag, ← huout, hg, countdownReset,
            countdownResetOp, Op.apply, clearManyEval, clearStackEval, hvstk, u]
      have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
        (RoutineComposition.seq_executes _ _ h4 h5))
      change (headerScalarFinishRoutine p dest hdest strict).Executes s (countdownReset (clearManyEval [.inr dest] v)) _ at he
      rw [hr] at he
      have hm : cleanupMass [.inr dest] v = n := by simp [cleanupMass, hvstk, huout]
      simp only [hm, List.length_cons, List.length_nil] at hd
      exact ⟨1 + (a + (d + 1 + 1)), by omega, he⟩
  | true =>
      have h3 := RoutineControl.branch_true Prod.snd (Atom.routine cleanupNoop)
        (clearManyRoutine [.inr dest]) hg (Atom.executes cleanupNoop v)
      have h4 := Atom.executes (countdownResetOp (K := NumericStack K) (F := F)) v
      have hr : countdownReset v = headerScalarFinishResult dest strict C s := by
        apply countdownStore_ext
        · simp [headerScalarFinishResult, ← hvflag, ← huout, hg, countdownReset,
            countdownResetOp, Op.apply, hvstate, u]
        · simp [headerScalarFinishResult, ← hvflag, ← huout, hg, countdownReset,
            countdownResetOp, Op.apply, hvstk, u]
      have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
        (RoutineComposition.seq_executes _ _ h3 h4))
      refine ⟨1 + (a + (2 + 1)), by omega, ?_⟩
      simpa only [cleanupNoop, Op.apply, ← hr] using he

def headerScalarEval (p : HeaderScratchPorts K) (dest : K) (strict : Bool) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) : CountdownStore (NumericStack K) F :=
  headerScalarFinishResult dest strict C (guardedNumericEval dest C s)

def headerScalarBound (L C : ℕ) := numericRecordStepBound L C + 9 * C + 16

def HeaderScalarEntry (p : HeaderScratchPorts K) (dest : K) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) : Prop :=
  NumericLoopInv C L s ∧ s.stk (.inr dest) = [] ∧
    ∀ j : HeaderScratchPort, s.stk (.inr (p j)) = []

theorem headerScalar_executes (p : HeaderScratchPorts K) (dest counter : K)
    (hdc : dest ≠ counter) (hdest : ∀ j : HeaderScratchPort, dest ≠ p j)
    (strict : Bool) (C L : ℕ) (s : CountdownStore (NumericStack K) F)
    (hs : HeaderScalarEntry p dest C L s) :
    ∃ n ≤ headerScalarBound L C,
      (headerScalarRoutine p dest counter hdest strict).Executes s
        (headerScalarEval p dest strict C s) n := by
  let u := guardedNumericEval dest C s
  obtain ⟨a, ha, h1, huInv⟩ := guardedNumeric_executes dest counter hdc C L s hs.1
  have hufresh (j : HeaderScratchPort) : u.stk (.inr (p j)) = [] :=
    (guardedNumeric_extra dest (p j) (hdest j).symm C s).trans (hs.2.2 j)
  have hv : ∃ n ≤ C, (u.stk (.inr dest)).tail = List.replicate n true := by
    cases hf : s.state.2 with
    | false => exact ⟨0, Nat.zero_le _, by simp [u, guardedNumericEval, hf, countdownReset,
        countdownResetOp, Op.apply, hs.2.1]⟩
    | true =>
        cases hp : readSaturatedBinaryNatFrame C (s.stk (.inl .source)) with
        | none => exact ⟨0, Nat.zero_le _, by simp [u, guardedNumericEval, hf, numericRecordEval,
            numericRecordResult, hp, numericStore, numericStacks, hs.2.1]⟩
        | some q =>
            rcases q with ⟨n, rest⟩
            exact ⟨n, readSaturated_value_le C _ n rest hp, by
              simp [u, guardedNumericEval, hf, numericRecordEval, numericRecordResult,
                hp, numericStore, numericStacks, hs.2.1, reverse_unaryFrame_append]⟩
  obtain ⟨n, hn, hv⟩ := hv
  obtain ⟨b, hb, h2⟩ := headerScalarFinish_executes p dest hdest strict C n u
    huInv.2.2.2.1 hv hufresh
  exact ⟨a + b, by unfold headerScalarBound; omega, RoutineComposition.seq_executes _ _ h1 h2⟩

def observeHeaderScalar (dest : K) (s : CountdownStore (NumericStack K) F) : Option (ℕ × List Bool) :=
  if s.state.2 then some ((s.stk (.inr dest)).length, s.stk (.inl .source)) else none

theorem headerScalar_observation (p : HeaderScratchPorts K) (dest : K)
    (strict : Bool) (C : ℕ) (s : CountdownStore (NumericStack K) F)
    (hd : s.stk (.inr dest) = []) :
    observeHeaderScalar dest (headerScalarEval p dest strict C s) =
      if s.state.2 then headerScalarRead strict C (s.stk (.inl .source)) else none := by
  cases hf : s.state.2 with
  | false => simp [headerScalarEval, headerScalarFinishResult, guardedNumericEval, hf,
      countdownReset, countdownResetOp, countdownPop, countdownPopOp, Op.apply,
      observeHeaderScalar, hd]
  | true =>
      cases hp : readSaturatedBinaryNatFrame C (s.stk (.inl .source)) with
      | none => simp [headerScalarEval, headerScalarFinishResult, guardedNumericEval, hf,
          numericRecordEval, numericRecordResult, hp, numericStore, numericStacks,
          countdownPop, countdownPopOp, Op.apply, observeHeaderScalar, headerScalarRead, hd]
      | some q =>
          rcases q with ⟨n, rest⟩
          simp [headerScalarEval, headerScalarFinishResult, guardedNumericEval, hf,
            numericRecordEval, numericRecordResult, hp, numericStore, numericStacks,
            countdownPop, countdownPopOp, Op.apply, observeHeaderScalar, headerScalarRead,
            hd, reverse_unaryFrame_append]

theorem headerScalar_extra (p : HeaderScratchPorts K) (dest k : K) (hkd : k ≠ dest)
    (strict : Bool) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    (headerScalarEval p dest strict C s).stk (.inr k) = s.stk (.inr k) := by
  unfold headerScalarEval headerScalarFinishResult
  split <;> simp [countdownPop, countdownPopOp, Op.apply, hkd,
    guardedNumeric_extra dest k hkd C s]

theorem headerScalar_frame (p : HeaderScratchPorts K) (dest : K)
    (strict : Bool) (C : ℕ) (s : CountdownStore (NumericStack K) F) :
    (headerScalarEval p dest strict C s).state.1 = (s.state.1.1, false) := by
  apply Prod.ext
  · exact guardedNumeric_frame dest C s
  · rfl

theorem headerScalar_failed (p : HeaderScratchPorts K) (dest : K)
    (strict : Bool) (C : ℕ) (s : CountdownStore (NumericStack K) F)
    (hf : s.state.2 = false) (hd : s.stk (.inr dest) = []) :
    headerScalarEval p dest strict C s = countdownReset s := by
  apply countdownStore_ext
  · simp [headerScalarEval, headerScalarFinishResult, guardedNumericEval, hf,
      countdownReset, countdownResetOp, Op.apply]
  · funext j
    by_cases hj : j = (.inr dest : NumericStack K)
    · subst j
      simp [headerScalarEval, headerScalarFinishResult, guardedNumericEval, hf,
        countdownReset, countdownResetOp, countdownPop, countdownPopOp, Op.apply, hd]
    · simp [headerScalarEval, headerScalarFinishResult, guardedNumericEval, hf,
        countdownReset, countdownResetOp, countdownPop, countdownPopOp, Op.apply, hj]

theorem headerScalar_numericInv (p : HeaderScratchPorts K) (dest : K)
    (strict : Bool) (C L : ℕ) (s : CountdownStore (NumericStack K) F)
    (hs : NumericLoopInv C L s) : NumericLoopInv C L (headerScalarEval p dest strict C s) := by
  have hu : NumericLoopInv C L (guardedNumericEval dest C s) := by
    cases hf : s.state.2 with
    | false => simpa [guardedNumericEval, hf, NumericLoopInv, countdownReset, countdownResetOp, Op.apply] using hs
    | true => simpa only [guardedNumericEval, hf, ↓reduceIte] using numericRecordEval_invariant dest C L s hs
  rcases hu with ⟨hp, hw, ho, hc, hL⟩
  unfold NumericLoopInv headerScalarEval headerScalarFinishResult
  split <;> simpa [countdownPop, countdownPopOp, Op.apply] using And.intro hp ⟨hw, ho, hc, hL⟩

theorem headerScalar_dest_bound (p : HeaderScratchPorts K) (dest : K)
    (strict : Bool) (C : ℕ) (s : CountdownStore (NumericStack K) F)
    (hd : s.stk (.inr dest) = []) :
    ((headerScalarEval p dest strict C s).stk (.inr dest)).length ≤ C := by
  cases hf : s.state.2 with
  | false => simp [headerScalar_failed p dest strict C s hf hd, countdownReset, countdownResetOp, Op.apply, hd]
  | true =>
      cases hp : readSaturatedBinaryNatFrame C (s.stk (.inl .source)) with
      | none => simp [headerScalarEval, headerScalarFinishResult, guardedNumericEval, hf,
          numericRecordEval, numericRecordResult, hp, numericStore, numericStacks,
          countdownPop, countdownPopOp, Op.apply]
      | some q =>
          rcases q with ⟨n, rest⟩
          have hn := readSaturated_value_le C _ n rest hp
          simp only [headerScalarEval, headerScalarFinishResult, guardedNumericEval, hf, ↓reduceIte,
            numericRecordEval, hp, numericRecordResult, numericStore, numericStacks,
            Function.update_same, hd, reverse_unaryFrame_append, countdownPop,
            countdownPopOp, Op.apply, List.tail_cons, List.length_replicate, Bool.true_and]
          split <;> simp_all

def switchedHeaderScalarRoutine (p : HeaderScratchPorts K) (dest counter large : K)
    (hdest : ∀ j : HeaderScratchPort, dest ≠ p j) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (numericCapSwap large (p .temp))
    (RoutineComposition.seq (headerScalarRoutine p dest counter hdest false)
      (numericCapSwap large (p .temp)))

def switchedHeaderScalarEval (p : HeaderScratchPorts K) (dest large : K) (D : ℕ)
    (s : CountdownStore (NumericStack K) F) : CountdownStore (NumericStack K) F :=
  numericCapSwapEval large (p .temp)
    (headerScalarEval p dest false D (numericCapSwapEval large (p .temp) s))

/-- Actual capped budget reader with both physical caps restored even on
failure. It saturates at D; it does NOT reject a budget equal to D. -/
theorem switchedHeaderScalar_executes (p : HeaderScratchPorts K) (dest counter large : K)
    (hdc : dest ≠ counter) (hdl : dest ≠ large)
    (hdest : ∀ j : HeaderScratchPort, dest ≠ p j)
    (hlarge : ∀ j : HeaderScratchPort, large ≠ p j) (C D L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : HeaderScalarEntry p dest C L s)
    (hD : s.stk (.inr large) = List.replicate D true) :
    ∃ n ≤ headerScalarBound L D + 3 * C + 3 * D + 6,
      (switchedHeaderScalarRoutine p dest counter large hdest).Executes s
        (switchedHeaderScalarEval p dest large D s) n ∧
      NumericLoopInv C L (switchedHeaderScalarEval p dest large D s) ∧
      (switchedHeaderScalarEval p dest large D s).stk (.inr large) = List.replicate D true ∧
      (switchedHeaderScalarEval p dest large D s).stk (.inr (p .temp)) = [] := by
  let u := numericCapSwapEval large (p .temp) s
  obtain ⟨h1, hi1, hl1, ht1⟩ := numericCapSwap_executes large (p .temp) (hlarge .temp)
    C D L s hs.1 hD (hs.2.2 .temp)
  have hud : u.stk (.inr dest) = [] := by
    rw [capExchange_outside (.inl .cap : NumericStack K) (.inr large) (.inr (p .temp))
      (.inr dest) (by simp) (by simpa using hdl) (by simpa using hdest .temp)]
    exact hs.2.1
  have huscratch (j : HeaderScratchPort) : u.stk (.inr (p j)) = [] := by
    by_cases hj : j = .temp
    · subst j; exact ht1
    · rw [capExchange_outside (.inl .cap : NumericStack K) (.inr large) (.inr (p .temp))
        (.inr (p j)) (by simp) (by simpa using (hlarge j).symm) (by simpa using hj)]
      exact hs.2.2 j
  obtain ⟨a, ha, h2⟩ := headerScalar_executes p dest counter hdc hdest false D L u ⟨hi1, hud, huscratch⟩
  let v := headerScalarEval p dest false D u
  have hiv := headerScalar_numericInv p dest false D L u hi1
  have hlv : v.stk (.inr large) = List.replicate C true :=
    (headerScalar_extra p dest large hdl.symm false D u).trans hl1
  have htv : v.stk (.inr (p .temp)) = [] :=
    (headerScalar_extra p dest (p .temp) (hdest .temp).symm false D u).trans ht1
  obtain ⟨h3, hi3, hl3, ht3⟩ := numericCapSwap_executes large (p .temp) (hlarge .temp)
    D C L v hiv hlv htv
  exact ⟨2 * C + D + 3 + (a + (2 * D + C + 3)), by omega,
    RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3), hi3, hl3, ht3⟩

theorem switchedHeaderScalar_observation (p : HeaderScratchPorts K) (dest large : K)
    (hdl : dest ≠ large) (hdt : dest ≠ p .temp) (D : ℕ)
    (s : CountdownStore (NumericStack K) F) (hd : s.stk (.inr dest) = []) :
    observeHeaderScalar dest (switchedHeaderScalarEval p dest large D s) =
      if s.state.2 then readSaturatedBinaryNatFrame D (s.stk (.inl .source)) else none := by
  have ho (t : CountdownStore (NumericStack K) F) :
      observeHeaderScalar dest (numericCapSwapEval large (p .temp) t) = observeHeaderScalar dest t := by
    have hsrc := capExchange_outside (.inl .cap : NumericStack K) (.inr large) (.inr (p .temp))
      (.inl .source) (by simp) (by simp) (by simp) t
    have hdv := capExchange_outside (.inl .cap : NumericStack K) (.inr large) (.inr (p .temp))
      (.inr dest) (by simp) (by simpa using hdl) (by simpa using hdt) t
    unfold observeHeaderScalar
    change (if t.state.2 then some (((numericCapSwapEval large (p .temp) t).stk (.inr dest)).length,
      (numericCapSwapEval large (p .temp) t).stk (.inl .source)) else none) = _
    rw [hsrc, hdv]
  have hsrc := capExchange_outside (.inl .cap : NumericStack K) (.inr large) (.inr (p .temp))
    (.inl .source) (by simp) (by simp) (by simp) s
  have hdv := capExchange_outside (.inl .cap : NumericStack K) (.inr large) (.inr (p .temp))
    (.inr dest) (by simp) (by simpa using hdl) (by simpa using hdt) s
  rw [switchedHeaderScalarEval, ho, headerScalar_observation p dest false D _ (hdv.trans hd),
    headerScalarRead_saturated, hsrc]
  rfl

inductive VerifierHeaderPort where
  | universe | rows | budget | large | counter | temp | residue | subtrahend
  deriving DecidableEq, Fintype

abbrev VerifierHeaderPorts (K : Type) := VerifierHeaderPort ↪ K

@[simp] theorem verifierHeaderPorts_eq (p : VerifierHeaderPorts K) (a b : VerifierHeaderPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def verifierHeaderScratch (p : VerifierHeaderPorts K) : HeaderScratchPorts K where
  toFun := fun
    | .temp => p .temp
    | .residue => p .residue
    | .subtrahend => p .subtrahend
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

theorem verifierHeader_universe_distinct (p : VerifierHeaderPorts K) (j : HeaderScratchPort) :
    p .universe ≠ verifierHeaderScratch p j := by cases j <;> simp [verifierHeaderScratch]
theorem verifierHeader_rows_distinct (p : VerifierHeaderPorts K) (j : HeaderScratchPort) :
    p .rows ≠ verifierHeaderScratch p j := by cases j <;> simp [verifierHeaderScratch]
theorem verifierHeader_budget_distinct (p : VerifierHeaderPorts K) (j : HeaderScratchPort) :
    p .budget ≠ verifierHeaderScratch p j := by cases j <;> simp [verifierHeaderScratch]
theorem verifierHeader_large_distinct (p : VerifierHeaderPorts K) (j : HeaderScratchPort) :
    p .large ≠ verifierHeaderScratch p j := by cases j <;> simp [verifierHeaderScratch]

def verifierHeadersRoutine (p : VerifierHeaderPorts K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq
    (headerScalarRoutine (verifierHeaderScratch p) (p .universe) (p .counter)
      (verifierHeader_universe_distinct p) true)
    (RoutineComposition.seq
      (headerScalarRoutine (verifierHeaderScratch p) (p .rows) (p .counter)
        (verifierHeader_rows_distinct p) true)
      (switchedHeaderScalarRoutine (verifierHeaderScratch p) (p .budget) (p .counter) (p .large)
        (verifierHeader_budget_distinct p)))

def verifierHeadersAfterN (p : VerifierHeaderPorts K) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) :=
  headerScalarEval (verifierHeaderScratch p) (p .universe) true C s

def verifierHeadersAfterM (p : VerifierHeaderPorts K) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) :=
  headerScalarEval (verifierHeaderScratch p) (p .rows) true C (verifierHeadersAfterN p C s)

def verifierHeadersEval (p : VerifierHeaderPorts K) (C D : ℕ)
    (s : CountdownStore (NumericStack K) F) :=
  switchedHeaderScalarEval (verifierHeaderScratch p) (p .budget) (p .large) D
    (verifierHeadersAfterM p C s)

def VerifierHeadersEntry (p : VerifierHeaderPorts K) (C D L : ℕ)
    (s : CountdownStore (NumericStack K) F) : Prop :=
  NumericLoopInv C L s ∧ s.stk (.inr (p .large)) = List.replicate D true ∧
    ∀ j : VerifierHeaderPort, j ≠ .large → s.stk (.inr (p j)) = []

def verifierHeadersBound (L C D : ℕ) : ℕ :=
  2 * headerScalarBound L C + headerScalarBound L D + 3 * C + 3 * D + 6

theorem verifierHeaders_executes (p : VerifierHeaderPorts K) (C D L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : VerifierHeadersEntry p C D L s) :
    ∃ n ≤ verifierHeadersBound L C D,
      (verifierHeadersRoutine p).Executes s (verifierHeadersEval p C D s) n ∧
      NumericLoopInv C L (verifierHeadersEval p C D s) ∧
      (verifierHeadersEval p C D s).stk (.inr (p .large)) = List.replicate D true ∧
      (verifierHeadersEval p C D s).stk (.inr (p .temp)) = [] := by
  let h := verifierHeaderScratch p
  have hscratch (j : HeaderScratchPort) : s.stk (.inr (h j)) = [] := by
    cases j <;> exact hs.2.2 _ (by decide)
  have hnentry : HeaderScalarEntry h (p .universe) C L s :=
    ⟨hs.1, hs.2.2 .universe (by decide), hscratch⟩
  obtain ⟨a, ha, h1⟩ := headerScalar_executes h (p .universe) (p .counter)
    (by simp) (verifierHeader_universe_distinct p) true C L s hnentry
  let u := verifierHeadersAfterN p C s
  have hui : NumericLoopInv C L u := headerScalar_numericInv h (p .universe) true C L s hs.1
  have hux (j : VerifierHeaderPort) (hj : j ≠ .universe) : u.stk (.inr (p j)) = s.stk (.inr (p j)) :=
    headerScalar_extra h (p .universe) (p j) (by simpa using hj) true C s
  have huscratch (j : HeaderScratchPort) : u.stk (.inr (h j)) = [] := by
    cases j <;> exact (hux _ (by decide)).trans (hs.2.2 _ (by decide))
  have hmentry : HeaderScalarEntry h (p .rows) C L u :=
    ⟨hui, (hux .rows (by decide)).trans (hs.2.2 .rows (by decide)), huscratch⟩
  obtain ⟨b, hb, h2⟩ := headerScalar_executes h (p .rows) (p .counter)
    (by simp) (verifierHeader_rows_distinct p) true C L u hmentry
  let v := verifierHeadersAfterM p C s
  have hvi : NumericLoopInv C L v := headerScalar_numericInv h (p .rows) true C L u hui
  have hvx (j : VerifierHeaderPort) (hj : j ≠ .rows) : v.stk (.inr (p j)) = u.stk (.inr (p j)) :=
    headerScalar_extra h (p .rows) (p j) (by simpa using hj) true C u
  have hvscratch (j : HeaderScratchPort) : v.stk (.inr (h j)) = [] := by
    cases j <;> exact (hvx _ (by decide)).trans ((hux _ (by decide)).trans (hs.2.2 _ (by decide)))
  have hbentry : HeaderScalarEntry h (p .budget) C L v :=
    ⟨hvi, (hvx .budget (by decide)).trans ((hux .budget (by decide)).trans
      (hs.2.2 .budget (by decide))), hvscratch⟩
  have hlarge : v.stk (.inr (p .large)) = List.replicate D true :=
    (hvx .large (by decide)).trans ((hux .large (by decide)).trans hs.2.1)
  obtain ⟨c, hc, h3, hfinal, hcap, htemp⟩ := switchedHeaderScalar_executes h
    (p .budget) (p .counter) (p .large) (by simp) (by simp)
    (verifierHeader_budget_distinct p) (verifierHeader_large_distinct p) C D L v hbentry hlarge
  exact ⟨a + (b + c), by unfold verifierHeadersBound; omega,
    RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3), hfinal, hcap, htemp⟩

def readVerifierHeaders (L cap : ℕ) (bits : List Bool) : Option ((ℕ × ℕ × ℕ) × List Bool) :=
  (readBoundedNatFrame L bits).bind (fun qN =>
    (readBoundedNatFrame L qN.2).bind (fun qm =>
      (readSaturatedBinaryNatFrame cap qm.2).map (fun qB => ((qN.1, qm.1, qB.1), qB.2))))

def observeVerifierHeaders (p : VerifierHeaderPorts K) (s : CountdownStore (NumericStack K) F) :
    Option ((ℕ × ℕ × ℕ) × List Bool) :=
  if s.state.2 then some (((s.stk (.inr (p .universe))).length,
    (s.stk (.inr (p .rows))).length, (s.stk (.inr (p .budget))).length), s.stk (.inl .source)) else none

theorem observeHeaderScalar_none (dest : K) (s : CountdownStore (NumericStack K) F) :
    observeHeaderScalar dest s = none ↔ s.state.2 = false := by
  cases h : s.state.2 <;> simp [observeHeaderScalar, h]

theorem observeHeaderScalar_some (dest : K) (s : CountdownStore (NumericStack K) F)
    (n : ℕ) (rest : List Bool) :
    observeHeaderScalar dest s = some (n, rest) ↔
      s.state.2 = true ∧ (s.stk (.inr dest)).length = n ∧ s.stk (.inl .source) = rest := by
  cases h : s.state.2 <;> simp [observeHeaderScalar, h, Prod.mk.injEq]

theorem switchedHeaderScalar_extra (p : HeaderScratchPorts K) (dest large k : K)
    (hkd : k ≠ dest) (hkl : k ≠ large) (hkt : k ≠ p .temp) (D : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    (switchedHeaderScalarEval p dest large D s).stk (.inr k) = s.stk (.inr k) := by
  unfold switchedHeaderScalarEval
  rw [capExchange_outside (.inl .cap : NumericStack K) (.inr large) (.inr (p .temp))
    (.inr k) (by simp) (by simpa using hkl) (by simpa using hkt)]
  rw [headerScalar_extra p dest k hkd false D]
  exact capExchange_outside (.inl .cap : NumericStack K) (.inr large) (.inr (p .temp))
    (.inr k) (by simp) (by simpa using hkl) (by simpa using hkt) s

/-- Exact three-header observation on arbitrary Boolean words. N,m use
the sentinel L+1 and reject it; the third header is merely saturated at
cap. The remaining word is the ORIGINAL unary count plus concatenated
self-delimiting tree forest. No row parser or new framing is substituted. -/
theorem verifierHeaders_observation (p : VerifierHeaderPorts K) (L cap : ℕ)
    (s : CountdownStore (NumericStack K) F)
    (hN0 : s.stk (.inr (p .universe)) = []) (hm0 : s.stk (.inr (p .rows)) = [])
    (hB0 : s.stk (.inr (p .budget)) = []) :
    observeVerifierHeaders p (verifierHeadersEval p (L + 1) cap s) =
      if s.state.2 then readVerifierHeaders L cap (s.stk (.inl .source)) else none := by
  let h := verifierHeaderScratch p
  let u := verifierHeadersAfterN p (L + 1) s
  let v := verifierHeadersAfterM p (L + 1) s
  let w := verifierHeadersEval p (L + 1) cap s
  have hum0 : u.stk (.inr (p .rows)) = [] :=
    (headerScalar_extra h (p .universe) (p .rows) (by simp) true (L + 1) s).trans hm0
  have huB0 : u.stk (.inr (p .budget)) = [] :=
    (headerScalar_extra h (p .universe) (p .budget) (by simp) true (L + 1) s).trans hB0
  have hvB0 : v.stk (.inr (p .budget)) = [] :=
    (headerScalar_extra h (p .rows) (p .budget) (by simp) true (L + 1) u).trans huB0
  have hvN : v.stk (.inr (p .universe)) = u.stk (.inr (p .universe)) :=
    headerScalar_extra h (p .rows) (p .universe) (by simp) true (L + 1) u
  have hwN : w.stk (.inr (p .universe)) = v.stk (.inr (p .universe)) :=
    switchedHeaderScalar_extra h (p .budget) (p .large) (p .universe)
      (by simp) (by simp) (by simp [h, verifierHeaderScratch]) cap v
  have hwm : w.stk (.inr (p .rows)) = v.stk (.inr (p .rows)) :=
    switchedHeaderScalar_extra h (p .budget) (p .large) (p .rows)
      (by simp) (by simp) (by simp [h, verifierHeaderScratch]) cap v
  have hnobs : observeHeaderScalar (p .universe) u =
      if s.state.2 then readBoundedNatFrame L (s.stk (.inl .source)) else none := by
    simpa only [headerScalarRead_bounded] using headerScalar_observation h (p .universe) true (L + 1) s hN0
  have hmobs : observeHeaderScalar (p .rows) v =
      if u.state.2 then readBoundedNatFrame L (u.stk (.inl .source)) else none := by
    simpa only [headerScalarRead_bounded] using headerScalar_observation h (p .rows) true (L + 1) u hum0
  have hbobs : observeHeaderScalar (p .budget) w =
      if v.state.2 then readSaturatedBinaryNatFrame cap (v.stk (.inl .source)) else none :=
    switchedHeaderScalar_observation h (p .budget) (p .large) (by simp)
      (by simp [h, verifierHeaderScratch]) cap v hvB0
  cases hf : s.state.2 with
  | false =>
      have huf : u.state.2 = false := (observeHeaderScalar_none _ _).mp (by simpa [hf] using hnobs)
      have hvf : v.state.2 = false := (observeHeaderScalar_none _ _).mp (by simpa [huf] using hmobs)
      have hwf : w.state.2 = false := (observeHeaderScalar_none _ _).mp (by simpa [hvf] using hbobs)
      simp [observeVerifierHeaders, hf, hwf, w]
  | true =>
      cases hn : readBoundedNatFrame L (s.stk (.inl .source)) with
      | none =>
          have huf : u.state.2 = false := (observeHeaderScalar_none _ _).mp (by simpa [hf, hn] using hnobs)
          have hvf : v.state.2 = false := (observeHeaderScalar_none _ _).mp (by simpa [huf] using hmobs)
          have hwf : w.state.2 = false := (observeHeaderScalar_none _ _).mp (by simpa [hvf] using hbobs)
          simp [observeVerifierHeaders, hf, hwf, w, readVerifierHeaders, hn]
      | some qN =>
          rcases qN with ⟨N, rN⟩
          obtain ⟨huf, huN, huword⟩ := (observeHeaderScalar_some _ _ N rN).mp (by simpa [hf, hn] using hnobs)
          cases hm : readBoundedNatFrame L rN with
          | none =>
              have hvf : v.state.2 = false := (observeHeaderScalar_none _ _).mp (by simpa [huf, huword, hm] using hmobs)
              have hwf : w.state.2 = false := (observeHeaderScalar_none _ _).mp (by simpa [hvf] using hbobs)
              simp [observeVerifierHeaders, hf, hwf, w, readVerifierHeaders, hn, hm]
          | some qm =>
              rcases qm with ⟨m, rm⟩
              obtain ⟨hvf, hvm, hvword⟩ := (observeHeaderScalar_some _ _ m rm).mp
                (by simpa [huf, huword, hm] using hmobs)
              cases hB : readSaturatedBinaryNatFrame cap rm with
              | none =>
                  have hwf : w.state.2 = false := (observeHeaderScalar_none _ _).mp
                    (by simpa [hvf, hvword, hB] using hbobs)
                  simp [observeVerifierHeaders, hf, hwf, w, readVerifierHeaders, hn, hm, hB]
              | some qB =>
                  rcases qB with ⟨B, rest⟩
                  obtain ⟨hwf, hwB, hwword⟩ := (observeHeaderScalar_some _ _ B rest).mp
                    (by simpa [hvf, hvword, hB] using hbobs)
                  change (if w.state.2 then some (((w.stk (.inr (p .universe))).length,
                    (w.stk (.inr (p .rows))).length, (w.stk (.inr (p .budget))).length),
                    w.stk (.inl .source)) else none) = _
                  simp [hf, hwf, hwB, hwword, hwN, hvN, huN, hwm, hvm, readVerifierHeaders, hn, hm, hB]

theorem readVerifierHeaders_bounds (L cap : ℕ) (bits rest : List Bool) (N m B : ℕ)
    (h : readVerifierHeaders L cap bits = some ((N, m, B), rest)) :
    N ≤ L ∧ m ≤ L ∧ B ≤ cap ∧ N + m * N + 3 ≤ L * L + L + 3 := by
  unfold readVerifierHeaders at h
  cases hN : readBoundedNatFrame L bits with
  | none => simp [hN] at h
  | some qN =>
      rcases qN with ⟨n, rN⟩
      cases hm : readBoundedNatFrame L rN with
      | none => simp [hN, hm] at h
      | some qm =>
          rcases qm with ⟨k, rm⟩
          cases hB : readSaturatedBinaryNatFrame cap rm with
          | none => simp [hN, hm, hB] at h
          | some qB =>
              rcases qB with ⟨b, rb⟩
              have he : ((n, k, b), rb) = ((N, m, B), rest) := by simpa [hN, hm, hB] using h
              have hn : n ≤ L := by
                unfold readBoundedNatFrame at hN
                cases hx : readSaturatedBinaryNatFrame (L + 1) bits with
                | none => simp [hx] at hN
                | some z => split at hN <;> simp_all
              have hk : k ≤ L := by
                unfold readBoundedNatFrame at hm
                cases hx : readSaturatedBinaryNatFrame (L + 1) rN with
                | none => simp [hx] at hm
                | some z => split at hm <;> simp_all
              have hb := readSaturated_value_le cap rm b rb hB
              have hprod := Nat.mul_le_mul hk hn
              have hvals : n = N ∧ k = m ∧ b = B := by simpa only [Prod.mk.injEq] using (congrArg Prod.fst he)
              rcases hvals with ⟨rfl, rfl, rfl⟩
              exact ⟨hn, hk, hb, by omega⟩

theorem headerScalar_unary (p : HeaderScratchPorts K) (dest : K) (strict : Bool) (C : ℕ)
    (s : CountdownStore (NumericStack K) F) (hd : s.stk (.inr dest) = []) :
    (headerScalarEval p dest strict C s).stk (.inr dest) =
      List.replicate ((headerScalarEval p dest strict C s).stk (.inr dest)).length true := by
  cases hf : s.state.2 with
  | false => simp [headerScalar_failed p dest strict C s hf hd, countdownReset, countdownResetOp, Op.apply, hd]
  | true =>
      cases hp : readSaturatedBinaryNatFrame C (s.stk (.inl .source)) with
      | none => simp [headerScalarEval, headerScalarFinishResult, guardedNumericEval, hf,
          numericRecordEval, numericRecordResult, hp, numericStore, numericStacks,
          countdownPop, countdownPopOp, Op.apply]
      | some q =>
          rcases q with ⟨n, rest⟩
          cases hc : cellCompareAnswer (headerScalarMode strict) C n <;>
            simp [headerScalarEval, headerScalarFinishResult, guardedNumericEval, hf,
              numericRecordEval, numericRecordResult, hp, numericStore, numericStacks,
              countdownPop, countdownPopOp, Op.apply, hd, reverse_unaryFrame_append, hc]

theorem switchedHeaderScalar_unary (p : HeaderScratchPorts K) (dest large : K)
    (hdl : dest ≠ large) (hdt : dest ≠ p .temp) (D : ℕ)
    (s : CountdownStore (NumericStack K) F) (hd : s.stk (.inr dest) = []) :
    (switchedHeaderScalarEval p dest large D s).stk (.inr dest) =
      List.replicate ((switchedHeaderScalarEval p dest large D s).stk (.inr dest)).length true := by
  let u := numericCapSwapEval large (p .temp) s
  have hud : u.stk (.inr dest) = [] :=
    (capExchange_outside (.inl .cap : NumericStack K) (.inr large) (.inr (p .temp))
      (.inr dest) (by simp) (by simpa using hdl) (by simpa using hdt) s).trans hd
  have hx := capExchange_outside (.inl .cap : NumericStack K) (.inr large) (.inr (p .temp))
    (.inr dest) (by simp) (by simpa using hdl) (by simpa using hdt)
    (headerScalarEval p dest false D u)
  unfold switchedHeaderScalarEval
  rw [hx]
  exact headerScalar_unary p dest false D u hud

theorem verifierHeaders_extra (p : VerifierHeaderPorts K) (C D : ℕ)
    (s : CountdownStore (NumericStack K) F) (k : K)
    (hkN : k ≠ p .universe) (hkm : k ≠ p .rows) (hkB : k ≠ p .budget)
    (hkl : k ≠ p .large) (hkt : k ≠ p .temp) :
    (verifierHeadersEval p C D s).stk (.inr k) = s.stk (.inr k) := by
  unfold verifierHeadersEval
  rw [switchedHeaderScalar_extra (verifierHeaderScratch p) (p .budget) (p .large) k
    hkB hkl (by simpa [verifierHeaderScratch] using hkt)]
  rw [headerScalar_extra (verifierHeaderScratch p) (p .rows) k hkm true C]
  exact headerScalar_extra (verifierHeaderScratch p) (p .universe) k hkN true C s

theorem verifierHeaders_unary (p : VerifierHeaderPorts K) (C D : ℕ)
    (s : CountdownStore (NumericStack K) F)
    (hN0 : s.stk (.inr (p .universe)) = []) (hm0 : s.stk (.inr (p .rows)) = [])
    (hB0 : s.stk (.inr (p .budget)) = []) :
    ∀ j : VerifierHeaderPort, j = .universe ∨ j = .rows ∨ j = .budget →
      (verifierHeadersEval p C D s).stk (.inr (p j)) =
        List.replicate ((verifierHeadersEval p C D s).stk (.inr (p j))).length true := by
  let h := verifierHeaderScratch p
  let u := verifierHeadersAfterN p C s
  let v := verifierHeadersAfterM p C s
  have hum0 : u.stk (.inr (p .rows)) = [] :=
    (headerScalar_extra h (p .universe) (p .rows) (by simp) true C s).trans hm0
  have hvB0 : v.stk (.inr (p .budget)) = [] :=
    (headerScalar_extra h (p .rows) (p .budget) (by simp) true C u).trans
      ((headerScalar_extra h (p .universe) (p .budget) (by simp) true C s).trans hB0)
  intro j hj
  rcases hj with rfl | rfl | rfl
  · have hx := switchedHeaderScalar_extra h (p .budget) (p .large) (p .universe)
      (by simp) (by simp) (by simp [h, verifierHeaderScratch]) D v
    have hy := headerScalar_extra h (p .rows) (p .universe) (by simp) true C u
    change (switchedHeaderScalarEval h (p .budget) (p .large) D v).stk _ = _
    rw [hx, hy]
    exact headerScalar_unary h (p .universe) true C s hN0
  · have hx := switchedHeaderScalar_extra h (p .budget) (p .large) (p .rows)
      (by simp) (by simp) (by simp [h, verifierHeaderScratch]) D v
    change (switchedHeaderScalarEval h (p .budget) (p .large) D v).stk _ = _
    rw [hx]
    exact headerScalar_unary h (p .rows) true C u hum0
  · exact switchedHeaderScalar_unary h (p .budget) (p .large) (by simp)
      (by simp [h, verifierHeaderScratch]) D v hvB0

def verifierDimensionsRoutine (p : VerifierHeaderPorts K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (mixedCountPeekOp (.inr (p .universe))))
    (RoutineComposition.seq (wordDuplicateRoutine (.inr (p .rows)) (.inr (p .residue)) (.inr (p .temp)))
      (RoutineComposition.seq (Atom.routine (countdownPopOp (.inr (p .temp))))
        (RoutineComposition.seq (Atom.routine (mixedCountPeekOp (.inr (p .temp))))
          (clearManyRoutine [.inr (p .temp)]))))

def verifierDimensionsResult (N m : ℕ) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  ⟨(s.state.1, s.state.2 && decide (0 < N) && decide (2 ≤ m)), s.stk⟩

theorem verifierDimensions_executes (p : VerifierHeaderPorts K) (N m : ℕ)
    (s : CountdownStore (NumericStack K) F)
    (hN : s.stk (.inr (p .universe)) = List.replicate N true)
    (hm : s.stk (.inr (p .rows)) = List.replicate m true)
    (ht : s.stk (.inr (p .temp)) = []) (hr : s.stk (.inr (p .residue)) = []) :
    ∃ n ≤ 4 * m + 8,
      (verifierDimensionsRoutine p).Executes s (verifierDimensionsResult N m s) n := by
  let u := (mixedCountPeekOp (.inr (p .universe))).apply s
  let v := wordDuplicateEval (.inr (p .rows)) (.inr (p .temp)) u
  let w := countdownPop (.inr (p .temp)) v
  let z := (mixedCountPeekOp (.inr (p .temp))).apply w
  have h1 := Atom.executes (mixedCountPeekOp (.inr (p .universe))) s
  have h2 := wordDuplicate_executes (.inr (p .rows) : NumericStack K)
    (.inr (p .residue)) (.inr (p .temp)) (by simp) (by simp) (by simp) u hr
  have h3 := Atom.executes (countdownPopOp (.inr (p .temp))) v
  have h4 := Atom.executes (mixedCountPeekOp (.inr (p .temp))) w
  obtain ⟨a, ha, h5⟩ := clearMany_executes [.inr (p .temp)] z
  have hlen : (z.stk (.inr (p .temp))).length ≤ m := by
    simp only [z, w, v, u, mixedCountPeekOp, countdownPop, countdownPopOp, Op.apply,
      wordDuplicateEval, Function.update_same, hm, ht, List.append_nil]
    cases m <;> simp [List.replicate_succ]
  have hrfinal : clearManyEval [.inr (p .temp)] z = verifierDimensionsResult N m s := by
    apply countdownStore_ext
    · have hhead : (List.replicate N true).head?.isSome = decide (0 < N) := by cases N <;> simp [List.replicate_succ]
      simp [clearMany_state, z, w, v, u, mixedCountPeekOp, countdownPop, countdownPopOp,
        wordDuplicateEval, Op.apply, hN, hm, ht, hhead, replicate_tail_nonempty_iff_two,
        verifierDimensionsResult, Bool.and_assoc]
    · funext j
      by_cases hj : j = (.inr (p .temp) : NumericStack K)
      · subst j; simp [clearManyEval, clearStackEval, verifierDimensionsResult, ht]
      · simp [clearManyEval, clearStackEval, verifierDimensionsResult, z, w, v, u,
          mixedCountPeekOp, countdownPop, countdownPopOp, wordDuplicateEval, Op.apply, hj]
  rw [hrfinal] at h5
  have hmcopy : (u.stk (.inr (p .rows))).length = m := by simpa [u, mixedCountPeekOp, Op.apply] using congrArg List.length hm
  rw [hmcopy] at h2
  have hmass : cleanupMass [.inr (p .temp)] z ≤ m := by simpa [cleanupMass] using hlen
  simp only [List.length_cons, List.length_nil] at ha
  exact ⟨1 + (3 * m + 3 + (1 + (1 + a))), by omega,
    RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
      (RoutineComposition.seq_executes _ _ h3 (RoutineComposition.seq_executes _ _ h4 h5)))⟩

def alphabetAddThreeRoutine (types : K) : Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (tallyPushOp (.inr types)))
    (RoutineComposition.seq (Atom.routine (tallyPushOp (.inr types))) (Atom.routine (tallyPushOp (.inr types))))

def verifierAlphabetRoutine (p : VerifierHeaderPorts K) (types : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (numericCapSwap (p .universe) (p .temp))
    (RoutineComposition.seq (preservingUnaryProductRoutine (p .rows) (p .temp) types (p .counter))
      (RoutineComposition.seq (numericCapSwap (p .universe) (p .temp))
        (RoutineComposition.seq (wordDuplicateRoutine (.inr (p .universe)) (.inr (p .temp)) (.inr types))
          (alphabetAddThreeRoutine types))))

def verifierAlphabetResult (types : K) (N m : ℕ) (s : CountdownStore (NumericStack K) F) :
    CountdownStore (NumericStack K) F :=
  ⟨((s.state.1.1, false), true), Function.update s.stk (.inr types) (List.replicate (N + m * N + 3) true)⟩

def verifierAlphabetBound (C N m : ℕ) := 3 * N * m + 9 * N + 12 * m + 3 * C + 24

/-- A is constructed AFTER bounded header success by a real preserved
operand multiplication, restoring the original small cap. Neither N nor
m lives in finite control and neither is assumed unary-size for free. -/
theorem verifierAlphabet_executes (p : VerifierHeaderPorts K) (types : K)
    (htypes : ∀ j : VerifierHeaderPort, types ≠ p j) (C N m L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : NumericLoopInv C L s) (hflag : s.state.2 = true)
    (hN : s.stk (.inr (p .universe)) = List.replicate N true)
    (hm : s.stk (.inr (p .rows)) = List.replicate m true)
    (ht : s.stk (.inr (p .temp)) = []) (hc : s.stk (.inr (p .counter)) = [])
    (ha : s.stk (.inr types) = []) :
    ∃ n ≤ verifierAlphabetBound C N m,
      (verifierAlphabetRoutine p types).Executes s (verifierAlphabetResult types N m s) n := by
  let u := numericCapSwapEval (p .universe) (p .temp) s
  obtain ⟨h1, hui, huN, hut⟩ := numericCapSwap_executes (p .universe) (p .temp) (by simp)
    C N L s hs hN ht
  have hux (k : K) (hkN : k ≠ p .universe) (hkt : k ≠ p .temp) :
      u.stk (.inr k) = s.stk (.inr k) :=
    capExchange_outside (.inl .cap : NumericStack K) (.inr (p .universe)) (.inr (p .temp))
      (.inr k) (by simp) (by simpa using hkN) (by simpa using hkt) s
  have hum : u.stk (.inr (p .rows)) = List.replicate m true := (hux _ (by simp) (by simp)).trans hm
  have huc : u.stk (.inr (p .counter)) = [] := (hux _ (by simp) (by simp)).trans hc
  have hua : u.stk (.inr types) = [] := (hux _ (htypes .universe) (htypes .temp)).trans ha
  obtain ⟨a, haTime, h2⟩ := preservingUnaryProduct_store (p .rows) (p .temp) types (p .counter)
    (by simp) (htypes .rows) (htypes .temp) (htypes .counter) (by simp) (by simp)
    N m L u hui hflag hum hut hua huc
  let v := preservingProductStoreEval types N m u
  have hvInv : NumericLoopInv N L v := by simpa [v, preservingProductStoreEval, NumericLoopInv] using hui
  have hvN : v.stk (.inr (p .universe)) = List.replicate C true := by
    simpa [v, preservingProductStoreEval, (htypes .universe).symm] using huN
  have hvt : v.stk (.inr (p .temp)) = [] := by
    simpa [v, preservingProductStoreEval, (htypes .temp).symm] using hut
  obtain ⟨h3, hwi, hwN, hwt⟩ := numericCapSwap_executes (p .universe) (p .temp) (by simp)
    N C L v hvInv hvN hvt
  let w := numericCapSwapEval (p .universe) (p .temp) v
  have hwa : w.stk (.inr types) = List.replicate (N * m) true := by
    rw [capExchange_outside (.inl .cap : NumericStack K) (.inr (p .universe)) (.inr (p .temp))
      (.inr types) (by simp) (by simpa using htypes .universe) (by simpa using htypes .temp)]
    simp [v, preservingProductStoreEval]
  have h4 := wordDuplicate_executes (.inr (p .universe) : NumericStack K) (.inr (p .temp)) (.inr types)
    (by simp) (by simpa using (htypes .universe).symm) (by simpa using (htypes .temp).symm) w hwt
  rw [hwN, List.length_replicate] at h4
  let z := wordDuplicateEval (.inr (p .universe)) (.inr types) w
  let z1 := (tallyPushOp (.inr types)).apply z
  let z2 := (tallyPushOp (.inr types)).apply z1
  let z3 := (tallyPushOp (.inr types)).apply z2
  have h5 : (alphabetAddThreeRoutine types).Executes z z3 3 :=
    RoutineComposition.seq_executes _ _ (Atom.executes (tallyPushOp (.inr types)) z)
      (RoutineComposition.seq_executes _ _ (Atom.executes (tallyPushOp (.inr types)) z1)
        (Atom.executes (tallyPushOp (.inr types)) z2))
  have hwRestore : w.stk = Function.update s.stk (.inr types) (List.replicate (N * m) true) := by
    have he1 := capExchange_effect (.inl .cap : NumericStack K) (.inr (p .universe)) (.inr (p .temp))
      (by simp) (by simp) (by simp) s ht
    have he2 := capExchange_effect (.inl .cap : NumericStack K) (.inr (p .universe)) (.inr (p .temp))
      (by simp) (by simp) (by simp) v hvt
    funext j
    simp [w, he2, v, preservingProductStoreEval, u, he1, capExchangeResult,
      hN, hs.2.2.2.1, ht, htypes, List.reverse_replicate]
  have hz : z3 = verifierAlphabetResult types N m s := by
    apply countdownStore_ext
    · rfl
    · funext j
      by_cases hj : j = (.inr types : NumericStack K)
      · subst j
        simp [z3, z2, z1, z, tallyPushOp, Op.apply, wordDuplicateEval, hwN, hwa,
          List.replicate_append_replicate, verifierAlphabetResult, Nat.mul_comm,
          List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp [z3, z2, z1, z, tallyPushOp, Op.apply, wordDuplicateEval, hj,
          hwRestore, verifierAlphabetResult]
  rw [hz] at h5
  exact ⟨(2 * C + N + 3) + (a + ((2 * N + C + 3) + ((3 * N + 3) + 3))),
    by unfold verifierAlphabetBound; omega,
    RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
      (RoutineComposition.seq_executes _ _ h3 (RoutineComposition.seq_executes _ _ h4 h5)))⟩

theorem verifierHeaders_dimension_bounds (p : VerifierHeaderPorts K) (C D : ℕ)
    (s : CountdownStore (NumericStack K) F)
    (hN0 : s.stk (.inr (p .universe)) = []) (hm0 : s.stk (.inr (p .rows)) = []) :
    ((verifierHeadersEval p C D s).stk (.inr (p .universe))).length ≤ C ∧
      ((verifierHeadersEval p C D s).stk (.inr (p .rows))).length ≤ C := by
  let h := verifierHeaderScratch p
  let u := verifierHeadersAfterN p C s
  let v := verifierHeadersAfterM p C s
  have hum0 : u.stk (.inr (p .rows)) = [] :=
    (headerScalar_extra h (p .universe) (p .rows) (by simp) true C s).trans hm0
  have hN := headerScalar_dest_bound h (p .universe) true C s hN0
  have hm := headerScalar_dest_bound h (p .rows) true C u hum0
  have hvN := headerScalar_extra h (p .rows) (p .universe) (by simp) true C u
  have hwN := switchedHeaderScalar_extra h (p .budget) (p .large) (p .universe)
    (by simp) (by simp) (by simp [h, verifierHeaderScratch]) D v
  have hwm := switchedHeaderScalar_extra h (p .budget) (p .large) (p .rows)
    (by simp) (by simp) (by simp [h, verifierHeaderScratch]) D v
  constructor
  · change ((switchedHeaderScalarEval h (p .budget) (p .large) D v).stk _).length ≤ C
    rw [hwN, hvN]; exact hN
  · change ((switchedHeaderScalarEval h (p .budget) (p .large) D v).stk _).length ≤ C
    rw [hwm]; exact hm

def verifierHeaderAlphabetRoutine (p : VerifierHeaderPorts K) (types : K) :
    Routine (fun _ : NumericStack K => Bool) (CountdownState F) :=
  RoutineComposition.seq (verifierHeadersRoutine p)
    (RoutineComposition.seq (verifierDimensionsRoutine p)
      (RoutineControl.branch Prod.snd (verifierAlphabetRoutine p types) (Atom.routine cleanupNoop)))

def verifierHeaderDimensionsEval (p : VerifierHeaderPorts K) (C D : ℕ)
    (s : CountdownStore (NumericStack K) F) : CountdownStore (NumericStack K) F :=
  let u := verifierHeadersEval p C D s
  verifierDimensionsResult (u.stk (.inr (p .universe))).length (u.stk (.inr (p .rows))).length u

def verifierHeaderAlphabetEval (p : VerifierHeaderPorts K) (types : K) (C D : ℕ)
    (s : CountdownStore (NumericStack K) F) : CountdownStore (NumericStack K) F :=
  let u := verifierHeaderDimensionsEval p C D s
  if u.state.2 then verifierAlphabetResult types (u.stk (.inr (p .universe))).length
    (u.stk (.inr (p .rows))).length u else u

def verifierHeaderAlphabetBound (L C D : ℕ) : ℕ :=
  verifierHeadersBound L C D + 3 * C * C + 28 * C + 33

/-- Actual THREE headers, required dimensions and paid A production in a
single success-gated sequence. Caps are still physical entry operands:
their exact pair-derived creation is the next enclosing obligation. -/
theorem verifierHeaderAlphabet_executes (p : VerifierHeaderPorts K) (types : K)
    (htypes : ∀ j : VerifierHeaderPort, types ≠ p j) (C D L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : VerifierHeadersEntry p C D L s)
    (htypes0 : s.stk (.inr types) = []) :
    ∃ n ≤ verifierHeaderAlphabetBound L C D,
      (verifierHeaderAlphabetRoutine p types).Executes s (verifierHeaderAlphabetEval p types C D s) n := by
  let u := verifierHeadersEval p C D s
  let N := (u.stk (.inr (p .universe))).length
  let m := (u.stk (.inr (p .rows))).length
  let v := verifierDimensionsResult N m u
  obtain ⟨a, ha, h1, huInv, hlarge, hut⟩ := verifierHeaders_executes p C D L s hs
  have hNu : u.stk (.inr (p .universe)) = List.replicate N true :=
    verifierHeaders_unary p C D s (hs.2.2 .universe (by decide))
      (hs.2.2 .rows (by decide)) (hs.2.2 .budget (by decide)) .universe (by simp)
  have hmu : u.stk (.inr (p .rows)) = List.replicate m true :=
    verifierHeaders_unary p C D s (hs.2.2 .universe (by decide))
      (hs.2.2 .rows (by decide)) (hs.2.2 .budget (by decide)) .rows (by simp)
  have hur : u.stk (.inr (p .residue)) = [] :=
    (verifierHeaders_extra p C D s (p .residue) (by simp) (by simp) (by simp) (by simp) (by simp)).trans
      (hs.2.2 .residue (by decide))
  have huc : u.stk (.inr (p .counter)) = [] :=
    (verifierHeaders_extra p C D s (p .counter) (by simp) (by simp) (by simp) (by simp) (by simp)).trans
      (hs.2.2 .counter (by decide))
  have huTypes : u.stk (.inr types) = [] :=
    (verifierHeaders_extra p C D s types (htypes .universe) (htypes .rows)
      (htypes .budget) (htypes .large) (htypes .temp)).trans htypes0
  have hbds := verifierHeaders_dimension_bounds p C D s
    (hs.2.2 .universe (by decide)) (hs.2.2 .rows (by decide))
  have hNle : N ≤ C := hbds.1
  have hmle : m ≤ C := hbds.2
  obtain ⟨b, hb, h2⟩ := verifierDimensions_executes p N m u hNu hmu hut hur
  cases hg : v.state.2 with
  | false =>
      have h3 := RoutineControl.branch_false Prod.snd (verifierAlphabetRoutine p types)
        (Atom.routine cleanupNoop) hg (Atom.executes cleanupNoop v)
      refine ⟨a + (b + 2), by unfold verifierHeaderAlphabetBound; omega, ?_⟩
      simpa only [verifierHeaderAlphabetRoutine, verifierHeaderAlphabetEval, verifierHeaderDimensionsEval,
        hg, Bool.false_eq_true, ↓reduceIte, cleanupNoop, Op.apply] using
        RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3)
  | true =>
      obtain ⟨c, hc, h3⟩ := verifierAlphabet_executes p types htypes C N m L v huInv hg hNu hmu hut huc huTypes
      have h4 := RoutineControl.branch_true Prod.snd (verifierAlphabetRoutine p types)
        (Atom.routine cleanupNoop) hg h3
      have hprod := Nat.mul_le_mul hNle hmle
      refine ⟨a + (b + (c + 1)), ?_, ?_⟩
      · unfold verifierHeaderAlphabetBound verifierAlphabetBound at *
        nlinarith
      · simpa only [verifierHeaderAlphabetRoutine, verifierHeaderAlphabetEval, verifierHeaderDimensionsEval,
          hg, ↓reduceIte] using
          RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h4)

def readDimensionedVerifierHeaders (L cap : ℕ) (bits : List Bool) :
    Option ((ℕ × ℕ × ℕ) × List Bool) :=
  (readVerifierHeaders L cap bits).bind (fun q =>
    if 0 < q.1.1 ∧ 2 ≤ q.1.2.1 then some q else none)

theorem verifierHeaderAlphabet_observation (p : VerifierHeaderPorts K) (types : K)
    (htypes : ∀ j : VerifierHeaderPort, types ≠ p j) (L cap : ℕ)
    (s : CountdownStore (NumericStack K) F)
    (hN0 : s.stk (.inr (p .universe)) = []) (hm0 : s.stk (.inr (p .rows)) = [])
    (hB0 : s.stk (.inr (p .budget)) = []) :
    observeVerifierHeaders p (verifierHeaderAlphabetEval p types (L + 1) cap s) =
      if s.state.2 then readDimensionedVerifierHeaders L cap (s.stk (.inl .source)) else none := by
  let u := verifierHeadersEval p (L + 1) cap s
  have ho := verifierHeaders_observation p L cap s hN0 hm0 hB0
  have hlocal : observeVerifierHeaders p (verifierHeaderAlphabetEval p types (L + 1) cap s) =
      (observeVerifierHeaders p u).bind (fun q =>
        if 0 < q.1.1 ∧ 2 ≤ q.1.2.1 then some q else none) := by
    have hx (j : VerifierHeaderPort) : p j ≠ types := (htypes j).symm
    by_cases hN : 0 < (u.stk (.inr (p .universe))).length
    all_goals by_cases hm : 2 ≤ (u.stk (.inr (p .rows))).length
    all_goals
      cases hf : u.state.2 <;>
        simp [verifierHeaderAlphabetEval, verifierHeaderDimensionsEval, verifierDimensionsResult,
          verifierAlphabetResult, observeVerifierHeaders, hf, htypes, hx, hN, hm, u, Bool.and_assoc]
  rw [hlocal, ho]
  cases hf : s.state.2 <;> simp [hf, readDimensionedVerifierHeaders]

/- The THREE original headers, exact strict/saturated observation,
required dimensions and paid A production now have a composed source
proposal. This file must continue through actual pair-derived cap
preparation and the initial-store boundary before supplying the whole
controller. One shared guard inventory, globally absorbing rejection,
all-path final cleanup/halt and a single polynomial remain unjoined.
All source is unelaborated. VerifierMachineWitness and
EncodedSourceHardness remain independent. -/

/-- The observation is a real store observation, not a freely supplied
header witness. This destructor is used at the grammar phase boundary. -/
theorem observeVerifierHeaders_some (p : VerifierHeaderPorts K)
    (s : CountdownStore (NumericStack K) F) (N m B : ℕ) (rest : List Bool) :
    observeVerifierHeaders p s = some ((N, m, B), rest) ↔
      s.state.2 = true ∧ (s.stk (.inr (p .universe))).length = N ∧
      (s.stk (.inr (p .rows))).length = m ∧
      (s.stk (.inr (p .budget))).length = B ∧ s.stk (.inl .source) = rest := by
  cases hf : s.state.2 <;> simp [observeVerifierHeaders, hf, Prod.mk.injEq, and_assoc]

theorem verifierHeaderAlphabet_extra (p : VerifierHeaderPorts K) (types k : K)
    (hk : ∀ j : VerifierHeaderPort, k ≠ p j) (hkt : k ≠ types) (C D : ℕ)
    (s : CountdownStore (NumericStack K) F) :
    (verifierHeaderAlphabetEval p types C D s).stk (.inr k) = s.stk (.inr k) := by
  unfold verifierHeaderAlphabetEval
  split
  · simpa [verifierAlphabetResult, hkt, verifierHeaderDimensionsEval,
      verifierDimensionsResult] using
      verifierHeaders_extra p C D s k (hk .universe) (hk .rows) (hk .budget) (hk .large) (hk .temp)
  · simpa [verifierHeaderDimensionsEval, verifierDimensionsResult] using
      verifierHeaders_extra p C D s k (hk .universe) (hk .rows) (hk .budget) (hk .large) (hk .temp)

theorem verifierHeaderAlphabet_numericInv (p : VerifierHeaderPorts K) (types : K)
    (C D L : ℕ) (s : CountdownStore (NumericStack K) F)
    (hs : VerifierHeadersEntry p C D L s) :
    NumericLoopInv C L (verifierHeaderAlphabetEval p types C D s) := by
  obtain ⟨a, ha, he, hi, hl, ht⟩ := verifierHeaders_executes p C D L s hs
  unfold verifierHeaderAlphabetEval
  split <;> simpa [verifierHeaderDimensionsEval, verifierDimensionsResult,
    verifierAlphabetResult, NumericLoopInv] using hi

theorem verifierHeaderAlphabet_unary (p : VerifierHeaderPorts K) (types : K)
    (htypes : ∀ j : VerifierHeaderPort, types ≠ p j) (C D : ℕ)
    (s : CountdownStore (NumericStack K) F)
    (hN : s.stk (.inr (p .universe)) = []) (hm : s.stk (.inr (p .rows)) = [])
    (hB : s.stk (.inr (p .budget)) = []) (j : VerifierHeaderPort)
    (hj : j = .universe ∨ j = .rows ∨ j = .budget) :
    (verifierHeaderAlphabetEval p types C D s).stk (.inr (p j)) =
      List.replicate ((verifierHeaderAlphabetEval p types C D s).stk (.inr (p j))).length true := by
  have hu := verifierHeaders_unary p C D s hN hm hB j hj
  unfold verifierHeaderAlphabetEval
  split <;> simpa [verifierHeaderDimensionsEval, verifierDimensionsResult,
    verifierAlphabetResult, (htypes j).symm] using hu

/-- Success really produced A on a physical tape. No valid-target
assumption or semantic A<=input-length estimate is used here. -/
theorem verifierHeaderAlphabet_types (p : VerifierHeaderPorts K) (types : K)
    (htypes : ∀ j : VerifierHeaderPort, types ≠ p j) (C D : ℕ)
    (s : CountdownStore (NumericStack K) F)
    (hf : (verifierHeaderAlphabetEval p types C D s).state.2 = true) :
    (verifierHeaderAlphabetEval p types C D s).stk (.inr types) =
      List.replicate
        (((verifierHeaderAlphabetEval p types C D s).stk (.inr (p .universe))).length +
          ((verifierHeaderAlphabetEval p types C D s).stk (.inr (p .rows))).length *
          ((verifierHeaderAlphabetEval p types C D s).stk (.inr (p .universe))).length + 3) true := by
  let u := verifierHeaderDimensionsEval p C D s
  by_cases hu : u.state.2 = true
  · have hu' : (verifierHeaderDimensionsEval p C D s).state.2 = true := hu
    simp [verifierHeaderAlphabetEval, hu', verifierAlphabetResult,
      (htypes .universe).symm, (htypes .rows).symm]
  · have huf : u.state.2 = false := Bool.eq_false_iff.mpr hu
    have hu' : (verifierHeaderDimensionsEval p C D s).state.2 = false := huf
    simp [verifierHeaderAlphabetEval, hu'] at hf

theorem readDimensionedVerifierHeaders_some (L cap : ℕ) (bits rest : List Bool) (N m B : ℕ) :
    readDimensionedVerifierHeaders L cap bits = some ((N, m, B), rest) ↔
      readVerifierHeaders L cap bits = some ((N, m, B), rest) ∧ 0 < N ∧ 2 ≤ m := by
  unfold readDimensionedVerifierHeaders
  cases h : readVerifierHeaders L cap bits with
  | none => simp
  | some q =>
      change (if 0 < q.1.1 ∧ 2 ≤ q.1.2.1 then some q else none) =
        some ((N, m, B), rest) ↔ some q = some ((N, m, B), rest) ∧ 0 < N ∧ 2 ≤ m
      by_cases hd : 0 < q.1.1 ∧ 2 ≤ q.1.2.1
      · rw [if_pos hd]
        constructor
        · intro he
          have hq := Option.some.inj he
          subst q
          exact ⟨rfl, hd⟩
        · exact fun he => he.1
      · rw [if_neg hd]
        constructor
        · intro he; cases he
        · rintro ⟨he, hN, hm⟩
          have hq := Option.some.inj he
          subst q
          exact False.elim (hd ⟨hN, hm⟩)

end PolytomyReductionModel.WholeVerifierController
