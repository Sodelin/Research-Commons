/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Fixed finite canonical port layout and a fully instantiated actual
descending type countdown. Membership/query/leaf bodies are the actual
previous routines, not supplied oracles. Ordered output/cost semantics
and whole block/constructor initialization remain separate obligations.
-/
import PolytomyCanonicalCallerInvariant

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

inductive CanonicalFilterPort where
  | typeIndex | rowIndex | threshold | blockCode | remaining | count | cost | temp | output
  deriving DecidableEq, Fintype

def canonicalFilterLayout : CanonicalLeafLayout CanonicalFilterPort where
  port
    | .remaining => .remaining
    | .count => .count
    | .temp => .temp
    | .cost => .cost
    | .block => .blockCode
    | .value => .typeIndex
    | .output => .output
  injective := by intro a b h; cases a <;> cases b <;> simp_all

abbrev CanonicalFilterStack := SelectedQueryCallerStack CanonicalFilterPort
abbrev CanonicalFilterStore := CountdownStore CanonicalFilterStack SelectedRowFrame

def realTypeBodyRoutine : Routine (fun _ : CanonicalFilterStack => Bool) (CountdownState SelectedRowFrame) :=
  realCanonicalTypeRoutine canonicalFilterLayout .rowIndex .threshold

def realTypeBodyEval (T : ℕ) (s : CanonicalFilterStore) :=
  realCanonicalTypeResult canonicalFilterLayout .rowIndex (s.stk (.inr .typeIndex)).length T
    (selectedCallerBase s) (selectedCallerExtra s)

structure RealTypeLoopInv (L S I T B : ℕ) (s : CanonicalFilterStore) : Prop where
  scan : UnaryScanReady 0 L (selectedCallerBase s)
  query_empty : s.stk (.inl (.inr .queries)) = []
  type_unary : IsUnaryWord (s.stk (.inr .typeIndex))
  type_bound : (s.stk (.inr .typeIndex)).length ≤ S
  row_bound : (s.stk (.inr .rowIndex)).length ≤ I
  threshold_word : s.stk (.inr .threshold) = List.replicate T true
  temp_empty : s.stk (.inr .temp) = []
  remaining_bound : (s.stk (.inr .remaining)).length ≤ S
  block_bound : (s.stk (.inr .blockCode)).length ≤ B

theorem RealTypeLoopInv_of_stacks (L S I T B : ℕ) (s t : CanonicalFilterStore)
    (hs : RealTypeLoopInv L S I T B s) (h : ∀ k, t.stk k = s.stk k) : RealTypeLoopInv L S I T B t := by
  refine ⟨UnaryScanReady_of_stacks 0 L _ _ hs.scan (fun k => h (.inl k)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h]; exact hs.query_empty
  · rw [h]; exact hs.type_unary
  · rw [h]; exact hs.type_bound
  · rw [h]; exact hs.row_bound
  · rw [h]; exact hs.threshold_word
  · rw [h]; exact hs.temp_empty
  · rw [h]; exact hs.remaining_bound
  · rw [h]; exact hs.block_bound

theorem unaryWord_tail (xs : List Bool) (h : IsUnaryWord xs) : IsUnaryWord xs.tail := by
  unfold IsUnaryWord at *
  rw [h, List.tail_replicate]
  simp

theorem realTypeLoop_pop_invariant (L S I T B : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeLoopInv L S I T B s) :
    RealTypeLoopInv L S I T B (countdownPop (.inr .typeIndex) s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply UnaryScanReady_of_stacks 0 L _ _ hs.scan
    intro k
    simp [selectedCallerBase, countdownPop, countdownPopOp, Op.apply]
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.query_empty
  · rw [countdownPop_counter]
    exact unaryWord_tail _ hs.type_unary
  · rw [countdownPop_counter, List.length_tail]
    exact (Nat.sub_le _ _).trans hs.type_bound
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.row_bound
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.threshold_word
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.temp_empty
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.remaining_bound
  · simpa [countdownPop, countdownPopOp, Op.apply] using hs.block_bound

theorem realTypeBody_invariant (L S I T B : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeLoopInv L S I T B s) : RealTypeLoopInv L S I T B (realTypeBodyEval T s) := by
  let C := (s.stk (.inr .typeIndex)).length
  let base := selectedCallerBase s
  let extra := selectedCallerExtra s
  have hC : extra .typeIndex = List.replicate C true := hs.type_unary
  obtain ⟨hready, hquery, horig⟩ := realCanonicalType_ready canonicalFilterLayout .rowIndex C L T base hs.scan extra hC
  have hextra : ∀ k : CanonicalFilterPort, k ≠ .remaining → k ≠ .count → k ≠ .cost → k ≠ .output →
      (realTypeBodyEval T s).stk (.inr k) = s.stk (.inr k) := by
    intro k hkr hkc hkcost hko
    exact realCanonicalType_extra canonicalFilterLayout .rowIndex C T base extra k hkr hkc hkcost hko
  refine ⟨hready, hquery, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hextra .typeIndex (by decide) (by decide) (by decide) (by decide)]; exact hs.type_unary
  · rw [hextra .typeIndex (by decide) (by decide) (by decide) (by decide)]; exact hs.type_bound
  · rw [hextra .rowIndex (by decide) (by decide) (by decide) (by decide)]; exact hs.row_bound
  · rw [hextra .threshold (by decide) (by decide) (by decide) (by decide)]; exact hs.threshold_word
  · rw [hextra .temp (by decide) (by decide) (by decide) (by decide)]; exact hs.temp_empty
  · exact (realCanonicalType_remaining_le canonicalFilterLayout .rowIndex C T base extra).trans hs.remaining_bound
  · rw [hextra .blockCode (by decide) (by decide) (by decide) (by decide)]; exact hs.block_bound

def realTypeBodyBound (L S I T B : ℕ) :=
  selectedQueryBound S L I + 13 * S + 3 * I + 4 * T + 3 * B + 34

theorem realTypeBody_executes (L S I T B : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeLoopInv L S I T B s) :
    ∃ n ≤ realTypeBodyBound L S I T B, realTypeBodyRoutine.Executes s (realTypeBodyEval T s) n := by
  let C := (s.stk (.inr .typeIndex)).length
  obtain ⟨n, hn, he, hflag⟩ := realCanonicalType_executes canonicalFilterLayout .rowIndex .threshold
    (by decide) (by decide) C L T (selectedCallerBase s) hs.scan hs.query_empty (selectedCallerExtra s)
    hs.temp_empty hs.type_unary hs.threshold_word
  rw [selectedCaller_split] at he
  have hprod : 7 * C * L^2 ≤ 7 * S * L^2 :=
    Nat.mul_le_mul_right (L^2) (Nat.mul_le_mul_left 7 hs.type_bound)
  have hq : selectedQueryBound C L (s.stk (.inr .rowIndex)).length ≤ selectedQueryBound S L I := by
    unfold selectedQueryBound
    have hc := hs.type_bound
    have hi := hs.row_bound
    change C ≤ S at hc
    have hmul : 7 * C * L ^ 2 ≤ 7 * S * L ^ 2 :=
      Nat.mul_le_mul_right (L ^ 2) (Nat.mul_le_mul_left 7 hc)
    omega
  refine ⟨n, ?_, he⟩
  change n ≤ realBlockMembershipBound C L (s.stk (.inr .rowIndex)).length T +
    3 * (s.stk (.inr .remaining)).length + 3 * C + 3 * (s.stk (.inr .blockCode)).length + 18 at hn
  have hc := hs.type_bound
  have hi := hs.row_bound
  have hr := hs.remaining_bound
  have hb := hs.block_bound
  change C ≤ S at hc
  unfold realBlockMembershipBound at hn
  unfold realTypeBodyBound
  omega

theorem realTypeBody_counter (T : ℕ) (s : CanonicalFilterStore) :
    (realTypeBodyEval T s).stk (.inr .typeIndex) = s.stk (.inr .typeIndex) :=
  realCanonicalType_counter canonicalFilterLayout .rowIndex _ T _ _

theorem realTypeBody_success (T : ℕ) (s : CanonicalFilterStore) : (realTypeBodyEval T s).state.2 = true :=
  canonicalLeafGate_success _ _

def realTypeLoopContract (L S I T B : ℕ) :
    CountdownContract (.inr CanonicalFilterPort.typeIndex) realTypeBodyRoutine (realTypeBodyEval T)
      (RealTypeLoopInv L S I T B) (realTypeBodyBound L S I T B) where
  peek_closed s hs := RealTypeLoopInv_of_stacks L S I T B s _ hs (fun _ => rfl)
  pop_closed s hs hg := realTypeLoop_pop_invariant L S I T B s hs
  body_closed s hs := realTypeBody_invariant L S I T B s hs
  reset_closed s hs := RealTypeLoopInv_of_stacks L S I T B s _ hs (fun _ => rfl)
  counter_preserved s hs := realTypeBody_counter T s
  body_executes s hs := realTypeBody_executes L S I T B s hs

def realTypeLoopRoutine : Routine (fun _ : CanonicalFilterStack => Bool) (CountdownState SelectedRowFrame) :=
  countdownRoutine (.inr .typeIndex) realTypeBodyRoutine

def realTypeLoopEval (T : ℕ) (s : CanonicalFilterStore) :=
  countdownEval (.inr .typeIndex) (realTypeBodyEval T) s

theorem realTypeLoop_success (T : ℕ) (s : CanonicalFilterStore) (hs : s.state.2 = true) :
    (realTypeLoopEval T s).state.2 = true := by
  have hloop : ∀ n (t : CanonicalFilterStore), t.state.2 = true →
      (countdownLoopEval (.inr .typeIndex) (realTypeBodyEval T) n t).state.2 = true := by
    intro n
    induction n with
    | zero => intro t ht; exact ht
    | succ n ih =>
        intro t ht
        cases hg : countdownGuard t.state with
        | false => simpa [countdownLoopEval, hg] using ht
        | true =>
            rw [countdownLoopEval, hg]
            simp only [↓reduceIte]
            exact ih _ (realTypeBody_success T (countdownPop (.inr .typeIndex) t))
  exact hloop _ (countdownPeek (.inr .typeIndex) s) hs

theorem realTypeLoop_executes (L S I T B : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeLoopInv L S I T B s) (hok : s.state.2 = true) :
    ∃ n ≤ S * (realTypeBodyBound L S I T B + 3) + 3,
      realTypeLoopRoutine.Executes s (realTypeLoopEval T s) n ∧
      RealTypeLoopInv L S I T B (realTypeLoopEval T s) ∧
      (realTypeLoopEval T s).state.2 = true ∧
      (realTypeLoopEval T s).state.1.2 = false ∧
      (realTypeLoopEval T s).stk (.inr .typeIndex) = [] := by
  obtain ⟨n, hn, he, hi, hg, hz⟩ := countdownRoutine_executes (.inr .typeIndex)
    realTypeBodyRoutine (realTypeBodyEval T) (RealTypeLoopInv L S I T B) (realTypeBodyBound L S I T B)
    (realTypeLoopContract L S I T B) s hs
  have hflag := realTypeLoop_success T s hok
  have hmul := Nat.mul_le_mul_right (realTypeBodyBound L S I T B + 3) hs.type_bound
  exact ⟨n, by omega, he, hi, hflag, hg, hz hflag⟩

/- Every actual body and observation-side invariant premise used for
this OPERATIONAL loop has now been instantiated. Its physical type tape
is popped before each body, so an initial true^S visits S-1,...,0. An
unbounded S/L/I/T/B is a proof bound, not a field of finite control. The
original record's validity, exact row/block parameters and ordered output
filter/comb-cost semantics must still be joined for the final canonical
block theorem. No complete constructor/verifier/hardness or kernel closure
is inferred merely from this loop's actual transition-bound proposal.
-/

end PolytomyReductionModel
