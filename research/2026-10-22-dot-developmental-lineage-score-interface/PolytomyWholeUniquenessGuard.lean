/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Continuation of the ONE restricted marked-star verifier. The target is
global CELL uniqueness in both the supplied forest and the certificate.
Each selected leaf searches only strictly later legal positions; it is
never compared against its own occurrence. Both cell coordinates matter.

This in-progress module must be joined to the exact Nodup predicate and
the final verifier. Its partial source is not whole-claim completion.
-/
import PolytomyWholeCladeComposition

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

/-- The saved inner search word/mask are freshly populated by actual
restoring copies and one physical pop each. Only those copies are popped;
the universal cursor is unchanged until its ordinary subsequent step. -/
def uniqueTailsPrepared (p : InclusionPorts K) (s : CountdownStore K F) : CountdownStore K F :=
  countdownPop (p (.inner .originalMask))
    (wordDuplicateEval (p (.outer .mask)) (p (.inner .originalMask))
      (countdownPop (p (.inner .originalWord))
        (wordDuplicateEval (p (.outer .word)) (p (.inner .originalWord)) s)))

def uniqueTailsRoutine (p : InclusionPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq
    (wordDuplicateRoutine (p (.outer .word)) (p (.outer .temp)) (p (.inner .originalWord)))
    (RoutineComposition.seq (Atom.routine (countdownPopOp (p (.inner .originalWord))))
      (RoutineComposition.seq
        (wordDuplicateRoutine (p (.outer .mask)) (p (.outer .temp)) (p (.inner .originalMask)))
        (Atom.routine (countdownPopOp (p (.inner .originalMask))))))

def uniqueTailsOwned (p : InclusionPorts K) : List K :=
  [p (.inner .originalWord), p (.inner .originalMask)]

theorem uniqueTailsPrepared_state (p : InclusionPorts K) (s : CountdownStore K F) :
    (uniqueTailsPrepared p s).state = s.state := rfl

theorem uniqueTailsPrepared_stacks (p : InclusionPorts K) (s : CountdownStore K F)
    (hw : s.stk (p (.inner .originalWord)) = []) (hm : s.stk (p (.inner .originalMask)) = []) :
    (uniqueTailsPrepared p s).stk =
      Function.update (Function.update s.stk (p (.inner .originalWord))
        (s.stk (p (.outer .word))).tail) (p (.inner .originalMask)) (s.stk (p (.outer .mask))).tail := by
  simp [uniqueTailsPrepared, countdownPop, countdownPopOp, wordDuplicateEval, Op.apply, hw, hm]

theorem uniqueTails_executes (p : InclusionPorts K) (s : CountdownStore K F)
    (ht : s.stk (p (.outer .temp)) = []) :
    (uniqueTailsRoutine p).Executes s (uniqueTailsPrepared p s)
      (3 * (s.stk (p (.outer .word))).length + 3 * (s.stk (p (.outer .mask))).length + 8) := by
  let u := wordDuplicateEval (p (.outer .word)) (p (.inner .originalWord)) s
  let v := countdownPop (p (.inner .originalWord)) u
  let w := wordDuplicateEval (p (.outer .mask)) (p (.inner .originalMask)) v
  have h1 := wordDuplicate_executes (p (.outer .word)) (p (.outer .temp)) (p (.inner .originalWord))
    (by simp) (by simp) (by simp) s ht
  have h2 := Atom.executes (countdownPopOp (p (.inner .originalWord))) u
  have ht' : v.stk (p (.outer .temp)) = [] := by
    simpa [v, u, countdownPop, countdownPopOp, wordDuplicateEval, Op.apply] using ht
  have hm' : v.stk (p (.outer .mask)) = s.stk (p (.outer .mask)) := by
    simp [v, u, countdownPop, countdownPopOp, wordDuplicateEval, Op.apply]
  have h3 := wordDuplicate_executes (p (.outer .mask)) (p (.outer .temp)) (p (.inner .originalMask))
    (by simp) (by simp) (by simp) v ht'
  have h4 := Atom.executes (countdownPopOp (p (.inner .originalMask))) w
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
    (RoutineComposition.seq_executes _ _ h3 h4))
  simpa only [hm', uniqueTailsRoutine, uniqueTailsPrepared, u, v, w,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he

/-- Only a leaf reverses the membership answer. An internal node's skip
answer remains true. This is a physical first-bit peek, not a semantic
tree constructor test. The selected-query cache is restored to true. -/
def uniqueLeafPeekOp (p : InclusionPorts K) : Op K Bool (CountdownState F) :=
  .peek (p (.outer .word)) (fun st b => ((st.1.1, b.getD false), st.2))

def uniqueLeafAnswerOp : Op K Bool (CountdownState F) :=
  .load (fun st => ((st.1.1, true), if st.1.2 then !st.2 else st.2))

def noLaterCellCheck (m A : ℕ) (word mask : List Bool) : Bool :=
  let b := inclusionCheck m A word.tail mask.tail word
  if word.head?.getD false then !b else b

/-- W and originalMask are specification parameters, never unbounded
machine-control values. The physical current mask is related to this
expression by the cursor invariant, so no unpaid drop is performed. -/
def uniqueCellCheck (m A W : ℕ) (originalMask word : List Bool) : Bool :=
  noLaterCellCheck m A word (originalMask.drop (W - word.length))

def uniqueQueryEval (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  clearManyEval (uniqueTailsOwned p)
    (uniqueLeafAnswerOp.apply ((uniqueLeafPeekOp p).apply
      (inclusionQueryEval p m A (uniqueTailsPrepared p s))))

def uniqueQueryRoutine (p : InclusionPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (uniqueTailsRoutine p)
    (RoutineComposition.seq (inclusionQueryRoutine p)
      (RoutineComposition.seq (Atom.routine (uniqueLeafPeekOp p))
        (RoutineComposition.seq (Atom.routine uniqueLeafAnswerOp) (clearManyRoutine (uniqueTailsOwned p)))))

def UniqueStackInv (p : InclusionPorts K) (m A W L : ℕ) (originalMask : List Bool)
    (stk : K → List Bool) : Prop :=
  InclusionStackInv p m A L [] [] stk ∧
  (stk (p (.outer .word))).length ≤ W ∧
  (stk (p (.outer .mask))).length ≤ (stk (p (.outer .word))).length ∧
  stk (p (.outer .mask)) = originalMask.drop (W - (stk (p (.outer .word))).length)

theorem uniqueTails_prepared_inv (p : InclusionPorts K) (m A W L : ℕ) (originalMask : List Bool)
    (s : CountdownStore K F) (hs : UniqueStackInv p m A W L originalMask s.stk) :
    InclusionStackInv p m A L (s.stk (p (.outer .word))).tail (s.stk (p (.outer .mask))).tail
      (uniqueTailsPrepared p s).stk := by
  rcases hs.1 with ⟨hq, hw, hm, _, _, hwork⟩
  have hstk := uniqueTailsPrepared_stacks p s hw hm
  have hx (j : K) (hjw : j ≠ p (.inner .originalWord)) (hjm : j ≠ p (.inner .originalMask)) :
      (uniqueTailsPrepared p s).stk j = s.stk j := by rw [hstk]; simp [hjw, hjm]
  have ho (j : RangeCursorPort) : (uniqueTailsPrepared p s).stk (p (.outer j)) = s.stk (p (.outer j)) :=
    hx _ (by simp) (by simp)
  have htail : (s.stk (p (.outer .word))).tail.length ≤ (s.stk (p (.outer .word))).length := by
    cases s.stk (p (.outer .word)) <;> simp
  have hfit : (s.stk (p (.outer .mask))).tail.length ≤ (s.stk (p (.outer .word))).tail.length := by
    have hf := hs.2.2.1
    cases s.stk (p (.outer .mask)) <;> cases s.stk (p (.outer .word)) <;> simp_all
  refine ⟨?_, ?_, ?_, htail.trans hq.1, hfit, ?_⟩
  · simpa only [ho] using hq
  · rw [hstk]; simp
  · rw [hstk]; simp
  · intro j hj
    have hjw : j ≠ p (.inner .originalWord) := by
      intro he; rw [he] at hj
      simp [rangeAllWork, matchRangePorts, inclusionInnerPorts, inclusionMatchPortMap] at hj
    have hjm : j ≠ p (.inner .originalMask) := by
      intro he; rw [he] at hj
      simp [rangeAllWork, matchRangePorts, inclusionInnerPorts, inclusionMatchPortMap] at hj
    exact (hx j hjw hjm).trans (hwork j hj)

theorem uniqueQuery_result (p : InclusionPorts K) (m A W L : ℕ) (originalMask : List Bool)
    (s : CountdownStore K F) (hs : UniqueStackInv p m A W L originalMask s.stk)
    (hselected : s.state.1.2 = true) :
    uniqueQueryEval p m A s = cellCompareFlagStore
      (uniqueCellCheck m A W originalMask (s.stk (p (.outer .word)))) s := by
  let u := uniqueTailsPrepared p s
  have hu := uniqueTails_prepared_inv p m A W L originalMask s hs
  have hinc := inclusionQuery_result p m A L (s.stk (p (.outer .word))).tail
    (s.stk (p (.outer .mask))).tail u hu hselected
  have hstk := uniqueTailsPrepared_stacks p s hs.1.2.1 hs.1.2.2.1
  have hword : u.stk (p (.outer .word)) = s.stk (p (.outer .word)) := by rw [hstk]; simp
  apply countdownStore_ext
  · change (clearManyEval (uniqueTailsOwned p)
      (uniqueLeafAnswerOp.apply ((uniqueLeafPeekOp p).apply (inclusionQueryEval p m A u)))).state = _
    rw [hinc, clearMany_state]
    simp only [uniqueLeafAnswerOp, uniqueLeafPeekOp, Op.apply, cellCompareFlagStore,
      hword, uniqueCellCheck, noLaterCellCheck, u, uniqueTailsPrepared_state, ← hs.2.2.2]
    exact Prod.ext (Prod.ext rfl hselected.symm) rfl
  · change (clearManyEval (uniqueTailsOwned p)
      (uniqueLeafAnswerOp.apply ((uniqueLeafPeekOp p).apply (inclusionQueryEval p m A u)))).stk = s.stk
    rw [hinc]
    funext j
    by_cases hw : j = p (.inner .originalWord)
    · subst j
      simp [clearManyEval, clearStackEval, uniqueTailsOwned, uniqueLeafAnswerOp,
        uniqueLeafPeekOp, Op.apply, cellCompareFlagStore, hs.1.2.1]
    by_cases hm : j = p (.inner .originalMask)
    · subst j
      simp [clearManyEval, clearStackEval, uniqueTailsOwned, uniqueLeafAnswerOp,
        uniqueLeafPeekOp, Op.apply, cellCompareFlagStore, hs.1.2.2.1]
    · simp only [uniqueLeafAnswerOp, uniqueLeafPeekOp, Op.apply, cellCompareFlagStore,
        clearManyEval, uniqueTailsOwned, clearStackEval]
      simp [hstk, hw, hm]

def uniqueQueryBound (m A L : ℕ) : ℕ := inclusionQueryBound m A L + 8 * L + 13

theorem uniqueQuery_executes (p : InclusionPorts K) (m A W L : ℕ) (originalMask : List Bool)
    (s : CountdownStore K F) (hs : UniqueStackInv p m A W L originalMask s.stk)
    (hselected : s.state.1.2 = true) :
    ∃ n ≤ uniqueQueryBound m A L,
      (uniqueQueryRoutine p).Executes s
        (cellCompareFlagStore (uniqueCellCheck m A W originalMask (s.stk (p (.outer .word)))) s) n := by
  let u := uniqueTailsPrepared p s
  let v := inclusionQueryEval p m A u
  let w := uniqueLeafAnswerOp.apply ((uniqueLeafPeekOp p).apply v)
  have hu := uniqueTails_prepared_inv p m A W L originalMask s hs
  have h1 := uniqueTails_executes p s hs.1.1.2.2.2.2.2.2.1
  obtain ⟨a, ha, h2⟩ := inclusionQuery_executes p m A L (s.stk (p (.outer .word))).tail
    (s.stk (p (.outer .mask))).tail u hu hselected
  have hresult := inclusionQuery_result p m A L (s.stk (p (.outer .word))).tail
    (s.stk (p (.outer .mask))).tail u hu hselected
  rw [← hresult] at h2
  have h3 := Atom.executes (uniqueLeafPeekOp p) v
  have h4 := Atom.executes (uniqueLeafAnswerOp (K := K) (F := F)) ((uniqueLeafPeekOp p).apply v)
  obtain ⟨b, hb, h5⟩ := clearMany_executes (uniqueTailsOwned p) w
  have hstk := uniqueTailsPrepared_stacks p s hs.1.2.1 hs.1.2.2.1
  have hmass : cleanupMass (uniqueTailsOwned p) w ≤ 2 * L := by
    have hL := hs.1.1.1
    have hfit := hs.2.2.1
    have hw : (s.stk (p (.outer .word))).tail.length ≤ (s.stk (p (.outer .word))).length := by
      cases s.stk (p (.outer .word)) <;> simp
    have hm : (s.stk (p (.outer .mask))).tail.length ≤ (s.stk (p (.outer .mask))).length := by
      cases s.stk (p (.outer .mask)) <;> simp
    simp only [cleanupMass, uniqueTailsOwned, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, w, v, hresult, uniqueLeafAnswerOp, uniqueLeafPeekOp, Op.apply, cellCompareFlagStore]
    rw [hstk]
    simp
    omega
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
    (RoutineComposition.seq_executes _ _ h3 (RoutineComposition.seq_executes _ _ h4 h5)))
  change (uniqueQueryRoutine p).Executes s (uniqueQueryEval p m A s) _ at he
  rw [uniqueQuery_result p m A W L originalMask s hs hselected] at he
  refine ⟨3 * (s.stk (p (.outer .word))).length + 3 * (s.stk (p (.outer .mask))).length + 8 +
    (a + (1 + (1 + b))), ?_, he⟩
  have hL := hs.1.1.1
  have hfit := hs.2.2.1
  simp only [uniqueTailsOwned, List.length_cons, List.length_nil] at hb
  unfold uniqueQueryBound
  omega

theorem drop_tail_succ {X : Type} (xs : List X) (n : ℕ) :
    (xs.drop n).tail = xs.drop (n + 1) := by
  induction n generalizing xs with
  | zero => cases xs <;> rfl
  | succ n ih => cases xs with
      | nil => rfl
      | cons x xs => exact ih xs

theorem maskTail_eq_shift (W : ℕ) (originalMask word mask : List Bool)
    (hW : word.length ≤ W) (hfit : mask.length ≤ word.length)
    (hm : mask = originalMask.drop (W - word.length)) :
    mask.tail = originalMask.drop (W - word.tail.length) := by
  cases word with
  | nil =>
      have hnil : mask = [] := List.eq_nil_of_length_eq_zero (by simpa using hfit)
      simpa only [hnil, List.tail_nil, List.length_nil, Nat.sub_zero] using hm
  | cons b bits =>
      rw [hm, drop_tail_succ]
      congr 1
      simp only [List.length_cons, List.tail_cons] at hW ⊢
      omega

def uniqueMaskedContract (p : InclusionPorts K) (m A W L : ℕ) (originalMask : List Bool) :
    MaskedQueryContract (inclusionOuterPorts p) (uniqueQueryRoutine p)
      (uniqueCellCheck m A W originalMask) (UniqueStackInv p m A W L originalMask)
      (uniqueQueryBound m A L) where
  positive := by unfold uniqueQueryBound; omega
  query_executes s hs hselected := uniqueQuery_executes p m A W L originalMask s hs hselected
  cursor_closed stk hs := by
    have hbase := (inclusionMaskedContract p m A L [] []).cursor_closed stk hs.1
    have hw : (stk (p (.outer .word))).tail.length ≤ (stk (p (.outer .word))).length := by
      cases stk (p (.outer .word)) <;> simp
    have hfit : (stk (p (.outer .mask))).tail.length ≤ (stk (p (.outer .word))).tail.length := by
      have hf := hs.2.2.1
      cases stk (p (.outer .mask)) <;> cases stk (p (.outer .word)) <;> simp_all
    have hshift := maskTail_eq_shift W originalMask (stk (p (.outer .word)))
      (stk (p (.outer .mask))) hs.2.1 hs.2.2.1 hs.2.2.2
    refine ⟨hbase, ?_, ?_, ?_⟩
    · simpa [inclusionOuterPorts] using hw.trans hs.2.1
    · simpa [inclusionOuterPorts] using hfit
    · simpa [inclusionOuterPorts] using hshift
  counter_closed stk hs := by
    have hbase := (inclusionMaskedContract p m A L [] []).counter_closed stk hs.1
    refine ⟨hbase, ?_⟩
    simpa [inclusionOuterPorts] using hs.2

def UniqueEntry (p : InclusionPorts K) (m A L : ℕ) (s : CountdownStore K F) : Prop :=
  RangeAllEntry (inclusionOuterPorts p) m A L s ∧
  s.stk (p (.inner .originalWord)) = [] ∧ s.stk (p (.inner .originalMask)) = [] ∧
  ∀ j ∈ rangeAllWork (matchRangePorts (inclusionInnerPorts p)), s.stk j = []

theorem uniqueAll_prepared_inv (p : InclusionPorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : UniqueEntry p m A L s) :
    UniqueStackInv p m A (s.stk (p (.outer .originalWord))).length L
      (s.stk (p (.outer .originalMask))) (rangeAllPrepared (inclusionOuterPorts p) s).stk := by
  let o := inclusionOuterPorts p
  have hentry : InclusionEntry p m A L [] [] s :=
    ⟨hs.1, hs.2.1, hs.2.2.1, by simp, by simp, hs.2.2.2⟩
  have hbase := inclusion_prepared_inv p m A L [] [] s hentry
  have hf (j : RangeCursorPort) (hj : o j ∈ rangeAllWork o) : s.stk (o j) = [] := hs.1.2.2.2.2 _ hj
  have hstk := rangeAllPrepared_stacks o s (hf .word (by simp [rangeAllWork]))
    (hf .mask (by simp [rangeAllWork])) (hf .counter (by simp [rangeAllWork]))
  refine ⟨hbase, ?_, ?_, ?_⟩
  · rw [hstk]; simp [o, inclusionOuterPorts]
  · rw [hstk]; simpa [o, inclusionOuterPorts] using hs.1.2.1
  · rw [hstk]; simp [o, inclusionOuterPorts]

def uniqueAllRoutine (p : InclusionPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  maskedAllRoutine (inclusionOuterPorts p) (uniqueQueryRoutine p)

def uniqueAllAnswer (m A : ℕ) (word mask : List Bool) : Bool :=
  (rawMarkedSuffixes word mask).all (uniqueCellCheck m A word.length mask)

def uniqueAllResult (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨((s.state.1.1, false), uniqueAllAnswer m A
    (s.stk (p (.outer .originalWord))) (s.stk (p (.outer .originalMask)))), s.stk⟩

def uniqueAllBound (m A L : ℕ) : ℕ := L * (uniqueQueryBound m A L + 7) + 12 * L + 17

theorem uniqueAll_executes (p : InclusionPorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : UniqueEntry p m A L s) :
    ∃ n ≤ uniqueAllBound m A L,
      (uniqueAllRoutine p).Executes s (uniqueAllResult p m A s) n := by
  let o := inclusionOuterPorts p
  let W := (s.stk (o .originalWord)).length
  let mask := s.stk (o .originalMask)
  have hf (j : RangeCursorPort) (hj : o j ∈ rangeAllWork o) : s.stk (o j) = [] := hs.1.2.2.2.2 _ hj
  exact maskedAll_executes o (uniqueQueryRoutine p) (uniqueCellCheck m A W mask)
    (UniqueStackInv p m A W L mask) (uniqueQueryBound m A L) L
    (uniqueMaskedContract p m A W L mask) s hs.1.1 hs.1.2.1
    (hf .word (by simp [rangeAllWork])) (hf .mask (by simp [rangeAllWork]))
    (hf .counter (by simp [rangeAllWork])) (hf .temp (by simp [rangeAllWork]))
    (uniqueAll_prepared_inv p m A L s hs)

def rawLeafValue (m A : ℕ) (word : List Bool) : Option (ℕ × ℕ) :=
  (filterRawLeafCell m A (readRawLeafCell word)).map Prod.fst

def rawMarkedCells (m A : ℕ) (word mask : List Bool) : List (ℕ × ℕ) :=
  (rawMarkedSuffixes word mask).filterMap (rawLeafValue m A)

theorem rawCellMatch_value (m A : ℕ) (c : ℕ × ℕ) (word : List Bool) :
    rawCellMatch m A c.1 c.2 word = true ↔ rawLeafValue m A word = some c := by
  rcases c with ⟨B, T⟩
  cases hr : filterRawLeafCell m A (readRawLeafCell word) with
  | none => simp [rawCellMatch, rawLeafValue, hr]
  | some pair =>
      rcases pair with ⟨⟨b, t⟩, rest⟩
      simp [rawCellMatch, rawLeafValue, hr]

theorem rawMarkedCells_membership (m A : ℕ) (c : ℕ × ℕ) (word mask : List Bool) :
    (rawMarkedSuffixes word mask).any (rawCellMatch m A c.1 c.2) =
      decide (c ∈ rawMarkedCells m A word mask) := by
  apply bool_eq_of_true_iff
  simp only [List.any_eq_true, decide_eq_true_eq, rawMarkedCells, List.mem_filterMap,
    rawCellMatch_value]

theorem rawLeafValue_some_head (m A : ℕ) (word : List Bool) (c : ℕ × ℕ)
    (hc : rawLeafValue m A word = some c) : word.head?.getD false = true := by
  cases word with
  | nil => simp [rawLeafValue, readRawLeafCell, filterRawLeafCell] at hc
  | cons b bits => cases b with
      | false => simp [rawLeafValue, readRawLeafCell, filterRawLeafCell] at hc
      | true => rfl

theorem noLaterCellCheck_of_some (m A : ℕ) (word mask : List Bool) (c : ℕ × ℕ)
    (hc : rawLeafValue m A word = some c) :
    noLaterCellCheck m A word mask = !decide (c ∈ rawMarkedCells m A word.tail mask.tail) := by
  have hh := rawLeafValue_some_head m A word c hc
  cases hr : filterRawLeafCell m A (readRawLeafCell word) with
  | none => simp [rawLeafValue, hr] at hc
  | some pair =>
      rcases pair with ⟨d, rest⟩
      have hd : d = c := by simpa only [rawLeafValue, hr, Option.map_some, Option.some.injEq] using hc
      simp only [noLaterCellCheck, hh, Bool.true_eq_true, ↓reduceIte, inclusionCheck, hr, hd]
      exact congrArg Bool.not (rawMarkedCells_membership m A c word.tail mask.tail)

def RawSelectedLeafValid (m A : ℕ) (word mask : List Bool) : Prop :=
  ∀ suffix ∈ rawMarkedSuffixes word mask,
    suffix.head?.getD false = true → (rawLeafValue m A suffix).isSome = true

theorem forestMaskCellCheck_selected_valid (N m : ℕ) (word mask : List Bool)
    (hcheck : forestMaskCellCheck N m word mask = true) :
    RawSelectedLeafValid m (N + m * N + 3) word mask := by
  intro suffix hs hh
  have hc := (List.all_eq_true.mp hcheck) suffix hs
  cases suffix with
  | nil => simp at hh
  | cons b bits => cases b with
      | false => simp at hh
      | true =>
          unfold rawLeafValue
          rw [← readOriginalLeafCell_filtered N m (true :: bits)]
          simp only [readOriginalLeafCell]
          cases hp : readCellBits N m bits with
          | none => simp [legalSuffixCellCheck, hp] at hc
          | some pair => simp [hp]

def rawUniqueRec (m A : ℕ) : List Bool → List Bool → Bool
  | [], _ => true
  | _, [] => true
  | b :: bits, mark :: mask =>
      if mark then noLaterCellCheck m A (b :: bits) (mark :: mask) && rawUniqueRec m A bits mask
      else rawUniqueRec m A bits mask

/-- The logical offset is justified by the physical cursor invariant;
this theorem does not add a free drop operation to the machine. -/
theorem markedUnique_eq_rec (m A W : ℕ) (originalMask word mask : List Bool)
    (hW : word.length ≤ W) (hfit : mask.length ≤ word.length)
    (hm : mask = originalMask.drop (W - word.length)) :
    (rawMarkedSuffixes word mask).all (uniqueCellCheck m A W originalMask) = rawUniqueRec m A word mask := by
  revert hW hfit hm
  induction word generalizing mask with
  | nil => intro hW hfit hm; rfl
  | cons b bits ih =>
      intro hW hfit hm
      cases mask with
      | nil => rfl
      | cons mark mask =>
          have hW' : bits.length ≤ W := by simp only [List.length_cons] at hW; omega
          have hfit' : mask.length ≤ bits.length := by simp only [List.length_cons] at hfit; omega
          have hm' := maskTail_eq_shift W originalMask (b :: bits) (mark :: mask) hW hfit hm
          have hi := ih mask hW' hfit' hm'
          cases mark with
          | false => simpa only [rawMarkedSuffixes, rawUniqueRec, Bool.false_eq_true, ↓reduceIte] using hi
          | true =>
              simp only [rawMarkedSuffixes, rawUniqueRec, Bool.true_eq_true, ↓reduceIte, List.all_cons]
              rw [hi]
              unfold uniqueCellCheck
              rw [← hm]

theorem rawUniqueRec_nodup (m A : ℕ) (word mask : List Bool)
    (hv : RawSelectedLeafValid m A word mask) :
    rawUniqueRec m A word mask = decide ((rawMarkedCells m A word mask).Nodup) := by
  revert hv
  induction word generalizing mask with
  | nil => intro hv; simp [rawUniqueRec, rawMarkedCells, rawMarkedSuffixes]
  | cons b bits ih =>
      intro hv
      cases mask with
      | nil => simp [rawUniqueRec, rawMarkedCells, rawMarkedSuffixes]
      | cons mark mask =>
          have ht : RawSelectedLeafValid m A bits mask := by
            intro suffix hs hh
            apply hv suffix ?_ hh
            cases mark <;> simp [rawMarkedSuffixes, hs]
          cases mark with
          | false =>
              simpa only [rawUniqueRec, rawMarkedCells, rawMarkedSuffixes, Bool.false_eq_true, ↓reduceIte] using ih mask ht
          | true =>
              cases b with
              | false =>
                  have hc : rawMarkedCells m A (false :: bits) (true :: mask) = rawMarkedCells m A bits mask := by
                    simp [rawMarkedCells, rawMarkedSuffixes, rawLeafValue, readRawLeafCell, filterRawLeafCell]
                  have hn : noLaterCellCheck m A (false :: bits) (true :: mask) = true := rfl
                  simp only [rawUniqueRec, Bool.true_eq_true, ↓reduceIte, hn, Bool.true_and, hc]
                  exact ih mask ht
              | true =>
                  have hvh : (rawLeafValue m A (true :: bits)).isSome = true :=
                    hv (true :: bits) (by simp [rawMarkedSuffixes]) rfl
                  cases hc : rawLeafValue m A (true :: bits) with
                  | none => simp [hc] at hvh
                  | some c =>
                      have hcells : rawMarkedCells m A (true :: bits) (true :: mask) =
                          c :: rawMarkedCells m A bits mask := by
                        simp [rawMarkedCells, rawMarkedSuffixes, hc]
                      have hn := noLaterCellCheck_of_some m A (true :: bits) (true :: mask) c hc
                      simp only [rawUniqueRec, Bool.true_eq_true, ↓reduceIte, hn, List.tail_cons, hcells]
                      rw [ih mask ht]
                      apply bool_eq_of_true_iff
                      simp [List.nodup_cons]

theorem uniqueAllAnswer_nodup (m A : ℕ) (word mask : List Bool)
    (hfit : mask.length ≤ word.length) (hv : RawSelectedLeafValid m A word mask) :
    uniqueAllAnswer m A word mask = decide ((rawMarkedCells m A word mask).Nodup) := by
  rw [uniqueAllAnswer, markedUnique_eq_rec m A word.length mask word mask (Nat.le_refl _) hfit
    (by simp), rawUniqueRec_nodup m A word mask hv]

theorem rawLeafValue_leaf (N m : ℕ) (c : ℕ × ℕ) (rest : List Bool)
    (hc : rawCellValid N m c) :
    rawLeafValue m (N + m * N + 3) (rawCellTreeBits (.leaf c) ++ rest) = some c := by
  change c.1 ≤ m ∧ c.2 < N + m * N + 3 at hc
  simp [rawLeafValue, rawCellTreeBits, readRawLeafCell, filterRawLeafCell,
    List.append_assoc, readUnaryFrame_encode, hc]

theorem rawLeafValue_node (m A : ℕ) (l r : BTree (ℕ × ℕ)) (rest : List Bool) :
    rawLeafValue m A (rawCellTreeBits (.node l r) ++ rest) = none := rfl

theorem rawMarkedCells_views (N m : ℕ) (R : BTree (ℕ × ℕ)) (rest : List Bool)
    (hR : rawTreeValid N m R) :
    ((rawNodeViews R rest).map rawViewSuffix).filterMap (rawLeafValue m (N + m * N + 3)) = scanLeaves R := by
  revert hR
  induction R generalizing rest with
  | leaf c =>
      intro hR
      have hc : rawCellValid N m c := hR c (by simp [scanLeaves])
      simp only [rawNodeViews, List.map_cons, List.map_nil, List.filterMap_cons,
        rawViewSuffix, rawLeafValue_leaf N m c rest hc, List.filterMap_nil, scanLeaves]
  | node l r ihl ihr =>
      intro hR
      have hlr := (rawTreeValid_node N m l r).mp hR
      simp only [rawNodeViews, List.map_cons, List.map_append, List.filterMap_cons,
        List.filterMap_append, rawViewSuffix, rawLeafValue_node, scanLeaves]
      rw [ihl (rawCellTreeBits r ++ rest) hlr.1, ihr rest hlr.2]

theorem rawMarkedCells_forest (N m : ℕ) (Rs : List (BTree (ℕ × ℕ))) (rest : List Bool)
    (hRs : ∀ R ∈ Rs, rawTreeValid N m R) :
    rawMarkedCells m (N + m * N + 3) (rawForestWord Rs ++ rest) (rawForestNodeMask Rs) =
      Rs.flatMap scanLeaves := by
  revert hRs
  induction Rs with
  | nil => intro hRs; simp [rawMarkedCells, rawForestWord, rawForestNodeMask, rawMarkedSuffixes]
  | cons R Rs ih =>
      intro hRs
      have hR := hRs R (by simp)
      have ht : ∀ T ∈ Rs, rawTreeValid N m T := by intro T h; exact hRs T (by simp [h])
      have hsplit : rawMarkedSuffixes (rawForestWord (R :: Rs) ++ rest) (rawForestNodeMask (R :: Rs)) =
          (rawNodeViews R (rawForestWord Rs ++ rest)).map rawViewSuffix ++
            rawMarkedSuffixes (rawForestWord Rs ++ rest) (rawForestNodeMask Rs) := by
        simpa only [rawForestWord, rawForestNodeMask, List.flatMap_cons, List.append_assoc] using
          rawMarkedSuffixes_tree R (rawForestWord Rs ++ rest) (rawForestNodeMask Rs)
      unfold rawMarkedCells
      rw [hsplit, List.filterMap_append, rawMarkedCells_views N m R (rawForestWord Rs ++ rest) hR]
      change scanLeaves R ++ rawMarkedCells m (N + m * N + 3)
        (rawForestWord Rs ++ rest) (rawForestNodeMask Rs) = _
      rw [ih ht, List.flatMap_cons]

theorem nodup_map_injective_exact {X Y : Type} (f : X → Y) (hf : Function.Injective f) (xs : List X) :
    (xs.map f).Nodup ↔ xs.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hm : f x ∈ xs.map f ↔ x ∈ xs := by
        constructor
        · intro h
          obtain ⟨y, hy, he⟩ := List.mem_map.mp h
          simpa only [hf he] using hy
        · intro h
          exact List.mem_map.mpr ⟨x, h, rfl⟩
      simp only [List.map_cons, List.nodup_cons, hm, ih]

/-- Original typed CELL uniqueness, reconstructed from parser and range
observations. q can be the whole target row count or one certificate.
The list spans ALL supplied rows, so cross-row duplicates also reject.
Residual bytes are explicit; the enclosing end guard enforces emptiness.
-/
theorem uniqueAllAnswer_observed_typed (N m q : ℕ) (word mask rest : List Bool)
    (hparse : rawForestMaskParse word.length q word = some (rest, mask))
    (hcheck : forestMaskCellCheck N m word mask = true) :
    ∃ Ts : List (BTree (Cell N m)), Ts.length = q ∧ word = Ts.flatMap treeBits ++ rest ∧
      uniqueAllAnswer m (N + m * N + 3) word mask = decide ((Ts.flatMap scanLeaves).Nodup) := by
  obtain ⟨Rs, hq, hw, hm⟩ := (rawForestMaskParse_all_words word rest mask q).mp hparse
  have hR := (forestMaskCellCheck_iff N m Rs rest).mp (by simpa only [← hw, ← hm] using hcheck)
  have hlen := rawForestMaskParse_consumption word rest mask q hparse
  have hfit : mask.length ≤ word.length := by omega
  have hv := forestMaskCellCheck_selected_valid N m word mask hcheck
  obtain ⟨Ts, hTs⟩ := (rawForestValid_iff_typed N m Rs).mp hR
  refine ⟨Ts, ?_, ?_, ?_⟩
  · simpa only [← hTs, List.length_map] using hq
  · simpa only [← hTs, rawForestWord_map_codes] using hw
  · rw [uniqueAllAnswer_nodup m (N + m * N + 3) word mask hfit hv, hw, hm,
      rawMarkedCells_forest N m Rs rest hR, ← hTs, rawForestCodes_leaves]
    apply bool_eq_of_true_iff
    simp only [decide_eq_true_eq]
    exact nodup_map_injective_exact cellNatCode (cellNatCode_injective N m) (Ts.flatMap scanLeaves)

theorem uniqueAll_executes_observed_typed (p : InclusionPorts K) (N m q L : ℕ)
    (s : CountdownStore K F) (rest : List Bool)
    (hs : UniqueEntry p m (N + m * N + 3) L s)
    (hparse : rawForestMaskParse (s.stk (p (.outer .originalWord))).length q
      (s.stk (p (.outer .originalWord))) = some (rest, s.stk (p (.outer .originalMask))))
    (hcheck : forestMaskCellCheck N m (s.stk (p (.outer .originalWord)))
      (s.stk (p (.outer .originalMask))) = true) :
    ∃ Ts : List (BTree (Cell N m)), ∃ n : ℕ, Ts.length = q ∧
      s.stk (p (.outer .originalWord)) = Ts.flatMap treeBits ++ rest ∧
      n ≤ uniqueAllBound m (N + m * N + 3) L ∧
      (uniqueAllRoutine p).Executes s
        ⟨((s.state.1.1, false), decide ((Ts.flatMap scanLeaves).Nodup)), s.stk⟩ n := by
  obtain ⟨Ts, hq, hw, hans⟩ := uniqueAllAnswer_observed_typed N m q
    (s.stk (p (.outer .originalWord))) (s.stk (p (.outer .originalMask))) rest hparse hcheck
  obtain ⟨n, hn, he⟩ := uniqueAll_executes p m (N + m * N + 3) L s hs
  refine ⟨Ts, n, hq, hw, hn, ?_⟩
  simpa only [uniqueAllResult, hans] using he

/- The actual strict-later-position guard and its exact global typed
Nodup observation are now composed in source. No parser validity, cell
uniqueness or time bound is inferred merely from a constructor image.
The enclosing verifier still needs both invocations, type guards, score,
headers, accumulated rejection and exact clean halt. UNELABORATED source
is not VerifierMachineWitness or the separate EncodedSourceHardness.
-/

end PolytomyReductionModel.WholeVerifierController
