/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The ORIGINAL each-supplied-row-root marker guard. Markers are
not required in every internal target subtree. Physical marker operands
are copied from A and popped twice, then incremented once, not introduced
as uncharged arithmetic constants. The complete physical row countdown,
typed scanMarkers observation and local cleanup are proposed below.
-/
import PolytomyWholeCoverage
import PolytomyObservedCountdownFold
import PolytomyPartialCounterBounds

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

inductive RowMarkerPort where
  | word | rows | types | marker
  | scope (port : IndexedSubtreePort)
  | query (port : MatchCursorPort)
  deriving DecidableEq, Fintype

abbrev RowMarkerPorts (K : Type) := RowMarkerPort ↪ K

@[simp] theorem rowMarkerPorts_eq (p : RowMarkerPorts K) (a b : RowMarkerPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def rowMarkerScopeMap : IndexedSubtreePort → RowMarkerPort
  | .original => .word
  | j => .scope j

def rowMarkerQueryMap : MatchCursorPort → RowMarkerPort
  | .wantedKind => .marker
  | .cursor .originalWord => .word
  | .cursor .originalMask => .scope .output
  | .cursor .rows => .rows
  | .cursor .types => .types
  | j => .query j

theorem rowMarkerScopeMap_injective : Function.Injective rowMarkerScopeMap := by decide
theorem rowMarkerQueryMap_injective : Function.Injective rowMarkerQueryMap := by decide

def rowMarkerScopePorts (p : RowMarkerPorts K) : IndexedSubtreePorts K where
  toFun := fun j => p (rowMarkerScopeMap j)
  inj' := fun _ _ h => rowMarkerScopeMap_injective (p.injective h)

def rowMarkerQueryPorts (p : RowMarkerPorts K) : MatchCursorPorts K where
  toFun := fun j => p (rowMarkerQueryMap j)
  inj' := fun _ _ h => rowMarkerQueryMap_injective (p.injective h)

def rowMarkerPrepared (p : RowMarkerPorts K) (s : CountdownStore K F) :=
  countdownPop (p .marker) (countdownPop (p .marker) (wordDuplicateEval (p .types) (p .marker) s))

def rowMarkerPrepareRoutine (p : RowMarkerPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (wordDuplicateRoutine (p .types) (p (.query (.cursor .temp))) (p .marker))
    (RoutineComposition.seq (Atom.routine (countdownPopOp (p .marker)))
      (Atom.routine (countdownPopOp (p .marker))))

theorem rowMarkerPrepared_stacks (p : RowMarkerPorts K) (A : ℕ) (s : CountdownStore K F)
    (hA : s.stk (p .types) = List.replicate A true) (hz : s.stk (p .marker) = []) :
    (rowMarkerPrepared p s).stk = Function.update s.stk (p .marker) (List.replicate (A - 2) true) := by
  cases A with
  | zero => simp [rowMarkerPrepared, countdownPop, countdownPopOp, wordDuplicateEval, Op.apply, hA, hz]
  | succ A => cases A <;>
      simp [rowMarkerPrepared, countdownPop, countdownPopOp, wordDuplicateEval, Op.apply, hA, hz,
        List.replicate_succ, Nat.succ_sub_succ_eq_sub]

theorem rowMarkerPrepare_executes (p : RowMarkerPorts K) (A : ℕ) (s : CountdownStore K F)
    (hA : s.stk (p .types) = List.replicate A true) (ht : s.stk (p (.query (.cursor .temp))) = []) :
    (rowMarkerPrepareRoutine p).Executes s (rowMarkerPrepared p s) (3 * A + 5) := by
  let u := wordDuplicateEval (p .types) (p .marker) s
  have h1 := wordDuplicate_executes (p .types) (p (.query (.cursor .temp))) (p .marker)
    (by simp) (by simp) (by simp) s ht
  have h2 := Atom.executes (countdownPopOp (p .marker)) u
  have h3 := Atom.executes (countdownPopOp (p .marker)) (countdownPop (p .marker) u)
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3)
  simpa only [rowMarkerPrepareRoutine, rowMarkerPrepared, hA, List.length_replicate,
    Nat.add_assoc] using he

def rowMarkerPairEval (p : RowMarkerPorts K) (m A T : ℕ) (s : CountdownStore K F) :=
  let u := typeMembershipResult (rowMarkerQueryPorts p) m A T s
  if u.state.2 then typeMembershipResult (rowMarkerQueryPorts p) m A (T + 1)
    ((tallyPushOp (p .marker)).apply u) else u

def rowMarkerPairRoutine (p : RowMarkerPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (typeMembershipRoutine (rowMarkerQueryPorts p))
    (RoutineControl.branch Prod.snd
      (RoutineComposition.seq (Atom.routine (tallyPushOp (p .marker)))
        (typeMembershipRoutine (rowMarkerQueryPorts p))) (Atom.routine cleanupNoop))

def rowMarkerPairBound (m A T L : ℕ) : ℕ :=
  typeMembershipBound m A T L + typeMembershipBound m A (T + 1) L + 2

theorem rowMarkerPair_executes (p : RowMarkerPorts K) (m A T L : ℕ)
    (s : CountdownStore K F) (hs : TypeAllEntry (rowMarkerQueryPorts p) m A T L s) :
    ∃ n ≤ rowMarkerPairBound m A T L,
      (rowMarkerPairRoutine p).Executes s (rowMarkerPairEval p m A T s) n := by
  let q := rowMarkerQueryPorts p
  let u := typeMembershipResult q m A T s
  let v := (tallyPushOp (p .marker)).apply u
  obtain ⟨a, ha, h1⟩ := typeMembership_executes q m A T L s hs
  have hbranch : ∃ n ≤ typeMembershipBound m A (T + 1) L + 2,
      (RoutineControl.branch Prod.snd
        (RoutineComposition.seq (Atom.routine (tallyPushOp (p .marker))) (typeMembershipRoutine q))
        (Atom.routine cleanupNoop)).Executes u (rowMarkerPairEval p m A T s) n := by
    cases hu : u.state.2 with
    | false =>
        have he := RoutineControl.branch_false Prod.snd
          (RoutineComposition.seq (Atom.routine (tallyPushOp (p .marker))) (typeMembershipRoutine q))
          (Atom.routine cleanupNoop) hu (Atom.executes cleanupNoop u)
        exact ⟨2, by omega, by simpa [rowMarkerPairEval, hu, u, cleanupNoop, Op.apply] using he⟩
    | true =>
        have hv : TypeAllEntry q m A (T + 1) L v := by
          rcases hs with ⟨⟨hL, hfit, hm, hA, hwork⟩, hT⟩
          refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · simpa [v, u, tallyPushOp, Op.apply, typeMembershipResult, q, rowMarkerQueryPorts,
              rowMarkerQueryMap, matchRangePorts] using hL
          · simpa [v, u, tallyPushOp, Op.apply, typeMembershipResult, q, rowMarkerQueryPorts,
              rowMarkerQueryMap, matchRangePorts] using hfit
          · simpa [v, u, tallyPushOp, Op.apply, typeMembershipResult, q, rowMarkerQueryPorts,
              rowMarkerQueryMap, matchRangePorts] using hm
          · simpa [v, u, tallyPushOp, Op.apply, typeMembershipResult, q, rowMarkerQueryPorts,
              rowMarkerQueryMap, matchRangePorts] using hA
          · intro j hj
            have hn : j ≠ p .marker := by
              intro he; rw [he] at hj
              simp [rangeAllWork, matchRangePorts, q, rowMarkerQueryPorts, rowMarkerQueryMap] at hj
            simpa [v, u, tallyPushOp, Op.apply, typeMembershipResult, hn] using hwork j hj
          · have hT' : s.stk (p .marker) = List.replicate T true := hT
            simp [v, u, tallyPushOp, Op.apply, typeMembershipResult, q, rowMarkerQueryPorts,
              rowMarkerQueryMap, hT', List.replicate_succ, Nat.add_comm T 1]
        obtain ⟨b, hb, h2⟩ := typeMembership_executes q m A (T + 1) L v hv
        have hpush := Atom.executes (tallyPushOp (p .marker)) u
        have he := RoutineControl.branch_true Prod.snd
          (RoutineComposition.seq (Atom.routine (tallyPushOp (p .marker))) (typeMembershipRoutine q))
          (Atom.routine cleanupNoop) hu (RoutineComposition.seq_executes _ _ hpush h2)
        exact ⟨(1 + b) + 1, by omega, by simpa only [rowMarkerPairEval, hu, ↓reduceIte] using he⟩
  obtain ⟨b, hb, h2⟩ := hbranch
  exact ⟨a + b, by unfold rowMarkerPairBound; omega, RoutineComposition.seq_executes _ _ h1 h2⟩

theorem rowMarkerPair_flag (p : RowMarkerPorts K) (m A T : ℕ) (s : CountdownStore K F) :
    (rowMarkerPairEval p m A T s).state.2 =
      typeMembershipAnswer m A T (s.stk (p .word)) (s.stk (p (.scope .output))) &&
      typeMembershipAnswer m A (T + 1) (s.stk (p .word)) (s.stk (p (.scope .output))) := by
  cases hf : typeMembershipAnswer m A T (s.stk (p .word)) (s.stk (p (.scope .output))) <;>
    simp [rowMarkerPairEval, typeMembershipResult, rowMarkerQueryPorts, rowMarkerQueryMap,
      tallyPushOp, Op.apply, hf]

theorem rowMarkerPair_extra (p : RowMarkerPorts K) (m A T : ℕ) (s : CountdownStore K F)
    (j : K) (hj : j ≠ p .marker) :
    (rowMarkerPairEval p m A T s).stk j = s.stk j := by
  unfold rowMarkerPairEval
  split <;> simp [typeMembershipResult, tallyPushOp, Op.apply, hj]

def RowMarkerEntry (p : RowMarkerPorts K) (m A L : ℕ) (s : CountdownStore K F) : Prop :=
  ScopeEntry (rowMarkerScopePorts p) L s ∧ TypeAllEntry (rowMarkerQueryPorts p) m A 0 L s

def rowMarkerParsed (p : RowMarkerPorts K) (s : CountdownStore K F) :=
  indexedSubtreeEval (rowMarkerScopePorts p) 0 s

theorem rowMarkerParsed_extra (p : RowMarkerPorts K) (s : CountdownStore K F)
    (j : RowMarkerPort) (hjs : j ≠ .scope .source) (hjd : j ≠ .scope .discarded)
    (hjp : j ≠ .scope .pending) (hjr : j ≠ .scope .reverse) (hjo : j ≠ .scope .output) :
    (rowMarkerParsed p s).stk (p j) = s.stk (p j) :=
  indexedSubtree_extra (rowMarkerScopePorts p) 0 s (p j)
    (by simpa [rowMarkerScopePorts, rowMarkerScopeMap] using hjs)
    (by simpa [rowMarkerScopePorts, rowMarkerScopeMap] using hjd)
    (by simpa [rowMarkerScopePorts, rowMarkerScopeMap] using hjp)
    (by simpa [rowMarkerScopePorts, rowMarkerScopeMap] using hjr)
    (by simpa [rowMarkerScopePorts, rowMarkerScopeMap] using hjo)

theorem rowMarkerParsed_entry (p : RowMarkerPorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : RowMarkerEntry p m A L s) :
    TypeAllEntry (rowMarkerQueryPorts p) m A 0 L (rowMarkerParsed p s) := by
  let q := rowMarkerQueryPorts p
  let r := rowMarkerScopePorts p
  let u := rowMarkerParsed p s
  have hx (j : MatchCursorPort) (hj : j ≠ .cursor .originalMask) : u.stk (q j) = s.stk (q j) := by
    apply rowMarkerParsed_extra
    all_goals cases j with
      | wantedBlock => simp [rowMarkerQueryMap]
      | wantedKind => simp [rowMarkerQueryMap]
      | cursor a => cases a <;> simp_all [rowMarkerQueryMap]
  have hw : u.stk (p .word) = s.stk (p .word) :=
    rowMarkerParsed_extra p s .word (by decide) (by decide) (by decide) (by decide) (by decide)
  have hmask := (scope_bounds r s).2
  rcases hs.2 with ⟨⟨hL, hfit, hm, hA, hwork⟩, hT⟩
  refine ⟨⟨?_, ?_, (hx _ (by decide)).trans hm, (hx _ (by decide)).trans hA, ?_⟩,
    (hx _ (by decide)).trans hT⟩
  · simpa [q, matchRangePorts, rowMarkerQueryPorts, rowMarkerQueryMap, hw] using hL
  · simpa [q, matchRangePorts, rowMarkerQueryPorts, rowMarkerQueryMap,
      r, rowMarkerScopePorts, rowMarkerScopeMap, hw] using hmask
  · intro j hj
    have he : u.stk j = s.stk j := by
      simp only [rangeAllWork, List.mem_cons, List.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals apply hx; decide
    exact he.trans (hwork j hj)

theorem rowMarkerPrepared_entry (p : RowMarkerPorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : TypeAllEntry (rowMarkerQueryPorts p) m A 0 L s) :
    TypeAllEntry (rowMarkerQueryPorts p) m A (A - 2) L (rowMarkerPrepared p s) := by
  let q := rowMarkerQueryPorts p
  have hA : s.stk (p .types) = List.replicate A true := hs.1.2.2.2.1
  have hz : s.stk (p .marker) = [] := hs.2
  have hstk := rowMarkerPrepared_stacks p A s hA hz
  have hx (j : MatchCursorPort) (hj : j ≠ .wantedKind) :
      (rowMarkerPrepared p s).stk (q j) = s.stk (q j) := by
    rw [hstk]
    have hn : q j ≠ p .marker := by
      cases j with
      | wantedBlock => simp [q, rowMarkerQueryPorts, rowMarkerQueryMap]
      | wantedKind => exact (hj rfl).elim
      | cursor a => cases a <;> simp [q, rowMarkerQueryPorts, rowMarkerQueryMap]
    simp [hn]
  refine ⟨⟨?_, ?_, (hx _ (by decide)).trans hs.1.2.2.1,
    (hx _ (by decide)).trans hs.1.2.2.2.1, ?_⟩, ?_⟩
  · simpa only [matchRangePorts, hx _ (by decide)] using hs.1.1
  · simpa only [matchRangePorts, hx _ (by decide), hx _ (by decide)] using hs.1.2.1
  · intro j hj
    have he : (rowMarkerPrepared p s).stk j = s.stk j := by
      simp only [rangeAllWork, List.mem_cons, List.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals apply hx; decide
    exact he.trans (hs.1.2.2.2.2 j hj)
  · rw [hstk]
    simp [q, rowMarkerQueryPorts, rowMarkerQueryMap]

def rowMarkerQueried (p : RowMarkerPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  let u := rowMarkerParsed p s
  if u.state.2 then rowMarkerPairEval p m A (A - 2) (rowMarkerPrepared p u) else u

def rowMarkerQueryRoutine (p : RowMarkerPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (indexedSubtreeRoutine (rowMarkerScopePorts p))
    (RoutineControl.branch Prod.snd (RoutineComposition.seq (rowMarkerPrepareRoutine p) (rowMarkerPairRoutine p))
      (Atom.routine cleanupNoop))

def rowMarkerQueryBound (m A L : ℕ) : ℕ := 9 * L + 3 * A + rowMarkerPairBound m A (A - 2) L + 27

theorem rowMarkerQuery_executes (p : RowMarkerPorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : RowMarkerEntry p m A L s) :
    ∃ n ≤ rowMarkerQueryBound m A L,
      (rowMarkerQueryRoutine p).Executes s (rowMarkerQueried p m A s) n := by
  let u := rowMarkerParsed p s
  let v := rowMarkerPrepared p u
  let q := rowMarkerQueryPorts p
  have huentry := rowMarkerParsed_entry p m A L s hs
  have hv := rowMarkerPrepared_entry p m A L u huentry
  obtain ⟨a, ha, h1⟩ := scope_executes (rowMarkerScopePorts p) L s hs.1
  have hbranch : ∃ n ≤ 3 * A + rowMarkerPairBound m A (A - 2) L + 6,
      (RoutineControl.branch Prod.snd (RoutineComposition.seq (rowMarkerPrepareRoutine p) (rowMarkerPairRoutine p))
        (Atom.routine cleanupNoop)).Executes u (rowMarkerQueried p m A s) n := by
    cases hf : u.state.2 with
    | false =>
        have he := RoutineControl.branch_false Prod.snd
          (RoutineComposition.seq (rowMarkerPrepareRoutine p) (rowMarkerPairRoutine p))
          (Atom.routine cleanupNoop) hf (Atom.executes cleanupNoop u)
        exact ⟨2, by omega, by simpa [rowMarkerQueried, hf, cleanupNoop, Op.apply, u] using he⟩
    | true =>
        have hA : u.stk (p .types) = List.replicate A true := huentry.1.2.2.2.1
        have ht : u.stk (p (.query (.cursor .temp))) = [] :=
          huentry.1.2.2.2.2 _ (by simp [rangeAllWork, matchRangePorts, q, rowMarkerQueryPorts, rowMarkerQueryMap])
        have hprep := rowMarkerPrepare_executes p A u hA ht
        obtain ⟨b, hb, hpair⟩ := rowMarkerPair_executes p m A (A - 2) L v hv
        have he := RoutineControl.branch_true Prod.snd
          (RoutineComposition.seq (rowMarkerPrepareRoutine p) (rowMarkerPairRoutine p))
          (Atom.routine cleanupNoop) hf (RoutineComposition.seq_executes _ _ hprep hpair)
        exact ⟨(3 * A + 5 + b) + 1, by omega,
          by simpa only [rowMarkerQueried, hf, ↓reduceIte] using he⟩
  obtain ⟨b, hb, h2⟩ := hbranch
  exact ⟨a + b, by unfold rowMarkerQueryBound; omega, RoutineComposition.seq_executes _ _ h1 h2⟩

def rowMarkerRootAnswer (m A : ℕ) (word : List Bool) : Bool :=
  match rawForestMaskParse word.length 1 word with
  | none => false
  | some (_, mask) => typeMembershipAnswer m A (A - 2) word mask &&
      typeMembershipAnswer m A (A - 2 + 1) word mask

theorem rowMarkerQueried_flag (p : RowMarkerPorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : RowMarkerEntry p m A L s) :
    (rowMarkerQueried p m A s).state.2 = rowMarkerRootAnswer m A (s.stk (p .word)) := by
  let u := rowMarkerParsed p s
  have hu := rowMarkerParsed_entry p m A L s hs
  have hA : u.stk (p .types) = List.replicate A true := hu.1.2.2.2.1
  have hz : u.stk (p .marker) = [] := hu.2
  have hstk := rowMarkerPrepared_stacks p A u hA hz
  have hw : u.stk (p .word) = s.stk (p .word) :=
    rowMarkerParsed_extra p s .word (by decide) (by decide) (by decide) (by decide) (by decide)
  have hobs := scope_observation (rowMarkerScopePorts p) s
  unfold rowMarkerRootAnswer
  rw [← hobs]
  cases hf : u.state.2 with
  | false => simp [rowMarkerQueried, indexedSubtreeObservation, hf, u]
  | true =>
      simp only [rowMarkerQueried, hf, ↓reduceIte, rowMarkerPair_flag]
      rw [hstk]
      simp [indexedSubtreeObservation, hf, u, hw, rowMarkerScopePorts, rowMarkerScopeMap]

theorem rowMarkerQueried_extra (p : RowMarkerPorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : RowMarkerEntry p m A L s) (j : K) (hj : j ≠ p .marker) :
    (rowMarkerQueried p m A s).stk j = (rowMarkerParsed p s).stk j := by
  let u := rowMarkerParsed p s
  have hu := rowMarkerParsed_entry p m A L s hs
  have hstk := rowMarkerPrepared_stacks p A u hu.1.2.2.2.1 hu.2
  unfold rowMarkerQueried
  cases hf : u.state.2 with
  | false => simp [hf, u]
  | true =>
      simp only [hf, ↓reduceIte, rowMarkerPair_extra p m A (A - 2) (rowMarkerPrepared p u) j hj]
      rw [hstk]
      simp [hj]

theorem rowMarkerQueried_marker_bound (p : RowMarkerPorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : RowMarkerEntry p m A L s) :
    ((rowMarkerQueried p m A s).stk (p .marker)).length ≤ A + 1 := by
  let u := rowMarkerParsed p s
  have hu := rowMarkerParsed_entry p m A L s hs
  have hz : u.stk (p .marker) = [] := hu.2
  have hstk := rowMarkerPrepared_stacks p A u hu.1.2.2.2.1 hz
  unfold rowMarkerQueried
  cases hf : u.state.2 with
  | false => simp [hf, u, hz]
  | true =>
      simp only [hf, ↓reduceIte, rowMarkerPairEval]
      split <;>
        simp [typeMembershipResult, tallyPushOp, Op.apply, hstk]
      all_goals omega

theorem rowMarkerQueried_frame (p : RowMarkerPorts K) (m A : ℕ) (s : CountdownStore K F) :
    (rowMarkerQueried p m A s).state.1.1 = s.state.1.1 := by
  have hf := congrArg Prod.fst (indexedSubtree_work_clean (rowMarkerScopePorts p) 0 s).1
  unfold rowMarkerQueried
  split
  · unfold rowMarkerPairEval
    split <;> simpa [typeMembershipResult, tallyPushOp, Op.apply, rowMarkerPrepared,
      countdownPop, countdownPopOp, wordDuplicateEval] using hf
  · exact hf

def rowMarkerAdvanceOwned (p : RowMarkerPorts K) : List K :=
  [p .word, p .marker, p (.scope .output)]

/-- Keep the parser's actual residual, not a guessed byte offset. Two
physical reversing transfers preserve its original order and empty both
the residual source and temporary port. -/
def rowMarkerAdvanceEval (p : RowMarkerPorts K) (s : CountdownStore K F) :=
  reverseMoveEval (p (.scope .temp)) (p .word)
    (reverseMoveEval (p (.scope .source)) (p (.scope .temp))
      (clearManyEval (rowMarkerAdvanceOwned p) s))

def rowMarkerAdvanceRoutine (p : RowMarkerPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (clearManyRoutine (rowMarkerAdvanceOwned p))
    (RoutineComposition.seq (frameReverseRoutine (p (.scope .source)) (p (.scope .temp)))
      (frameReverseRoutine (p (.scope .temp)) (p .word)))

def rowMarkerAdvanceResult (p : RowMarkerPorts K) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨s.state, Function.update (Function.update (Function.update (Function.update s.stk
    (p .word) (s.stk (p (.scope .source)))) (p .marker) []) (p (.scope .output)) [])
      (p (.scope .source)) []⟩

theorem rowMarkerAdvance_result (p : RowMarkerPorts K) (s : CountdownStore K F)
    (ht : s.stk (p (.scope .temp)) = []) :
    rowMarkerAdvanceEval p s = rowMarkerAdvanceResult p s := by
  apply countdownStore_ext
  · simp only [rowMarkerAdvanceEval, reverseMoveEval, clearMany_state, rowMarkerAdvanceResult]
  · funext j
    by_cases hjw : j = p .word
    · subst j
      simp [rowMarkerAdvanceEval, rowMarkerAdvanceResult, reverseMoveEval,
        clearManyEval, rowMarkerAdvanceOwned, clearStackEval, ht]
    by_cases hjm : j = p .marker
    · subst j
      simp [rowMarkerAdvanceEval, rowMarkerAdvanceResult, reverseMoveEval,
        clearManyEval, rowMarkerAdvanceOwned, clearStackEval, ht]
    by_cases hjo : j = p (.scope .output)
    · subst j
      simp [rowMarkerAdvanceEval, rowMarkerAdvanceResult, reverseMoveEval,
        clearManyEval, rowMarkerAdvanceOwned, clearStackEval, ht]
    by_cases hjs : j = p (.scope .source)
    · subst j
      simp [rowMarkerAdvanceEval, rowMarkerAdvanceResult, reverseMoveEval,
        clearManyEval, rowMarkerAdvanceOwned, clearStackEval, ht]
    by_cases hjt : j = p (.scope .temp)
    · subst j
      simp [rowMarkerAdvanceEval, rowMarkerAdvanceResult, reverseMoveEval,
        clearManyEval, rowMarkerAdvanceOwned, clearStackEval, ht]
    · simp [rowMarkerAdvanceEval, rowMarkerAdvanceResult, reverseMoveEval,
        clearManyEval, rowMarkerAdvanceOwned, clearStackEval, hjw, hjm, hjo, hjs, hjt]

theorem rowMarkerAdvance_executes (p : RowMarkerPorts K) (A L : ℕ) (s : CountdownStore K F)
    (hw : (s.stk (p .word)).length ≤ L)
    (hm : (s.stk (p .marker)).length ≤ A + 1)
    (ho : (s.stk (p (.scope .output))).length ≤ L)
    (hr : (s.stk (p (.scope .source))).length ≤ L)
    (ht : s.stk (p (.scope .temp)) = []) :
    ∃ n ≤ 4 * L + A + 7,
      (rowMarkerAdvanceRoutine p).Executes s (rowMarkerAdvanceResult p s) n := by
  let u := clearManyEval (rowMarkerAdvanceOwned p) s
  let v := reverseMoveEval (p (.scope .source)) (p (.scope .temp)) u
  obtain ⟨a, ha, h1⟩ := clearMany_executes (rowMarkerAdvanceOwned p) s
  have hsource : u.stk (p (.scope .source)) = s.stk (p (.scope .source)) :=
    clearMany_outside _ _ (by simp [rowMarkerAdvanceOwned])
  have htemp : u.stk (p (.scope .temp)) = [] :=
    (clearMany_outside _ _ (by simp [rowMarkerAdvanceOwned])).trans ht
  have hvt : v.stk (p (.scope .temp)) = (s.stk (p (.scope .source))).reverse := by
    simp [v, reverseMoveEval, htemp, hsource]
  have h2 := reverseMove_executes (p (.scope .source)) (p (.scope .temp)) (by simp) u
  have h3 := reverseMove_executes (p (.scope .temp)) (p .word) (by simp) v
  rw [hsource] at h2
  rw [hvt, List.length_reverse] at h3
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3)
  change (rowMarkerAdvanceRoutine p).Executes s (rowMarkerAdvanceEval p s) _ at he
  rw [rowMarkerAdvance_result p s ht] at he
  refine ⟨a + ((s.stk (p (.scope .source))).length + 1 +
    ((s.stk (p (.scope .source))).length + 1)), ?_, he⟩
  simp only [cleanupMass, rowMarkerAdvanceOwned, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at ha
  omega

def rowMarkerStepEval (p : RowMarkerPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  rowMarkerAdvanceResult p (rowMarkerQueried p m A s)

def rowMarkerStepRoutine (p : RowMarkerPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (rowMarkerQueryRoutine p) (rowMarkerAdvanceRoutine p)

def rowMarkerStepBound (m A L : ℕ) : ℕ := rowMarkerQueryBound m A L + 4 * L + A + 7

theorem rowMarkerStep_executes (p : RowMarkerPorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : RowMarkerEntry p m A L s) :
    ∃ n ≤ rowMarkerStepBound m A L,
      (rowMarkerStepRoutine p).Executes s (rowMarkerStepEval p m A s) n := by
  let u := rowMarkerParsed p s
  let v := rowMarkerQueried p m A s
  have hx (j : RowMarkerPort) (hj : j ≠ .marker) : v.stk (p j) = u.stk (p j) :=
    rowMarkerQueried_extra p m A L s hs (p j) (by simpa using hj)
  have hw : v.stk (p .word) = s.stk (p .word) :=
    (hx .word (by decide)).trans (rowMarkerParsed_extra p s .word
      (by decide) (by decide) (by decide) (by decide) (by decide))
  have ht : v.stk (p (.scope .temp)) = [] :=
    (hx _ (by decide)).trans ((rowMarkerParsed_extra p s (.scope .temp)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hs.1.2 .temp (by decide)))
  have hbounds := scope_bounds (rowMarkerScopePorts p) s
  have hL : (s.stk (p .word)).length ≤ L := hs.1.1
  have hr : (v.stk (p (.scope .source))).length ≤ L := by
    rw [hx _ (by decide)]
    exact hbounds.1.trans hL
  have ho : (v.stk (p (.scope .output))).length ≤ L := by
    rw [hx _ (by decide)]
    exact hbounds.2.trans hL
  obtain ⟨a, ha, h1⟩ := rowMarkerQuery_executes p m A L s hs
  obtain ⟨b, hb, h2⟩ := rowMarkerAdvance_executes p A L v (by rw [hw]; exact hL)
    (rowMarkerQueried_marker_bound p m A L s hs) ho hr ht
  exact ⟨a + b, by unfold rowMarkerStepBound; omega, RoutineComposition.seq_executes _ _ h1 h2⟩

theorem rowMarkerStep_stacks (p : RowMarkerPorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : RowMarkerEntry p m A L s) :
    (rowMarkerStepEval p m A s).stk = Function.update s.stk (p .word)
      ((rowMarkerParsed p s).stk (p (.scope .source))) := by
  let r := rowMarkerScopePorts p
  let u := rowMarkerParsed p s
  let v := rowMarkerQueried p m A s
  have hclean := scope_cleaned_stacks r L s hs.1
  have hx (j : K) (hj : j ≠ p .marker) : v.stk j = u.stk j := rowMarkerQueried_extra p m A L s hs j hj
  have hmarker : s.stk (p .marker) = [] := hs.2.2
  funext j
  by_cases hjw : j = p .word
  · subst j
    simp [rowMarkerStepEval, rowMarkerAdvanceResult, hx _ (by simp), u, v]
  by_cases hjm : j = p .marker
  · subst j
    simp [rowMarkerStepEval, rowMarkerAdvanceResult, hmarker]
  by_cases hjs : j = p (.scope .source)
  · subst j
    have hz : s.stk (p (.scope .source)) = [] := hs.1.2 .source (by decide)
    simp [rowMarkerStepEval, rowMarkerAdvanceResult, hz]
  by_cases hjo : j = p (.scope .output)
  · subst j
    have hz : s.stk (p (.scope .output)) = [] := hs.1.2 .output (by decide)
    simp [rowMarkerStepEval, rowMarkerAdvanceResult, hz]
  · have hjowned : j ∉ subtreeScopeOwned r := by
      simp [subtreeScopeOwned, r, rowMarkerScopePorts, rowMarkerScopeMap, hjs, hjo]
    have huj : u.stk j = s.stk j := by
      have hh := congrFun hclean j
      rw [clearMany_outside _ _ hjowned] at hh
      exact hh
    simp [rowMarkerStepEval, rowMarkerAdvanceResult, hjw, hjm, hjs, hjo, hx j hjm, huj, v]

theorem rowMarkerEntry_transport (p : RowMarkerPorts K) (m A L : ℕ)
    (s t : CountdownStore K F) (hs : RowMarkerEntry p m A L s)
    (hL : (t.stk (p .word)).length ≤ L)
    (hx : ∀ j : RowMarkerPort, j ≠ .word → t.stk (p j) = s.stk (p j)) :
    RowMarkerEntry p m A L t := by
  let q := rowMarkerQueryPorts p
  have hq (j : MatchCursorPort) (hj : j ≠ .cursor .originalWord) : t.stk (q j) = s.stk (q j) := by
    apply hx
    cases j with
    | wantedBlock => simp [rowMarkerQueryMap]
    | wantedKind => simp [rowMarkerQueryMap]
    | cursor a => cases a <;> simp_all [rowMarkerQueryMap]
  have hs0 : s.stk (p (.scope .output)) = [] := hs.1.2 .output (by decide)
  refine ⟨⟨hL, ?_⟩, ⟨⟨hL, ?_, (hq _ (by decide)).trans hs.2.1.2.2.1,
    (hq _ (by decide)).trans hs.2.1.2.2.2.1, ?_⟩, (hq _ (by decide)).trans hs.2.2⟩⟩
  · intro j hj
    have hn : rowMarkerScopeMap j ≠ .word := by cases j <;> simp_all [rowMarkerScopeMap]
    exact (hx _ hn).trans (hs.1.2 j hj)
  · simpa [matchRangePorts, q, rowMarkerQueryPorts, rowMarkerQueryMap,
      hx (.scope .output) (by decide), hs0] using Nat.zero_le (t.stk (p .word)).length
  · intro j hj
    have he : t.stk j = s.stk j := by
      simp only [rangeAllWork, List.mem_cons, List.mem_singleton] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals apply hq; decide
    exact he.trans (hs.2.1.2.2.2.2 j hj)

theorem rowMarkerStep_closed (p : RowMarkerPorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : RowMarkerEntry p m A L s) :
    RowMarkerEntry p m A L (rowMarkerStepEval p m A s) := by
  have hstk := rowMarkerStep_stacks p m A L s hs
  apply rowMarkerEntry_transport p m A L s _ hs
  · rw [hstk, Function.update_same]
    exact (scope_bounds (rowMarkerScopePorts p) s).1.trans hs.1.1
  · intro j hj
    rw [hstk]
    simp [hj]

def rowMarkerCountdownContract (p : RowMarkerPorts K) (counter : K)
    (hc : ∀ j : RowMarkerPort, counter ≠ p j) (m A L : ℕ) :
    CountdownContract counter (rowMarkerStepRoutine p) (rowMarkerStepEval p m A)
      (RowMarkerEntry p m A L) (rowMarkerStepBound m A L) where
  peek_closed s hs := hs
  pop_closed s hs hg := by
    apply rowMarkerEntry_transport p m A L s _ hs
    · simpa [countdownPop, countdownPopOp, Op.apply, (hc .word).symm] using hs.1.1
    · intro j hj
      simp [countdownPop, countdownPopOp, Op.apply, (hc j).symm]
  body_closed s hs := rowMarkerStep_closed p m A L s hs
  reset_closed s hs := hs
  counter_preserved s hs := by
    rw [rowMarkerStep_stacks p m A L s hs]
    simp [hc .word]
  body_executes s hs := rowMarkerStep_executes p m A L s hs

def rowMarkersLoopRoutine (p : RowMarkerPorts K) (counter : K) :=
  countdownRoutine counter (rowMarkerStepRoutine p)

def rowMarkersLoopEval (p : RowMarkerPorts K) (counter : K) (m A : ℕ) (s : CountdownStore K F) :=
  countdownEval counter (rowMarkerStepEval p m A) s

theorem rowMarkersLoop_executes (p : RowMarkerPorts K) (counter : K)
    (hc : ∀ j : RowMarkerPort, counter ≠ p j) (m A L : ℕ)
    (s : CountdownStore K F) (hs : RowMarkerEntry p m A L s) :
    ∃ n ≤ (s.stk counter).length * (rowMarkerStepBound m A L + 3) + 3,
      (rowMarkersLoopRoutine p counter).Executes s (rowMarkersLoopEval p counter m A s) n ∧
      RowMarkerEntry p m A L (rowMarkersLoopEval p counter m A s) ∧
      (rowMarkersLoopEval p counter m A s).state.1.2 = false ∧
      ((rowMarkersLoopEval p counter m A s).state.2 = true →
        (rowMarkersLoopEval p counter m A s).stk counter = []) :=
  countdownRoutine_executes counter (rowMarkerStepRoutine p) (rowMarkerStepEval p m A)
    (RowMarkerEntry p m A L) (rowMarkerStepBound m A L) (rowMarkerCountdownContract p counter hc m A L) s hs

theorem typeMembershipAnswer_tree (N m T : ℕ) (R : BTree (ℕ × ℕ)) (rest : List Bool)
    (hR : rawTreeValid N m R) :
    typeMembershipAnswer m (N + m * N + 3) T (rawCellTreeBits R ++ rest) (rawNodeMask R) =
      decide (T ∈ (scanLeaves R).map Prod.snd) := by
  rw [typeMembershipAnswer_cells]
  have hc := rawMarkedCells_forest N m [R] rest (by
    intro U hU
    have he : U = R := by simpa only [List.mem_singleton] using hU
    subst U
    exact hR)
  have hcells : rawMarkedCells m (N + m * N + 3) (rawCellTreeBits R ++ rest) (rawNodeMask R) = scanLeaves R := by
    simpa only [rawForestWord, rawForestNodeMask, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hc
  rw [hcells]

theorem injective_map_member_iff {X Y : Type} (f : X → Y) (hf : Function.Injective f) (x : X) (xs : List X) :
    f x ∈ xs.map f ↔ x ∈ xs := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hx
    have hxy : y = x := hf he
    simpa only [hxy] using hy
  · intro hx
    exact List.mem_map.mpr ⟨x, hx, rfl⟩

theorem rowMarkerRootAnswer_typed {N m : ℕ} (T : BTree (Cell N m)) (rest : List Bool) :
    rowMarkerRootAnswer m (N + m * N + 3) (treeBits T ++ rest) = scanMarkers T := by
  have hword : treeBits T = rawCellTreeBits (rawTreeCodes T) := (rawTreeCodes_bits T).symm
  rw [hword, rowMarkerRootAnswer, rawForestMaskParse_one,
    typeMembershipAnswer_tree N m _ (rawTreeCodes T) rest (rawTreeCodes_valid T),
    typeMembershipAnswer_tree N m _ (rawTreeCodes T) rest (rawTreeCodes_valid T), rawTreeCodes_leaves]
  let z0 : Terminal N m := .inr (.inr (0 : Fin 2))
  let z1 : Terminal N m := .inr (.inr (1 : Fin 2))
  have h0 : terminalCode N m z0 = N + m * N + 3 - 2 := by
    change N + (m * N + 1) + 0 = N + m * N + 3 - 2
    omega
  have h1 : terminalCode N m z1 = N + m * N + 3 - 2 + 1 := by
    change N + (m * N + 1) + 1 = N + m * N + 3 - 2 + 1
    omega
  have hmap : ((scanLeaves T).map cellNatCode).map Prod.snd =
      ((scanLeaves T).map Prod.snd).map (terminalCode N m) := by
    simp only [List.map_map, Function.comp_def, cellNatCode]
  rw [hmap, ← h0, ← h1,
    injective_map_member_iff (terminalCode N m) (terminalCode_injective N m) z0,
    injective_map_member_iff (terminalCode N m) (terminalCode_injective N m) z1]
  rfl

theorem rowMarkerStep_typed (p : RowMarkerPorts K) (N m L : ℕ)
    (s : CountdownStore K F) (T : BTree (Cell N m)) (rest : List Bool)
    (hs : RowMarkerEntry p m (N + m * N + 3) L s)
    (hw : s.stk (p .word) = treeBits T ++ rest) :
    (rowMarkerStepEval p m (N + m * N + 3) s).state.2 = scanMarkers T ∧
    (rowMarkerStepEval p m (N + m * N + 3) s).stk (p .word) = rest := by
  have hflag := rowMarkerQueried_flag p m (N + m * N + 3) L s hs
  rw [hw, rowMarkerRootAnswer_typed] at hflag
  refine ⟨hflag, ?_⟩
  rw [rowMarkerStep_stacks p m (N + m * N + 3) L s hs, Function.update_same]
  have hobs := indexedSubtree_view (rowMarkerScopePorts p) 0 s (rawTreeCodes T) rest
    (by simpa only [List.drop_zero, rowMarkerScopePorts, rowMarkerScopeMap, rawTreeCodes_bits] using hw)
  let u := rowMarkerParsed p s
  cases hf : u.state.2 with
  | false => simp [indexedSubtreeObservation, hf, u] at hobs
  | true =>
      have hp : u.stk (p (.scope .source)) = rest ∧ u.stk (p (.scope .output)) = rawNodeMask (rawTreeCodes T) := by
        simpa only [indexedSubtreeObservation, hf, ↓reduceIte, Option.some.injEq, Prod.mk.injEq,
          rowMarkerScopePorts, rowMarkerScopeMap] using hobs
      exact hp.1

/-- Each loop iteration consumes ONE entire original self-delimiting row,
not one node and not a fabricated per-row length frame. Marker failure
stops the countdown; no later row can reactivate it. -/
theorem rowMarkersLoop_flag (p : RowMarkerPorts K) (counter : K)
    (hc : ∀ j : RowMarkerPort, counter ≠ p j) (N m L fuel : ℕ) :
    ∀ (s : CountdownStore K F) (Ts : List (BTree (Cell N m))) (rest : List Bool),
      RowMarkerEntry p m (N + m * N + 3) L s →
      s.stk (p .word) = Ts.flatMap treeBits ++ rest →
      (s.stk counter).length = Ts.length → (s.stk counter).length ≤ fuel →
      s.state.1.2 = (s.stk counter).head?.isSome →
      (countdownLoopEval counter (rowMarkerStepEval p m (N + m * N + 3)) fuel s).state.2 =
        s.state.2 && Ts.all scanMarkers := by
  induction fuel with
  | zero =>
      intro s Ts rest hs hw hcount hlen hpeek
      have hTs : Ts = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [countdownLoopEval, hTs]
  | succ fuel ih =>
      intro s Ts rest hs hw hcount hlen hpeek
      cases Ts with
      | nil =>
          have hz : s.stk counter = [] := List.eq_nil_of_length_eq_zero (by simpa using hcount)
          simp [countdownLoopEval, countdownGuard, hpeek, hz]
      | cons T Ts =>
          cases hf : s.state.2 with
          | false => simp [countdownLoopEval, countdownGuard, hf]
          | true =>
              have hnon : (s.stk counter).head?.isSome = true := by
                cases hh : s.stk counter with
                | nil => simp [hh] at hcount
                | cons b bs => rfl
              have hg : countdownGuard s.state = true := by simp [countdownGuard, hpeek, hnon, hf]
              let v := countdownPop counter s
              let w := rowMarkerStepEval p m (N + m * N + 3) v
              let u := countdownPeek counter w
              let contract := rowMarkerCountdownContract p counter hc m (N + m * N + 3) L
              have hv : RowMarkerEntry p m (N + m * N + 3) L v := contract.pop_closed s hs hg
              have hvword : v.stk (p .word) = treeBits T ++ (Ts.flatMap treeBits ++ rest) := by
                simpa [v, countdownPop, countdownPopOp, Op.apply, (hc .word).symm,
                  List.flatMap_cons, List.append_assoc] using hw
              have hstep := rowMarkerStep_typed p N m L v T (Ts.flatMap treeBits ++ rest) hv hvword
              have hu : RowMarkerEntry p m (N + m * N + 3) L u :=
                contract.peek_closed w (contract.body_closed v hv)
              have huc : u.stk counter = (s.stk counter).tail := by
                change w.stk counter = _
                rw [contract.counter_preserved v hv, countdownPop_counter]
              have hucount : (u.stk counter).length = Ts.length := by
                rw [huc]
                cases hh : s.stk counter with
                | nil => simp [hh] at hcount
                | cons b bs => simpa [hh] using hcount
              have hulen : (u.stk counter).length ≤ fuel := by
                rw [huc]
                cases hh : s.stk counter with
                | nil => simp
                | cons b bs => simpa [hh] using hlen
              have hi := ih u Ts rest hu hstep.2 hucount hulen (countdownPeek_control counter w)
              simp only [countdownLoopEval, hg, ↓reduceIte]
              rw [hi]
              change w.state.2 && Ts.all scanMarkers = _
              rw [hstep.1]
              simp [hf]

def rowMarkersAllPrepared (p : RowMarkerPorts K) (saved counter : K) (s : CountdownStore K F) :=
  forestSyntaxStartOp.apply ((tallyPushOp counter).apply
    (wordDuplicateEval (p .rows) counter (wordDuplicateEval saved (p .word) s)))

def rowMarkersAllPrepareRoutine (p : RowMarkerPorts K) (saved counter : K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  let temp := p (.query (.cursor .temp))
  RoutineComposition.seq (wordDuplicateRoutine saved temp (p .word))
    (RoutineComposition.seq (wordDuplicateRoutine (p .rows) temp counter)
      (RoutineComposition.seq (Atom.routine (tallyPushOp counter)) (Atom.routine forestSyntaxStartOp)))

theorem rowMarkersAllPrepared_stacks (p : RowMarkerPorts K) (saved counter : K)
    (hsaved : ∀ j : RowMarkerPort, saved ≠ p j) (hcounter : ∀ j : RowMarkerPort, counter ≠ p j)
    (hsc : saved ≠ counter) (m : ℕ) (s : CountdownStore K F)
    (hw : s.stk (p .word) = []) (hc : s.stk counter = [])
    (hm : s.stk (p .rows) = List.replicate m true) :
    (rowMarkersAllPrepared p saved counter s).stk =
      Function.update (Function.update s.stk (p .word) (s.stk saved)) counter (List.replicate (m + 1) true) := by
  simp [rowMarkersAllPrepared, forestSyntaxStartOp, tallyPushOp, Op.apply, wordDuplicateEval,
    hw, hc, hm, hsc, hcounter .word, List.replicate_succ, Nat.add_comm m 1]

theorem rowMarkersAllPrepare_executes (p : RowMarkerPorts K) (saved counter : K)
    (hsaved : ∀ j : RowMarkerPort, saved ≠ p j) (hcounter : ∀ j : RowMarkerPort, counter ≠ p j)
    (m : ℕ) (s : CountdownStore K F)
    (hm : s.stk (p .rows) = List.replicate m true)
    (ht : s.stk (p (.query (.cursor .temp))) = []) :
    (rowMarkersAllPrepareRoutine p saved counter).Executes s (rowMarkersAllPrepared p saved counter s)
      (3 * (s.stk saved).length + 3 * m + 8) := by
  let temp := p (.query (.cursor .temp))
  let u := wordDuplicateEval saved (p .word) s
  let v := wordDuplicateEval (p .rows) counter u
  have h1 := wordDuplicate_executes saved temp (p .word) (hsaved _) (hsaved _) (by simp [temp]) s ht
  have htu : u.stk temp = [] := by simp [u, wordDuplicateEval, temp, ht]
  have hmu : u.stk (p .rows) = List.replicate m true := by simp [u, wordDuplicateEval, hm]
  have h2 := wordDuplicate_executes (p .rows) temp counter (by simp [temp])
    (hcounter _).symm (hcounter _).symm u htu
  have h3 := Atom.executes (tallyPushOp counter) v
  have h4 := Atom.executes (forestSyntaxStartOp (K := K) (F := F)) ((tallyPushOp counter).apply v)
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
    (RoutineComposition.seq_executes _ _ h3 h4))
  simpa only [rowMarkersAllPrepareRoutine, rowMarkersAllPrepared, hmu, List.length_replicate,
    temp, u, v, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using he

def RowMarkersAllEntry (p : RowMarkerPorts K) (saved counter : K) (m A L : ℕ)
    (s : CountdownStore K F) : Prop :=
  RowMarkerEntry p m A L s ∧ (s.stk saved).length ≤ L ∧
    s.stk (p .word) = [] ∧ s.stk counter = []

theorem rowMarkersAll_prepared_entry (p : RowMarkerPorts K) (saved counter : K)
    (hsaved : ∀ j : RowMarkerPort, saved ≠ p j) (hcounter : ∀ j : RowMarkerPort, counter ≠ p j)
    (hsc : saved ≠ counter) (m A L : ℕ) (s : CountdownStore K F)
    (hs : RowMarkersAllEntry p saved counter m A L s) :
    RowMarkerEntry p m A L (rowMarkersAllPrepared p saved counter s) := by
  have hm : s.stk (p .rows) = List.replicate m true := hs.1.2.1.2.2.1
  have hstk := rowMarkersAllPrepared_stacks p saved counter hsaved hcounter hsc m s hs.2.2.1 hs.2.2.2 hm
  apply rowMarkerEntry_transport p m A L s _ hs.1
  · rw [hstk]
    simpa [hcounter .word] using hs.2.1
  · intro j hj
    rw [hstk]
    simp [hj, (hcounter j).symm]

theorem rowMarkerStep_outside (p : RowMarkerPorts K) (m A : ℕ) (s : CountdownStore K F)
    (j : K) (hj : ∀ a : RowMarkerPort, j ≠ p a) :
    (rowMarkerStepEval p m A s).stk j = s.stk j := by
  have hparse : (rowMarkerParsed p s).stk j = s.stk j :=
    indexedSubtree_extra (rowMarkerScopePorts p) 0 s j (hj _) (hj _) (hj _) (hj _) (hj _)
  have hquery : (rowMarkerQueried p m A s).stk j = s.stk j := by
    unfold rowMarkerQueried
    split
    · rw [rowMarkerPair_extra p m A (A - 2) _ j (hj .marker)]
      simpa [rowMarkerPrepared, countdownPop, countdownPopOp, wordDuplicateEval, Op.apply, hj .marker] using hparse
    · exact hparse
  simp [rowMarkerStepEval, rowMarkerAdvanceResult, hj .word, hj .marker,
    hj (.scope .output), hj (.scope .source), hquery]

def rowMarkersAllEval (p : RowMarkerPorts K) (saved counter : K) (m A : ℕ) (s : CountdownStore K F) :=
  clearManyEval [p .word, counter]
    (rowMarkersLoopEval p counter m A (rowMarkersAllPrepared p saved counter s))

def rowMarkersAllRoutine (p : RowMarkerPorts K) (saved counter : K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (rowMarkersAllPrepareRoutine p saved counter)
    (RoutineComposition.seq (rowMarkersLoopRoutine p counter) (clearManyRoutine [p .word, counter]))

def rowMarkersAllBound (m A L : ℕ) : ℕ := (m + 1) * (rowMarkerStepBound m A L + 3) + 4 * L + 4 * m + 15

theorem rowMarkersAll_executes (p : RowMarkerPorts K) (saved counter : K)
    (hsaved : ∀ j : RowMarkerPort, saved ≠ p j) (hcounter : ∀ j : RowMarkerPort, counter ≠ p j)
    (hsc : saved ≠ counter) (m A L : ℕ) (s : CountdownStore K F)
    (hs : RowMarkersAllEntry p saved counter m A L s) :
    ∃ n ≤ rowMarkersAllBound m A L,
      (rowMarkersAllRoutine p saved counter).Executes s (rowMarkersAllEval p saved counter m A s) n ∧
      (rowMarkersAllEval p saved counter m A s).stk = s.stk ∧
      (rowMarkersAllEval p saved counter m A s).state.1 = (s.state.1.1, false) := by
  let u := rowMarkersAllPrepared p saved counter s
  let v := rowMarkersLoopEval p counter m A u
  have hm : s.stk (p .rows) = List.replicate m true := hs.1.2.1.2.2.1
  have ht : s.stk (p (.query (.cursor .temp))) = [] :=
    hs.1.2.1.2.2.2.2 _ (by simp [rangeAllWork, matchRangePorts, rowMarkerQueryPorts, rowMarkerQueryMap])
  have hstk := rowMarkersAllPrepared_stacks p saved counter hsaved hcounter hsc m s hs.2.2.1 hs.2.2.2 hm
  have huc : u.stk counter = List.replicate (m + 1) true := by rw [hstk]; simp
  have hu := rowMarkersAll_prepared_entry p saved counter hsaved hcounter hsc m A L s hs
  have h1 := rowMarkersAllPrepare_executes p saved counter hsaved hcounter m s hm ht
  obtain ⟨a, ha, h2, hv, hvguard, hvempty⟩ := rowMarkersLoop_executes p counter hcounter m A L u hu
  obtain ⟨b, hb, h3⟩ := clearMany_executes [p .word, counter] v
  have hcv : (v.stk counter).length ≤ m + 1 := by
    have hh := countdown_counter_le counter (rowMarkerStepEval p m A)
      (fun t => rowMarkerStep_outside p m A t counter hcounter) u
    simpa only [huc, List.length_replicate] using hh
  have hwv : (v.stk (p .word)).length ≤ L := hv.1.1
  have hmass : cleanupMass [p .word, counter] v ≤ L + m + 1 := by
    simp only [cleanupMass, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  let contract := rowMarkerCountdownContract p counter hcounter m A L
  have hvextra (j : K) (hjw : j ≠ p .word) (hjc : j ≠ counter) : v.stk j = s.stk j := by
    have hh := countdownLoop_preserves_on counter (rowMarkerStepRoutine p) (rowMarkerStepEval p m A)
      (RowMarkerEntry p m A L) (rowMarkerStepBound m A L) contract (fun t => t.stk j)
      (fun _ => rfl) (by intro t; simp [countdownPop, countdownPopOp, Op.apply, hjc])
      (by intro t ht; rw [rowMarkerStep_stacks p m A L t ht]; simp [hjw])
      (u.stk counter).length (countdownPeek counter u) hu
    have hstart : u.stk j = s.stk j := by rw [hstk]; simp [hjw, hjc]
    exact hh.trans hstart
  have hvframe : v.state.1.1 = s.state.1.1 := by
    exact countdownLoop_preserves counter (rowMarkerStepEval p m A) (fun t => t.state.1.1)
      (fun _ => rfl) (fun _ => rfl) (fun t => rowMarkerQueried_frame p m A t)
      (u.stk counter).length (countdownPeek counter u)
  have hout : (rowMarkersAllEval p saved counter m A s).stk = s.stk := by
    funext j
    by_cases hjw : j = p .word
    · subst j
      rw [show (rowMarkersAllEval p saved counter m A s).stk (p .word) = [] from clearMany_member _ _ (by simp)]
      exact hs.2.2.1.symm
    by_cases hjc : j = counter
    · subst j
      rw [show (rowMarkersAllEval p saved counter m A s).stk counter = [] from clearMany_member _ _ (by simp)]
      exact hs.2.2.2.symm
    · change (clearManyEval [p .word, counter] v).stk j = _
      rw [clearMany_outside _ _ (by simp [hjw, hjc])]
      exact hvextra j hjw hjc
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3)
  refine ⟨3 * (s.stk saved).length + 3 * m + 8 + (a + b), ?_, he, hout, ?_⟩
  · rw [huc, List.length_replicate] at ha
    simp only [List.length_cons, List.length_nil] at hb
    unfold rowMarkersAllBound
    omega
  · rw [show (rowMarkersAllEval p saved counter m A s).state = v.state from clearMany_state _ _]
    exact Prod.ext hvframe hvguard

theorem rowMarkersAll_flag_typed (p : RowMarkerPorts K) (saved counter : K)
    (hsaved : ∀ j : RowMarkerPort, saved ≠ p j) (hcounter : ∀ j : RowMarkerPort, counter ≠ p j)
    (hsc : saved ≠ counter) (N m L : ℕ) (s : CountdownStore K F)
    (hs : RowMarkersAllEntry p saved counter m (N + m * N + 3) L s)
    (Ts : List (BTree (Cell N m))) (rest : List Bool)
    (hword : s.stk saved = Ts.flatMap treeBits ++ rest) (hlen : Ts.length = m + 1) :
    (rowMarkersAllEval p saved counter m (N + m * N + 3) s).state.2 = Ts.all scanMarkers := by
  let u := rowMarkersAllPrepared p saved counter s
  have hm : s.stk (p .rows) = List.replicate m true := hs.1.2.1.2.2.1
  have hstk := rowMarkersAllPrepared_stacks p saved counter hsaved hcounter hsc m s hs.2.2.1 hs.2.2.2 hm
  have hu := rowMarkersAll_prepared_entry p saved counter hsaved hcounter hsc m (N + m * N + 3) L s hs
  have huc : u.stk counter = List.replicate (m + 1) true := by rw [hstk]; simp
  have huw : u.stk (p .word) = Ts.flatMap treeBits ++ rest := by
    rw [hstk]
    simpa [hcounter .word] using hword
  have hi := rowMarkersLoop_flag p counter hcounter N m L (u.stk counter).length
    (countdownPeek counter u) Ts rest hu huw
    (by rw [huc, List.length_replicate, hlen]) (le_refl _) (countdownPeek_control counter u)
  change (clearManyEval [p .word, counter]
    (rowMarkersLoopEval p counter m (N + m * N + 3) u)).state.2 = _
  rw [clearMany_state]
  simpa only [rowMarkersAllPrepared, countdownPeek, countdownPeekOp, forestSyntaxStartOp,
    Op.apply, Bool.true_and] using hi

theorem rowMarkersAll_executes_typed (p : RowMarkerPorts K) (saved counter : K)
    (hsaved : ∀ j : RowMarkerPort, saved ≠ p j) (hcounter : ∀ j : RowMarkerPort, counter ≠ p j)
    (hsc : saved ≠ counter) (N m L : ℕ) (s : CountdownStore K F)
    (hs : RowMarkersAllEntry p saved counter m (N + m * N + 3) L s)
    (Ts : List (BTree (Cell N m))) (rest : List Bool)
    (hword : s.stk saved = Ts.flatMap treeBits ++ rest) (hlen : Ts.length = m + 1) :
    ∃ n ≤ rowMarkersAllBound m (N + m * N + 3) L,
      (rowMarkersAllRoutine p saved counter).Executes s
        ⟨((s.state.1.1, false), Ts.all scanMarkers), s.stk⟩ n := by
  obtain ⟨n, hn, he, hstk, hframe⟩ :=
    rowMarkersAll_executes p saved counter hsaved hcounter hsc m (N + m * N + 3) L s hs
  have hflag := rowMarkersAll_flag_typed p saved counter hsaved hcounter hsc N m L s hs Ts rest hword hlen
  have hresult : rowMarkersAllEval p saved counter m (N + m * N + 3) s =
      ⟨((s.state.1.1, false), Ts.all scanMarkers), s.stk⟩ := by
    apply countdownStore_ext
    · exact Prod.ext hframe hflag
    · exact hstk
  exact ⟨n, hn, hresult ▸ he⟩

/-- q=m+1 is the same original row count already checked by the forest
phase. The counter is actually copied from m and pushed once. The trees
below are reconstructed, not supplied as a constructor-origin promise.
Residual bytes stay explicit and are excluded from all row scopes. -/
theorem rowMarkersAll_executes_observed_typed (p : RowMarkerPorts K) (saved counter : K)
    (hsaved : ∀ j : RowMarkerPort, saved ≠ p j) (hcounter : ∀ j : RowMarkerPort, counter ≠ p j)
    (hsc : saved ≠ counter) (N m L : ℕ) (s : CountdownStore K F)
    (hs : RowMarkersAllEntry p saved counter m (N + m * N + 3) L s)
    (mask rest : List Bool)
    (hparse : rawForestMaskParse (s.stk saved).length (m + 1) (s.stk saved) = some (rest, mask))
    (hcheck : forestMaskCellCheck N m (s.stk saved) mask = true) :
    ∃ Ts : List (BTree (Cell N m)), ∃ n : ℕ, Ts.length = m + 1 ∧
      s.stk saved = Ts.flatMap treeBits ++ rest ∧
      n ≤ rowMarkersAllBound m (N + m * N + 3) L ∧
      (rowMarkersAllRoutine p saved counter).Executes s
        ⟨((s.state.1.1, false), Ts.all scanMarkers), s.stk⟩ n := by
  obtain ⟨Rs, hq, hw, hm⟩ := (rawForestMaskParse_all_words (s.stk saved) rest mask (m + 1)).mp hparse
  have hR := (forestMaskCellCheck_iff N m Rs rest).mp (by simpa only [← hw, ← hm] using hcheck)
  obtain ⟨Ts, hTs⟩ := (rawForestValid_iff_typed N m Rs).mp hR
  have hlen : Ts.length = m + 1 := by simpa only [← hTs, List.length_map] using hq
  have hword : s.stk saved = Ts.flatMap treeBits ++ rest := by
    simpa only [← hTs, rawForestWord_map_codes] using hw
  obtain ⟨n, hn, he⟩ := rowMarkersAll_executes_typed p saved counter hsaved hcounter hsc N m L s hs Ts rest hword hlen
  exact ⟨Ts, n, hlen, hword, hn, he⟩

/- The original row-root guard now has a proposed complete physical
countdown, exact scanMarkers observation, bounded failure cleanup and
restored tapes. This remains UNELABORATED and is not a final verifier.
Actual root-inclusive certificate score, bounded header/dimension/cap
preparation and all one-inventory/rejection/clean-halt/time joins remain.
VerifierMachineWitness and EncodedSourceHardness are independent gaps. -/

end PolytomyReductionModel.WholeVerifierController
