/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

One actual subtree scope followed by the paid last-occurrence type tally.
The physical word may retain sibling/ancestor residual bytes. Its newly
parsed mask ends at THIS subtree, so those bytes cannot suppress its last
type occurrences. The root scope is not omitted. This is the scalar caller
for mixedness/coverage/score, not the completed whole verifier.
-/
import PolytomyWholeTypeCount

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

inductive ScopedTypePort where
  | word | rows | types | output
  | scope (port : IndexedSubtreePort)
  | count (port : InclusionPort)
  deriving DecidableEq, Fintype

abbrev ScopedTypePorts (K : Type) := ScopedTypePort ↪ K

@[simp] theorem scopedTypePorts_eq (p : ScopedTypePorts K) (a b : ScopedTypePort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def scopedTypeScopeMap : IndexedSubtreePort → ScopedTypePort
  | .original => .word
  | j => .scope j

def scopedTypeCountMap : InclusionPort → ScopedTypePort
  | .outer .originalWord => .word
  | .outer .originalMask => .scope .output
  | .outer .rows => .rows
  | .outer .types => .types
  | j => .count j

theorem scopedTypeScopeMap_injective : Function.Injective scopedTypeScopeMap := by decide
theorem scopedTypeCountMap_injective : Function.Injective scopedTypeCountMap := by decide

def scopedTypeScopePorts (p : ScopedTypePorts K) : IndexedSubtreePorts K where
  toFun := fun j => p (scopedTypeScopeMap j)
  inj' := fun _ _ h => scopedTypeScopeMap_injective (p.injective h)

def scopedTypeCountPorts (p : ScopedTypePorts K) : InclusionPorts K where
  toFun := fun j => p (scopedTypeCountMap j)
  inj' := fun _ _ h => scopedTypeCountMap_injective (p.injective h)

theorem scopedType_output_distinct (p : ScopedTypePorts K) (j : InclusionPort) :
    p .output ≠ scopedTypeCountPorts p j := by
  cases j with
  | outer r => cases r <;> simp [scopedTypeCountPorts, scopedTypeCountMap]
  | inner r => cases r <;> simp [scopedTypeCountPorts, scopedTypeCountMap]

def ScopedTypeEntry (p : ScopedTypePorts K) (m A L : ℕ) (s : CountdownStore K F) : Prop :=
  ScopeEntry (scopedTypeScopePorts p) L s ∧ UniqueEntry (scopedTypeCountPorts p) m A L s

theorem scopedTypeEntry_transport (p : ScopedTypePorts K) (m A L : ℕ)
    (s t : CountdownStore K F) (hs : ScopedTypeEntry p m A L s)
    (hL : (t.stk (p .word)).length ≤ L)
    (hx : ∀ j : ScopedTypePort, j ≠ .word → t.stk (p j) = s.stk (p j)) :
    ScopedTypeEntry p m A L t := by
  let c := scopedTypeCountPorts p
  have hc (j : InclusionPort) (hj : j ≠ .outer .originalWord) : t.stk (c j) = s.stk (c j) := by
    apply hx
    cases j with
    | outer r => cases r <;> simp_all [scopedTypeCountMap]
    | inner r => cases r <;> simp [scopedTypeCountMap]
  have hs0 : s.stk (p (.scope .output)) = [] := hs.1.2 .output (by decide)
  have hwork (j : K) (hj : j ∈ rangeAllWork (inclusionOuterPorts c) ++
      rangeAllWork (matchRangePorts (inclusionInnerPorts c))) : t.stk j = s.stk j := by
    simp only [List.mem_append, rangeAllWork, List.mem_cons, List.mem_singleton] at hj
    rcases hj with hj | hj
    all_goals rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply hc; decide
  refine ⟨⟨hL, ?_⟩, ?_⟩
  · intro j hj
    have hn : scopedTypeScopeMap j ≠ .word := by cases j <;> simp_all [scopedTypeScopeMap]
    exact (hx _ hn).trans (hs.1.2 j hj)
  · rcases hs.2 with ⟨⟨_, _, hm, hA, houter⟩, hIW, hIM, hinner⟩
    refine ⟨⟨hL, ?_, (hc _ (by decide)).trans hm, (hc _ (by decide)).trans hA, ?_⟩,
      (hc _ (by decide)).trans hIW, (hc _ (by decide)).trans hIM, ?_⟩
    · simpa [inclusionOuterPorts, c, scopedTypeCountPorts, scopedTypeCountMap,
        hx (.scope .output) (by decide), hs0] using Nat.zero_le (t.stk (p .word)).length
    · intro j hj
      exact (hwork j (List.mem_append_left _ hj)).trans (houter j hj)
    · intro j hj
      exact (hwork j (List.mem_append_right _ hj)).trans (hinner j hj)

def scopedTypeParsed (p : ScopedTypePorts K) (s : CountdownStore K F) :=
  indexedSubtreeEval (scopedTypeScopePorts p) 0 s

theorem scopedTypeParsed_extra (p : ScopedTypePorts K) (s : CountdownStore K F)
    (j : ScopedTypePort) (hjs : j ≠ .scope .source) (hjd : j ≠ .scope .discarded)
    (hjp : j ≠ .scope .pending) (hjr : j ≠ .scope .reverse) (hjo : j ≠ .scope .output) :
    (scopedTypeParsed p s).stk (p j) = s.stk (p j) :=
  indexedSubtree_extra (scopedTypeScopePorts p) 0 s (p j)
    (by simpa [scopedTypeScopePorts, scopedTypeScopeMap] using hjs)
    (by simpa [scopedTypeScopePorts, scopedTypeScopeMap] using hjd)
    (by simpa [scopedTypeScopePorts, scopedTypeScopeMap] using hjp)
    (by simpa [scopedTypeScopePorts, scopedTypeScopeMap] using hjr)
    (by simpa [scopedTypeScopePorts, scopedTypeScopeMap] using hjo)

theorem scopedTypeParsed_count_entry (p : ScopedTypePorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : ScopedTypeEntry p m A L s) :
    UniqueEntry (scopedTypeCountPorts p) m A L (scopedTypeParsed p s) := by
  let c := scopedTypeCountPorts p
  let r := scopedTypeScopePorts p
  let u := scopedTypeParsed p s
  have hx (j : InclusionPort) (hj : j ≠ .outer .originalMask) : u.stk (c j) = s.stk (c j) := by
    apply scopedTypeParsed_extra
    all_goals cases j with
      | outer a => cases a <;> simp_all [c, scopedTypeCountPorts, scopedTypeCountMap]
      | inner a => cases a <;> simp_all [c, scopedTypeCountPorts, scopedTypeCountMap]
  have hword : u.stk (p .word) = s.stk (p .word) :=
    scopedTypeParsed_extra p s .word (by decide) (by decide) (by decide) (by decide) (by decide)
  have hmask := (scope_bounds r s).2
  have hwork (j : K) (hj : j ∈ rangeAllWork (inclusionOuterPorts c) ++
      rangeAllWork (matchRangePorts (inclusionInnerPorts c))) : u.stk j = s.stk j := by
    simp only [List.mem_append, rangeAllWork, List.mem_cons, List.mem_singleton] at hj
    rcases hj with hj | hj
    all_goals rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply hx; decide
  rcases hs.2 with ⟨⟨hL, hfit, hm, hA, houtwork⟩, hIW, hIM, hinwork⟩
  refine ⟨⟨?_, ?_, (hx _ (by decide)).trans hm, (hx _ (by decide)).trans hA, ?_⟩,
    (hx _ (by decide)).trans hIW, (hx _ (by decide)).trans hIM, ?_⟩
  · simpa [c, inclusionOuterPorts, scopedTypeCountPorts, scopedTypeCountMap, hword] using hL
  · simpa [c, inclusionOuterPorts, scopedTypeCountPorts, scopedTypeCountMap,
      r, scopedTypeScopePorts, scopedTypeScopeMap, hword] using hmask
  · intro j hj
    exact (hwork j (List.mem_append_left _ hj)).trans (houtwork j hj)
  · intro j hj
    exact (hwork j (List.mem_append_right _ hj)).trans (hinwork j hj)

def scopedTypeCounted (p : ScopedTypePorts K) (m A : ℕ) (s : CountdownStore K F) :=
  let u := scopedTypeParsed p s
  if u.state.2 then typeCountResult (scopedTypeCountPorts p) (p .output) m A u else u

def scopedTypeEval (p : ScopedTypePorts K) (m A : ℕ) (s : CountdownStore K F) :=
  inclusionSelectedOp.apply (clearManyEval (subtreeScopeOwned (scopedTypeScopePorts p))
    (scopedTypeCounted p m A s))

def scopedTypeRoutine (p : ScopedTypePorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (indexedSubtreeRoutine (scopedTypeScopePorts p))
    (RoutineComposition.seq
      (RoutineControl.branch Prod.snd (typeCountRoutine (scopedTypeCountPorts p) (p .output))
        (Atom.routine cleanupNoop))
      (RoutineComposition.seq (clearManyRoutine (subtreeScopeOwned (scopedTypeScopePorts p)))
        (Atom.routine inclusionSelectedOp)))

def scopedTypeResult (p : ScopedTypePorts K) (m A : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  match scopedTypeAnswer m A (s.stk (p .word)) with
  | none => ⟨((s.state.1.1, true), false), s.stk⟩
  | some n => ⟨((s.state.1.1, true), true),
      Function.update s.stk (p .output) (List.replicate n true ++ s.stk (p .output))⟩

theorem scopedType_result (p : ScopedTypePorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : ScopedTypeEntry p m A L s) :
    scopedTypeEval p m A s = scopedTypeResult p m A s := by
  let r := scopedTypeScopePorts p
  let c := scopedTypeCountPorts p
  let u := scopedTypeParsed p s
  have hw : u.stk (p .word) = s.stk (p .word) :=
    scopedTypeParsed_extra p s .word (by decide) (by decide) (by decide) (by decide) (by decide)
  have ho : u.stk (p .output) = s.stk (p .output) :=
    scopedTypeParsed_extra p s .output (by decide) (by decide) (by decide) (by decide) (by decide)
  have hf : u.state.1.1 = s.state.1.1 := congrArg Prod.fst (indexedSubtree_work_clean r 0 s).1
  have hobs := scope_observation r s
  have hclean := scope_cleaned_stacks r L s hs.1
  have howned (j : K) (hj : j ∈ subtreeScopeOwned r) : j ≠ p .output := by
    simp only [subtreeScopeOwned, List.mem_cons, List.mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp [r, scopedTypeScopePorts, scopedTypeScopeMap]
  unfold scopedTypeResult scopedTypeAnswer
  rw [← hobs]
  cases hu : u.state.2 with
  | false =>
      apply countdownStore_ext
      · simp only [scopedTypeEval, scopedTypeCounted, hu, Bool.false_eq_true, ↓reduceIte,
          clearMany_state, inclusionSelectedOp, Op.apply, indexedSubtreeObservation, hf, u]
      · simpa only [scopedTypeEval, scopedTypeCounted, hu, Bool.false_eq_true, ↓reduceIte,
          inclusionSelectedOp, Op.apply, indexedSubtreeObservation, u] using hclean
  | true =>
      apply countdownStore_ext
      · simp [scopedTypeEval, scopedTypeCounted, hu, typeCountResult, clearMany_state,
          inclusionSelectedOp, Op.apply, indexedSubtreeObservation, hf, u]
      · funext j
        by_cases hjo : j = p .output
        · subst j
          rw [show (scopedTypeEval p m A s).stk (p .output) =
              (scopedTypeCounted p m A s).stk (p .output) from
            clearMany_outside _ _ (by intro hh; exact howned _ hh rfl)]
          simp [scopedTypeCounted, hu, typeCountResult, indexedSubtreeObservation,
            c, scopedTypeCountPorts, scopedTypeCountMap, hw, ho, u]
        · have hsame : (scopedTypeEval p m A s).stk j = (clearManyEval (subtreeScopeOwned r) u).stk j := by
            by_cases hj : j ∈ subtreeScopeOwned r
            · change (clearManyEval (subtreeScopeOwned r) (scopedTypeCounted p m A s)).stk j = _
              rw [clearMany_member _ _ hj, clearMany_member _ _ hj]
            · change (clearManyEval (subtreeScopeOwned r) (scopedTypeCounted p m A s)).stk j = _
              rw [clearMany_outside _ _ hj, clearMany_outside _ _ hj]
              simp [scopedTypeCounted, hu, typeCountResult, hjo, u]
          rw [hsame]
          simpa [indexedSubtreeObservation, hu, hjo, u] using congrFun hclean j

def scopedTypeBound (m A L : ℕ) : ℕ := typeCountBound m A L + 11 * L + 27

theorem scopedType_executes (p : ScopedTypePorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : ScopedTypeEntry p m A L s) :
    ∃ n ≤ scopedTypeBound m A L,
      (scopedTypeRoutine p).Executes s (scopedTypeResult p m A s) n := by
  let r := scopedTypeScopePorts p
  let c := scopedTypeCountPorts p
  let u := scopedTypeParsed p s
  let v := scopedTypeCounted p m A s
  obtain ⟨a, ha, h1⟩ := scope_executes r L s hs.1
  have hentry := scopedTypeParsed_count_entry p m A L s hs
  have hbranch : ∃ n ≤ typeCountBound m A L + 2,
      (RoutineControl.branch Prod.snd (typeCountRoutine c (p .output)) (Atom.routine cleanupNoop)).Executes u v n := by
    cases hu : u.state.2 with
    | false =>
        have he := RoutineControl.branch_false Prod.snd (typeCountRoutine c (p .output))
          (Atom.routine cleanupNoop) hu (Atom.executes cleanupNoop u)
        refine ⟨2, by omega, ?_⟩
        simpa only [v, scopedTypeCounted, hu, Bool.false_eq_true, ↓reduceIte, cleanupNoop, Op.apply] using he
    | true =>
        obtain ⟨n, hn, he⟩ := typeCount_executes c (p .output) (scopedType_output_distinct p) m A L u hentry
        have hb := RoutineControl.branch_true Prod.snd (typeCountRoutine c (p .output))
          (Atom.routine cleanupNoop) hu he
        exact ⟨n + 1, by omega, by simpa only [v, scopedTypeCounted, hu, ↓reduceIte] using hb⟩
  obtain ⟨b, hb, h2⟩ := hbranch
  obtain ⟨d, hd, h3⟩ := clearMany_executes (subtreeScopeOwned r) v
  have hbounds := scope_bounds r s
  have hmass : cleanupMass (subtreeScopeOwned r) v ≤ 2 * L := by
    have hL := hs.1.1
    have hvs : v.stk (r .source) = u.stk (r .source) := by
      cases hu : u.state.2 <;>
        simp [v, scopedTypeCounted, hu, typeCountResult, r, scopedTypeScopePorts, scopedTypeScopeMap, u]
    have hvo : v.stk (r .output) = u.stk (r .output) := by
      cases hu : u.state.2 <;>
        simp [v, scopedTypeCounted, hu, typeCountResult, r, scopedTypeScopePorts, scopedTypeScopeMap, u]
    simp only [cleanupMass, subtreeScopeOwned, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hvs, hvo]
    omega
  have h4 := Atom.executes (inclusionSelectedOp (K := K) (F := F)) (clearManyEval (subtreeScopeOwned r) v)
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
    (RoutineComposition.seq_executes _ _ h3 h4))
  change (scopedTypeRoutine p).Executes s (scopedTypeEval p m A s) _ at he
  rw [scopedType_result p m A L s hs] at he
  refine ⟨a + (b + (d + 1)), ?_, he⟩
  simp only [subtreeScopeOwned, List.length_cons, List.length_nil] at hd
  unfold scopedTypeBound
  omega

/-- Exact scope: residual bytes are allowed, but they do not enter the
type cardinality or the output. This includes the root when called at it.
Range validity of this raw subtree is derived by the enclosing forest
guard; it is not inferred merely from the syntax parser succeeding. -/
theorem scopedType_executes_tree (p : ScopedTypePorts K) (N m L : ℕ)
    (s : CountdownStore K F) (R : BTree (ℕ × ℕ)) (rest : List Bool)
    (hs : ScopedTypeEntry p m (N + m * N + 3) L s)
    (hword : s.stk (p .word) = rawCellTreeBits R ++ rest) (hR : rawTreeValid N m R) :
    ∃ n ≤ scopedTypeBound m (N + m * N + 3) L,
      (scopedTypeRoutine p).Executes s
        ⟨((s.state.1.1, true), true), Function.update s.stk (p .output)
          (List.replicate (scanDistinctCount ((scanLeaves R).map Prod.snd)) true ++ s.stk (p .output))⟩ n := by
  obtain ⟨n, hn, he⟩ := scopedType_executes p m (N + m * N + 3) L s hs
  refine ⟨n, hn, ?_⟩
  simpa only [scopedTypeResult, hword, scopedTypeAnswer_tree N m R rest hR] using he

theorem scopedTypeAnswer_bound (m A : ℕ) (word : List Bool) (n : ℕ)
    (hn : scopedTypeAnswer m A word = some n) : n ≤ word.length := by
  unfold scopedTypeAnswer at hn
  cases hp : rawForestMaskParse word.length 1 word with
  | none => simp [hp] at hn
  | some pair =>
      rcases pair with ⟨rest, mask⟩
      have he : typeCountAnswer m A word mask = n := by simpa only [hp, Option.some.injEq] using hn
      have hlen := rawForestMaskParse_consumption word rest mask 1 hp
      have hc := typeCountAnswer_le m A word mask
      omega

/-! ## Physical root-mixedness guard: two unary positions, no numerical oracle -/

def scopedMixedAnswer (m A : ℕ) (word : List Bool) : Bool :=
  match scopedTypeAnswer m A word with
  | none => false
  | some n => decide (2 ≤ n)

def mixedCountPeekOp (out : K) : Op K Bool (CountdownState F) :=
  .peek out (fun st h => (st.1, st.2 && h.isSome))

def scopedMixedInternalEval (p : ScopedTypePorts K) (m A : ℕ) (s : CountdownStore K F) :=
  clearManyEval [p .output] ((mixedCountPeekOp (p .output)).apply
    (countdownPop (p .output) (scopedTypeResult p m A s)))

def scopedMixedInternalRoutine (p : ScopedTypePorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (scopedTypeRoutine p)
    (RoutineComposition.seq (Atom.routine (countdownPopOp (p .output)))
      (RoutineComposition.seq (Atom.routine (mixedCountPeekOp (p .output)))
        (clearManyRoutine [p .output])))

theorem replicate_tail_nonempty_iff_two (n : ℕ) :
    ((List.replicate n true).tail).head?.isSome = decide (2 ≤ n) := by
  cases n with
  | zero => simp
  | succ n => cases n <;> simp [List.replicate_succ]

theorem scopedMixedInternal_result (p : ScopedTypePorts K) (m A : ℕ) (s : CountdownStore K F)
    (hout : s.stk (p .output) = []) :
    scopedMixedInternalEval p m A s =
      ⟨((s.state.1.1, true), scopedMixedAnswer m A (s.stk (p .word))), s.stk⟩ := by
  cases ha : scopedTypeAnswer m A (s.stk (p .word)) with
  | none =>
      apply countdownStore_ext
      · simp [scopedMixedInternalEval, scopedTypeResult, scopedMixedAnswer, ha,
          countdownPop, countdownPopOp, mixedCountPeekOp, clearMany_state, Op.apply, hout]
      · funext j
        by_cases hj : j = p .output
        · subst j
          simp [scopedMixedInternalEval, clearManyEval, clearStackEval, hout]
        · simp [scopedMixedInternalEval, scopedTypeResult, ha, countdownPop, countdownPopOp,
            mixedCountPeekOp, clearManyEval, clearStackEval, Op.apply, hj]
  | some n =>
      apply countdownStore_ext
      · simp [scopedMixedInternalEval, scopedTypeResult, scopedMixedAnswer, ha,
          countdownPop, countdownPopOp, mixedCountPeekOp, clearMany_state, Op.apply, hout,
          replicate_tail_nonempty_iff_two]
      · funext j
        by_cases hj : j = p .output
        · subst j
          simp [scopedMixedInternalEval, clearManyEval, clearStackEval, hout]
        · simp [scopedMixedInternalEval, scopedTypeResult, ha, countdownPop, countdownPopOp,
            mixedCountPeekOp, clearManyEval, clearStackEval, Op.apply, hj]

theorem scopedMixedInternal_executes (p : ScopedTypePorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : ScopedTypeEntry p m A L s) (hout : s.stk (p .output) = []) :
    ∃ n ≤ scopedTypeBound m A L + L + 4,
      (scopedMixedInternalRoutine p).Executes s
        ⟨((s.state.1.1, true), scopedMixedAnswer m A (s.stk (p .word))), s.stk⟩ n := by
  let u := scopedTypeResult p m A s
  let v := countdownPop (p .output) u
  let w := (mixedCountPeekOp (p .output)).apply v
  obtain ⟨a, ha, h1⟩ := scopedType_executes p m A L s hs
  have h2 := Atom.executes (countdownPopOp (p .output)) u
  have h3 := Atom.executes (mixedCountPeekOp (p .output)) v
  obtain ⟨b, hb, h4⟩ := clearMany_executes [p .output] w
  have hlen : (w.stk (p .output)).length ≤ L := by
    cases hh : scopedTypeAnswer m A (s.stk (p .word)) with
    | none => simp [w, v, u, scopedTypeResult, hh, countdownPop, countdownPopOp, mixedCountPeekOp, Op.apply, hout]
    | some n =>
        have hn := scopedTypeAnswer_bound m A (s.stk (p .word)) n hh
        have hL : (s.stk (p .word)).length ≤ L := hs.1.1
        have ht : (List.replicate n true).tail.length ≤ n := by
          cases n <;> simp [List.replicate_succ]
        simp only [w, v, u, scopedTypeResult, hh, countdownPop, countdownPopOp,
          mixedCountPeekOp, Op.apply, Function.update_same, hout, List.append_nil]
        omega
  have hmass : cleanupMass [p .output] w ≤ L := by simpa [cleanupMass] using hlen
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
    (RoutineComposition.seq_executes _ _ h3 h4))
  change (scopedMixedInternalRoutine p).Executes s (scopedMixedInternalEval p m A s) _ at he
  rw [scopedMixedInternal_result p m A s hout] at he
  refine ⟨a + (1 + (1 + b)), ?_, he⟩
  simp only [List.length_cons, List.length_nil] at hb
  omega

def internalTagPeekOp (word : K) : Op K Bool (CountdownState F) :=
  .peek word (fun st h => ((st.1.1, decide (h = some false)), st.2))

def mixedRootAnswer (m A : ℕ) (word : List Bool) : Bool :=
  if word.head? = some false then scopedMixedAnswer m A word else true

def mixedRootRoutine (p : ScopedTypePorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (Atom.routine (internalTagPeekOp (p .word)))
    (RoutineComposition.seq
      (RoutineControl.branch (fun st => st.1.2) (scopedMixedInternalRoutine p) (Atom.routine forestSyntaxStartOp))
      (Atom.routine inclusionSelectedOp))

def mixedRootBound (m A L : ℕ) : ℕ := scopedTypeBound m A L + L + 7

theorem mixedRoot_executes (p : ScopedTypePorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : ScopedTypeEntry p m A L s) (hout : s.stk (p .output) = [])
    (hselected : s.state.1.2 = true) :
    ∃ n ≤ mixedRootBound m A L,
      (mixedRootRoutine p).Executes s (cellCompareFlagStore (mixedRootAnswer m A (s.stk (p .word))) s) n := by
  let u := (internalTagPeekOp (p .word)).apply s
  have h1 := Atom.executes (internalTagPeekOp (p .word)) s
  by_cases hh : (s.stk (p .word)).head? = some false
  · have hu : u.state.1.2 = true := by simp [u, internalTagPeekOp, Op.apply, hh]
    obtain ⟨a, ha, h2⟩ := scopedMixedInternal_executes p m A L u hs hout
    have hbranch := RoutineControl.branch_true (fun st : CountdownState F => st.1.2)
      (scopedMixedInternalRoutine p) (Atom.routine forestSyntaxStartOp) hu h2
    have h3 := Atom.executes (inclusionSelectedOp (K := K) (F := F))
      (⟨((u.state.1.1, true), scopedMixedAnswer m A (u.stk (p .word))), u.stk⟩ : CountdownStore K F)
    have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ hbranch h3)
    refine ⟨1 + ((a + 1) + 1), by unfold mixedRootBound; omega, ?_⟩
    simpa [mixedRootRoutine, mixedRootAnswer, hh, u, internalTagPeekOp, inclusionSelectedOp,
      Op.apply, cellCompareFlagStore, hselected] using he
  · have hu : u.state.1.2 = false := by simp [u, internalTagPeekOp, Op.apply, hh]
    have hbranch := RoutineControl.branch_false (fun st : CountdownState F => st.1.2)
      (scopedMixedInternalRoutine p) (Atom.routine forestSyntaxStartOp) hu (Atom.executes forestSyntaxStartOp u)
    have h3 := Atom.executes (inclusionSelectedOp (K := K) (F := F)) (forestSyntaxStartOp.apply u)
    have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ hbranch h3)
    refine ⟨4, by unfold mixedRootBound scopedTypeBound; omega, ?_⟩
    simpa [mixedRootRoutine, mixedRootAnswer, hh, u, internalTagPeekOp, inclusionSelectedOp,
      forestSyntaxStartOp, Op.apply, cellCompareFlagStore, hselected] using he

/- Next in the SAME whole controller: physical mixedness comparison on
each internal scope; markers at each supplied row root only; global
coverage; every certificate internal/root score; bounded headers; and
rejection/cleanup/halt joins. No VerifierMachineWitness is claimed here. -/

end PolytomyReductionModel.WholeVerifierController
