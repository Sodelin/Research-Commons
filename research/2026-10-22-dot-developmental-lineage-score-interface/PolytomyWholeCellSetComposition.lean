/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Continuation of the SAME restricted encoded marked-star verifier.
The aim here is the actual two-way CELL-set scan used by both the global
certificate guard and the every-fixed-clade/existing-certificate-clade
nest. This file does not broaden the language to arbitrary Carta/DAG
inputs, supply all target guards, count the objective, or close the final
VerifierMachineWitness/EncodedSourceHardness premises.
-/
import PolytomyWholeBoundedPairController

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

inductive InclusionPort where
  | outer (port : RangeCursorPort)
  | inner (port : RangeCursorPort)
  deriving DecidableEq, Fintype

abbrev InclusionPorts (K : Type) := InclusionPort ↪ K

@[simp] theorem inclusionPorts_eq (p : InclusionPorts K) (a b : InclusionPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def inclusionOuterPorts (p : InclusionPorts K) : RangeCursorPorts K where
  toFun := fun j => p (.outer j)
  inj' := by intro a b h; simpa using p.injective h

def inclusionMatchPortMap : MatchCursorPort → InclusionPort
  | .wantedBlock => .outer .block
  | .wantedKind => .outer .kind
  | .cursor .rows => .outer .rows
  | .cursor .types => .outer .types
  | .cursor j => .inner j

theorem inclusionMatchPortMap_injective : Function.Injective inclusionMatchPortMap := by decide

def inclusionInnerPorts (p : InclusionPorts K) : MatchCursorPorts K where
  toFun := fun j => p (inclusionMatchPortMap j)
  inj' := fun _ _ h => inclusionMatchPortMap_injective (p.injective h)

def inclusionCheck (m A : ℕ) (target mask bits : List Bool) : Bool :=
  match filterRawLeafCell m A (readRawLeafCell bits) with
  | none => true
  | some (c, _) => (rawMarkedSuffixes target mask).any (rawCellMatch m A c.1 c.2)

/-- Restore the selected-query cache. The generic mask controller invokes
the query ONLY at cache=true; the nested membership search resets its own
cache. This is finite control, not an unbounded saved index. -/
def inclusionSelectedOp : Op K Bool (CountdownState F) :=
  .load (fun st => ((st.1.1, true), st.2))

def inclusionParsed (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  rangeLeafParsed (inclusionOuterPorts p) m A s

def inclusionSearched (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  let v := inclusionParsed p m A s
  if v.state.2 then
    cellMembershipResult (inclusionInnerPorts p) m A
      (v.stk (p (.outer .block))).length (v.stk (p (.outer .kind))).length v
  else forestSyntaxStartOp.apply v

def inclusionQueryEval (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  inclusionSelectedOp.apply (clearManyEval (rangeQueryOwned (inclusionOuterPorts p))
    (inclusionSearched p m A s))

def inclusionQueryRoutine (p : InclusionPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  let o := inclusionOuterPorts p
  RoutineComposition.seq (wordDuplicateRoutine (o .word) (o .temp) (o .source))
    (RoutineComposition.seq (typedLeafCellRoutine (rangeTypedPorts o))
      (RoutineComposition.seq
        (RoutineControl.branch Prod.snd (cellMembershipRoutine (inclusionInnerPorts p))
          (Atom.routine forestSyntaxStartOp))
        (RoutineComposition.seq (clearManyRoutine (rangeQueryOwned o)) (Atom.routine inclusionSelectedOp))))

def InclusionStackInv (p : InclusionPorts K) (m A L : ℕ) (target mask : List Bool)
    (stk : K → List Bool) : Prop :=
  ((stk (p (.outer .word))).length ≤ L ∧
    stk (p (.outer .rows)) = List.replicate m true ∧
    stk (p (.outer .types)) = List.replicate A true ∧
    stk (p (.outer .source)) = [] ∧ stk (p (.outer .block)) = [] ∧
    stk (p (.outer .kind)) = [] ∧ stk (p (.outer .temp)) = [] ∧
    stk (p (.outer .residue)) = [] ∧ stk (p (.outer .subtrahend)) = []) ∧
  stk (p (.inner .originalWord)) = target ∧ stk (p (.inner .originalMask)) = mask ∧
  target.length ≤ L ∧ mask.length ≤ target.length ∧
  ∀ j ∈ rangeAllWork (matchRangePorts (inclusionInnerPorts p)), stk j = []

theorem inclusionSearched_stacks (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) :
    (inclusionSearched p m A s).stk = (inclusionParsed p m A s).stk := by
  unfold inclusionSearched
  cases hf : (inclusionParsed p m A s).state.2 <;>
    simp [hf, cellMembershipResult, forestSyntaxStartOp, Op.apply]

theorem inclusionSearched_frame (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) :
    (inclusionSearched p m A s).state.1.1 = s.state.1.1 := by
  have hv := typedLeafCell_frame (rangeTypedPorts (inclusionOuterPorts p)) m A
    (rangeLeafPrepared (inclusionOuterPorts p) s)
  unfold inclusionSearched
  cases hf : (inclusionParsed p m A s).state.2 <;>
    simpa [hf, cellMembershipResult, forestSyntaxStartOp, Op.apply] using congrArg Prod.fst hv

theorem inclusionSearched_flag (p : InclusionPorts K) (m A L : ℕ) (target mask : List Bool)
    (s : CountdownStore K F) (hs : InclusionStackInv p m A L target mask s.stk) :
    (inclusionSearched p m A s).state.2 =
      inclusionCheck m A target mask (s.stk (p (.outer .word))) := by
  let o := inclusionOuterPorts p
  let u := rangeLeafPrepared o s
  let v := inclusionParsed p m A s
  have huSource : u.stk (o .source) = s.stk (o .word) := by
    simp [u, o, rangeLeafPrepared, wordDuplicateEval, inclusionOuterPorts, hs.1.2.2.2.1]
  have hvstk : v.stk = (rawLeafCellEval (typedRawCellPorts (rangeTypedPorts o)) u).stk :=
    typedLeafCell_stacks (rangeTypedPorts o) m A u
  have hvx (j : RangeCursorPort) : v.stk (p (.inner j)) = s.stk (p (.inner j)) := by
    rw [hvstk, rawLeafCell_extra (typedRawCellPorts (rangeTypedPorts o)) (p (.inner j))
      (by simp [o, inclusionOuterPorts, typedRawCellPorts, rangeTypedPorts])
      (by simp [o, inclusionOuterPorts, typedRawCellPorts, rangeTypedPorts])
      (by simp [o, inclusionOuterPorts, typedRawCellPorts, rangeTypedPorts])]
    simp [u, rangeLeafPrepared, wordDuplicateEval, o, inclusionOuterPorts]
  have ho := typedLeafCell_observation (rangeTypedPorts o) m A u
  rw [huSource] at ho
  unfold inclusionCheck
  rw [← ho]
  cases hf : v.state.2 <;>
    simp [inclusionSearched, rawLeafCellObservation, typedRawCellPorts, rangeTypedPorts,
      cellMembershipResult, forestSyntaxStartOp, Op.apply, inclusionInnerPorts,
      inclusionMatchPortMap, hvx, hs.2.1, hs.2.2.1, hf, v, o, inclusionOuterPorts]

theorem inclusionQuery_result (p : InclusionPorts K) (m A L : ℕ) (target mask : List Bool)
    (s : CountdownStore K F) (hs : InclusionStackInv p m A L target mask s.stk)
    (hselected : s.state.1.2 = true) :
    inclusionQueryEval p m A s =
      cellCompareFlagStore (inclusionCheck m A target mask (s.stk (p (.outer .word)))) s := by
  let o := inclusionOuterPorts p
  have hrestore := rangeLeaf_result o m A L s hs.1
  have hstack : (clearManyEval (rangeQueryOwned o) (inclusionSearched p m A s)).stk =
      (rangeLeafEval o m A s).stk := by
    simp only [rangeLeafEval, rangeQueryOwned, clearManyEval, clearStackEval,
      inclusionSearched_stacks, inclusionParsed]
  apply countdownStore_ext
  · change (((clearManyEval (rangeQueryOwned o) (inclusionSearched p m A s)).state.1.1, true),
      (clearManyEval (rangeQueryOwned o) (inclusionSearched p m A s)).state.2) = _
    rw [clearMany_state, inclusionSearched_frame, inclusionSearched_flag p m A L target mask s hs]
    exact Prod.ext (Prod.ext rfl hselected.symm) rfl
  · change (clearManyEval (rangeQueryOwned o) (inclusionSearched p m A s)).stk = s.stk
    rw [hstack, hrestore]
    rfl

theorem inclusionParsed_inner_entry (p : InclusionPorts K) (m A L : ℕ) (target mask : List Bool)
    (s : CountdownStore K F) (hs : InclusionStackInv p m A L target mask s.stk) :
    let v := inclusionParsed p m A s
    MatchAllEntry (inclusionInnerPorts p) m A
      (v.stk (p (.outer .block))).length (v.stk (p (.outer .kind))).length L v ∧
    (v.stk (p (.outer .block))).length ≤ L ∧
    (v.stk (p (.outer .kind))).length ≤ L ∧
    cleanupMass (rangeQueryOwned (inclusionOuterPorts p)) v ≤ 3 * L := by
  rcases hs with ⟨⟨hL, hm, hA, hsource, hb, hk, ht, hr, hd⟩, hword, hmask, hTL, hfit, hwork⟩
  let o := inclusionOuterPorts p
  let i := inclusionInnerPorts p
  let u := rangeLeafPrepared o s
  let v := inclusionParsed p m A s
  have huSource : u.stk (o .source) = s.stk (o .word) := by
    simp [u, rangeLeafPrepared, wordDuplicateEval, o, inclusionOuterPorts, hsource]
  have huL : (u.stk (o .source)).length ≤ L := by rw [huSource]; exact hL
  have huExtra (j : K) (hj : j ≠ o .source) : u.stk j = s.stk j := by
    simp [u, rangeLeafPrepared, wordDuplicateEval, hj]
  have hbu := (huExtra (o .block) (by simp)).trans hb
  have hku := (huExtra (o .kind) (by simp)).trans hk
  have hvstk : v.stk = (rawLeafCellEval (typedRawCellPorts (rangeTypedPorts o)) u).stk :=
    typedLeafCell_stacks (rangeTypedPorts o) m A u
  have hbds := rawLeafCell_bounds (typedRawCellPorts (rangeTypedPorts o)) L u huL hbu hku
  have hunary := rawLeafCell_unary (typedRawCellPorts (rangeTypedPorts o)) u hbu hku
  have hvx (j : K) (hjs : j ≠ o .source) (hjb : j ≠ o .block) (hjk : j ≠ o .kind) :
      v.stk j = s.stk j := by
    rw [hvstk, rawLeafCell_extra (typedRawCellPorts (rangeTypedPorts o)) j hjs hjb hjk]
    exact huExtra j hjs
  have hwv : v.stk (p (.inner .originalWord)) = target :=
    (hvx _ (by simp [o, inclusionOuterPorts]) (by simp [o, inclusionOuterPorts])
      (by simp [o, inclusionOuterPorts])).trans hword
  have hmv : v.stk (p (.inner .originalMask)) = mask :=
    (hvx _ (by simp [o, inclusionOuterPorts]) (by simp [o, inclusionOuterPorts])
      (by simp [o, inclusionOuterPorts])).trans hmask
  have hmV := (hvx (o .rows) (by simp) (by simp) (by simp)).trans hm
  have hAV := (hvx (o .types) (by simp) (by simp) (by simp)).trans hA
  have hfresh (j : K) (hj : j ∈ rangeAllWork (matchRangePorts i)) : v.stk j = [] := by
    have hjs : j ≠ o .source := by
      intro he; rw [he] at hj
      simpa [rangeAllWork, matchRangePorts, i, inclusionInnerPorts, inclusionMatchPortMap,
        o, inclusionOuterPorts] using hj
    have hjb : j ≠ o .block := by
      intro he; rw [he] at hj
      simpa [rangeAllWork, matchRangePorts, i, inclusionInnerPorts, inclusionMatchPortMap,
        o, inclusionOuterPorts] using hj
    have hjk : j ≠ o .kind := by
      intro he; rw [he] at hj
      simpa [rangeAllWork, matchRangePorts, i, inclusionInnerPorts, inclusionMatchPortMap,
        o, inclusionOuterPorts] using hj
    exact (hvx j hjs hjb hjk).trans (hwork j hj)
  have hB : v.stk (p (.outer .block)) = List.replicate (v.stk (p (.outer .block))).length true := by
    simpa only [hvstk, typedRawCellPorts, rangeTypedPorts, o, inclusionOuterPorts] using hunary.1
  have hT : v.stk (p (.outer .kind)) = List.replicate (v.stk (p (.outer .kind))).length true := by
    simpa only [hvstk, typedRawCellPorts, rangeTypedPorts, o, inclusionOuterPorts] using hunary.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_, ?_, hfresh⟩, ?_, ?_⟩
    · simpa [matchRangePorts, i, inclusionInnerPorts, inclusionMatchPortMap, hwv] using hTL
    · simpa [matchRangePorts, i, inclusionInnerPorts, inclusionMatchPortMap, hwv, hmv] using hfit
    · simpa [matchRangePorts, i, inclusionInnerPorts, inclusionMatchPortMap, o, inclusionOuterPorts] using hmV
    · simpa [matchRangePorts, i, inclusionInnerPorts, inclusionMatchPortMap, o, inclusionOuterPorts] using hAV
    · exact hB
    · exact hT
  · simpa only [hvstk, typedRawCellPorts, rangeTypedPorts, o, inclusionOuterPorts] using hbds.2.1
  · simpa only [hvstk, typedRawCellPorts, rangeTypedPorts, o, inclusionOuterPorts] using hbds.2.2
  · have hsum := Nat.add_le_add (Nat.add_le_add hbds.1 hbds.2.1) hbds.2.2
    simp only [cleanupMass, rangeQueryOwned, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hvstk]
    simp only [typedRawCellPorts, rangeTypedPorts] at hsum
    omega

def inclusionQueryBound (m A L : ℕ) : ℕ :=
  L * (34 * L + 4 * m + 4 * A + 64) + 30 * L + 4 * m + 4 * A + 56

/-- The nested membership machine is actually invoked here with the
physically parsed cell operands. Their lengths are derived, not promised
as uncharged control data. All inner and outer query work is cleaned. -/
theorem inclusionQuery_executes (p : InclusionPorts K) (m A L : ℕ) (target mask : List Bool)
    (s : CountdownStore K F) (hs : InclusionStackInv p m A L target mask s.stk)
    (hselected : s.state.1.2 = true) :
    ∃ n ≤ inclusionQueryBound m A L,
      (inclusionQueryRoutine p).Executes s
        (cellCompareFlagStore (inclusionCheck m A target mask (s.stk (p (.outer .word)))) s) n := by
  let o := inclusionOuterPorts p
  let i := inclusionInnerPorts p
  let u := rangeLeafPrepared o s
  let v := inclusionParsed p m A s
  let w := inclusionSearched p m A s
  have hquery : RangeQueryInv o m A L s := hs.1
  rcases hquery with ⟨hL, hm, hA, hsource, hb, hk, ht, hr, hd⟩
  have huSource : u.stk (o .source) = s.stk (o .word) := by
    simp [u, rangeLeafPrepared, wordDuplicateEval, hsource]
  have huL : (u.stk (o .source)).length ≤ L := by rw [huSource]; exact hL
  have huExtra (j : K) (hj : j ≠ o .source) : u.stk j = s.stk j := by
    simp [u, rangeLeafPrepared, wordDuplicateEval, hj]
  have h1 := wordDuplicate_executes (o .word) (o .temp) (o .source)
    (by simp) (by simp) (by simp) s ht
  obtain ⟨a, ha, h2⟩ := typedLeafCell_executes (rangeTypedPorts o) m A L u huL
    ((huExtra _ (by simp)).trans hm) ((huExtra _ (by simp)).trans hA)
    ((huExtra _ (by simp)).trans hb) ((huExtra _ (by simp)).trans hk)
    ((huExtra _ (by simp)).trans ht) ((huExtra _ (by simp)).trans hr)
    ((huExtra _ (by simp)).trans hd)
  obtain ⟨hinner, hB, hT, hmass⟩ := inclusionParsed_inner_entry p m A L target mask s hs
  have hbranch : ∃ n ≤ L * (34 * L + 4 * m + 4 * A + 64) + 12 * L + 19,
      (RoutineControl.branch Prod.snd (cellMembershipRoutine i) (Atom.routine forestSyntaxStartOp)).Executes
        v w n := by
    cases hf : v.state.2 with
    | false =>
        have he := RoutineControl.branch_false Prod.snd (cellMembershipRoutine i)
          (Atom.routine forestSyntaxStartOp) hf (Atom.executes forestSyntaxStartOp v)
        refine ⟨2, by omega, ?_⟩
        simpa only [w, inclusionSearched, hf, Bool.false_eq_true, ↓reduceIte] using he
    | true =>
        obtain ⟨n, hn, he⟩ := cellMembership_executes i m A
          (v.stk (p (.outer .block))).length (v.stk (p (.outer .kind))).length L v hinner
        have hb := RoutineControl.branch_true Prod.snd (cellMembershipRoutine i)
          (Atom.routine forestSyntaxStartOp) hf he
        have hcoef : 26 * L + 4 * m + 4 * A + 4 * (v.stk (p (.outer .block))).length +
            4 * (v.stk (p (.outer .kind))).length + 64 ≤ 34 * L + 4 * m + 4 * A + 64 := by omega
        have hmul := Nat.mul_le_mul_right L hcoef
        rw [Nat.mul_comm _ L, Nat.mul_comm _ L] at hmul
        refine ⟨n + 1, by omega, ?_⟩
        simpa only [w, inclusionSearched, hf, ↓reduceIte] using hb
  obtain ⟨b, hbtime, h3⟩ := hbranch
  obtain ⟨c, hc, h4⟩ := clearMany_executes (rangeQueryOwned o) w
  have hmassW : cleanupMass (rangeQueryOwned o) w ≤ 3 * L := by
    simpa only [cleanupMass, w, inclusionSearched_stacks] using hmass
  have h5 := Atom.executes (inclusionSelectedOp (K := K) (F := F))
    (clearManyEval (rangeQueryOwned o) w)
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
    (RoutineComposition.seq_executes _ _ h3 (RoutineComposition.seq_executes _ _ h4 h5)))
  change (inclusionQueryRoutine p).Executes s (inclusionQueryEval p m A s) _ at he
  rw [inclusionQuery_result p m A L target mask s hs hselected] at he
  refine ⟨3 * (s.stk (o .word)).length + 3 + (a + (b + (c + 1))), ?_, he⟩
  simp only [rangeQueryOwned, List.length_cons, List.length_nil] at hc
  unfold inclusionQueryBound
  omega

def inclusionMaskedContract (p : InclusionPorts K) (m A L : ℕ) (target mask : List Bool) :
    MaskedQueryContract (inclusionOuterPorts p) (inclusionQueryRoutine p)
      (inclusionCheck m A target mask) (InclusionStackInv p m A L target mask)
      (inclusionQueryBound m A L) where
  positive := by unfold inclusionQueryBound; omega
  query_executes s hs hselected := inclusionQuery_executes p m A L target mask s hs hselected
  cursor_closed stk hs := by
    have ht : (stk (p (.outer .word))).tail.length ≤ (stk (p (.outer .word))).length := by
      cases stk (p (.outer .word)) <;> simp
    unfold InclusionStackInv at hs ⊢
    simpa [inclusionOuterPorts, rangeAllWork, matchRangePorts, inclusionInnerPorts,
      inclusionMatchPortMap] using And.intro (And.intro (ht.trans hs.1.1) hs.1.2) hs.2
  counter_closed stk hs := by
    simpa [InclusionStackInv, inclusionOuterPorts, rangeAllWork, matchRangePorts,
      inclusionInnerPorts, inclusionMatchPortMap] using hs

def InclusionEntry (p : InclusionPorts K) (m A L : ℕ) (target mask : List Bool)
    (s : CountdownStore K F) : Prop :=
  RangeAllEntry (inclusionOuterPorts p) m A L s ∧
  s.stk (p (.inner .originalWord)) = target ∧ s.stk (p (.inner .originalMask)) = mask ∧
  target.length ≤ L ∧ mask.length ≤ target.length ∧
  ∀ j ∈ rangeAllWork (matchRangePorts (inclusionInnerPorts p)), s.stk j = []

theorem inclusion_prepared_inv (p : InclusionPorts K) (m A L : ℕ) (target mask : List Bool)
    (s : CountdownStore K F) (hs : InclusionEntry p m A L target mask s) :
    InclusionStackInv p m A L target mask (rangeAllPrepared (inclusionOuterPorts p) s).stk := by
  rcases hs with ⟨⟨hL, hfit, hm, hA, hwork⟩, hword, hmask, hTL, hTfit, hinner⟩
  let o := inclusionOuterPorts p
  have hf (j : RangeCursorPort) (hj : o j ∈ rangeAllWork o) : s.stk (o j) = [] := hwork _ hj
  have hustk := rangeAllPrepared_stacks o s (hf .word (by simp [rangeAllWork]))
    (hf .mask (by simp [rangeAllWork])) (hf .counter (by simp [rangeAllWork]))
  rw [hustk]
  have hsource := hf .source (by simp [rangeAllWork])
  have hblock := hf .block (by simp [rangeAllWork])
  have hkind := hf .kind (by simp [rangeAllWork])
  have htemp := hf .temp (by simp [rangeAllWork])
  have hresidue := hf .residue (by simp [rangeAllWork])
  have hsub := hf .subtrahend (by simp [rangeAllWork])
  unfold InclusionStackInv
  simpa [o, inclusionOuterPorts, rangeAllWork, matchRangePorts, inclusionInnerPorts,
    inclusionMatchPortMap] using
    And.intro (And.intro hL ⟨hm, hA, hsource, hblock, hkind, htemp, hresidue, hsub⟩)
      ⟨hword, hmask, hTL, hTfit, hinner⟩

def cellSubsetRoutine (p : InclusionPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  maskedAllRoutine (inclusionOuterPorts p) (inclusionQueryRoutine p)

def cellSubsetResult (p : InclusionPorts K) (m A : ℕ) (target mask : List Bool)
    (s : CountdownStore K F) :=
  maskedAllResult (inclusionOuterPorts p) (inclusionCheck m A target mask) s

def cellSubsetBound (m A L : ℕ) : ℕ := L * (inclusionQueryBound m A L + 7) + 12 * L + 17

/-- Complete universal leaf-inclusion scan, including the actual nested
existential search for each candidate and cleanup on both failure paths.
No global uniqueness or clade correspondence is inferred from inclusion. -/
theorem cellSubset_executes (p : InclusionPorts K) (m A L : ℕ) (target mask : List Bool)
    (s : CountdownStore K F) (hs : InclusionEntry p m A L target mask s) :
    ∃ n ≤ cellSubsetBound m A L,
      (cellSubsetRoutine p).Executes s (cellSubsetResult p m A target mask s) n := by
  let o := inclusionOuterPorts p
  have hf (j : RangeCursorPort) (hj : o j ∈ rangeAllWork o) : s.stk (o j) = [] := hs.1.2.2.2.2 _ hj
  exact maskedAll_executes o (inclusionQueryRoutine p) (inclusionCheck m A target mask)
    (InclusionStackInv p m A L target mask) (inclusionQueryBound m A L) L
    (inclusionMaskedContract p m A L target mask) s hs.1.1 hs.1.2.1
    (hf .word (by simp [rangeAllWork])) (hf .mask (by simp [rangeAllWork]))
    (hf .counter (by simp [rangeAllWork])) (hf .temp (by simp [rangeAllWork]))
    (inclusion_prepared_inv p m A L target mask s hs)

def inclusionSwapMap : InclusionPort → InclusionPort
  | .outer .originalWord => .inner .originalWord
  | .outer .originalMask => .inner .originalMask
  | .inner .originalWord => .outer .originalWord
  | .inner .originalMask => .outer .originalMask
  | j => j

theorem inclusionSwapMap_involutive : Function.Involutive inclusionSwapMap := by decide

def inclusionSwapPorts (p : InclusionPorts K) : InclusionPorts K where
  toFun := fun j => p (inclusionSwapMap j)
  inj' := by
    intro a b h
    have hh := congrArg inclusionSwapMap (p.injective h)
    simpa only [inclusionSwapMap_involutive] using hh

def CellSetEntry (p : InclusionPorts K) (m A L : ℕ) (s : CountdownStore K F) : Prop :=
  (s.stk (p (.outer .originalWord))).length ≤ L ∧
  (s.stk (p (.outer .originalMask))).length ≤ (s.stk (p (.outer .originalWord))).length ∧
  (s.stk (p (.inner .originalWord))).length ≤ L ∧
  (s.stk (p (.inner .originalMask))).length ≤ (s.stk (p (.inner .originalWord))).length ∧
  s.stk (p (.outer .rows)) = List.replicate m true ∧
  s.stk (p (.outer .types)) = List.replicate A true ∧
  ∀ j ∈ rangeAllWork (inclusionOuterPorts p) ++ rangeAllWork (matchRangePorts (inclusionInnerPorts p)),
    s.stk j = []

theorem cellSetEntry_first (p : InclusionPorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : CellSetEntry p m A L s) :
    InclusionEntry p m A L (s.stk (p (.inner .originalWord))) (s.stk (p (.inner .originalMask))) s := by
  rcases hs with ⟨hL, hfit, hTL, hTfit, hm, hA, hwork⟩
  exact ⟨⟨hL, hfit, hm, hA, fun j hj => hwork j (List.mem_append.mpr (Or.inl hj))⟩,
    rfl, rfl, hTL, hTfit, fun j hj => hwork j (List.mem_append.mpr (Or.inr hj))⟩

theorem cellSetEntry_swap (p : InclusionPorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : CellSetEntry p m A L s) : CellSetEntry (inclusionSwapPorts p) m A L s := by
  rcases hs with ⟨hL, hfit, hTL, hTfit, hm, hA, hwork⟩
  refine ⟨hTL, hTfit, hL, hfit, hm, hA, ?_⟩
  simpa [rangeAllWork, inclusionOuterPorts, matchRangePorts, inclusionInnerPorts,
    inclusionMatchPortMap, inclusionSwapPorts, inclusionSwapMap] using hwork

def cellSetRoutine (p : InclusionPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (cellSubsetRoutine p)
    (RoutineControl.branch Prod.snd (cellSubsetRoutine (inclusionSwapPorts p)) (Atom.routine cleanupNoop))

def cellSetAnswer (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) : Bool :=
  (rawMarkedSuffixes (s.stk (p (.outer .originalWord))) (s.stk (p (.outer .originalMask)))).all
    (inclusionCheck m A (s.stk (p (.inner .originalWord))) (s.stk (p (.inner .originalMask)))) &&
  (rawMarkedSuffixes (s.stk (p (.inner .originalWord))) (s.stk (p (.inner .originalMask)))).all
    (inclusionCheck m A (s.stk (p (.outer .originalWord))) (s.stk (p (.outer .originalMask))))

def cellSetResult (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨((s.state.1.1, false), cellSetAnswer p m A s), s.stk⟩

def cellSetWordsAnswer (m A : ℕ) (left leftMask right rightMask : List Bool) : Bool :=
  (rawMarkedSuffixes left leftMask).all (inclusionCheck m A right rightMask) &&
  (rawMarkedSuffixes right rightMask).all (inclusionCheck m A left leftMask)

theorem cellSetAnswer_words (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) :
    cellSetAnswer p m A s = cellSetWordsAnswer m A
      (s.stk (p (.outer .originalWord))) (s.stk (p (.outer .originalMask)))
      (s.stk (p (.inner .originalWord))) (s.stk (p (.inner .originalMask))) := rfl

/-- BOTH directions are actual nested scan programs. The second is guarded
by the first universal result; its local membership resets cannot turn a
failed first inclusion into success. All data tapes are exactly restored. -/
theorem cellSet_executes (p : InclusionPorts K) (m A L : ℕ) (s : CountdownStore K F)
    (hs : CellSetEntry p m A L s) :
    ∃ n ≤ 2 * cellSubsetBound m A L + 1,
      (cellSetRoutine p).Executes s (cellSetResult p m A s) n := by
  let target := s.stk (p (.inner .originalWord))
  let mask := s.stk (p (.inner .originalMask))
  let u := cellSubsetResult p m A target mask s
  obtain ⟨a, ha, h1⟩ := cellSubset_executes p m A L target mask s (cellSetEntry_first p m A L s hs)
  have hu : CellSetEntry (inclusionSwapPorts p) m A L u := cellSetEntry_swap p m A L s hs
  cases hf : u.state.2 with
  | false =>
      have h2 := RoutineControl.branch_false Prod.snd (cellSubsetRoutine (inclusionSwapPorts p))
        (Atom.routine cleanupNoop) hf (Atom.executes cleanupNoop u)
      have he := RoutineComposition.seq_executes _ _ h1 h2
      have hresult : u = cellSetResult p m A s := by
        apply countdownStore_ext
        · have hfalse : cellSetAnswer p m A s = false := by
            unfold cellSetAnswer
            change u.state.2 && _ = false
            simp [hf]
          change ((s.state.1.1, false), u.state.2) = ((s.state.1.1, false), cellSetAnswer p m A s)
          rw [hf, hfalse]
        · rfl
      have hpos : 1 ≤ cellSubsetBound m A L := by unfold cellSubsetBound; omega
      refine ⟨a + 2, by omega, ?_⟩
      simpa only [cellSetRoutine, cleanupNoop, Op.apply, hresult] using he
  | true =>
      obtain ⟨b, hb, h2⟩ := cellSubset_executes (inclusionSwapPorts p) m A L
        (u.stk ((inclusionSwapPorts p) (.inner .originalWord)))
        (u.stk ((inclusionSwapPorts p) (.inner .originalMask))) u
        (cellSetEntry_first (inclusionSwapPorts p) m A L u hu)
      have hbranch := RoutineControl.branch_true Prod.snd (cellSubsetRoutine (inclusionSwapPorts p))
        (Atom.routine cleanupNoop) hf h2
      have he := RoutineComposition.seq_executes _ _ h1 hbranch
      have hresult : cellSubsetResult (inclusionSwapPorts p) m A
          (u.stk ((inclusionSwapPorts p) (.inner .originalWord)))
          (u.stk ((inclusionSwapPorts p) (.inner .originalMask))) u = cellSetResult p m A s := by
        apply countdownStore_ext
        · have hfirst : (rawMarkedSuffixes (s.stk (p (.outer .originalWord)))
              (s.stk (p (.outer .originalMask)))).all (inclusionCheck m A target mask) = true := hf
          simp [cellSubsetResult, maskedAllResult, cellSetResult, cellSetAnswer, u,
            inclusionOuterPorts, inclusionSwapPorts, inclusionSwapMap, hfirst, target, mask]
        · rfl
      rw [hresult] at he
      exact ⟨a + (b + 1), by omega, he⟩

def inclusionCodeCheck (m A : ℕ) (target mask : List Bool) (c : ℕ × ℕ) : Bool :=
  if c.1 ≤ m ∧ c.2 < A then (rawMarkedSuffixes target mask).any (rawCellMatch m A c.1 c.2) else true

theorem inclusionCheck_leaf (m A : ℕ) (target mask : List Bool) (c : ℕ × ℕ) (rest : List Bool) :
    inclusionCheck m A target mask (rawCellTreeBits (.leaf c) ++ rest) =
      inclusionCodeCheck m A target mask c := by
  by_cases hv : c.1 ≤ m ∧ c.2 < A <;>
    simp [inclusionCheck, inclusionCodeCheck, rawCellTreeBits, readRawLeafCell,
      filterRawLeafCell, List.append_assoc, readUnaryFrame_encode, hv]

theorem inclusionCheck_node (m A : ℕ) (target mask : List Bool)
    (l r : BTree (ℕ × ℕ)) (rest : List Bool) :
    inclusionCheck m A target mask (rawCellTreeBits (.node l r) ++ rest) = true := rfl

theorem inclusionCheck_views (m A : ℕ) (target mask : List Bool)
    (R : BTree (ℕ × ℕ)) (rest : List Bool) :
    ((rawNodeViews R rest).map rawViewSuffix).all (inclusionCheck m A target mask) =
      (scanLeaves R).all (inclusionCodeCheck m A target mask) := by
  induction R generalizing rest with
  | leaf c =>
      simpa only [rawNodeViews, rawViewSuffix, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, Bool.and_true, scanLeaves] using inclusionCheck_leaf m A target mask c rest
  | node l r ihl ihr =>
      simp only [rawNodeViews, List.map_cons, List.map_append, List.all_cons,
        List.all_append, rawViewSuffix, inclusionCheck_node, Bool.true_and, scanLeaves, ihl, ihr]

theorem inclusionCheck_forest (m A : ℕ) (target mask : List Bool)
    (Rs : List (BTree (ℕ × ℕ))) (rest : List Bool) :
    (rawMarkedSuffixes (rawForestWord Rs ++ rest) (rawForestNodeMask Rs)).all
      (inclusionCheck m A target mask) =
      (Rs.flatMap scanLeaves).all (inclusionCodeCheck m A target mask) := by
  induction Rs with
  | nil => simp [rawForestWord, rawForestNodeMask, rawMarkedSuffixes]
  | cons R Rs ih =>
      have hsplit : rawMarkedSuffixes (rawForestWord (R :: Rs) ++ rest) (rawForestNodeMask (R :: Rs)) =
          (rawNodeViews R (rawForestWord Rs ++ rest)).map rawViewSuffix ++
            rawMarkedSuffixes (rawForestWord Rs ++ rest) (rawForestNodeMask Rs) := by
        simpa only [rawForestWord, rawForestNodeMask, List.flatMap_cons, List.append_assoc] using
          rawMarkedSuffixes_tree R (rawForestWord Rs ++ rest) (rawForestNodeMask Rs)
      rw [hsplit, List.all_append, inclusionCheck_views, ih, List.flatMap_cons, List.all_append]

theorem bool_eq_of_true_iff (a b : Bool) (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The range hypotheses are necessary: the local skip branch is for
internal nodes, not a way to accept an invalid leaf. The preceding actual
grammar/range phase supplies precisely these hypotheses before this scan. -/
theorem inclusionCheck_forest_valid (N m : ℕ) (Rs Ss : List (BTree (ℕ × ℕ)))
    (rest targetRest : List Bool)
    (hR : ∀ R ∈ Rs, rawTreeValid N m R) (hS : ∀ S ∈ Ss, rawTreeValid N m S) :
    (rawMarkedSuffixes (rawForestWord Rs ++ rest) (rawForestNodeMask Rs)).all
      (inclusionCheck m (N + m * N + 3) (rawForestWord Ss ++ targetRest) (rawForestNodeMask Ss)) =
      scanSubset (Rs.flatMap scanLeaves) (Ss.flatMap scanLeaves) := by
  apply bool_eq_of_true_iff
  rw [inclusionCheck_forest]
  simp only [scanSubset, List.all_eq_true, decide_eq_true_eq]
  have hvalid (c : ℕ × ℕ) (hc : c ∈ Rs.flatMap scanLeaves) : c.1 ≤ m ∧ c.2 < N + m * N + 3 := by
    obtain ⟨R, hmem, hleaf⟩ := List.mem_flatMap.mp hc
    exact hR R hmem c hleaf
  constructor
  · intro h c hc
    have hh := h c hc
    simp only [inclusionCodeCheck, hvalid c hc, ↓reduceIte] at hh
    exact (rawCellMembership_forest_valid N m c.1 c.2 Ss targetRest hS).mp hh
  · intro h c hc
    simp only [inclusionCodeCheck, hvalid c hc, ↓reduceIte]
    exact (rawCellMembership_forest_valid N m c.1 c.2 Ss targetRest hS).mpr (h c hc)

theorem cellSetAnswer_raw_forests (p : InclusionPorts K) (N m : ℕ)
    (s : CountdownStore K F) (Rs Ss : List (BTree (ℕ × ℕ))) (rest targetRest : List Bool)
    (hw : s.stk (p (.outer .originalWord)) = rawForestWord Rs ++ rest)
    (hm : s.stk (p (.outer .originalMask)) = rawForestNodeMask Rs)
    (htw : s.stk (p (.inner .originalWord)) = rawForestWord Ss ++ targetRest)
    (htm : s.stk (p (.inner .originalMask)) = rawForestNodeMask Ss)
    (hR : ∀ R ∈ Rs, rawTreeValid N m R) (hS : ∀ S ∈ Ss, rawTreeValid N m S) :
    cellSetAnswer p m (N + m * N + 3) s = scanSetEq (Rs.flatMap scanLeaves) (Ss.flatMap scanLeaves) := by
  unfold cellSetAnswer
  rw [hw, hm, htw, htm, inclusionCheck_forest_valid N m Rs Ss rest targetRest hR hS,
    inclusionCheck_forest_valid N m Ss Rs targetRest rest hS hR]
  rfl

/-- BOTH forests are reconstructed from actual parser/range observations.
This is the exact set predicate, not equality of leaf type multisets. -/
theorem cellSetAnswer_observed_forests (p : InclusionPorts K) (N m q r : ℕ)
    (s : CountdownStore K F) (rest targetRest : List Bool)
    (hparse : rawForestMaskParse (s.stk (p (.outer .originalWord))).length q
      (s.stk (p (.outer .originalWord))) = some (rest, s.stk (p (.outer .originalMask))))
    (htparse : rawForestMaskParse (s.stk (p (.inner .originalWord))).length r
      (s.stk (p (.inner .originalWord))) = some (targetRest, s.stk (p (.inner .originalMask))))
    (hcheck : forestMaskCellCheck N m (s.stk (p (.outer .originalWord)))
      (s.stk (p (.outer .originalMask))) = true)
    (htcheck : forestMaskCellCheck N m (s.stk (p (.inner .originalWord)))
      (s.stk (p (.inner .originalMask))) = true) :
    ∃ Rs Ss : List (BTree (ℕ × ℕ)), Rs.length = q ∧ Ss.length = r ∧
      s.stk (p (.outer .originalWord)) = rawForestWord Rs ++ rest ∧
      s.stk (p (.inner .originalWord)) = rawForestWord Ss ++ targetRest ∧
      (∀ R ∈ Rs, rawTreeValid N m R) ∧ (∀ S ∈ Ss, rawTreeValid N m S) ∧
      cellSetAnswer p m (N + m * N + 3) s = scanSetEq (Rs.flatMap scanLeaves) (Ss.flatMap scanLeaves) := by
  obtain ⟨Rs, hq, hw, hm⟩ := (rawForestMaskParse_all_words _ rest _ q).mp hparse
  obtain ⟨Ss, hr, htw, htm⟩ := (rawForestMaskParse_all_words _ targetRest _ r).mp htparse
  have hR := (forestMaskCellCheck_iff N m Rs rest).mp (by simpa only [← hw, ← hm] using hcheck)
  have hS := (forestMaskCellCheck_iff N m Ss targetRest).mp (by simpa only [← htw, ← htm] using htcheck)
  exact ⟨Rs, Ss, hq, hr, hw, htw, hR, hS,
    cellSetAnswer_raw_forests p N m s Rs Ss rest targetRest hw hm htw htm hR hS⟩

theorem rawTreeCodes_leaves {N m : ℕ} (T : BTree (Cell N m)) :
    scanLeaves (rawTreeCodes T) = (scanLeaves T).map cellNatCode := by
  induction T with
  | leaf a => rfl
  | node l r ihl ihr => simp only [rawTreeCodes, scanLeaves, List.map_append, ihl, ihr]

theorem rawForestCodes_leaves {N m : ℕ} (Ts : List (BTree (Cell N m))) :
    (Ts.map rawTreeCodes).flatMap scanLeaves = (Ts.flatMap scanLeaves).map cellNatCode := by
  induction Ts with
  | nil => rfl
  | cons T Ts ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append, rawTreeCodes_leaves, ih]

theorem scanSubset_map_injective {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (hf : Function.Injective f) (xs ys : List X) :
    scanSubset (xs.map f) (ys.map f) = scanSubset xs ys := by
  apply bool_eq_of_true_iff
  simp only [scanSubset, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h x hx
    have hm := h (f x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
    obtain ⟨y, hy, he⟩ := List.mem_map.mp hm
    have hxy := hf he
    simpa only [hxy] using hy
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact List.mem_map.mpr ⟨x, h x hx, rfl⟩

theorem scanSetEq_map_injective {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (hf : Function.Injective f) (xs ys : List X) :
    scanSetEq (xs.map f) (ys.map f) = scanSetEq xs ys := by
  rw [scanSetEq, scanSubset_map_injective f hf, scanSubset_map_injective f hf]
  rfl

/-- End-to-end semantic boundary for this COMPONENT: the actual paid
two-direction scan returns exactly the original typed CELL-set predicate
on the two forests reconstructed from parser/range observations. This is
not a constructor-image promise and does not replace any clade quantifier.
-/
theorem cellSetAnswer_observed_typed_forests (p : InclusionPorts K) (N m q r : ℕ)
    (s : CountdownStore K F) (rest targetRest : List Bool)
    (hparse : rawForestMaskParse (s.stk (p (.outer .originalWord))).length q
      (s.stk (p (.outer .originalWord))) = some (rest, s.stk (p (.outer .originalMask))))
    (htparse : rawForestMaskParse (s.stk (p (.inner .originalWord))).length r
      (s.stk (p (.inner .originalWord))) = some (targetRest, s.stk (p (.inner .originalMask))))
    (hcheck : forestMaskCellCheck N m (s.stk (p (.outer .originalWord)))
      (s.stk (p (.outer .originalMask))) = true)
    (htcheck : forestMaskCellCheck N m (s.stk (p (.inner .originalWord)))
      (s.stk (p (.inner .originalMask))) = true) :
    ∃ Ts Us : List (BTree (Cell N m)), Ts.length = q ∧ Us.length = r ∧
      s.stk (p (.outer .originalWord)) = Ts.flatMap treeBits ++ rest ∧
      s.stk (p (.inner .originalWord)) = Us.flatMap treeBits ++ targetRest ∧
      cellSetAnswer p m (N + m * N + 3) s = scanSetEq (Ts.flatMap scanLeaves) (Us.flatMap scanLeaves) := by
  obtain ⟨Rs, Ss, hq, hr, hw, htw, hR, hS, hans⟩ :=
    cellSetAnswer_observed_forests p N m q r s rest targetRest hparse htparse hcheck htcheck
  obtain ⟨Ts, hTs⟩ := (rawForestValid_iff_typed N m Rs).mp hR
  obtain ⟨Us, hUs⟩ := (rawForestValid_iff_typed N m Ss).mp hS
  have hq' : Ts.length = q := by simpa only [← hTs, List.length_map] using hq
  have hr' : Us.length = r := by simpa only [← hUs, List.length_map] using hr
  refine ⟨Ts, Us, hq', hr', ?_, ?_, ?_⟩
  · simpa only [← hTs, rawForestWord_map_codes] using hw
  · simpa only [← hUs, rawForestWord_map_codes] using htw
  · rw [hans, ← hTs, ← hUs, rawForestCodes_leaves, rawForestCodes_leaves,
      scanSetEq_map_injective cellNatCode (cellNatCode_injective N m)]

/- Both directional scans and their exact typed CELL-set interpretation
are now composed in source. They still must be placed in the final fixed
inventory, using masks from actual parsing or selected-subtree queries.
Uniqueness, the EVERY fixed-clade / EXISTS certificate-clade nest, target
markers/mixedness/coverage, the actual root-inclusive score, headers and
clean halt remain separate unclosed full-controller clauses. This packet
does not supply VerifierMachineWitness or EncodedSourceHardness, and it
does not carry any compilation or machine-verification claim.
-/

end PolytomyReductionModel.WholeVerifierController
