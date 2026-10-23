/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual terminal-TYPE membership/counting for the same restricted verifier.
Unlike CELL uniqueness/clade equality, this query ignores the block tag
AFTER checking that both fields are in the original permitted ranges.

The intended complete chain is physical type enumeration, distinct-type
count, EACH-row marker guard, EVERY-target-internal mixedness, global
coverage and EVERY-certificate-internal/root-inclusive actual star score.
This source must continue through those joins, not stop at membership.

All bounds are parameterized in physical m,A,L. Bounded binary-header
guards must execute BEFORE computing/materializing A=N+mN+3. No unary-size
assumption or A<=target-length conclusion is granted before its guards.
-/
import PolytomyMaskedTally
import Mathlib.Data.List.Dedup

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

def rawTypeMatch (m A T : ℕ) (bits : List Bool) : Bool :=
  match filterRawLeafCell m A (readRawLeafCell bits) with
  | none => false
  | some (c, _) => decide (c.2 = T)

def typeLeafCompared (p : MatchCursorPorts K) (m A T : ℕ) (s : CountdownStore K F) :=
  let v := rangeLeafParsed (matchRangePorts p) m A s
  guardedCellCompareEval .eq T (v.stk (p (.cursor .kind))).length v

def typeLeafEval (p : MatchCursorPorts K) (m A T : ℕ) (s : CountdownStore K F) :=
  searchFlipOp.apply (clearManyEval (rangeQueryOwned (matchRangePorts p)) (typeLeafCompared p m A T s))

def typeLeafRoutine (p : MatchCursorPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  let r := matchRangePorts p
  RoutineComposition.seq (wordDuplicateRoutine (r .word) (r .temp) (r .source))
    (RoutineComposition.seq (typedLeafCellRoutine (rangeTypedPorts r))
      (RoutineComposition.seq (guardedCellCompareRoutine (matchComparePorts p true) .eq)
        (RoutineComposition.seq (clearManyRoutine (rangeQueryOwned r)) (Atom.routine searchFlipOp))))

def TypeQueryInv (p : MatchCursorPorts K) (m A T L : ℕ) (s : CountdownStore K F) : Prop :=
  RangeQueryInv (matchRangePorts p) m A L s ∧ s.stk (p .wantedKind) = List.replicate T true

theorem typeLeafCompared_stacks (p : MatchCursorPorts K) (m A T : ℕ) (s : CountdownStore K F) :
    (typeLeafCompared p m A T s).stk = (rangeLeafParsed (matchRangePorts p) m A s).stk := by
  unfold typeLeafCompared
  rw [guardedCellCompare_stacks]

theorem typeLeafCompared_flag (p : MatchCursorPorts K) (m A T : ℕ)
    (s : CountdownStore K F) (hz : s.stk (p (.cursor .source)) = []) :
    (typeLeafCompared p m A T s).state.2 = rawTypeMatch m A T (s.stk (p (.cursor .word))) := by
  let r := matchRangePorts p
  let u := rangeLeafPrepared r s
  let v := rangeLeafParsed r m A s
  have hu : u.stk (r .source) = s.stk (r .word) := by
    simp [u, r, rangeLeafPrepared, wordDuplicateEval, matchRangePorts, hz]
  have ho := typedLeafCell_observation (rangeTypedPorts r) m A u
  rw [hu] at ho
  unfold rawTypeMatch
  rw [← ho]
  change (guardedCellCompareEval .eq T (v.stk (r .kind)).length v).state.2 = _
  rw [guardedCellCompare_flag]
  cases hf : v.state.2 <;>
    simp [rawLeafCellObservation, typedRawCellPorts, rangeTypedPorts,
      cellCompareAnswer, hf, r, matchRangePorts]

theorem typeLeaf_result (p : MatchCursorPorts K) (m A T L : ℕ) (s : CountdownStore K F)
    (hs : TypeQueryInv p m A T L s) :
    typeLeafEval p m A T s = cellCompareFlagStore
      (!rawTypeMatch m A T (s.stk (p (.cursor .word)))) s := by
  let r := matchRangePorts p
  have hrestore := rangeLeaf_result r m A L s hs.1
  have hstack : (clearManyEval (rangeQueryOwned r) (typeLeafCompared p m A T s)).stk =
      (rangeLeafEval r m A s).stk := by
    change (clearManyEval (rangeQueryOwned r) (typeLeafCompared p m A T s)).stk =
      (clearManyEval (rangeQueryOwned r) (rangeLeafParsed r m A s)).stk
    simp only [rangeQueryOwned, clearManyEval, clearStackEval, typeLeafCompared_stacks]
  have hframe : (typeLeafCompared p m A T s).state.1 = s.state.1 := by
    unfold typeLeafCompared
    rw [guardedCellCompare_frame]
    exact typedLeafCell_frame (rangeTypedPorts r) m A (rangeLeafPrepared r s)
  apply countdownStore_ext
  · change ((clearManyEval (rangeQueryOwned r) (typeLeafCompared p m A T s)).state.1,
      !(clearManyEval (rangeQueryOwned r) (typeLeafCompared p m A T s)).state.2) = _
    rw [clearMany_state, hframe, typeLeafCompared_flag p m A T s hs.1.2.2.2.1]
    rfl
  · change (clearManyEval (rangeQueryOwned r) (typeLeafCompared p m A T s)).stk = s.stk
    rw [hstack, hrestore]
    rfl

def typeLeafBound (m A T L : ℕ) : ℕ := 22 * L + 4 * m + 4 * A + 4 * T + 47

theorem typeLeaf_executes (p : MatchCursorPorts K) (m A T L : ℕ) (s : CountdownStore K F)
    (hs : TypeQueryInv p m A T L s) :
    ∃ n ≤ typeLeafBound m A T L,
      (typeLeafRoutine p).Executes s
        (cellCompareFlagStore (!rawTypeMatch m A T (s.stk (p (.cursor .word)))) s) n := by
  rcases hs with ⟨⟨hL, hm, hA, hsource, hb, hk, ht, hr, hd⟩, hT⟩
  let r := matchRangePorts p
  let u := rangeLeafPrepared r s
  let v := rangeLeafParsed r m A s
  let z := typeLeafCompared p m A T s
  have huSource : u.stk (r .source) = s.stk (r .word) := by
    simp [u, rangeLeafPrepared, wordDuplicateEval, hsource]
  have huExtra (j : K) (hj : j ≠ r .source) : u.stk j = s.stk j := by
    simp [u, rangeLeafPrepared, wordDuplicateEval, hj]
  have huL : (u.stk (r .source)).length ≤ L := by rw [huSource]; exact hL
  have hbu := (huExtra (r .block) (by simp)).trans hb
  have hku := (huExtra (r .kind) (by simp)).trans hk
  have h1 := wordDuplicate_executes (r .word) (r .temp) (r .source)
    (by simp) (by simp) (by simp) s ht
  obtain ⟨a, ha, h2⟩ := typedLeafCell_executes (rangeTypedPorts r) m A L u huL
    ((huExtra _ (by simp)).trans hm) ((huExtra _ (by simp)).trans hA)
    hbu hku ((huExtra _ (by simp)).trans ht)
    ((huExtra _ (by simp)).trans hr) ((huExtra _ (by simp)).trans hd)
  have hbds := rawLeafCell_bounds (typedRawCellPorts (rangeTypedPorts r)) L u huL hbu hku
  have hunary := rawLeafCell_unary (typedRawCellPorts (rangeTypedPorts r)) u hbu hku
  have hvstk : v.stk = (rawLeafCellEval (typedRawCellPorts (rangeTypedPorts r)) u).stk :=
    typedLeafCell_stacks (rangeTypedPorts r) m A u
  have hvx (j : K) (hjs : j ≠ r .source) (hjb : j ≠ r .block) (hjk : j ≠ r .kind) :
      v.stk j = s.stk j := by
    rw [hvstk, rawLeafCell_extra (typedRawCellPorts (rangeTypedPorts r)) j hjs hjb hjk]
    exact huExtra j hjs
  have hvk : v.stk (r .kind) = List.replicate (v.stk (r .kind)).length true := by
    simpa only [hvstk, typedRawCellPorts, rangeTypedPorts] using hunary.2
  have hvT : v.stk (p .wantedKind) = List.replicate T true :=
    (hvx _ (by simp [r, matchRangePorts]) (by simp [r, matchRangePorts])
      (by simp [r, matchRangePorts])).trans hT
  have hvt := (hvx (r .temp) (by simp) (by simp) (by simp)).trans ht
  have hvr := (hvx (r .residue) (by simp) (by simp) (by simp)).trans hr
  have hvd := (hvx (r .subtrahend) (by simp) (by simp) (by simp)).trans hd
  obtain ⟨b, hbt, h3⟩ := guardedCellCompare_executes (matchComparePorts p true) .eq
    T (v.stk (r .kind)).length v
    (by simpa [matchComparePorts] using hvT)
    (by simpa [matchComparePorts, r, matchRangePorts] using hvk)
    (by simpa [matchComparePorts, r, matchRangePorts] using hvr)
    (by simpa [matchComparePorts, r, matchRangePorts] using hvd)
    (by simpa [matchComparePorts, r, matchRangePorts] using hvt)
  obtain ⟨c, hc, h4⟩ := clearMany_executes (rangeQueryOwned r) z
  have h5 := Atom.executes (searchFlipOp (K := K) (F := F)) (clearManyEval (rangeQueryOwned r) z)
  have hmass : cleanupMass (rangeQueryOwned r) z ≤ 3 * L := by
    have hsum := Nat.add_le_add (Nat.add_le_add hbds.1 hbds.2.1) hbds.2.2
    simp only [cleanupMass, rangeQueryOwned, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, z, typeLeafCompared_stacks, hvstk]
    simp only [typedRawCellPorts, rangeTypedPorts] at hsum
    omega
  have hkL : (v.stk (r .kind)).length ≤ L := by
    simpa only [hvstk, typedRawCellPorts, rangeTypedPorts] using hbds.2.2
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
    (RoutineComposition.seq_executes _ _ h3 (RoutineComposition.seq_executes _ _ h4 h5)))
  change (typeLeafRoutine p).Executes s (typeLeafEval p m A T s) _ at he
  rw [typeLeaf_result p m A T L s ⟨⟨hL, hm, hA, hsource, hb, hk, ht, hr, hd⟩, hT⟩] at he
  refine ⟨3 * (s.stk (r .word)).length + 3 + (a + (b + (c + 1))), ?_, he⟩
  simp only [rangeQueryOwned, List.length_cons, List.length_nil] at hc
  unfold typeLeafBound
  omega

def TypeStackInv (p : MatchCursorPorts K) (m A T L : ℕ) (stk : K → List Bool) : Prop :=
  ((stk (p (.cursor .word))).length ≤ L ∧
    stk (p (.cursor .rows)) = List.replicate m true ∧
    stk (p (.cursor .types)) = List.replicate A true ∧
    stk (p (.cursor .source)) = [] ∧ stk (p (.cursor .block)) = [] ∧
    stk (p (.cursor .kind)) = [] ∧ stk (p (.cursor .temp)) = [] ∧
    stk (p (.cursor .residue)) = [] ∧ stk (p (.cursor .subtrahend)) = []) ∧
  stk (p .wantedKind) = List.replicate T true

def typeMaskedContract (p : MatchCursorPorts K) (m A T L : ℕ) :
    MaskedQueryContract (matchRangePorts p) (typeLeafRoutine p)
      (fun bits => !rawTypeMatch m A T bits) (TypeStackInv p m A T L)
      (typeLeafBound m A T L) where
  positive := by unfold typeLeafBound; omega
  query_executes s hs hselected := typeLeaf_executes p m A T L s hs
  cursor_closed stk hs := by
    have ht : (stk (p (.cursor .word))).tail.length ≤ (stk (p (.cursor .word))).length := by
      cases stk (p (.cursor .word)) <;> simp
    unfold TypeStackInv at hs ⊢
    simpa [matchRangePorts] using And.intro (And.intro (ht.trans hs.1.1) hs.1.2) hs.2
  counter_closed stk hs := by simpa [TypeStackInv, matchRangePorts] using hs

def TypeAllEntry (p : MatchCursorPorts K) (m A T L : ℕ) (s : CountdownStore K F) : Prop :=
  RangeAllEntry (matchRangePorts p) m A L s ∧ s.stk (p .wantedKind) = List.replicate T true

theorem typeAll_prepared_inv (p : MatchCursorPorts K) (m A T L : ℕ)
    (s : CountdownStore K F) (hs : TypeAllEntry p m A T L s) :
    TypeStackInv p m A T L (rangeAllPrepared (matchRangePorts p) s).stk := by
  rcases hs with ⟨⟨hL, hfit, hm, hA, hwork⟩, hT⟩
  let r := matchRangePorts p
  have hf (j : RangeCursorPort) (hj : r j ∈ rangeAllWork r) : s.stk (r j) = [] := hwork _ hj
  have hustk := rangeAllPrepared_stacks r s (hf .word (by simp [rangeAllWork]))
    (hf .mask (by simp [rangeAllWork])) (hf .counter (by simp [rangeAllWork]))
  rw [hustk]
  unfold TypeStackInv
  have hsource := hf .source (by simp [rangeAllWork])
  have hblock := hf .block (by simp [rangeAllWork])
  have hkind := hf .kind (by simp [rangeAllWork])
  have htemp := hf .temp (by simp [rangeAllWork])
  have hresidue := hf .residue (by simp [rangeAllWork])
  have hsub := hf .subtrahend (by simp [rangeAllWork])
  simpa [r, matchRangePorts] using
    And.intro (And.intro hL ⟨hm, hA, hsource, hblock, hkind, htemp, hresidue, hsub⟩) hT

def typeMembershipRoutine (p : MatchCursorPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (maskedAllRoutine (matchRangePorts p) (typeLeafRoutine p))
    (Atom.routine searchFlipOp)

def typeMembershipAnswer (m A T : ℕ) (word mask : List Bool) : Bool :=
  (rawMarkedSuffixes word mask).any (rawTypeMatch m A T)

def typeMembershipResult (p : MatchCursorPorts K) (m A T : ℕ) (s : CountdownStore K F) :
    CountdownStore K F :=
  ⟨((s.state.1.1, false), typeMembershipAnswer m A T
    (s.stk (p (.cursor .originalWord))) (s.stk (p (.cursor .originalMask)))), s.stk⟩

def typeMembershipBound (m A T L : ℕ) : ℕ := L * (typeLeafBound m A T L + 7) + 12 * L + 18

theorem typeMembership_executes (p : MatchCursorPorts K) (m A T L : ℕ)
    (s : CountdownStore K F) (hs : TypeAllEntry p m A T L s) :
    ∃ n ≤ typeMembershipBound m A T L,
      (typeMembershipRoutine p).Executes s (typeMembershipResult p m A T s) n := by
  let r := matchRangePorts p
  let q := fun bits => !rawTypeMatch m A T bits
  have hf (j : RangeCursorPort) (hj : r j ∈ rangeAllWork r) : s.stk (r j) = [] := hs.1.2.2.2.2 _ hj
  obtain ⟨n, hn, he⟩ := maskedAll_executes r (typeLeafRoutine p) q (TypeStackInv p m A T L)
    (typeLeafBound m A T L) L (typeMaskedContract p m A T L) s
    hs.1.1 hs.1.2.1 (hf .word (by simp [rangeAllWork])) (hf .mask (by simp [rangeAllWork]))
    (hf .counter (by simp [rangeAllWork])) (hf .temp (by simp [rangeAllWork]))
    (typeAll_prepared_inv p m A T L s hs)
  have hflip := Atom.executes (searchFlipOp (K := K) (F := F)) (maskedAllResult r q s)
  have hresult : searchFlipOp.apply (maskedAllResult r q s) = typeMembershipResult p m A T s := by
    apply countdownStore_ext
    · simp [maskedAllResult, typeMembershipResult, typeMembershipAnswer, searchFlipOp,
        Op.apply, r, q, matchRangePorts, all_not_flip_eq_any]
    · rfl
  rw [hresult] at hflip
  exact ⟨n + 1, by unfold typeMembershipBound; omega, RoutineComposition.seq_executes _ _ he hflip⟩

theorem rawTypeMatch_value (m A T : ℕ) (word : List Bool) :
    rawTypeMatch m A T word = true ↔ ∃ c, rawLeafValue m A word = some c ∧ c.2 = T := by
  cases hr : filterRawLeafCell m A (readRawLeafCell word) with
  | none => simp [rawTypeMatch, rawLeafValue, hr]
  | some pair =>
      rcases pair with ⟨⟨b, t⟩, rest⟩
      simp [rawTypeMatch, rawLeafValue, hr]

theorem typeMembershipAnswer_cells (m A T : ℕ) (word mask : List Bool) :
    typeMembershipAnswer m A T word mask =
      decide (T ∈ (rawMarkedCells m A word mask).map Prod.snd) := by
  apply bool_eq_of_true_iff
  simp only [typeMembershipAnswer, List.any_eq_true, decide_eq_true_eq,
    rawMarkedCells, List.mem_map, List.mem_filterMap, rawTypeMatch_value]
  constructor
  · rintro ⟨bits, hbits, c, hc, hT⟩
    exact ⟨c, ⟨bits, hbits, hc⟩, hT⟩
  · rintro ⟨c, ⟨bits, hbits, hc⟩, hT⟩
    exact ⟨bits, hbits, c, hc, hT⟩

/- The counter will count LAST occurrences among the physical masked
leaf positions, rather than enumerate 0..A-1. Thus its iteration fuel is
the parsed word length even when A is binary-described. Actual bounded
header/range preparation still precedes every typed query. -/

def typeAbsentCheck (m A : ℕ) (target mask word : List Bool) : Bool :=
  match filterRawLeafCell m A (readRawLeafCell word) with
  | none => false
  | some (c, _) => !typeMembershipAnswer m A c.2 target mask

def typeAbsentSearched (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  let v := inclusionParsed p m A s
  if v.state.2 then searchFlipOp.apply (typeMembershipResult (inclusionInnerPorts p) m A
    (v.stk (p (.outer .kind))).length v) else v

def typeAbsentQueryEval (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  inclusionSelectedOp.apply (clearManyEval (rangeQueryOwned (inclusionOuterPorts p))
    (typeAbsentSearched p m A s))

def typeAbsentBranch (p : InclusionPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineControl.branch Prod.snd
    (RoutineComposition.seq (typeMembershipRoutine (inclusionInnerPorts p)) (Atom.routine searchFlipOp))
    (Atom.routine cleanupNoop)

def typeAbsentQueryRoutine (p : InclusionPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  let o := inclusionOuterPorts p
  RoutineComposition.seq (wordDuplicateRoutine (o .word) (o .temp) (o .source))
    (RoutineComposition.seq (typedLeafCellRoutine (rangeTypedPorts o))
      (RoutineComposition.seq (typeAbsentBranch p)
        (RoutineComposition.seq (clearManyRoutine (rangeQueryOwned o)) (Atom.routine inclusionSelectedOp))))

theorem typeAbsentSearched_stacks (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) :
    (typeAbsentSearched p m A s).stk = (inclusionParsed p m A s).stk := by
  unfold typeAbsentSearched
  cases hf : (inclusionParsed p m A s).state.2 <;>
    simp [hf, typeMembershipResult, searchFlipOp, Op.apply]

theorem typeAbsentSearched_frame (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) :
    (typeAbsentSearched p m A s).state.1.1 = s.state.1.1 := by
  have hv := typedLeafCell_frame (rangeTypedPorts (inclusionOuterPorts p)) m A
    (rangeLeafPrepared (inclusionOuterPorts p) s)
  unfold typeAbsentSearched
  cases hf : (inclusionParsed p m A s).state.2 <;>
    simpa [hf, typeMembershipResult, searchFlipOp, Op.apply] using congrArg Prod.fst hv

theorem typeAbsentSearched_flag (p : InclusionPorts K) (m A L : ℕ) (target mask : List Bool)
    (s : CountdownStore K F) (hs : InclusionStackInv p m A L target mask s.stk) :
    (typeAbsentSearched p m A s).state.2 =
      typeAbsentCheck m A target mask (s.stk (p (.outer .word))) := by
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
  unfold typeAbsentCheck
  rw [← ho]
  cases hf : v.state.2 <;>
    simp [typeAbsentSearched, rawLeafCellObservation, typedRawCellPorts, rangeTypedPorts,
      typeMembershipResult, searchFlipOp, Op.apply, inclusionInnerPorts,
      inclusionMatchPortMap, hvx, hs.2.1, hs.2.2.1, hf, v, o, inclusionOuterPorts]

theorem typeAbsentQuery_result (p : InclusionPorts K) (m A L : ℕ) (target mask : List Bool)
    (s : CountdownStore K F) (hs : InclusionStackInv p m A L target mask s.stk)
    (hselected : s.state.1.2 = true) :
    typeAbsentQueryEval p m A s =
      cellCompareFlagStore (typeAbsentCheck m A target mask (s.stk (p (.outer .word)))) s := by
  let o := inclusionOuterPorts p
  have hrestore := rangeLeaf_result o m A L s hs.1
  have hstack : (clearManyEval (rangeQueryOwned o) (typeAbsentSearched p m A s)).stk =
      (rangeLeafEval o m A s).stk := by
    simp only [rangeLeafEval, rangeQueryOwned, clearManyEval, clearStackEval,
      typeAbsentSearched_stacks, inclusionParsed]
  apply countdownStore_ext
  · change (((clearManyEval (rangeQueryOwned o) (typeAbsentSearched p m A s)).state.1.1, true),
      (clearManyEval (rangeQueryOwned o) (typeAbsentSearched p m A s)).state.2) = _
    rw [clearMany_state, typeAbsentSearched_frame, typeAbsentSearched_flag p m A L target mask s hs]
    exact Prod.ext (Prod.ext rfl hselected.symm) rfl
  · change (clearManyEval (rangeQueryOwned o) (typeAbsentSearched p m A s)).stk = s.stk
    rw [hstack, hrestore]
    rfl

def typeAbsentBound (m A L : ℕ) : ℕ :=
  L * (26 * L + 4 * m + 4 * A + 54) + 30 * L + 4 * m + 4 * A + 57

theorem typeAbsentQuery_executes (p : InclusionPorts K) (m A L : ℕ) (target mask : List Bool)
    (s : CountdownStore K F) (hs : InclusionStackInv p m A L target mask s.stk)
    (hselected : s.state.1.2 = true) :
    ∃ n ≤ typeAbsentBound m A L,
      (typeAbsentQueryRoutine p).Executes s
        (cellCompareFlagStore (typeAbsentCheck m A target mask (s.stk (p (.outer .word)))) s) n := by
  let o := inclusionOuterPorts p
  let i := inclusionInnerPorts p
  let u := rangeLeafPrepared o s
  let v := inclusionParsed p m A s
  let w := typeAbsentSearched p m A s
  rcases hs.1 with ⟨hL, hm, hA, hsource, hb, hk, ht, hr, hd⟩
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
  have hbranch : ∃ n ≤ L * (26 * L + 4 * m + 4 * A + 54) + 12 * L + 20,
      (typeAbsentBranch p).Executes v w n := by
    cases hf : v.state.2 with
    | false =>
        have he := RoutineControl.branch_false Prod.snd
          (RoutineComposition.seq (typeMembershipRoutine i) (Atom.routine searchFlipOp))
          (Atom.routine cleanupNoop) hf (Atom.executes cleanupNoop v)
        refine ⟨2, by omega, ?_⟩
        simpa [typeAbsentBranch, w, typeAbsentSearched, hf, cleanupNoop, Op.apply] using he
    | true =>
        obtain ⟨n, hn, he⟩ := typeMembership_executes i m A
          (v.stk (p (.outer .kind))).length L v ⟨hinner.1, hinner.2.2⟩
        have hfexec := Atom.executes (searchFlipOp (K := K) (F := F))
          (typeMembershipResult i m A (v.stk (p (.outer .kind))).length v)
        have hb := RoutineControl.branch_true Prod.snd
          (RoutineComposition.seq (typeMembershipRoutine i) (Atom.routine searchFlipOp))
          (Atom.routine cleanupNoop) hf (RoutineComposition.seq_executes _ _ he hfexec)
        have hcoef : typeLeafBound m A (v.stk (p (.outer .kind))).length L + 7 ≤
            26 * L + 4 * m + 4 * A + 54 := by unfold typeLeafBound; omega
        have hmul := Nat.mul_le_mul_right L hcoef
        rw [Nat.mul_comm _ L, Nat.mul_comm _ L] at hmul
        refine ⟨(n + 1) + 1, by unfold typeMembershipBound at hn; omega, ?_⟩
        simpa only [typeAbsentBranch, w, typeAbsentSearched, hf, ↓reduceIte] using hb
  obtain ⟨b, hbtime, h3⟩ := hbranch
  obtain ⟨c, hc, h4⟩ := clearMany_executes (rangeQueryOwned o) w
  have hmassW : cleanupMass (rangeQueryOwned o) w ≤ 3 * L := by
    simpa only [cleanupMass, w, typeAbsentSearched_stacks] using hmass
  have h5 := Atom.executes (inclusionSelectedOp (K := K) (F := F)) (clearManyEval (rangeQueryOwned o) w)
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
    (RoutineComposition.seq_executes _ _ h3 (RoutineComposition.seq_executes _ _ h4 h5)))
  change (typeAbsentQueryRoutine p).Executes s (typeAbsentQueryEval p m A s) _ at he
  rw [typeAbsentQuery_result p m A L target mask s hs hselected] at he
  refine ⟨3 * (s.stk (o .word)).length + 3 + (a + (b + (c + 1))), ?_, he⟩
  simp only [rangeQueryOwned, List.length_cons, List.length_nil] at hc
  unfold typeAbsentBound
  omega

def noLaterTypeCheck (m A : ℕ) (word mask : List Bool) : Bool :=
  typeAbsentCheck m A word.tail mask.tail word

def lastTypeCheck (m A W : ℕ) (originalMask word : List Bool) : Bool :=
  noLaterTypeCheck m A word (originalMask.drop (W - word.length))

def lastTypeQueryEval (p : InclusionPorts K) (m A : ℕ) (s : CountdownStore K F) :=
  clearManyEval (uniqueTailsOwned p) (typeAbsentQueryEval p m A (uniqueTailsPrepared p s))

def lastTypeQueryRoutine (p : InclusionPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (uniqueTailsRoutine p)
    (RoutineComposition.seq (typeAbsentQueryRoutine p) (clearManyRoutine (uniqueTailsOwned p)))

theorem lastTypeQuery_result (p : InclusionPorts K) (m A W L : ℕ) (originalMask : List Bool)
    (s : CountdownStore K F) (hs : UniqueStackInv p m A W L originalMask s.stk)
    (hselected : s.state.1.2 = true) :
    lastTypeQueryEval p m A s = cellCompareFlagStore
      (lastTypeCheck m A W originalMask (s.stk (p (.outer .word)))) s := by
  let u := uniqueTailsPrepared p s
  have hu := uniqueTails_prepared_inv p m A W L originalMask s hs
  have hquery := typeAbsentQuery_result p m A L (s.stk (p (.outer .word))).tail
    (s.stk (p (.outer .mask))).tail u hu hselected
  have hstk := uniqueTailsPrepared_stacks p s hs.1.2.1 hs.1.2.2.1
  have hword : u.stk (p (.outer .word)) = s.stk (p (.outer .word)) := by rw [hstk]; simp
  apply countdownStore_ext
  · change (clearManyEval (uniqueTailsOwned p) (typeAbsentQueryEval p m A u)).state = _
    rw [hquery, clearMany_state]
    simp only [cellCompareFlagStore, hword, lastTypeCheck, noLaterTypeCheck,
      u, uniqueTailsPrepared_state, ← hs.2.2.2]
  · change (clearManyEval (uniqueTailsOwned p) (typeAbsentQueryEval p m A u)).stk = s.stk
    rw [hquery]
    funext j
    by_cases hw : j = p (.inner .originalWord)
    · subst j
      simp [clearManyEval, clearStackEval, uniqueTailsOwned, cellCompareFlagStore, hs.1.2.1]
    by_cases hm : j = p (.inner .originalMask)
    · subst j
      simp [clearManyEval, clearStackEval, uniqueTailsOwned, cellCompareFlagStore, hs.1.2.2.1]
    · simp only [cellCompareFlagStore, clearManyEval, uniqueTailsOwned, clearStackEval]
      simp [hstk, hw, hm]

def lastTypeQueryBound (m A L : ℕ) : ℕ := typeAbsentBound m A L + 8 * L + 11

theorem lastTypeQuery_executes (p : InclusionPorts K) (m A W L : ℕ) (originalMask : List Bool)
    (s : CountdownStore K F) (hs : UniqueStackInv p m A W L originalMask s.stk)
    (hselected : s.state.1.2 = true) :
    ∃ n ≤ lastTypeQueryBound m A L,
      (lastTypeQueryRoutine p).Executes s
        (cellCompareFlagStore (lastTypeCheck m A W originalMask (s.stk (p (.outer .word)))) s) n := by
  let u := uniqueTailsPrepared p s
  let v := typeAbsentQueryEval p m A u
  have hu := uniqueTails_prepared_inv p m A W L originalMask s hs
  have h1 := uniqueTails_executes p s hs.1.1.2.2.2.2.2.2.1
  obtain ⟨a, ha, h2⟩ := typeAbsentQuery_executes p m A L (s.stk (p (.outer .word))).tail
    (s.stk (p (.outer .mask))).tail u hu hselected
  have hresult := typeAbsentQuery_result p m A L (s.stk (p (.outer .word))).tail
    (s.stk (p (.outer .mask))).tail u hu hselected
  rw [← hresult] at h2
  obtain ⟨b, hb, h3⟩ := clearMany_executes (uniqueTailsOwned p) v
  have hstk := uniqueTailsPrepared_stacks p s hs.1.2.1 hs.1.2.2.1
  have hmass : cleanupMass (uniqueTailsOwned p) v ≤ 2 * L := by
    have hL := hs.1.1.1
    have hfit := hs.2.2.1
    have hw : (s.stk (p (.outer .word))).tail.length ≤ (s.stk (p (.outer .word))).length := by
      cases s.stk (p (.outer .word)) <;> simp
    have hm : (s.stk (p (.outer .mask))).tail.length ≤ (s.stk (p (.outer .mask))).length := by
      cases s.stk (p (.outer .mask)) <;> simp
    simp only [cleanupMass, uniqueTailsOwned, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, v, hresult, cellCompareFlagStore]
    rw [hstk]
    simp
    omega
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2 h3)
  change (lastTypeQueryRoutine p).Executes s (lastTypeQueryEval p m A s) _ at he
  rw [lastTypeQuery_result p m A W L originalMask s hs hselected] at he
  refine ⟨3 * (s.stk (p (.outer .word))).length + 3 * (s.stk (p (.outer .mask))).length + 8 +
    (a + b), ?_, he⟩
  have hL := hs.1.1.1
  have hfit := hs.2.2.1
  simp only [uniqueTailsOwned, List.length_cons, List.length_nil] at hb
  unfold lastTypeQueryBound
  omega

def lastTypeMaskedContract (p : InclusionPorts K) (m A W L : ℕ) (originalMask : List Bool) :
    MaskedQueryContract (inclusionOuterPorts p) (lastTypeQueryRoutine p)
      (lastTypeCheck m A W originalMask) (UniqueStackInv p m A W L originalMask)
      (lastTypeQueryBound m A L) where
  positive := by unfold lastTypeQueryBound; omega
  query_executes s hs hselected := lastTypeQuery_executes p m A W L originalMask s hs hselected
  cursor_closed := (uniqueMaskedContract p m A W L originalMask).cursor_closed
  counter_closed := (uniqueMaskedContract p m A W L originalMask).counter_closed

/-! ## Exact last-occurrence semantics, including repeated types in distinct cells -/

def lastOccurrenceCount {X : Type} [DecidableEq X] : List X → ℕ
  | [] => 0
  | x :: xs => (if x ∈ xs then 0 else 1) + lastOccurrenceCount xs

/-- The rightmost-occurrence convention matches List.dedup exactly.
This identity concerns TYPE values, not the identity of their cells. -/
theorem lastOccurrenceCount_eq_distinct {X : Type} [DecidableEq X] (xs : List X) :
    lastOccurrenceCount xs = scanDistinctCount xs := by
  induction xs with
  | nil => simp [lastOccurrenceCount, scanDistinctCount]
  | cons x xs ih =>
      by_cases hx : x ∈ xs
      · simpa only [lastOccurrenceCount, if_pos hx, Nat.zero_add, scanDistinctCount,
          List.dedup_cons_of_mem hx] using ih
      · simp only [lastOccurrenceCount, if_neg hx, scanDistinctCount,
          List.dedup_cons_of_notMem hx, List.length_cons] at ih ⊢
        omega

theorem noLaterTypeCheck_value (m A : ℕ) (word mask : List Bool) :
    noLaterTypeCheck m A word mask =
      match rawLeafValue m A word with
      | none => false
      | some c => !decide (c.2 ∈ (rawMarkedCells m A word.tail mask.tail).map Prod.snd) := by
  cases hr : filterRawLeafCell m A (readRawLeafCell word) with
  | none => simp [noLaterTypeCheck, typeAbsentCheck, rawLeafValue, hr]
  | some pair =>
      rcases pair with ⟨c, rest⟩
      simp [noLaterTypeCheck, typeAbsentCheck, rawLeafValue, hr, typeMembershipAnswer_cells]

def rawLastTypeRec (m A : ℕ) : List Bool → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | b :: bits, mark :: mask =>
      (if mark && noLaterTypeCheck m A (b :: bits) (mark :: mask) then 1 else 0) +
        rawLastTypeRec m A bits mask

theorem rawLastTypeRec_eq (m A : ℕ) (word mask : List Bool) :
    rawLastTypeRec m A word mask =
      lastOccurrenceCount ((rawMarkedCells m A word mask).map Prod.snd) := by
  induction word generalizing mask with
  | nil => simp [rawLastTypeRec, rawMarkedCells, rawMarkedSuffixes, lastOccurrenceCount]
  | cons b bits ih =>
      cases mask with
      | nil => simp [rawLastTypeRec, rawMarkedCells, rawMarkedSuffixes, lastOccurrenceCount]
      | cons mark mask =>
          cases mark with
          | false =>
              simpa [rawLastTypeRec, rawMarkedCells, rawMarkedSuffixes] using ih mask
          | true =>
              rw [rawLastTypeRec, noLaterTypeCheck_value]
              cases hc : rawLeafValue m A (b :: bits) with
              | none =>
                  simpa [hc, rawMarkedCells, rawMarkedSuffixes] using ih mask
              | some c =>
                  have hcells : rawMarkedCells m A (b :: bits) (true :: mask) =
                      c :: rawMarkedCells m A bits mask := by
                    simp [rawMarkedCells, rawMarkedSuffixes, hc]
                  simp only [hc, List.tail_cons, Bool.true_and, hcells, List.map_cons, lastOccurrenceCount]
                  rw [ih mask]
                  by_cases ht : c.2 ∈ (rawMarkedCells m A bits mask).map Prod.snd <;> simp [ht]

theorem maskedTally_lastType_eq_rec (m A W : ℕ) (originalMask word mask : List Bool)
    (hW : word.length ≤ W) (hfit : mask.length ≤ word.length)
    (hm : mask = originalMask.drop (W - word.length)) :
    maskedTally (lastTypeCheck m A W originalMask) word mask = rawLastTypeRec m A word mask := by
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
          simp only [maskedTally, rawLastTypeRec]
          rw [hi]
          unfold lastTypeCheck
          rw [← hm]

def typeCountAnswer (m A : ℕ) (word mask : List Bool) : ℕ :=
  maskedTally (lastTypeCheck m A word.length mask) word mask

theorem typeCountAnswer_distinct (m A : ℕ) (word mask : List Bool)
    (hfit : mask.length ≤ word.length) :
    typeCountAnswer m A word mask = scanDistinctCount ((rawMarkedCells m A word mask).map Prod.snd) := by
  rw [typeCountAnswer, maskedTally_lastType_eq_rec m A word.length mask word mask (Nat.le_refl _)
    hfit (by simp), rawLastTypeRec_eq, lastOccurrenceCount_eq_distinct]

theorem typeCountAnswer_le (m A : ℕ) (word mask : List Bool) :
    typeCountAnswer m A word mask ≤ mask.length := maskedTally_le_length _ _ _

theorem typeCountAnswer_tree (N m : ℕ) (R : BTree (ℕ × ℕ)) (rest : List Bool)
    (hR : rawTreeValid N m R) :
    typeCountAnswer m (N + m * N + 3) (rawCellTreeBits R ++ rest) (rawNodeMask R) =
      scanDistinctCount ((scanLeaves R).map Prod.snd) := by
  have hp := rawForestMaskParse_one R rest
  have hlen := rawForestMaskParse_consumption (rawCellTreeBits R ++ rest) rest (rawNodeMask R) 1 hp
  have hfit : (rawNodeMask R).length ≤ (rawCellTreeBits R ++ rest).length := by omega
  rw [typeCountAnswer_distinct _ _ _ _ hfit]
  have hc := rawMarkedCells_forest N m [R] rest (by
    intro T hT
    have he : T = R := by simpa only [List.mem_singleton] using hT
    subst T
    exact hR)
  simpa only [rawForestWord, rawForestNodeMask, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] using congrArg (fun cs => scanDistinctCount (cs.map Prod.snd)) hc

/-- Exactly one parsed subtree, not its entire physical suffix. This is
the semantic value the next scoped caller must implement. In particular
the root's count is included when that caller is used for star scoring. -/
def scopedTypeAnswer (m A : ℕ) (word : List Bool) : Option ℕ :=
  match rawForestMaskParse word.length 1 word with
  | none => none
  | some (_, mask) => some (typeCountAnswer m A word mask)

theorem scopedTypeAnswer_tree (N m : ℕ) (R : BTree (ℕ × ℕ)) (rest : List Bool)
    (hR : rawTreeValid N m R) :
    scopedTypeAnswer m (N + m * N + 3) (rawCellTreeBits R ++ rest) =
      some (scanDistinctCount ((scanLeaves R).map Prod.snd)) := by
  rw [scopedTypeAnswer, rawForestMaskParse_one, typeCountAnswer_tree N m R rest hR]

def typeCountRoutine (p : InclusionPorts K) (out : K) :
    Routine (fun _ : K => Bool) (CountdownState F) :=
  tallyAllRoutine (inclusionOuterPorts p) out (lastTypeQueryRoutine p)

def typeCountResult (p : InclusionPorts K) (out : K) (m A : ℕ) (s : CountdownStore K F) :
    CountdownStore K F :=
  ⟨((s.state.1.1, false), true), Function.update s.stk out
    (List.replicate (typeCountAnswer m A (s.stk (p (.outer .originalWord)))
      (s.stk (p (.outer .originalMask)))) true ++ s.stk out)⟩

def typeCountBound (m A L : ℕ) : ℕ := L * (lastTypeQueryBound m A L + 10) + 12 * L + 17

/-- All inner searches restore the accumulator as well as their other
unowned stacks. The ONLY accumulator change is the one paid push in the
outer selected-and-last-occurrence branch. -/
theorem typeCount_executes (p : InclusionPorts K) (out : K)
    (hout : ∀ j : InclusionPort, out ≠ p j) (m A L : ℕ)
    (s : CountdownStore K F) (hs : UniqueEntry p m A L s) :
    ∃ n ≤ typeCountBound m A L,
      (typeCountRoutine p out).Executes s (typeCountResult p out m A s) n := by
  let o := inclusionOuterPorts p
  let W := (s.stk (o .originalWord)).length
  let mask := s.stk (o .originalMask)
  have hf (j : RangeCursorPort) (hj : o j ∈ rangeAllWork o) : s.stk (o j) = [] := hs.1.2.2.2.2 _ hj
  have hpush : ∀ stk, UniqueStackInv p m A W L mask stk →
      UniqueStackInv p m A W L mask (Function.update stk out (true :: stk out)) := by
    intro stk hi
    have hx (j : InclusionPort) : (Function.update stk out (true :: stk out)) (p j) = stk (p j) :=
      Function.update_of_ne (hout j).symm _ _
    rcases hi with ⟨⟨hq, hw, hm, hTL, hfit, hwork⟩, hW, hfit', hshift⟩
    refine ⟨⟨?_, (hx _).trans hw, (hx _).trans hm, hTL, hfit, ?_⟩, ?_, ?_, ?_⟩
    · simpa only [hx] using hq
    · intro j hj
      have hjo : j ≠ out := by
        simp only [rangeAllWork, List.mem_cons, List.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact (hout _).symm
      rw [Function.update_of_ne hjo]
      exact hwork j (by assumption)
    · simpa only [hx] using hW
    · simpa only [hx] using hfit'
    · simpa only [hx] using hshift
  exact tallyAll_executes o out (fun j => hout (.outer j)) (lastTypeQueryRoutine p)
    (lastTypeCheck m A W mask) (UniqueStackInv p m A W L mask) (lastTypeQueryBound m A L) L
    (lastTypeMaskedContract p m A W L mask) hpush s hs.1.1 hs.1.2.1
    (hf .word (by simp [rangeAllWork])) (hf .mask (by simp [rangeAllWork]))
    (hf .counter (by simp [rangeAllWork])) (hf .temp (by simp [rangeAllWork]))
    (uniqueAll_prepared_inv p m A L s hs)

theorem scanDistinctCount_map_injective {X Y : Type} [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (hf : Function.Injective f) (xs : List X) :
    scanDistinctCount (xs.map f) = scanDistinctCount xs := by
  simp only [scanDistinctCount, List.dedup_map_of_injective hf, List.length_map]

/-- The forest is reconstructed from ORIGINAL parser/range observations.
The residual suffix remains explicit, but its positions are outside the
mask and cannot affect the count. A one-tree scope is the q=1 instance. -/
theorem typeCountAnswer_observed_typed (N m q : ℕ) (word mask rest : List Bool)
    (hparse : rawForestMaskParse word.length q word = some (rest, mask))
    (hcheck : forestMaskCellCheck N m word mask = true) :
    ∃ Ts : List (BTree (Cell N m)), Ts.length = q ∧ word = Ts.flatMap treeBits ++ rest ∧
      typeCountAnswer m (N + m * N + 3) word mask =
        scanDistinctCount ((Ts.flatMap scanLeaves).map Prod.snd) := by
  obtain ⟨Rs, hq, hw, hm⟩ := (rawForestMaskParse_all_words word rest mask q).mp hparse
  have hR := (forestMaskCellCheck_iff N m Rs rest).mp (by simpa only [← hw, ← hm] using hcheck)
  have hlen := rawForestMaskParse_consumption word rest mask q hparse
  have hfit : mask.length ≤ word.length := by omega
  obtain ⟨Ts, hTs⟩ := (rawForestValid_iff_typed N m Rs).mp hR
  refine ⟨Ts, ?_, ?_, ?_⟩
  · simpa only [← hTs, List.length_map] using hq
  · simpa only [← hTs, rawForestWord_map_codes] using hw
  · rw [typeCountAnswer_distinct m (N + m * N + 3) word mask hfit, hw, hm,
      rawMarkedCells_forest N m Rs rest hR, ← hTs, rawForestCodes_leaves]
    have hmapped : ((Ts.flatMap scanLeaves).map cellNatCode).map Prod.snd =
        ((Ts.flatMap scanLeaves).map Prod.snd).map (terminalCode N m) := by
      simp only [List.map_map, Function.comp_def, cellNatCode]
    rw [hmapped, scanDistinctCount_map_injective (terminalCode N m) (terminalCode_injective N m)]

theorem typeCount_executes_observed_typed (p : InclusionPorts K) (out : K)
    (hout : ∀ j : InclusionPort, out ≠ p j) (N m q L : ℕ)
    (s : CountdownStore K F) (rest : List Bool)
    (hs : UniqueEntry p m (N + m * N + 3) L s)
    (hparse : rawForestMaskParse (s.stk (p (.outer .originalWord))).length q
      (s.stk (p (.outer .originalWord))) = some (rest, s.stk (p (.outer .originalMask))))
    (hcheck : forestMaskCellCheck N m (s.stk (p (.outer .originalWord)))
      (s.stk (p (.outer .originalMask))) = true) :
    ∃ Ts : List (BTree (Cell N m)), ∃ n : ℕ, Ts.length = q ∧
      s.stk (p (.outer .originalWord)) = Ts.flatMap treeBits ++ rest ∧
      n ≤ typeCountBound m (N + m * N + 3) L ∧
      (typeCountRoutine p out).Executes s
        ⟨((s.state.1.1, false), true), Function.update s.stk out
          (List.replicate (scanDistinctCount ((Ts.flatMap scanLeaves).map Prod.snd)) true ++ s.stk out)⟩ n := by
  obtain ⟨Ts, hq, hw, hans⟩ := typeCountAnswer_observed_typed N m q
    (s.stk (p (.outer .originalWord))) (s.stk (p (.outer .originalMask))) rest hparse hcheck
  obtain ⟨n, hn, he⟩ := typeCount_executes p out hout m (N + m * N + 3) L s hs
  refine ⟨Ts, n, hq, hw, hn, ?_⟩
  simpa only [typeCountResult, hans] using he

/- The same-language controller still owes per-subtree scoping/mixedness,
row-root markers, global coverage, root-inclusive certificate scoring,
bounded header materialization, rejection-preserving joins and clean halt.
This supplied tally is not a whole verifier or an encoded-hardness proof. -/

end PolytomyReductionModel.WholeVerifierController
