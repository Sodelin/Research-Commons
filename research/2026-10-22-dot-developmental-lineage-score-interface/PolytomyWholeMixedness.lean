/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The original EVERY-target-internal-node mixedness guard, including all
internal nodes inside composite children and the roots of supplied rows.
Each selected internal node obtains its OWN paid, boundary-ending mask,
counts last terminal-type occurrences, tests two unary positions, and
clears the scalar before the common universal cursor continues.
-/
import PolytomyScopedTypeCount

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

inductive MixedPort where
  | outer (port : RangeCursorPort)
  | node (port : ScopedTypePort)
  deriving DecidableEq, Fintype

abbrev MixedPorts (K : Type) := MixedPort ↪ K

@[simp] theorem mixedPorts_eq (p : MixedPorts K) (a b : MixedPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def mixedOuterPorts (p : MixedPorts K) : RangeCursorPorts K where
  toFun := fun j => p (.outer j)
  inj' := by intro a b h; simpa using p.injective h

def mixedNodeMap : ScopedTypePort → MixedPort
  | .word => .outer .word
  | .rows => .outer .rows
  | .types => .outer .types
  | j => .node j

theorem mixedNodeMap_injective : Function.Injective mixedNodeMap := by decide

def mixedNodePorts (p : MixedPorts K) : ScopedTypePorts K where
  toFun := fun j => p (mixedNodeMap j)
  inj' := fun _ _ h => mixedNodeMap_injective (p.injective h)

/-- The dummy Unit frame only makes the state-independent physical entry
predicate into a predicate on tapes. It adds no control state or oracle. -/
def MixedStackInv (p : MixedPorts K) (m A L : ℕ) (stk : K → List Bool) : Prop :=
  ScopedTypeEntry (mixedNodePorts p) m A L
    (⟨(((), false), false), stk⟩ : CountdownStore K Unit) ∧
  stk (p (.node .output)) = []

theorem mixedInv_transport (p : MixedPorts K) (m A L : ℕ) (stk stk' : K → List Bool)
    (hs : MixedStackInv p m A L stk) (hL : (stk' (p (.outer .word))).length ≤ L)
    (hx : ∀ j : K, j ≠ p (.outer .word) → j ≠ p (.outer .mask) → j ≠ p (.outer .counter) → stk' j = stk j) :
    MixedStackInv p m A L stk' := by
  refine ⟨?_, (hx _ (by simp) (by simp) (by simp)).trans hs.2⟩
  apply scopedTypeEntry_transport (mixedNodePorts p) m A L _ _ hs.1 hL
  intro j hj
  apply hx
  all_goals cases j <;> simp_all [mixedNodePorts, mixedNodeMap]

def mixedMaskedContract (p : MixedPorts K) (m A L : ℕ) :
    MaskedQueryContract (mixedOuterPorts p) (mixedRootRoutine (mixedNodePorts p))
      (mixedRootAnswer m A) (MixedStackInv p m A L) (mixedRootBound m A L) where
  positive := by unfold mixedRootBound; omega
  query_executes s hs hselected := mixedRoot_executes (mixedNodePorts p) m A L s hs.1 hs.2 hselected
  cursor_closed stk hs := by
    apply mixedInv_transport p m A L stk _ hs
    · have ht : (stk (p (.outer .word))).tail.length ≤ (stk (p (.outer .word))).length := by
        cases stk (p (.outer .word)) <;> simp
      simpa [mixedOuterPorts] using ht.trans hs.1.1.1
    · intro j hjw hjm hjc
      simp [mixedOuterPorts, hjw, hjm]
  counter_closed stk hs := by
    apply mixedInv_transport p m A L stk _ hs
    · simpa [mixedOuterPorts] using hs.1.1.1
    · intro j hjw hjm hjc
      simp [mixedOuterPorts, hjc]

def MixedAllEntry (p : MixedPorts K) (m A L : ℕ) (s : CountdownStore K F) : Prop :=
  RangeAllEntry (mixedOuterPorts p) m A L s ∧ MixedStackInv p m A L s.stk

theorem mixedAll_prepared_inv (p : MixedPorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : MixedAllEntry p m A L s) :
    MixedStackInv p m A L (rangeAllPrepared (mixedOuterPorts p) s).stk := by
  let o := mixedOuterPorts p
  have hf (j : RangeCursorPort) (hj : o j ∈ rangeAllWork o) : s.stk (o j) = [] := hs.1.2.2.2.2 _ hj
  have hstk := rangeAllPrepared_stacks o s (hf .word (by simp [rangeAllWork]))
    (hf .mask (by simp [rangeAllWork])) (hf .counter (by simp [rangeAllWork]))
  apply mixedInv_transport p m A L s.stk _ hs.2
  · rw [hstk]
    simpa [o, mixedOuterPorts] using hs.1.1
  · intro j hjw hjm hjc
    rw [hstk]
    simp [o, mixedOuterPorts, hjw, hjm, hjc]

def mixedAllAnswer (m A : ℕ) (word mask : List Bool) : Bool :=
  (rawMarkedSuffixes word mask).all (mixedRootAnswer m A)

def mixedAllRoutine (p : MixedPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  maskedAllRoutine (mixedOuterPorts p) (mixedRootRoutine (mixedNodePorts p))

def mixedAllResult (p : MixedPorts K) (m A : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨((s.state.1.1, false), mixedAllAnswer m A (s.stk (p (.outer .originalWord)))
    (s.stk (p (.outer .originalMask)))), s.stk⟩

def mixedAllBound (m A L : ℕ) : ℕ := L * (mixedRootBound m A L + 7) + 12 * L + 17

theorem mixedAll_executes (p : MixedPorts K) (m A L : ℕ)
    (s : CountdownStore K F) (hs : MixedAllEntry p m A L s) :
    ∃ n ≤ mixedAllBound m A L,
      (mixedAllRoutine p).Executes s (mixedAllResult p m A s) n := by
  let o := mixedOuterPorts p
  have hf (j : RangeCursorPort) (hj : o j ∈ rangeAllWork o) : s.stk (o j) = [] := hs.1.2.2.2.2 _ hj
  exact maskedAll_executes o (mixedRootRoutine (mixedNodePorts p)) (mixedRootAnswer m A)
    (MixedStackInv p m A L) (mixedRootBound m A L) L (mixedMaskedContract p m A L) s
    hs.1.1 hs.1.2.1 (hf .word (by simp [rangeAllWork])) (hf .mask (by simp [rangeAllWork]))
    (hf .counter (by simp [rangeAllWork])) (hf .temp (by simp [rangeAllWork]))
    (mixedAll_prepared_inv p m A L s hs)

theorem mixedRootAnswer_leaf (m A : ℕ) (c : ℕ × ℕ) (rest : List Bool) :
    mixedRootAnswer m A (rawCellTreeBits (.leaf c) ++ rest) = true := by
  simp [mixedRootAnswer, rawCellTreeBits]

theorem mixedRootAnswer_node (N m : ℕ) (l r : BTree (ℕ × ℕ)) (rest : List Bool)
    (hR : rawTreeValid N m (.node l r)) :
    mixedRootAnswer m (N + m * N + 3) (rawCellTreeBits (.node l r) ++ rest) =
      decide (2 ≤ scanTypeCount Prod.snd (.node l r)) := by
  have hh : (rawCellTreeBits (.node l r) ++ rest).head? = some false := rfl
  rw [mixedRootAnswer, if_pos hh, scopedMixedAnswer, scopedTypeAnswer_tree N m (.node l r) rest hR]
  rfl

theorem mixedViews_tree (N m : ℕ) (R : BTree (ℕ × ℕ)) (rest : List Bool)
    (hR : rawTreeValid N m R) :
    ((rawNodeViews R rest).map rawViewSuffix).all (mixedRootAnswer m (N + m * N + 3)) =
      scanMixed Prod.snd R := by
  revert hR
  induction R generalizing rest with
  | leaf c =>
      intro hR
      simp only [rawNodeViews, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        rawViewSuffix, mixedRootAnswer_leaf, Bool.true_and, scanMixed]
  | node l r ihl ihr =>
      intro hR
      have hparts := (rawTreeValid_node N m l r).mp hR
      simp only [rawNodeViews, List.map_cons, List.map_append, List.all_cons, List.all_append,
        rawViewSuffix, mixedRootAnswer_node N m l r rest hR,
        ihl (rawCellTreeBits r ++ rest) hparts.1, ihr rest hparts.2, scanMixed, Bool.and_assoc]

theorem mixedAllAnswer_forest (N m : ℕ) (Rs : List (BTree (ℕ × ℕ))) (rest : List Bool)
    (hRs : ∀ R ∈ Rs, rawTreeValid N m R) :
    mixedAllAnswer m (N + m * N + 3) (rawForestWord Rs ++ rest) (rawForestNodeMask Rs) =
      Rs.all (scanMixed Prod.snd) := by
  revert hRs
  induction Rs with
  | nil => intro hRs; simp [mixedAllAnswer, rawForestWord, rawForestNodeMask, rawMarkedSuffixes]
  | cons R Rs ih =>
      intro hRs
      have hR := hRs R (by simp)
      have htail : ∀ T ∈ Rs, rawTreeValid N m T := fun T hT => hRs T (by simp [hT])
      simp only [mixedAllAnswer, rawForestWord, rawForestNodeMask, List.flatMap_cons,
        List.append_assoc, List.all_cons]
      rw [rawMarkedSuffixes_tree, List.all_append, mixedViews_tree N m R _ hR]
      exact congrArg (fun b => scanMixed Prod.snd R && b) (ih rest htail)

theorem scanTypeCount_rawTreeCodes {N m : ℕ} (T : BTree (Cell N m)) :
    scanTypeCount Prod.snd (rawTreeCodes T) = scanTypeCount Prod.snd T := by
  rw [scanTypeCount, rawTreeCodes_leaves]
  have hmap : ((scanLeaves T).map cellNatCode).map Prod.snd =
      ((scanLeaves T).map Prod.snd).map (terminalCode N m) := by
    simp only [List.map_map, Function.comp_def, cellNatCode]
  rw [hmap, scanDistinctCount_map_injective (terminalCode N m) (terminalCode_injective N m)]
  rfl

theorem scanMixed_rawTreeCodes {N m : ℕ} (T : BTree (Cell N m)) :
    scanMixed Prod.snd (rawTreeCodes T) = scanMixed Prod.snd T := by
  induction T with
  | leaf c => rfl
  | node l r ihl ihr =>
      change (decide (2 ≤ scanTypeCount Prod.snd (rawTreeCodes (.node l r))) &&
        scanMixed Prod.snd (rawTreeCodes l) && scanMixed Prod.snd (rawTreeCodes r)) = _
      rw [scanTypeCount_rawTreeCodes, ihl, ihr]
      rfl

theorem mixedAllAnswer_observed_typed (N m q : ℕ) (word mask rest : List Bool)
    (hparse : rawForestMaskParse word.length q word = some (rest, mask))
    (hcheck : forestMaskCellCheck N m word mask = true) :
    ∃ Ts : List (BTree (Cell N m)), Ts.length = q ∧ word = Ts.flatMap treeBits ++ rest ∧
      mixedAllAnswer m (N + m * N + 3) word mask = Ts.all (scanMixed Prod.snd) := by
  obtain ⟨Rs, hq, hw, hm⟩ := (rawForestMaskParse_all_words word rest mask q).mp hparse
  have hR := (forestMaskCellCheck_iff N m Rs rest).mp (by simpa only [← hw, ← hm] using hcheck)
  obtain ⟨Ts, hTs⟩ := (rawForestValid_iff_typed N m Rs).mp hR
  refine ⟨Ts, ?_, ?_, ?_⟩
  · simpa only [← hTs, List.length_map] using hq
  · simpa only [← hTs, rawForestWord_map_codes] using hw
  · rw [hw, hm, mixedAllAnswer_forest N m Rs rest hR, ← hTs, List.all_map]
    exact boolAll_congr_mem Ts _ _ (fun T hT => scanMixed_rawTreeCodes T)

theorem mixedAll_executes_observed_typed (p : MixedPorts K) (N m q L : ℕ)
    (s : CountdownStore K F) (rest : List Bool)
    (hs : MixedAllEntry p m (N + m * N + 3) L s)
    (hparse : rawForestMaskParse (s.stk (p (.outer .originalWord))).length q
      (s.stk (p (.outer .originalWord))) = some (rest, s.stk (p (.outer .originalMask))))
    (hcheck : forestMaskCellCheck N m (s.stk (p (.outer .originalWord)))
      (s.stk (p (.outer .originalMask))) = true) :
    ∃ Ts : List (BTree (Cell N m)), ∃ n : ℕ, Ts.length = q ∧
      s.stk (p (.outer .originalWord)) = Ts.flatMap treeBits ++ rest ∧
      n ≤ mixedAllBound m (N + m * N + 3) L ∧
      (mixedAllRoutine p).Executes s
        ⟨((s.state.1.1, false), Ts.all (scanMixed Prod.snd)), s.stk⟩ n := by
  obtain ⟨Ts, hq, hw, hans⟩ := mixedAllAnswer_observed_typed N m q
    (s.stk (p (.outer .originalWord))) (s.stk (p (.outer .originalMask))) rest hparse hcheck
  obtain ⟨n, hn, he⟩ := mixedAll_executes p m (N + m * N + 3) L s hs
  refine ⟨Ts, n, hq, hw, hn, ?_⟩
  simpa only [mixedAllResult, hans] using he

/- The local mixedness Boolean overwrites its incoming result. Entry must
be guarded by earlier whole-verifier success. Residual words remain
explicit; whole consumption comes from the original enclosing guards.
Markers, global coverage, actual root-inclusive score, bounded headers,
one inventory, monotone rejection and clean halt remain unclosed.
VerifierMachineWitness and EncodedSourceHardness remain independent.
-/

end PolytomyReductionModel.WholeVerifierController
