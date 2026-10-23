/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Continuation of the ONE restricted encoded marked-star verifier.
This module targets EVERY genuine node in EVERY supplied target tree,
including arbitrary composite-child internal nodes, and searches EVERY
genuine certificate node for the same CELL set. Candidate mismatch must
continue an existential search, not reject the entire pair immediately.

The final whole verifier, headers/guards/score/clean halt and the separate
encoded-source-hardness premise remain open. The exact point reached in
this module is stated at its end; definitions alone are not time proofs.
-/
import PolytomyWholeCellSetComposition

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K F : Type} [DecidableEq K]

inductive CladePort where
  | outer (port : RangeCursorPort)
  | inner (port : RangeCursorPort)
  | leftScope (port : IndexedSubtreePort)
  | rightScope (port : IndexedSubtreePort)
  | sets (port : InclusionPort)
  deriving DecidableEq, Fintype

abbrev CladePorts (K : Type) := CladePort ↪ K

@[simp] theorem cladePorts_eq (p : CladePorts K) (a b : CladePort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def cladeOuterPorts (p : CladePorts K) : RangeCursorPorts K where
  toFun := fun j => p (.outer j)
  inj' := by intro a b h; simpa using p.injective h

def cladeInnerPortMap : RangeCursorPort → CladePort
  | .rows => .outer .rows
  | .types => .outer .types
  | j => .inner j

theorem cladeInnerPortMap_injective : Function.Injective cladeInnerPortMap := by decide

def cladeInnerPorts (p : CladePorts K) : RangeCursorPorts K where
  toFun := fun j => p (cladeInnerPortMap j)
  inj' := fun _ _ h => cladeInnerPortMap_injective (p.injective h)

def cladeLeftScopePortMap : IndexedSubtreePort → CladePort
  | .original => .outer .word
  | j => .leftScope j

def cladeRightScopePortMap : IndexedSubtreePort → CladePort
  | .original => .inner .word
  | j => .rightScope j

theorem cladeLeftScopePortMap_injective : Function.Injective cladeLeftScopePortMap := by decide
theorem cladeRightScopePortMap_injective : Function.Injective cladeRightScopePortMap := by decide

def cladeLeftScopePorts (p : CladePorts K) : IndexedSubtreePorts K where
  toFun := fun j => p (cladeLeftScopePortMap j)
  inj' := fun _ _ h => cladeLeftScopePortMap_injective (p.injective h)

def cladeRightScopePorts (p : CladePorts K) : IndexedSubtreePorts K where
  toFun := fun j => p (cladeRightScopePortMap j)
  inj' := fun _ _ h => cladeRightScopePortMap_injective (p.injective h)

def cladeSetPortMap : InclusionPort → CladePort
  | .outer .originalWord => .outer .word
  | .outer .originalMask => .leftScope .output
  | .inner .originalWord => .inner .word
  | .inner .originalMask => .rightScope .output
  | .outer .rows => .outer .rows
  | .outer .types => .outer .types
  | j => .sets j

theorem cladeSetPortMap_injective : Function.Injective cladeSetPortMap := by decide

def cladeSetPorts (p : CladePorts K) : InclusionPorts K where
  toFun := fun j => p (cladeSetPortMap j)
  inj' := fun _ _ h => cladeSetPortMap_injective (p.injective h)

/-- The actual singleton-prefix parser supplies the candidate mask. The
candidate suffix may contain arbitrary later bytes; those bytes are not
part of the clade because the mask stops at the parsed subtree boundary. -/
def cladeCandidateContinue (m A : ℕ) (fixed fixedMask candidate : List Bool) : Bool :=
  match rawForestMaskParse candidate.length 1 candidate with
  | none => true
  | some (_, mask) => !cellSetWordsAnswer m A fixed fixedMask candidate mask

def cladeExistsAnswer (m A : ℕ) (fixed fixedMask certificate certificateMask : List Bool) : Bool :=
  !(rawMarkedSuffixes certificate certificateMask).all (cladeCandidateContinue m A fixed fixedMask)

def cladeFixedAnswer (m A : ℕ) (certificate certificateMask fixed : List Bool) : Bool :=
  match rawForestMaskParse fixed.length 1 fixed with
  | none => false
  | some (_, mask) => cladeExistsAnswer m A fixed mask certificate certificateMask

def allCladesAnswer (m A : ℕ) (target targetMask certificate certificateMask : List Bool) : Bool :=
  (rawMarkedSuffixes target targetMask).all (cladeFixedAnswer m A certificate certificateMask)

def subtreeScopeOwned (p : IndexedSubtreePorts K) : List K := [p .source, p .output]

def cladeCandidateParsed (p : CladePorts K) (s : CountdownStore K F) :=
  indexedSubtreeEval (cladeRightScopePorts p) 0 s

def cladeCandidateCompared (p : CladePorts K) (m A : ℕ) (s : CountdownStore K F) :=
  let u := cladeCandidateParsed p s
  if u.state.2 then cellSetResult (cladeSetPorts p) m A u else u

def cladeCandidateEval (p : CladePorts K) (m A : ℕ) (s : CountdownStore K F) :=
  inclusionSelectedOp.apply (clearManyEval (subtreeScopeOwned (cladeRightScopePorts p))
    (searchFlipOp.apply (cladeCandidateCompared p m A s)))

def cladeCandidateRoutine (p : CladePorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (indexedSubtreeRoutine (cladeRightScopePorts p))
    (RoutineComposition.seq
      (RoutineControl.branch Prod.snd (cellSetRoutine (cladeSetPorts p)) (Atom.routine cleanupNoop))
      (RoutineComposition.seq (Atom.routine searchFlipOp)
        (RoutineComposition.seq (clearManyRoutine (subtreeScopeOwned (cladeRightScopePorts p)))
          (Atom.routine inclusionSelectedOp))))

def cladeExistsRoutine (p : CladePorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (maskedAllRoutine (cladeInnerPorts p) (cladeCandidateRoutine p))
    (Atom.routine searchFlipOp)

def cladeExistsResult (p : CladePorts K) (m A : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨((s.state.1.1, false), cladeExistsAnswer m A
    (s.stk (p (.outer .word))) (s.stk (p (.leftScope .output)))
    (s.stk (p (.inner .originalWord))) (s.stk (p (.inner .originalMask)))), s.stk⟩

def cladeFixedParsed (p : CladePorts K) (s : CountdownStore K F) :=
  indexedSubtreeEval (cladeLeftScopePorts p) 0 s

def cladeFixedSearched (p : CladePorts K) (m A : ℕ) (s : CountdownStore K F) :=
  let u := cladeFixedParsed p s
  if u.state.2 then cladeExistsResult p m A u else u

def cladeFixedEval (p : CladePorts K) (m A : ℕ) (s : CountdownStore K F) :=
  inclusionSelectedOp.apply (clearManyEval (subtreeScopeOwned (cladeLeftScopePorts p))
    (cladeFixedSearched p m A s))

def cladeFixedRoutine (p : CladePorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (indexedSubtreeRoutine (cladeLeftScopePorts p))
    (RoutineComposition.seq
      (RoutineControl.branch Prod.snd (cladeExistsRoutine p) (Atom.routine cleanupNoop))
      (RoutineComposition.seq (clearManyRoutine (subtreeScopeOwned (cladeLeftScopePorts p)))
        (Atom.routine inclusionSelectedOp)))

def allCladesRoutine (p : CladePorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  maskedAllRoutine (cladeOuterPorts p) (cladeFixedRoutine p)

def ScopeEntry (p : IndexedSubtreePorts K) (L : ℕ) (s : CountdownStore K F) : Prop :=
  (s.stk (p .original)).length ≤ L ∧
  ∀ j : IndexedSubtreePort, j ≠ .original → s.stk (p j) = []

theorem scope_executes (p : IndexedSubtreePorts K) (L : ℕ) (s : CountdownStore K F)
    (hs : ScopeEntry p L s) :
    ∃ n ≤ 9 * L + 21, (indexedSubtreeRoutine p).Executes s (indexedSubtreeEval p 0 s) n := by
  obtain ⟨n, hn, he⟩ := indexedSubtree_executes p 0 s
    (hs.2 .index (by decide)) (hs.2 .source (by decide)) (hs.2 .discarded (by decide))
    (hs.2 .temp (by decide)) (hs.2 .pending (by decide))
    (hs.2 .reverse (by decide)) (hs.2 .output (by decide))
  exact ⟨n, by omega, he⟩

theorem scope_observation (p : IndexedSubtreePorts K) (s : CountdownStore K F) :
    indexedSubtreeObservation p (indexedSubtreeEval p 0 s) =
      rawForestMaskParse (s.stk (p .original)).length 1 (s.stk (p .original)) := by
  simpa only [rawIndexedSubtree, List.drop_zero] using indexedSubtree_observation p 0 s

theorem scope_success_consumption (p : IndexedSubtreePorts K) (s : CountdownStore K F)
    (hf : (indexedSubtreeEval p 0 s).state.2 = true) :
    ((indexedSubtreeEval p 0 s).stk (p .output)).length +
      ((indexedSubtreeEval p 0 s).stk (p .source)).length = (s.stk (p .original)).length := by
  have hp := scope_observation p s
  have hparse : rawForestMaskParse (s.stk (p .original)).length 1 (s.stk (p .original)) =
      some ((indexedSubtreeEval p 0 s).stk (p .source), (indexedSubtreeEval p 0 s).stk (p .output)) := by
    simpa only [indexedSubtreeObservation, hf, ↓reduceIte] using hp.symm
  exact rawForestMaskParse_consumption _ _ _ 1 hparse

theorem scope_bounds (p : IndexedSubtreePorts K) (s : CountdownStore K F) :
    ((indexedSubtreeEval p 0 s).stk (p .source)).length ≤ (s.stk (p .original)).length ∧
    ((indexedSubtreeEval p 0 s).stk (p .output)).length ≤ (s.stk (p .original)).length := by
  let u := replaySuffixResult (indexedSubtreeReplay p) 0 s
  have hu : u.stk (p .source) = s.stk (p .original) := by
    simpa only [indexedSubtreeReplay, List.drop_zero] using replaySuffix_source (indexedSubtreeReplay p) 0 s
  change ((treeMaskForwardResult (indexedSubtreeMask p) u.stk u.state.1
      (rawForestMaskParse (u.stk (p .source)).length 1 (u.stk (p .source)))).stk (p .source)).length ≤ _ ∧
    ((treeMaskForwardResult (indexedSubtreeMask p) u.stk u.state.1
      (rawForestMaskParse (u.stk (p .source)).length 1 (u.stk (p .source)))).stk (p .output)).length ≤ _
  rw [hu]
  cases hp : rawForestMaskParse (s.stk (p .original)).length 1 (s.stk (p .original)) with
  | none => simp [treeMaskForwardResult, treeMaskCallerStore, frameCallerStore, indexedSubtreeMask]
  | some pair =>
      rcases pair with ⟨rest, mask⟩
      have hlen := rawForestMaskParse_consumption (s.stk (p .original)) rest mask 1 hp
      simp only [treeMaskForwardResult, treeMaskCallerStore, frameCallerStore, indexedSubtreeMask]
      simp
      omega

theorem scope_cleaned_stacks (p : IndexedSubtreePorts K) (L : ℕ) (s : CountdownStore K F)
    (hs : ScopeEntry p L s) :
    (clearManyEval (subtreeScopeOwned p) (indexedSubtreeEval p 0 s)).stk = s.stk := by
  have hclean := indexedSubtree_work_clean p 0 s
  funext j
  by_cases howned : j ∈ subtreeScopeOwned p
  · rw [clearMany_member _ _ howned]
    simp only [subtreeScopeOwned, List.mem_cons, List.mem_singleton] at howned
    rcases howned with rfl | rfl
    · exact (hs.2 .source (by decide)).symm
    · exact (hs.2 .output (by decide)).symm
  · have hjs : j ≠ p .source := by intro h; apply howned; simp [subtreeScopeOwned, h]
    have hjo : j ≠ p .output := by intro h; apply howned; simp [subtreeScopeOwned, h]
    rw [clearMany_outside _ _ howned]
    by_cases hjp : j = p .pending
    · subst j; exact hclean.2.1.trans (hs.2 .pending (by decide)).symm
    by_cases hjr : j = p .reverse
    · subst j; exact hclean.2.2.1.trans (hs.2 .reverse (by decide)).symm
    by_cases hjd : j = p .discarded
    · subst j; exact hclean.2.2.2.trans (hs.2 .discarded (by decide)).symm
    exact indexedSubtree_extra p 0 s j hjs hjd hjp hjr hjo

def CladeCandidateInv (p : CladePorts K) (m A L : ℕ) (fixed fixedMask : List Bool)
    (stk : K → List Bool) : Prop :=
  (stk (p (.inner .word))).length ≤ L ∧
  stk (p (.outer .word)) = fixed ∧ stk (p (.leftScope .output)) = fixedMask ∧
  fixed.length ≤ L ∧ fixedMask.length ≤ fixed.length ∧
  stk (p (.outer .rows)) = List.replicate m true ∧
  stk (p (.outer .types)) = List.replicate A true ∧
  (∀ j : IndexedSubtreePort, j ≠ .original → stk ((cladeRightScopePorts p) j) = []) ∧
  ∀ j ∈ rangeAllWork (inclusionOuterPorts (cladeSetPorts p)) ++
      rangeAllWork (matchRangePorts (inclusionInnerPorts (cladeSetPorts p))), stk j = []

theorem cladeCandidate_scope_entry (p : CladePorts K) (m A L : ℕ) (fixed fixedMask : List Bool)
    (s : CountdownStore K F) (hs : CladeCandidateInv p m A L fixed fixedMask s.stk) :
    ScopeEntry (cladeRightScopePorts p) L s := ⟨hs.1, hs.2.2.2.2.2.2.2.1⟩

theorem cladeCandidate_parsed_set_entry (p : CladePorts K) (m A L : ℕ) (fixed fixedMask : List Bool)
    (s : CountdownStore K F) (hs : CladeCandidateInv p m A L fixed fixedMask s.stk) :
    CellSetEntry (cladeSetPorts p) m A L (cladeCandidateParsed p s) := by
  rcases hs with ⟨hL, hw, hm, hFL, hfit, hrows, htypes, hfresh, hsets⟩
  let r := cladeRightScopePorts p
  let u := cladeCandidateParsed p s
  have hx (j : K) (hjs : j ≠ r .source) (hjd : j ≠ r .discarded)
      (hjp : j ≠ r .pending) (hjr : j ≠ r .reverse) (hjo : j ≠ r .output) : u.stk j = s.stk j :=
    indexedSubtree_extra r 0 s j hjs hjd hjp hjr hjo
  have hfw : u.stk (p (.outer .word)) = fixed :=
    (hx _ (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])).trans hw
  have hfm : u.stk (p (.leftScope .output)) = fixedMask :=
    (hx _ (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])).trans hm
  have hcw : u.stk (p (.inner .word)) = s.stk (p (.inner .word)) :=
    hx _ (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
  have hcm := (scope_bounds r s).2
  have hrow : u.stk (p (.outer .rows)) = List.replicate m true :=
    (hx _ (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])).trans hrows
  have htype : u.stk (p (.outer .types)) = List.replicate A true :=
    (hx _ (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])
      (by simp [r, cladeRightScopePorts, cladeRightScopePortMap])).trans htypes
  have hclean (j : K) (hj : j ∈ rangeAllWork (inclusionOuterPorts (cladeSetPorts p)) ++
      rangeAllWork (matchRangePorts (inclusionInnerPorts (cladeSetPorts p)))) : u.stk j = [] := by
    have hne (a : IndexedSubtreePort) (ha : a ≠ .original) : j ≠ r a := by
      intro he; rw [he] at hj
      cases a <;> simp_all [rangeAllWork, inclusionOuterPorts, matchRangePorts,
        inclusionInnerPorts, inclusionMatchPortMap, cladeSetPorts, cladeSetPortMap,
        r, cladeRightScopePorts, cladeRightScopePortMap]
    exact (hx j (hne .source (by decide)) (hne .discarded (by decide))
      (hne .pending (by decide)) (hne .reverse (by decide)) (hne .output (by decide))).trans (hsets j hj)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hclean⟩
  · simpa [cladeSetPorts, cladeSetPortMap, hfw] using hFL
  · simpa [cladeSetPorts, cladeSetPortMap, hfw, hfm] using hfit
  · simpa [cladeSetPorts, cladeSetPortMap, hcw] using hL
  · simpa [cladeSetPorts, cladeSetPortMap, hcw, r, cladeRightScopePorts, cladeRightScopePortMap] using hcm
  · exact hrow
  · exact htype

theorem cladeCandidateCompared_stacks (p : CladePorts K) (m A : ℕ) (s : CountdownStore K F) :
    (cladeCandidateCompared p m A s).stk = (cladeCandidateParsed p s).stk := by
  unfold cladeCandidateCompared
  cases hf : (cladeCandidateParsed p s).state.2 <;> simp [hf, cellSetResult]

theorem cladeCandidate_result (p : CladePorts K) (m A L : ℕ) (fixed fixedMask : List Bool)
    (s : CountdownStore K F) (hs : CladeCandidateInv p m A L fixed fixedMask s.stk)
    (hselected : s.state.1.2 = true) :
    cladeCandidateEval p m A s = cellCompareFlagStore
      (cladeCandidateContinue m A fixed fixedMask (s.stk (p (.inner .word)))) s := by
  let r := cladeRightScopePorts p
  let u := cladeCandidateParsed p s
  have hx (j : CladePort) (hjs : j ≠ .rightScope .source) (hjd : j ≠ .rightScope .discarded)
      (hjp : j ≠ .rightScope .pending) (hjr : j ≠ .rightScope .reverse)
      (hjo : j ≠ .rightScope .output) : u.stk (p j) = s.stk (p j) :=
    indexedSubtree_extra r 0 s (p j)
      (by simpa [r, cladeRightScopePorts, cladeRightScopePortMap] using hjs)
      (by simpa [r, cladeRightScopePorts, cladeRightScopePortMap] using hjd)
      (by simpa [r, cladeRightScopePorts, cladeRightScopePortMap] using hjp)
      (by simpa [r, cladeRightScopePorts, cladeRightScopePortMap] using hjr)
      (by simpa [r, cladeRightScopePorts, cladeRightScopePortMap] using hjo)
  have hfw := (hx (.outer .word) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs.2.1
  have hfm := (hx (.leftScope .output) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs.2.2.1
  have hcw := hx (.inner .word) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hobs := scope_observation r s
  have hflag : !(cladeCandidateCompared p m A s).state.2 =
      cladeCandidateContinue m A fixed fixedMask (s.stk (p (.inner .word))) := by
    unfold cladeCandidateContinue
    rw [← hobs]
    cases hf : u.state.2 <;>
      simp [cladeCandidateCompared, indexedSubtreeObservation, hf, cellSetResult,
        cellSetAnswer_words, cladeSetPorts, cladeSetPortMap, hfw, hfm, hcw, u, r,
        cladeRightScopePorts, cladeRightScopePortMap]
  have hframe : (cladeCandidateCompared p m A s).state.1.1 = s.state.1.1 := by
    have hu := (indexedSubtree_work_clean r 0 s).1
    unfold cladeCandidateCompared
    cases hf : u.state.2 <;> simpa [hf, cellSetResult, u] using congrArg Prod.fst hu
  apply countdownStore_ext
  · change (((clearManyEval (subtreeScopeOwned r)
        (searchFlipOp.apply (cladeCandidateCompared p m A s))).state.1.1, true),
      (clearManyEval (subtreeScopeOwned r)
        (searchFlipOp.apply (cladeCandidateCompared p m A s))).state.2) = _
    rw [clearMany_state]
    change (((cladeCandidateCompared p m A s).state.1.1, true),
      !(cladeCandidateCompared p m A s).state.2) = _
    rw [hframe, hflag]
    exact Prod.ext (Prod.ext rfl hselected.symm) rfl
  · have hstack : (cladeCandidateEval p m A s).stk =
        (clearManyEval (subtreeScopeOwned r) (indexedSubtreeEval r 0 s)).stk := by
      simp only [cladeCandidateEval, inclusionSelectedOp, searchFlipOp, Op.apply,
        subtreeScopeOwned, clearManyEval, clearStackEval, cladeCandidateCompared_stacks,
        cladeCandidateParsed]
    rw [hstack]
    exact scope_cleaned_stacks r L s (cladeCandidate_scope_entry p m A L fixed fixedMask s hs)

def cladeCandidateBound (m A L : ℕ) : ℕ := 2 * cellSubsetBound m A L + 11 * L + 28

theorem cladeCandidate_executes (p : CladePorts K) (m A L : ℕ) (fixed fixedMask : List Bool)
    (s : CountdownStore K F) (hs : CladeCandidateInv p m A L fixed fixedMask s.stk)
    (hselected : s.state.1.2 = true) :
    ∃ n ≤ cladeCandidateBound m A L,
      (cladeCandidateRoutine p).Executes s
        (cellCompareFlagStore (cladeCandidateContinue m A fixed fixedMask (s.stk (p (.inner .word)))) s) n := by
  let r := cladeRightScopePorts p
  let u := cladeCandidateParsed p s
  let v := cladeCandidateCompared p m A s
  obtain ⟨a, ha, h1⟩ := scope_executes r L s (cladeCandidate_scope_entry p m A L fixed fixedMask s hs)
  have hentry := cladeCandidate_parsed_set_entry p m A L fixed fixedMask s hs
  have hbranch : ∃ n ≤ 2 * cellSubsetBound m A L + 2,
      (RoutineControl.branch Prod.snd (cellSetRoutine (cladeSetPorts p)) (Atom.routine cleanupNoop)).Executes u v n := by
    cases hf : u.state.2 with
    | false =>
        have he := RoutineControl.branch_false Prod.snd (cellSetRoutine (cladeSetPorts p))
          (Atom.routine cleanupNoop) hf (Atom.executes cleanupNoop u)
        refine ⟨2, by omega, ?_⟩
        simpa only [v, cladeCandidateCompared, hf, Bool.false_eq_true, ↓reduceIte, cleanupNoop, Op.apply] using he
    | true =>
        obtain ⟨n, hn, he⟩ := cellSet_executes (cladeSetPorts p) m A L u hentry
        have hb := RoutineControl.branch_true Prod.snd (cellSetRoutine (cladeSetPorts p))
          (Atom.routine cleanupNoop) hf he
        refine ⟨n + 1, by omega, ?_⟩
        simpa only [v, cladeCandidateCompared, hf, ↓reduceIte] using hb
  obtain ⟨b, hb, h2⟩ := hbranch
  have h3 := Atom.executes (searchFlipOp (K := K) (F := F)) v
  obtain ⟨c, hc, h4⟩ := clearMany_executes (subtreeScopeOwned r) (searchFlipOp.apply v)
  have hbds := scope_bounds r s
  have hmass : cleanupMass (subtreeScopeOwned r) (searchFlipOp.apply v) ≤ 2 * L := by
    simp only [cleanupMass, subtreeScopeOwned, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, searchFlipOp, Op.apply, v, cladeCandidateCompared_stacks]
    have hL := hs.1
    simp only [r, cladeRightScopePorts, cladeRightScopePortMap] at hbds
    omega
  have h5 := Atom.executes (inclusionSelectedOp (K := K) (F := F))
    (clearManyEval (subtreeScopeOwned r) (searchFlipOp.apply v))
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
    (RoutineComposition.seq_executes _ _ h3 (RoutineComposition.seq_executes _ _ h4 h5)))
  change (cladeCandidateRoutine p).Executes s (cladeCandidateEval p m A s) _ at he
  rw [cladeCandidate_result p m A L fixed fixedMask s hs hselected] at he
  refine ⟨a + (b + (1 + (c + 1))), ?_, he⟩
  simp only [subtreeScopeOwned, List.length_cons, List.length_nil] at hc
  unfold cladeCandidateBound
  omega

theorem cladeCandidateInv_transport (p : CladePorts K) (m A L : ℕ) (fixed fixedMask : List Bool)
    (stk stk' : K → List Bool) (hs : CladeCandidateInv p m A L fixed fixedMask stk)
    (hL : (stk' (p (.inner .word))).length ≤ L)
    (hx : ∀ j, j ≠ p (.inner .word) → j ≠ p (.inner .mask) → j ≠ p (.inner .counter) → stk' j = stk j) :
    CladeCandidateInv p m A L fixed fixedMask stk' := by
  rcases hs with ⟨_, hw, hm, hFL, hfit, hrows, htypes, hfresh, hsets⟩
  refine ⟨hL, ?_, ?_, hFL, hfit, ?_, ?_, ?_, ?_⟩
  · exact (hx _ (by simp) (by simp) (by simp)).trans hw
  · exact (hx _ (by simp) (by simp) (by simp)).trans hm
  · exact (hx _ (by simp) (by simp) (by simp)).trans hrows
  · exact (hx _ (by simp) (by simp) (by simp)).trans htypes
  · intro j hj
    have hn (a : RangeCursorPort) : (cladeRightScopePorts p) j ≠ p (.inner a) := by
      cases j <;> simp_all [cladeRightScopePorts, cladeRightScopePortMap]
    exact (hx _ (hn .word) (hn .mask) (hn .counter)).trans (hfresh j hj)
  · intro j hj
    have hn (a : RangeCursorPort) : j ≠ p (.inner a) := by
      intro he; rw [he] at hj
      cases a <;> simp_all [rangeAllWork, inclusionOuterPorts, matchRangePorts,
        inclusionInnerPorts, inclusionMatchPortMap, cladeSetPorts, cladeSetPortMap]
    exact (hx j (hn .word) (hn .mask) (hn .counter)).trans (hsets j hj)

def cladeCandidateContract (p : CladePorts K) (m A L : ℕ) (fixed fixedMask : List Bool) :
    MaskedQueryContract (cladeInnerPorts p) (cladeCandidateRoutine p)
      (cladeCandidateContinue m A fixed fixedMask) (CladeCandidateInv p m A L fixed fixedMask)
      (cladeCandidateBound m A L) where
  positive := by unfold cladeCandidateBound; omega
  query_executes s hs hselected := cladeCandidate_executes p m A L fixed fixedMask s hs hselected
  cursor_closed stk hs := by
    apply cladeCandidateInv_transport p m A L fixed fixedMask stk _ hs
    · have ht : (stk (p (.inner .word))).tail.length ≤ (stk (p (.inner .word))).length := by
        cases stk (p (.inner .word)) <;> simp
      simpa [cladeInnerPorts, cladeInnerPortMap] using ht.trans hs.1
    · intro j hjw hjm hjc
      simp [cladeInnerPorts, cladeInnerPortMap, hjw, hjm]
  counter_closed stk hs := by
    apply cladeCandidateInv_transport p m A L fixed fixedMask stk _ hs
    · simpa [cladeInnerPorts, cladeInnerPortMap] using hs.1
    · intro j hjw hjm hjc
      simp [cladeInnerPorts, cladeInnerPortMap, hjc]

def CladeExistsEntry (p : CladePorts K) (m A L : ℕ) (fixed fixedMask : List Bool)
    (s : CountdownStore K F) : Prop :=
  RangeAllEntry (cladeInnerPorts p) m A L s ∧
  s.stk (p (.outer .word)) = fixed ∧ s.stk (p (.leftScope .output)) = fixedMask ∧
  fixed.length ≤ L ∧ fixedMask.length ≤ fixed.length ∧
  (∀ j : IndexedSubtreePort, j ≠ .original → s.stk ((cladeRightScopePorts p) j) = []) ∧
  ∀ j ∈ rangeAllWork (inclusionOuterPorts (cladeSetPorts p)) ++
      rangeAllWork (matchRangePorts (inclusionInnerPorts (cladeSetPorts p))), s.stk j = []

theorem cladeExists_prepared_inv (p : CladePorts K) (m A L : ℕ) (fixed fixedMask : List Bool)
    (s : CountdownStore K F) (hs : CladeExistsEntry p m A L fixed fixedMask s) :
    CladeCandidateInv p m A L fixed fixedMask (rangeAllPrepared (cladeInnerPorts p) s).stk := by
  rcases hs with ⟨⟨hL, hfit, hm, hA, hwork⟩, hw, hmask, hFL, hFfit, hscope, hsets⟩
  let i := cladeInnerPorts p
  have hf (j : RangeCursorPort) (hj : i j ∈ rangeAllWork i) : s.stk (i j) = [] := hwork _ hj
  have hw0 := hf .word (by simp [rangeAllWork])
  have hm0 := hf .mask (by simp [rangeAllWork])
  have hc0 := hf .counter (by simp [rangeAllWork])
  have hbase : CladeCandidateInv p m A L fixed fixedMask s.stk := by
    refine ⟨?_, hw, hmask, hFL, hFfit, hm, hA, hscope, hsets⟩
    simpa only [i, cladeInnerPorts, cladeInnerPortMap, hw0, List.length_nil] using Nat.zero_le L
  have hstk := rangeAllPrepared_stacks i s hw0 hm0 hc0
  apply cladeCandidateInv_transport p m A L fixed fixedMask s.stk _ hbase
  · rw [hstk]
    simpa [i, cladeInnerPorts, cladeInnerPortMap] using hL
  · intro j hjw hjm hjc
    rw [hstk]
    simp [i, cladeInnerPorts, cladeInnerPortMap, hjw, hjm, hjc]

def cladeExistsBound (m A L : ℕ) : ℕ := L * (cladeCandidateBound m A L + 7) + 12 * L + 18

theorem cladeExists_executes (p : CladePorts K) (m A L : ℕ) (fixed fixedMask : List Bool)
    (s : CountdownStore K F) (hs : CladeExistsEntry p m A L fixed fixedMask s) :
    ∃ n ≤ cladeExistsBound m A L,
      (cladeExistsRoutine p).Executes s (cladeExistsResult p m A s) n := by
  let i := cladeInnerPorts p
  let q := cladeCandidateContinue m A fixed fixedMask
  have hf (j : RangeCursorPort) (hj : i j ∈ rangeAllWork i) : s.stk (i j) = [] := hs.1.2.2.2.2 _ hj
  obtain ⟨n, hn, he⟩ := maskedAll_executes i (cladeCandidateRoutine p) q
    (CladeCandidateInv p m A L fixed fixedMask) (cladeCandidateBound m A L) L
    (cladeCandidateContract p m A L fixed fixedMask) s hs.1.1 hs.1.2.1
    (hf .word (by simp [rangeAllWork])) (hf .mask (by simp [rangeAllWork]))
    (hf .counter (by simp [rangeAllWork])) (hf .temp (by simp [rangeAllWork]))
    (cladeExists_prepared_inv p m A L fixed fixedMask s hs)
  have hflip := Atom.executes (searchFlipOp (K := K) (F := F)) (maskedAllResult i q s)
  have hresult : searchFlipOp.apply (maskedAllResult i q s) = cladeExistsResult p m A s := by
    apply countdownStore_ext
    · simp [searchFlipOp, Op.apply, maskedAllResult, cladeExistsResult, cladeExistsAnswer,
        i, cladeInnerPorts, cladeInnerPortMap, q, hs.2.1, hs.2.2.1]
    · rfl
  rw [hresult] at hflip
  exact ⟨n + 1, by unfold cladeExistsBound; omega, RoutineComposition.seq_executes _ _ he hflip⟩

def CladeFixedInv (p : CladePorts K) (m A L : ℕ) (certificate certificateMask : List Bool)
    (stk : K → List Bool) : Prop :=
  (stk (p (.outer .word))).length ≤ L ∧
  stk (p (.inner .originalWord)) = certificate ∧ stk (p (.inner .originalMask)) = certificateMask ∧
  certificate.length ≤ L ∧ certificateMask.length ≤ certificate.length ∧
  stk (p (.outer .rows)) = List.replicate m true ∧
  stk (p (.outer .types)) = List.replicate A true ∧
  (∀ j : IndexedSubtreePort, j ≠ .original → stk ((cladeLeftScopePorts p) j) = []) ∧
  (∀ j : IndexedSubtreePort, j ≠ .original → stk ((cladeRightScopePorts p) j) = []) ∧
  (∀ j ∈ rangeAllWork (cladeInnerPorts p), stk j = []) ∧
  ∀ j ∈ rangeAllWork (inclusionOuterPorts (cladeSetPorts p)) ++
      rangeAllWork (matchRangePorts (inclusionInnerPorts (cladeSetPorts p))), stk j = []

theorem cladeFixed_scope_entry (p : CladePorts K) (m A L : ℕ) (certificate certificateMask : List Bool)
    (s : CountdownStore K F) (hs : CladeFixedInv p m A L certificate certificateMask s.stk) :
    ScopeEntry (cladeLeftScopePorts p) L s := ⟨hs.1, hs.2.2.2.2.2.2.2.1⟩

theorem cladeFixed_parsed_exists_entry (p : CladePorts K) (m A L : ℕ) (certificate certificateMask : List Bool)
    (s : CountdownStore K F) (hs : CladeFixedInv p m A L certificate certificateMask s.stk) :
    let u := cladeFixedParsed p s
    CladeExistsEntry p m A L (s.stk (p (.outer .word))) (u.stk (p (.leftScope .output))) u := by
  rcases hs with ⟨hL, hw, hm, hCL, hfit, hrows, htypes, hleft, hright, hinner, hsets⟩
  let l := cladeLeftScopePorts p
  let u := cladeFixedParsed p s
  have hx (j : K) (hjs : j ≠ l .source) (hjd : j ≠ l .discarded)
      (hjp : j ≠ l .pending) (hjr : j ≠ l .reverse) (hjo : j ≠ l .output) : u.stk j = s.stk j :=
    indexedSubtree_extra l 0 s j hjs hjd hjp hjr hjo
  have hc (j : RangeCursorPort) : u.stk (p (.inner j)) = s.stk (p (.inner j)) :=
    hx _ (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
  have ho (j : RangeCursorPort) : u.stk (p (.outer j)) = s.stk (p (.outer j)) :=
    hx _ (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
  have hiFresh (j : K) (hj : j ∈ rangeAllWork (cladeInnerPorts p)) : u.stk j = [] := by
    have hn (a : IndexedSubtreePort) (ha : a ≠ .original) : j ≠ l a := by
      intro he; rw [he] at hj
      cases a <;> simp_all [rangeAllWork, cladeInnerPorts, cladeInnerPortMap,
        l, cladeLeftScopePorts, cladeLeftScopePortMap]
    exact (hx j (hn .source (by decide)) (hn .discarded (by decide))
      (hn .pending (by decide)) (hn .reverse (by decide)) (hn .output (by decide))).trans (hinner j hj)
  have hrightFresh (j : IndexedSubtreePort) (hj : j ≠ .original) :
      u.stk ((cladeRightScopePorts p) j) = [] := by
    have hn (a : IndexedSubtreePort) (ha : a ≠ .original) : (cladeRightScopePorts p) j ≠ l a := by
      cases j <;> cases a <;> simp_all [l, cladeLeftScopePorts, cladeLeftScopePortMap,
        cladeRightScopePorts, cladeRightScopePortMap]
    exact (hx _ (hn .source (by decide)) (hn .discarded (by decide))
      (hn .pending (by decide)) (hn .reverse (by decide)) (hn .output (by decide))).trans (hright j hj)
  have hsFresh (j : K) (hj : j ∈ rangeAllWork (inclusionOuterPorts (cladeSetPorts p)) ++
      rangeAllWork (matchRangePorts (inclusionInnerPorts (cladeSetPorts p)))) : u.stk j = [] := by
    have hn (a : IndexedSubtreePort) (ha : a ≠ .original) : j ≠ l a := by
      intro he; rw [he] at hj
      cases a <;> simp_all [rangeAllWork, inclusionOuterPorts, matchRangePorts,
        inclusionInnerPorts, inclusionMatchPortMap, cladeSetPorts, cladeSetPortMap,
        l, cladeLeftScopePorts, cladeLeftScopePortMap]
    exact (hx j (hn .source (by decide)) (hn .discarded (by decide))
      (hn .pending (by decide)) (hn .reverse (by decide)) (hn .output (by decide))).trans (hsets j hj)
  have hb := (scope_bounds l s).2
  refine ⟨⟨?_, ?_, ?_, ?_, hiFresh⟩, ho .word, rfl, hL, ?_, hrightFresh, hsFresh⟩
  · simpa [cladeInnerPorts, cladeInnerPortMap, hc, hw] using hCL
  · simpa [cladeInnerPorts, cladeInnerPortMap, hc, hw, hm] using hfit
  · exact (ho .rows).trans hrows
  · exact (ho .types).trans htypes
  · exact hb

theorem cladeFixedSearched_stacks (p : CladePorts K) (m A : ℕ) (s : CountdownStore K F) :
    (cladeFixedSearched p m A s).stk = (cladeFixedParsed p s).stk := by
  unfold cladeFixedSearched
  cases hf : (cladeFixedParsed p s).state.2 <;> simp [hf, cladeExistsResult]

theorem cladeFixed_result (p : CladePorts K) (m A L : ℕ) (certificate certificateMask : List Bool)
    (s : CountdownStore K F) (hs : CladeFixedInv p m A L certificate certificateMask s.stk)
    (hselected : s.state.1.2 = true) :
    cladeFixedEval p m A s = cellCompareFlagStore
      (cladeFixedAnswer m A certificate certificateMask (s.stk (p (.outer .word)))) s := by
  let l := cladeLeftScopePorts p
  let u := cladeFixedParsed p s
  have hx (j : RangeCursorPort) : u.stk (p (.inner j)) = s.stk (p (.inner j)) :=
    indexedSubtree_extra l 0 s _ (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
  have how : u.stk (p (.outer .word)) = s.stk (p (.outer .word)) :=
    indexedSubtree_extra l 0 s _ (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
      (by simp [l, cladeLeftScopePorts, cladeLeftScopePortMap])
  have hobs := scope_observation l s
  have hflag : (cladeFixedSearched p m A s).state.2 =
      cladeFixedAnswer m A certificate certificateMask (s.stk (p (.outer .word))) := by
    unfold cladeFixedAnswer
    rw [← hobs]
    cases hf : u.state.2 <;>
      simp [cladeFixedSearched, indexedSubtreeObservation, hf, cladeExistsResult, hx, how,
        hs.2.1, hs.2.2.1, u, l, cladeLeftScopePorts, cladeLeftScopePortMap]
  have hframe : (cladeFixedSearched p m A s).state.1.1 = s.state.1.1 := by
    have hu := (indexedSubtree_work_clean l 0 s).1
    unfold cladeFixedSearched
    cases hf : u.state.2 <;> simpa [hf, cladeExistsResult, u] using congrArg Prod.fst hu
  apply countdownStore_ext
  · change (((clearManyEval (subtreeScopeOwned l) (cladeFixedSearched p m A s)).state.1.1, true),
      (clearManyEval (subtreeScopeOwned l) (cladeFixedSearched p m A s)).state.2) = _
    rw [clearMany_state, hframe, hflag]
    exact Prod.ext (Prod.ext rfl hselected.symm) rfl
  · have hstack : (cladeFixedEval p m A s).stk =
        (clearManyEval (subtreeScopeOwned l) (indexedSubtreeEval l 0 s)).stk := by
      simp only [cladeFixedEval, inclusionSelectedOp, Op.apply, subtreeScopeOwned,
        clearManyEval, clearStackEval, cladeFixedSearched_stacks, cladeFixedParsed]
    rw [hstack]
    exact scope_cleaned_stacks l L s (cladeFixed_scope_entry p m A L certificate certificateMask s hs)

def cladeFixedBound (m A L : ℕ) : ℕ := cladeExistsBound m A L + 11 * L + 26

theorem cladeFixed_executes (p : CladePorts K) (m A L : ℕ) (certificate certificateMask : List Bool)
    (s : CountdownStore K F) (hs : CladeFixedInv p m A L certificate certificateMask s.stk)
    (hselected : s.state.1.2 = true) :
    ∃ n ≤ cladeFixedBound m A L,
      (cladeFixedRoutine p).Executes s
        (cellCompareFlagStore (cladeFixedAnswer m A certificate certificateMask (s.stk (p (.outer .word)))) s) n := by
  let l := cladeLeftScopePorts p
  let u := cladeFixedParsed p s
  let v := cladeFixedSearched p m A s
  obtain ⟨a, ha, h1⟩ := scope_executes l L s (cladeFixed_scope_entry p m A L certificate certificateMask s hs)
  have hentry := cladeFixed_parsed_exists_entry p m A L certificate certificateMask s hs
  have hbranch : ∃ n ≤ cladeExistsBound m A L + 1,
      (RoutineControl.branch Prod.snd (cladeExistsRoutine p) (Atom.routine cleanupNoop)).Executes u v n := by
    cases hf : u.state.2 with
    | false =>
        have he := RoutineControl.branch_false Prod.snd (cladeExistsRoutine p)
          (Atom.routine cleanupNoop) hf (Atom.executes cleanupNoop u)
        have hpos : 1 ≤ cladeExistsBound m A L := by unfold cladeExistsBound; omega
        refine ⟨2, by omega, ?_⟩
        simpa only [v, cladeFixedSearched, hf, Bool.false_eq_true, ↓reduceIte, cleanupNoop, Op.apply] using he
    | true =>
        obtain ⟨n, hn, he⟩ := cladeExists_executes p m A L
          (s.stk (p (.outer .word))) (u.stk (p (.leftScope .output))) u hentry
        have hb := RoutineControl.branch_true Prod.snd (cladeExistsRoutine p) (Atom.routine cleanupNoop) hf he
        refine ⟨n + 1, by omega, ?_⟩
        simpa only [v, cladeFixedSearched, hf, ↓reduceIte] using hb
  obtain ⟨b, hb, h2⟩ := hbranch
  obtain ⟨c, hc, h3⟩ := clearMany_executes (subtreeScopeOwned l) v
  have hbds := scope_bounds l s
  have hmass : cleanupMass (subtreeScopeOwned l) v ≤ 2 * L := by
    simp only [cleanupMass, subtreeScopeOwned, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, v, cladeFixedSearched_stacks]
    have hL := hs.1
    simp only [l, cladeLeftScopePorts, cladeLeftScopePortMap] at hbds
    omega
  have h4 := Atom.executes (inclusionSelectedOp (K := K) (F := F)) (clearManyEval (subtreeScopeOwned l) v)
  have he := RoutineComposition.seq_executes _ _ h1 (RoutineComposition.seq_executes _ _ h2
    (RoutineComposition.seq_executes _ _ h3 h4))
  change (cladeFixedRoutine p).Executes s (cladeFixedEval p m A s) _ at he
  rw [cladeFixed_result p m A L certificate certificateMask s hs hselected] at he
  refine ⟨a + (b + (c + 1)), ?_, he⟩
  simp only [subtreeScopeOwned, List.length_cons, List.length_nil] at hc
  unfold cladeFixedBound
  omega

theorem cladeFixedInv_transport (p : CladePorts K) (m A L : ℕ) (certificate certificateMask : List Bool)
    (stk stk' : K → List Bool) (hs : CladeFixedInv p m A L certificate certificateMask stk)
    (hL : (stk' (p (.outer .word))).length ≤ L)
    (hx : ∀ j, j ≠ p (.outer .word) → j ≠ p (.outer .mask) → j ≠ p (.outer .counter) → stk' j = stk j) :
    CladeFixedInv p m A L certificate certificateMask stk' := by
  rcases hs with ⟨_, hw, hm, hCL, hfit, hrows, htypes, hleft, hright, hinner, hsets⟩
  refine ⟨hL, ?_, ?_, hCL, hfit, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hx _ (by simp) (by simp) (by simp)).trans hw
  · exact (hx _ (by simp) (by simp) (by simp)).trans hm
  · exact (hx _ (by simp) (by simp) (by simp)).trans hrows
  · exact (hx _ (by simp) (by simp) (by simp)).trans htypes
  · intro j hj
    have hn (a : RangeCursorPort) : (cladeLeftScopePorts p) j ≠ p (.outer a) := by
      cases j <;> simp_all [cladeLeftScopePorts, cladeLeftScopePortMap]
    exact (hx _ (hn .word) (hn .mask) (hn .counter)).trans (hleft j hj)
  · intro j hj
    have hn (a : RangeCursorPort) : (cladeRightScopePorts p) j ≠ p (.outer a) := by
      cases j <;> simp_all [cladeRightScopePorts, cladeRightScopePortMap]
    exact (hx _ (hn .word) (hn .mask) (hn .counter)).trans (hright j hj)
  · intro j hj
    have hn (a : RangeCursorPort) : j ≠ p (.outer a) := by
      intro he; rw [he] at hj
      cases a <;> simp_all [rangeAllWork, cladeInnerPorts, cladeInnerPortMap]
    exact (hx j (hn .word) (hn .mask) (hn .counter)).trans (hinner j hj)
  · intro j hj
    have hn (a : RangeCursorPort) : j ≠ p (.outer a) := by
      intro he; rw [he] at hj
      cases a <;> simp_all [rangeAllWork, inclusionOuterPorts, matchRangePorts,
        inclusionInnerPorts, inclusionMatchPortMap, cladeSetPorts, cladeSetPortMap]
    exact (hx j (hn .word) (hn .mask) (hn .counter)).trans (hsets j hj)

def cladeFixedContract (p : CladePorts K) (m A L : ℕ) (certificate certificateMask : List Bool) :
    MaskedQueryContract (cladeOuterPorts p) (cladeFixedRoutine p)
      (cladeFixedAnswer m A certificate certificateMask) (CladeFixedInv p m A L certificate certificateMask)
      (cladeFixedBound m A L) where
  positive := by unfold cladeFixedBound; omega
  query_executes s hs hselected := cladeFixed_executes p m A L certificate certificateMask s hs hselected
  cursor_closed stk hs := by
    apply cladeFixedInv_transport p m A L certificate certificateMask stk _ hs
    · have ht : (stk (p (.outer .word))).tail.length ≤ (stk (p (.outer .word))).length := by
        cases stk (p (.outer .word)) <;> simp
      simpa [cladeOuterPorts] using ht.trans hs.1
    · intro j hjw hjm hjc
      simp [cladeOuterPorts, hjw, hjm]
  counter_closed stk hs := by
    apply cladeFixedInv_transport p m A L certificate certificateMask stk _ hs
    · simpa [cladeOuterPorts] using hs.1
    · intro j hjw hjm hjc
      simp [cladeOuterPorts, hjc]

def AllCladesEntry (p : CladePorts K) (m A L : ℕ) (certificate certificateMask : List Bool)
    (s : CountdownStore K F) : Prop :=
  RangeAllEntry (cladeOuterPorts p) m A L s ∧
  s.stk (p (.inner .originalWord)) = certificate ∧ s.stk (p (.inner .originalMask)) = certificateMask ∧
  certificate.length ≤ L ∧ certificateMask.length ≤ certificate.length ∧
  (∀ j : IndexedSubtreePort, j ≠ .original → s.stk ((cladeLeftScopePorts p) j) = []) ∧
  (∀ j : IndexedSubtreePort, j ≠ .original → s.stk ((cladeRightScopePorts p) j) = []) ∧
  (∀ j ∈ rangeAllWork (cladeInnerPorts p), s.stk j = []) ∧
  ∀ j ∈ rangeAllWork (inclusionOuterPorts (cladeSetPorts p)) ++
      rangeAllWork (matchRangePorts (inclusionInnerPorts (cladeSetPorts p))), s.stk j = []

theorem allClades_prepared_inv (p : CladePorts K) (m A L : ℕ) (certificate certificateMask : List Bool)
    (s : CountdownStore K F) (hs : AllCladesEntry p m A L certificate certificateMask s) :
    CladeFixedInv p m A L certificate certificateMask (rangeAllPrepared (cladeOuterPorts p) s).stk := by
  rcases hs with ⟨⟨hL, hfit, hm, hA, hwork⟩, hw, hmask, hCL, hCfit, hleft, hright, hinner, hsets⟩
  let o := cladeOuterPorts p
  have hf (j : RangeCursorPort) (hj : o j ∈ rangeAllWork o) : s.stk (o j) = [] := hwork _ hj
  have hw0 := hf .word (by simp [rangeAllWork])
  have hm0 := hf .mask (by simp [rangeAllWork])
  have hc0 := hf .counter (by simp [rangeAllWork])
  have hbase : CladeFixedInv p m A L certificate certificateMask s.stk := by
    refine ⟨?_, hw, hmask, hCL, hCfit, hm, hA, hleft, hright, hinner, hsets⟩
    simpa only [o, cladeOuterPorts, hw0, List.length_nil] using Nat.zero_le L
  have hstk := rangeAllPrepared_stacks o s hw0 hm0 hc0
  apply cladeFixedInv_transport p m A L certificate certificateMask s.stk _ hbase
  · rw [hstk]
    simpa [o, cladeOuterPorts] using hL
  · intro j hjw hjm hjc
    rw [hstk]
    simp [o, cladeOuterPorts, hjw, hjm, hjc]

def allCladesResult (p : CladePorts K) (m A : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  ⟨((s.state.1.1, false), allCladesAnswer m A
    (s.stk (p (.outer .originalWord))) (s.stk (p (.outer .originalMask)))
    (s.stk (p (.inner .originalWord))) (s.stk (p (.inner .originalMask)))), s.stk⟩

def allCladesBound (m A L : ℕ) : ℕ := L * (cladeFixedBound m A L + 7) + 12 * L + 17

/-- This is the actual universal/existential/set-equality nest, not a
query oracle. It is defined on all saved words/masks satisfying physical
length/freshness conditions; its clade interpretation additionally uses
the preceding parser/range observations below. All incoming tapes are
restored, including on an early negative answer. -/
theorem allClades_executes (p : CladePorts K) (m A L : ℕ) (certificate certificateMask : List Bool)
    (s : CountdownStore K F) (hs : AllCladesEntry p m A L certificate certificateMask s) :
    ∃ n ≤ allCladesBound m A L,
      (allCladesRoutine p).Executes s (allCladesResult p m A s) n := by
  let o := cladeOuterPorts p
  let q := cladeFixedAnswer m A certificate certificateMask
  have hf (j : RangeCursorPort) (hj : o j ∈ rangeAllWork o) : s.stk (o j) = [] := hs.1.2.2.2.2 _ hj
  obtain ⟨n, hn, he⟩ := maskedAll_executes o (cladeFixedRoutine p) q
    (CladeFixedInv p m A L certificate certificateMask) (cladeFixedBound m A L) L
    (cladeFixedContract p m A L certificate certificateMask) s hs.1.1 hs.1.2.1
    (hf .word (by simp [rangeAllWork])) (hf .mask (by simp [rangeAllWork]))
    (hf .counter (by simp [rangeAllWork])) (hf .temp (by simp [rangeAllWork]))
    (allClades_prepared_inv p m A L certificate certificateMask s hs)
  have hresult : maskedAllResult o q s = allCladesResult p m A s := by
    apply countdownStore_ext
    · simp only [maskedAllResult, allCladesResult, allCladesAnswer, o, cladeOuterPorts,
        q, hs.2.1, hs.2.2.1]
    · rfl
  rw [hresult] at he
  exact ⟨n, hn, he⟩

/-- Pointwise equality is needed only on actually visited views. -/
theorem boolAll_congr_mem {X : Type} (xs : List X) (f g : X → Bool)
    (h : ∀ x ∈ xs, f x = g x) : xs.all f = xs.all g := by
  apply bool_eq_of_true_iff
  simp only [List.all_eq_true]
  constructor
  · intro hf x hx
    rw [← h x hx]
    exact hf x hx
  · intro hg x hx
    rw [h x hx]
    exact hg x hx

theorem rawNodeViews_valid (N m : ℕ) (R : BTree (ℕ × ℕ)) (rest : List Bool)
    (hR : rawTreeValid N m R) :
    ∀ v ∈ rawNodeViews R rest, rawTreeValid N m v.1 := by
  revert hR
  induction R generalizing rest with
  | leaf c =>
      intro hR v hv
      have he : v = (BTree.leaf c, rest) := by simpa only [rawNodeViews, List.mem_singleton] using hv
      simpa only [he] using hR
  | node l r ihl ihr =>
      intro hR
      have hlr := (rawTreeValid_node N m l r).mp hR
      intro v hv
      have hm : v = (BTree.node l r, rest) ∨
          v ∈ rawNodeViews l (rawCellTreeBits r ++ rest) ∨ v ∈ rawNodeViews r rest := by
        simpa only [rawNodeViews, List.mem_cons, List.mem_append] using hv
      rcases hm with he | hv | hv
      · simpa only [he] using hR
      · exact ihl (rawCellTreeBits r ++ rest) hlr.1 v hv
      · exact ihr rest hlr.2 v hv

theorem cellSetWords_trees (N m : ℕ) (R U : BTree (ℕ × ℕ)) (rest tail : List Bool)
    (hR : rawTreeValid N m R) (hU : rawTreeValid N m U) :
    cellSetWordsAnswer m (N + m * N + 3)
      (rawCellTreeBits R ++ rest) (rawNodeMask R) (rawCellTreeBits U ++ tail) (rawNodeMask U) =
      scanSetEq (scanLeaves R) (scanLeaves U) := by
  have hRs : ∀ T ∈ [R], rawTreeValid N m T := by intro T h; simpa only [List.mem_singleton.mp h] using hR
  have hUs : ∀ T ∈ [U], rawTreeValid N m T := by intro T h; simpa only [List.mem_singleton.mp h] using hU
  have hl := inclusionCheck_forest_valid N m [R] [U] rest tail hRs hUs
  have hr := inclusionCheck_forest_valid N m [U] [R] tail rest hUs hRs
  simp only [rawForestWord, rawForestNodeMask, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] at hl hr
  rw [cellSetWordsAnswer, hl, hr]
  rfl

theorem cladeCandidateContinue_trees (N m : ℕ) (R U : BTree (ℕ × ℕ)) (rest tail : List Bool)
    (hR : rawTreeValid N m R) (hU : rawTreeValid N m U) :
    cladeCandidateContinue m (N + m * N + 3)
      (rawCellTreeBits R ++ rest) (rawNodeMask R) (rawCellTreeBits U ++ tail) =
      !scanSetEq (scanLeaves R) (scanLeaves U) := by
  rw [cladeCandidateContinue, rawForestMaskParse_one]
  exact congrArg Bool.not (cellSetWords_trees N m R U rest tail hR hU)

theorem cladeExistsAnswer_trees (N m : ℕ) (R U : BTree (ℕ × ℕ)) (rest tail : List Bool)
    (hR : rawTreeValid N m R) (hU : rawTreeValid N m U) :
    cladeExistsAnswer m (N + m * N + 3)
      (rawCellTreeBits R ++ rest) (rawNodeMask R) (rawCellTreeBits U ++ tail) (rawNodeMask U) =
      (scanClades U).any (fun ys => scanSetEq (scanLeaves R) ys) := by
  have hviews : rawMarkedSuffixes (rawCellTreeBits U ++ tail) (rawNodeMask U) =
      (rawNodeViews U tail).map rawViewSuffix := by
    simpa only [List.append_nil, rawMarkedSuffixes] using rawMarkedSuffixes_tree U tail []
  unfold cladeExistsAnswer
  rw [hviews, List.all_map]
  have he := boolAll_congr_mem (rawNodeViews U tail)
    (fun v => cladeCandidateContinue m (N + m * N + 3)
      (rawCellTreeBits R ++ rest) (rawNodeMask R) (rawViewSuffix v))
    (fun v => !scanSetEq (scanLeaves R) (scanLeaves v.1))
    (fun v hv => cladeCandidateContinue_trees N m R v.1 rest v.2 hR (rawNodeViews_valid N m U tail hU v hv))
  rw [he, all_not_flip_eq_any]
  simpa only [List.any_map] using congrArg
    (fun xs : List (List (ℕ × ℕ)) => xs.any (fun ys => scanSetEq (scanLeaves R) ys))
    (rawNodeViews_clades U tail)

theorem cladeFixedAnswer_trees (N m : ℕ) (R U : BTree (ℕ × ℕ)) (rest tail : List Bool)
    (hR : rawTreeValid N m R) (hU : rawTreeValid N m U) :
    cladeFixedAnswer m (N + m * N + 3)
      (rawCellTreeBits U ++ tail) (rawNodeMask U) (rawCellTreeBits R ++ rest) =
      (scanClades U).any (fun ys => scanSetEq (scanLeaves R) ys) := by
  rw [cladeFixedAnswer, rawForestMaskParse_one]
  exact cladeExistsAnswer_trees N m R U rest tail hR hU

theorem allCladesAnswer_tree (N m : ℕ) (R U : BTree (ℕ × ℕ)) (rest tail : List Bool)
    (hR : rawTreeValid N m R) (hU : rawTreeValid N m U) :
    allCladesAnswer m (N + m * N + 3)
      (rawCellTreeBits R ++ rest) (rawNodeMask R) (rawCellTreeBits U ++ tail) (rawNodeMask U) =
      scanRefines R U := by
  have hviews : rawMarkedSuffixes (rawCellTreeBits R ++ rest) (rawNodeMask R) =
      (rawNodeViews R rest).map rawViewSuffix := by
    simpa only [List.append_nil, rawMarkedSuffixes] using rawMarkedSuffixes_tree R rest []
  unfold allCladesAnswer
  rw [hviews, List.all_map]
  have he := boolAll_congr_mem (rawNodeViews R rest)
    (fun v => cladeFixedAnswer m (N + m * N + 3)
      (rawCellTreeBits U ++ tail) (rawNodeMask U) (rawViewSuffix v))
    (fun v => (scanClades U).any (fun ys => scanSetEq (scanLeaves v.1) ys))
    (fun v hv => cladeFixedAnswer_trees N m v.1 U v.2 tail (rawNodeViews_valid N m R rest hR v hv) hU)
  rw [he]
  simpa only [List.all_map, scanRefines] using congrArg
    (fun xs : List (List (ℕ × ℕ)) => xs.all (fun cs => (scanClades U).any (fun ys => scanSetEq cs ys)))
    (rawNodeViews_clades R rest)

/-- Every clade of every supplied row, including internal clades inside
composite children. No replacement by a disjoint-triple decision problem. -/
theorem allCladesAnswer_forest (N m : ℕ) (Rs : List (BTree (ℕ × ℕ))) (U : BTree (ℕ × ℕ))
    (rest tail : List Bool) (hRs : ∀ R ∈ Rs, rawTreeValid N m R) (hU : rawTreeValid N m U) :
    allCladesAnswer m (N + m * N + 3)
      (rawForestWord Rs ++ rest) (rawForestNodeMask Rs) (rawCellTreeBits U ++ tail) (rawNodeMask U) =
      Rs.all (fun R => scanRefines R U) := by
  revert hRs
  induction Rs with
  | nil => intro hRs; simp [allCladesAnswer, rawForestWord, rawForestNodeMask, rawMarkedSuffixes]
  | cons R Rs ih =>
      intro hRs
      have hR := hRs R (by simp)
      have ht : ∀ T ∈ Rs, rawTreeValid N m T := by intro T h; exact hRs T (by simp [h])
      have hsplit : rawMarkedSuffixes (rawForestWord (R :: Rs) ++ rest) (rawForestNodeMask (R :: Rs)) =
          (rawNodeViews R (rawForestWord Rs ++ rest)).map rawViewSuffix ++
            rawMarkedSuffixes (rawForestWord Rs ++ rest) (rawForestNodeMask Rs) := by
        simpa only [rawForestWord, rawForestNodeMask, List.flatMap_cons, List.append_assoc] using
          rawMarkedSuffixes_tree R (rawForestWord Rs ++ rest) (rawForestNodeMask Rs)
      have hfirst := allCladesAnswer_tree N m R U (rawForestWord Rs ++ rest) tail hR hU
      have hv : rawMarkedSuffixes (rawCellTreeBits R ++ (rawForestWord Rs ++ rest)) (rawNodeMask R) =
          (rawNodeViews R (rawForestWord Rs ++ rest)).map rawViewSuffix := by
        simpa only [List.append_nil, rawMarkedSuffixes] using rawMarkedSuffixes_tree R (rawForestWord Rs ++ rest) []
      unfold allCladesAnswer at hfirst ⊢
      rw [hv] at hfirst
      rw [hsplit, List.all_append, hfirst]
      change scanRefines R U && allCladesAnswer m (N + m * N + 3)
        (rawForestWord Rs ++ rest) (rawForestNodeMask Rs) (rawCellTreeBits U ++ tail) (rawNodeMask U) = _
      rw [ih ht, List.all_cons]

theorem rawTreeCodes_clades {N m : ℕ} (T : BTree (Cell N m)) :
    scanClades (rawTreeCodes T) = (scanClades T).map (List.map cellNatCode) := by
  induction T with
  | leaf a => rfl
  | node l r ihl ihr =>
      simp only [rawTreeCodes, scanClades, List.map_cons, List.map_append, rawTreeCodes_leaves, ihl, ihr]

theorem scanRefines_rawTreeCodes {N m : ℕ} (R U : BTree (Cell N m)) :
    scanRefines (rawTreeCodes R) (rawTreeCodes U) = scanRefines R U := by
  simp only [scanRefines, rawTreeCodes_clades, List.all_map, List.any_map,
    scanSetEq_map_injective cellNatCode (cellNatCode_injective N m)]

/-- Both typed objects are reconstructed from the actual parser/range
observations, including the original one-tree certificate grammar. -/
theorem allCladesAnswer_observed_typed (N m q : ℕ) (target targetMask certificate certificateMask rest tail : List Bool)
    (hparse : rawForestMaskParse target.length q target = some (rest, targetMask))
    (hcparse : rawForestMaskParse certificate.length 1 certificate = some (tail, certificateMask))
    (hcheck : forestMaskCellCheck N m target targetMask = true)
    (hccheck : forestMaskCellCheck N m certificate certificateMask = true) :
    ∃ Ts : List (BTree (Cell N m)), ∃ U : BTree (Cell N m), Ts.length = q ∧
      target = Ts.flatMap treeBits ++ rest ∧ certificate = treeBits U ++ tail ∧
      allCladesAnswer m (N + m * N + 3) target targetMask certificate certificateMask =
        Ts.all (fun R => scanRefines R U) := by
  obtain ⟨Rs, hq, hw, hm⟩ := (rawForestMaskParse_all_words target rest targetMask q).mp hparse
  obtain ⟨V, hcw, hcm⟩ := rawForestMaskParse_one_sound certificate tail certificateMask hcparse
  have hR := (forestMaskCellCheck_iff N m Rs rest).mp (by simpa only [← hw, ← hm] using hcheck)
  have hV : rawTreeValid N m V := by
    have hs : ∀ T ∈ [V], rawTreeValid N m T := (forestMaskCellCheck_iff N m [V] tail).mp
      (by simpa only [rawForestWord, rawForestNodeMask, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, ← hcw, ← hcm] using hccheck)
    exact hs V (by simp)
  obtain ⟨Ts, hTs⟩ := (rawForestValid_iff_typed N m Rs).mp hR
  obtain ⟨U, hU⟩ := (rawTreeValid_iff_typed N m V).mp hV
  refine ⟨Ts, U, ?_, ?_, ?_, ?_⟩
  · simpa only [← hTs, List.length_map] using hq
  · simpa only [← hTs, rawForestWord_map_codes] using hw
  · simpa only [← hU, rawTreeCodes_bits] using hcw
  · rw [hw, hm, hcw, hcm, allCladesAnswer_forest N m Rs V rest tail hR hV,
      ← hTs, ← hU, List.all_map]
    exact boolAll_congr_mem Ts _ _ (fun R _ => scanRefines_rawTreeCodes R U)

/-- The complete paid clade component, joined to its original typed
predicate. The entry conditions are physical tape invariants; the typed
trees are outputs reconstructed here, not caller-supplied witnesses. -/
theorem allClades_executes_observed_typed (p : CladePorts K) (N m q L : ℕ)
    (s : CountdownStore K F) (rest tail : List Bool)
    (hs : AllCladesEntry p m (N + m * N + 3) L
      (s.stk (p (.inner .originalWord))) (s.stk (p (.inner .originalMask))) s)
    (hparse : rawForestMaskParse (s.stk (p (.outer .originalWord))).length q
      (s.stk (p (.outer .originalWord))) = some (rest, s.stk (p (.outer .originalMask))))
    (hcparse : rawForestMaskParse (s.stk (p (.inner .originalWord))).length 1
      (s.stk (p (.inner .originalWord))) = some (tail, s.stk (p (.inner .originalMask))))
    (hcheck : forestMaskCellCheck N m (s.stk (p (.outer .originalWord)))
      (s.stk (p (.outer .originalMask))) = true)
    (hccheck : forestMaskCellCheck N m (s.stk (p (.inner .originalWord)))
      (s.stk (p (.inner .originalMask))) = true) :
    ∃ Ts : List (BTree (Cell N m)), ∃ U : BTree (Cell N m), ∃ n : ℕ,
      Ts.length = q ∧ s.stk (p (.outer .originalWord)) = Ts.flatMap treeBits ++ rest ∧
      s.stk (p (.inner .originalWord)) = treeBits U ++ tail ∧
      n ≤ allCladesBound m (N + m * N + 3) L ∧
      (allCladesRoutine p).Executes s
        ⟨((s.state.1.1, false), Ts.all (fun R => scanRefines R U)), s.stk⟩ n := by
  obtain ⟨Ts, U, hq, hw, hcw, hans⟩ := allCladesAnswer_observed_typed N m q
    (s.stk (p (.outer .originalWord))) (s.stk (p (.outer .originalMask)))
    (s.stk (p (.inner .originalWord))) (s.stk (p (.inner .originalMask))) rest tail
    hparse hcparse hcheck hccheck
  obtain ⟨n, hn, he⟩ := allClades_executes p m (N + m * N + 3) L
    (s.stk (p (.inner .originalWord))) (s.stk (p (.inner .originalMask))) s hs
  refine ⟨Ts, U, n, hq, hw, hcw, hn, ?_⟩
  simpa only [allCladesResult, hans] using he

/- The actual EVERY target clade / EXISTS certificate clade nest and its
exact original typed scanRefines observation are now composed in source.
The term is UNELABORATED. It is not a compiler certificate and does not
yet supply the single whole VerifierMachineWitness. Target/certificate
uniqueness, marker/mixedness/coverage, root-inclusive distinct-type score,
headers, global rejection and clean halt remain independent obligations;
EncodedSourceHardness remains a separate final premise. -/

end PolytomyReductionModel.WholeVerifierController
