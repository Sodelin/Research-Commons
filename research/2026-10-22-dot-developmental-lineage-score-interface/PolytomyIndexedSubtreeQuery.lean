/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual physical-index replay and exact forward subtree-node mask. The
constructor of the mask handles arbitrary binary raw syntax, not only
canonical combs. Legal selection is proved through the original mask;
a parseable interior unary suffix is never silently promoted to a node.
-/
import PolytomyPhysicalSuffixReplay
import PolytomyForwardTreeMask
import PolytomyLegalIndexNavigation

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

inductive IndexedSubtreePort where
  | original | index | temp | source | discarded | pending | reverse | output
  deriving DecidableEq, Fintype

abbrev IndexedSubtreePorts (K : Type) := IndexedSubtreePort ↪ K

variable {K F : Type} [DecidableEq K]

@[simp] theorem indexedSubtreePorts_eq (p : IndexedSubtreePorts K) (a b : IndexedSubtreePort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def indexedSubtreeReplay (p : IndexedSubtreePorts K) : ReplayPorts K where
  toFun := fun
    | .original => p .original
    | .index => p .index
    | .temp => p .temp
    | .source => p .source
    | .discarded => p .discarded
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def indexedSubtreeMask (p : IndexedSubtreePorts K) : TreeMaskPorts K where
  source := p .source
  pending := p .pending
  reverse := p .reverse
  output := p .output
  hsp := by simp
  hsr := by simp
  hso := by simp
  hpr := by simp
  hpo := by simp
  hro := by simp

def indexedSubtreeRoutine (p : IndexedSubtreePorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (replaySuffixRoutine (indexedSubtreeReplay p))
    (treeMaskForwardRoutine (indexedSubtreeMask p))

def indexedSubtreeEval (p : IndexedSubtreePorts K) (I : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  let u := replaySuffixResult (indexedSubtreeReplay p) I s
  treeMaskForwardResult (indexedSubtreeMask p) u.stk u.state.1
    (rawForestMaskParse (u.stk (p .source)).length 1 (u.stk (p .source)))

theorem indexedSubtree_executes (p : IndexedSubtreePorts K) (I : ℕ) (s : CountdownStore K F)
    (hi : s.stk (p .index) = List.replicate I true)
    (hs : s.stk (p .source) = []) (hd : s.stk (p .discarded) = []) (ht : s.stk (p .temp) = [])
    (hp : s.stk (p .pending) = []) (hr : s.stk (p .reverse) = []) (ho : s.stk (p .output) = []) :
    ∃ n ≤ 9 * (s.stk (p .original)).length + 6 * I + 21,
      (indexedSubtreeRoutine p).Executes s (indexedSubtreeEval p I s) n := by
  let u := replaySuffixResult (indexedSubtreeReplay p) I s
  have hext (j : IndexedSubtreePort) (hjs : j ≠ .source) (hjd : j ≠ .discarded) :
      u.stk (p j) = s.stk (p j) :=
    (replaySuffix_preserves (indexedSubtreeReplay p) I s (p j)
      (by simpa [indexedSubtreeReplay] using hjs)
      (by simpa [indexedSubtreeReplay] using hjd)).2.2
  have hpU := (hext .pending (by decide) (by decide)).trans hp
  have hrU := (hext .reverse (by decide) (by decide)).trans hr
  have hoU := (hext .output (by decide) (by decide)).trans ho
  have hentry : treeMaskCallerStore (indexedSubtreeMask p) (Function.update u.stk (p .output) [])
      u.state.1 u.state.2 (u.stk (p .source)) [] [] = u := by
    apply countdownStore_ext
    · rfl
    · funext k
      by_cases hkO : k = p .output <;> by_cases hkP : k = p .pending <;>
        by_cases hkR : k = p .reverse <;> by_cases hkS : k = p .source <;>
        simp_all [treeMaskCallerStore, frameCallerStore, indexedSubtreeMask]
  obtain ⟨n1, hn1, h1⟩ := replaySuffix_executes (indexedSubtreeReplay p) I s hs hd ht hi
  obtain ⟨n2, hn2, h2⟩ := treeMaskForward_executes (indexedSubtreeMask p)
    u.stk u.state.1 u.state.2 (u.stk (p .source))
  rw [hentry] at h2
  have hlen := replaySuffix_source_bound (indexedSubtreeReplay p) I s
  have hall := RoutineComposition.seq_executes _ _ h1 h2
  exact ⟨n1 + n2, by omega, hall⟩

def indexedSubtreeObservation (p : IndexedSubtreePorts K) (s : CountdownStore K F) :
    Option (List Bool × List Bool) :=
  if s.state.2 then some (s.stk (p .source), s.stk (p .output)) else none

theorem indexedSubtree_observation (p : IndexedSubtreePorts K) (I : ℕ) (s : CountdownStore K F) :
    indexedSubtreeObservation p (indexedSubtreeEval p I s) = rawIndexedSubtree (s.stk (p .original)) I := by
  unfold indexedSubtreeObservation indexedSubtreeEval
  rw [treeMaskForward_observation]
  have hs := replaySuffix_source (indexedSubtreeReplay p) I s
  simpa only [indexedSubtreeReplay, rawIndexedSubtree] using
    congrArg (fun bits : List Bool => rawForestMaskParse bits.length 1 bits) hs

theorem indexedSubtree_view (p : IndexedSubtreePorts K) (I : ℕ) (s : CountdownStore K F)
    (T : BTree (ℕ × ℕ)) (rest : List Bool)
    (hv : (s.stk (p .original)).drop I = rawCellTreeBits T ++ rest) :
    indexedSubtreeObservation p (indexedSubtreeEval p I s) = some (rest, rawNodeMask T) := by
  rw [indexedSubtree_observation, rawIndexedSubtree, hv, rawForestMaskParse_one]

theorem indexedSubtree_legal_node (p : IndexedSubtreePorts K) (I : ℕ) (s : CountdownStore K F)
    (T : BTree (ℕ × ℕ)) (rest : List Bool)
    (hw : s.stk (p .original) = rawCellTreeBits T ++ rest)
    (hi : I ∈ rawMaskIndices (rawNodeMask T)) :
    ∃ v ∈ rawNodeViews T rest,
      indexedSubtreeObservation p (indexedSubtreeEval p I s) = some (v.2, rawNodeMask v.1) := by
  obtain ⟨v, hv, hs⟩ := rawMaskIndex_is_real_node T rest I hi
  refine ⟨v, hv, indexedSubtree_view p I s v.1 v.2 ?_⟩
  simpa only [hw, rawViewSuffix] using hs

theorem indexedSubtree_extra (p : IndexedSubtreePorts K) (I : ℕ) (s : CountdownStore K F)
    (j : K) (hjs : j ≠ p .source) (hjd : j ≠ p .discarded)
    (hjp : j ≠ p .pending) (hjr : j ≠ p .reverse) (hjo : j ≠ p .output) :
    (indexedSubtreeEval p I s).stk j = s.stk j := by
  let u := replaySuffixResult (indexedSubtreeReplay p) I s
  have hm := treeMaskForward_preserves (indexedSubtreeMask p) j hjs hjp hjr hjo u.stk u.state.1
    (rawForestMaskParse (u.stk (p .source)).length 1 (u.stk (p .source)))
  exact hm.2.2.2.trans (replaySuffix_preserves (indexedSubtreeReplay p) I s j hjs hjd).2.2

theorem indexedSubtree_work_clean (p : IndexedSubtreePorts K) (I : ℕ) (s : CountdownStore K F) :
    (indexedSubtreeEval p I s).state.1 = s.state.1 ∧
      (indexedSubtreeEval p I s).stk (p .pending) = [] ∧
      (indexedSubtreeEval p I s).stk (p .reverse) = [] ∧
      (indexedSubtreeEval p I s).stk (p .discarded) = [] := by
  let u := replaySuffixResult (indexedSubtreeReplay p) I s
  have hm := treeMaskForward_preserves (indexedSubtreeMask p) (p .discarded)
    (by simp [indexedSubtreeMask]) (by simp [indexedSubtreeMask])
    (by simp [indexedSubtreeMask]) (by simp [indexedSubtreeMask]) u.stk u.state.1
    (rawForestMaskParse (u.stk (p .source)).length 1 (u.stk (p .source)))
  have hr := replaySuffix_preserves (indexedSubtreeReplay p) I s (p .original)
    (by simp [indexedSubtreeReplay]) (by simp [indexedSubtreeReplay])
  exact ⟨hm.1.trans hr.1, hm.2.1, hm.2.2.1, hm.2.2.2.trans hr.2.1⟩

/- Exact selected-node masks plus the typed leaf query now support the
original clade-comparison route. They do not themselves execute the
outer/nested cursor scans, marker/type guards, cell-set comparisons,
score/budget accumulation or a full clean Boolean verifier. -/

end PolytomyReductionModel
