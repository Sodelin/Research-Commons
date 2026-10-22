/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual physical-index replay followed by the exact original typed leaf
query. The word/index and every unrelated caller tape survive. Every
index is covered, including end and overshoot. Legal node selection is
still the separate mask obligation, not inferred from a parseable suffix.
-/
import PolytomyTypedLeafCellQuery

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

inductive IndexedCellPort where
  | original | index | temp | source | discarded | block | kind
  | rows | types | residue | subtrahend
  deriving DecidableEq, Fintype

abbrev IndexedCellPorts (K : Type) := IndexedCellPort ↪ K

variable {K F : Type} [DecidableEq K]

@[simp] theorem indexedCellPorts_eq (p : IndexedCellPorts K) (a b : IndexedCellPort) :
    p a = p b ↔ a = b := ⟨p.injective, congrArg p⟩

def indexedCellReplay (p : IndexedCellPorts K) : ReplayPorts K where
  toFun := fun
    | .original => p .original
    | .index => p .index
    | .temp => p .temp
    | .source => p .source
    | .discarded => p .discarded
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def indexedCellTyped (p : IndexedCellPorts K) : TypedCellPorts K where
  toFun := fun
    | .source => p .source
    | .block => p .block
    | .kind => p .kind
    | .rows => p .rows
    | .types => p .types
    | .temp => p .temp
    | .residue => p .residue
    | .subtrahend => p .subtrahend
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

def indexedLeafCellRoutine (p : IndexedCellPorts K) : Routine (fun _ : K => Bool) (CountdownState F) :=
  RoutineComposition.seq (replaySuffixRoutine (indexedCellReplay p)) (typedLeafCellRoutine (indexedCellTyped p))

def indexedLeafCellEval (p : IndexedCellPorts K) (I m A : ℕ) (s : CountdownStore K F) : CountdownStore K F :=
  typedLeafCellEval (indexedCellTyped p) m A (replaySuffixResult (indexedCellReplay p) I s)

theorem indexedLeafCell_executes (p : IndexedCellPorts K) (I m A : ℕ) (s : CountdownStore K F)
    (hi : s.stk (p .index) = List.replicate I true)
    (hm : s.stk (p .rows) = List.replicate m true) (hA : s.stk (p .types) = List.replicate A true)
    (hs : s.stk (p .source) = []) (hd : s.stk (p .discarded) = [])
    (hb : s.stk (p .block) = []) (hk : s.stk (p .kind) = [])
    (ht : s.stk (p .temp) = []) (hr : s.stk (p .residue) = []) (hu : s.stk (p .subtrahend) = []) :
    ∃ n ≤ 17 * (s.stk (p .original)).length + 6 * I + 4 * m + 4 * A + 44,
      (indexedLeafCellRoutine p).Executes s (indexedLeafCellEval p I m A s) n := by
  let v := replaySuffixResult (indexedCellReplay p) I s
  have hext (j : IndexedCellPort) (hjs : j ≠ .source) (hjd : j ≠ .discarded) :
      v.stk (p j) = s.stk (p j) :=
    (replaySuffix_preserves (indexedCellReplay p) I s (p j)
      (by simpa [indexedCellReplay] using hjs)
      (by simpa [indexedCellReplay] using hjd)).2.2
  have hmV := (hext .rows (by decide) (by decide)).trans hm
  have hAV := (hext .types (by decide) (by decide)).trans hA
  have hbV := (hext .block (by decide) (by decide)).trans hb
  have hkV := (hext .kind (by decide) (by decide)).trans hk
  have htV := (hext .temp (by decide) (by decide)).trans ht
  have hrV := (hext .residue (by decide) (by decide)).trans hr
  have huV := (hext .subtrahend (by decide) (by decide)).trans hu
  have hlen : (v.stk (p .source)).length ≤ (s.stk (p .original)).length :=
    replaySuffix_source_bound (indexedCellReplay p) I s
  obtain ⟨n1, hn1, h1⟩ := replaySuffix_executes (indexedCellReplay p) I s hs hd ht hi
  obtain ⟨n2, hn2, h2⟩ := typedLeafCell_executes (indexedCellTyped p) m A
    (s.stk (p .original)).length v hlen hmV hAV hbV hkV htV hrV huV
  have hall := RoutineComposition.seq_executes _ _ h1 h2
  exact ⟨n1 + n2, by omega, hall⟩

theorem indexedLeafCell_original_observation (p : IndexedCellPorts K) (I N m : ℕ)
    (s : CountdownStore K F) :
    rawLeafCellObservation (typedRawCellPorts (indexedCellTyped p))
      (indexedLeafCellEval p I m (N + m * N + 3) s) =
      (readOriginalLeafCell N m ((s.stk (p .original)).drop I)).map
        (fun q => (cellNatCode q.1, q.2)) := by
  unfold indexedLeafCellEval
  rw [typedLeafCell_original_observation]
  have hs := replaySuffix_source (indexedCellReplay p) I s
  simpa only [indexedCellTyped, indexedCellReplay] using
    congrArg (fun bits => (readOriginalLeafCell N m bits).map (fun q => (cellNatCode q.1, q.2))) hs

theorem indexedLeafCell_extra (p : IndexedCellPorts K) (I m A : ℕ) (s : CountdownStore K F)
    (j : K) (hjs : j ≠ p .source) (hjd : j ≠ p .discarded)
    (hjb : j ≠ p .block) (hjk : j ≠ p .kind) :
    (indexedLeafCellEval p I m A s).stk j = s.stk j := by
  unfold indexedLeafCellEval
  rw [typedLeafCell_stacks,
    rawLeafCell_extra (typedRawCellPorts (indexedCellTyped p)) j hjs hjb hjk]
  exact (replaySuffix_preserves (indexedCellReplay p) I s j hjs hjd).2.2

theorem indexedLeafCell_frame (p : IndexedCellPorts K) (I m A : ℕ) (s : CountdownStore K F) :
    (indexedLeafCellEval p I m A s).state.1 = s.state.1 := by
  unfold indexedLeafCellEval
  rw [typedLeafCell_frame]
  exact (replaySuffix_preserves (indexedCellReplay p) I s (p .original)
    (by simp [indexedCellReplay]) (by simp [indexedCellReplay])).1

theorem indexedLeafCell_discarded (p : IndexedCellPorts K) (I m A : ℕ) (s : CountdownStore K F) :
    (indexedLeafCellEval p I m A s).stk (p .discarded) = [] := by
  unfold indexedLeafCellEval
  rw [typedLeafCell_stacks,
    rawLeafCell_extra (typedRawCellPorts (indexedCellTyped p)) (p .discarded)
      (by simp [typedRawCellPorts, indexedCellTyped]) (by simp [typedRawCellPorts, indexedCellTyped])
      (by simp [typedRawCellPorts, indexedCellTyped])]
  exact (replaySuffix_preserves (indexedCellReplay p) I s (p .original)
    (by simp [indexedCellReplay]) (by simp [indexedCellReplay])).2.1

/- No host oracle performs drop: the theorem's list expression describes
the exact observation of the charged physical replay and typed query.
No suffix is called a true node merely because it parses. Legal-mask
selection and complete independent-verifier scans/cleanup remain open.
-/

end PolytomyReductionModel
