/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual all-operational-state block contract for the ORIGINAL concrete
routine. It covers out-of-range selectors without pretending they are
original real blocks. Exact original observations remain separately proved.
-/
import PolytomyCanonicalUnaryData

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def operationalBlockEval (T : ℕ) (s : CanonicalFilterStore) :=
  clearStackEval (.inr .remaining)
    (canonicalCombPrefixEval (.inr .count) (.inr .output) (realTypeLoopEval T s))

def operationalBlockBound (L S I T B : ℕ) :=
  S * (realTypeBodyBound L S I T B + 3) + 2 * S + 6

theorem operationalBlock_eq_original (R : RawMSSCRecord) (b : Block R.rows.length) (s : CanonicalFilterStore) :
    operationalBlockEval (originalBlockThreshold R b) s = originalCanonicalBlockEval R b s := rfl

theorem operationalBlock_executes (L S I T B : ℕ) (s : CanonicalFilterStore)
    (hs : RealTypeLoopInv L S I T B s) (hu : RealTypeUnaryData s)
    (hok : s.state.2 = true) (hcount : s.stk (.inr .count) = []) :
    ∃ n ≤ operationalBlockBound L S I T B,
      originalCanonicalBlockRoutine.Executes s (operationalBlockEval T s) n ∧
      RealTypeLoopInv L S I T B (operationalBlockEval T s) ∧
      RealTypeUnaryData (operationalBlockEval T s) ∧
      (operationalBlockEval T s).stk (.inr .typeIndex) = [] ∧
      (operationalBlockEval T s).stk (.inr .count) = [] ∧
      (operationalBlockEval T s).stk (.inr .remaining) = [] ∧
      (operationalBlockEval T s).stk (.inl (.inr .original)) = s.stk (.inl (.inr .original)) ∧
      (operationalBlockEval T s).state.2 = true := by
  let u := realTypeLoopEval T s
  let v := canonicalCombPrefixEval (.inr CanonicalFilterPort.count) (.inr .output) u
  let q := (u.stk (.inr .count)).length
  let r := (u.stk (.inr .remaining)).length
  obtain ⟨n, hn, he, hi, hf, hg, htype⟩ := realTypeLoop_executes L S I T B s hs hok
  have hun := realTypeLoop_unary L S I T B s hs hu
  have hq : q ≤ S := by
    have hc := realTypeLoop_count_bound T s
    rw [hcount, List.length_nil, zero_add] at hc
    exact hc.trans hs.type_bound
  have hr : r ≤ S := hi.remaining_bound
  have hp := canonicalCombPrefix_executes (.inr CanonicalFilterPort.count : CanonicalFilterStack)
    (.inr .output) (by decide) u
  have hvr : v.stk (.inr .remaining) = u.stk (.inr .remaining) :=
    canonicalCombPrefix_extra _ _ _ (by decide) (by decide) u
  have hc := clearStack_executes (.inr CanonicalFilterPort.remaining : CanonicalFilterStack) v
  rw [hvr] at hc
  have hall := RoutineComposition.seq_executes _ _ he (RoutineComposition.seq_executes _ _ hp hc)
  have hout : ∀ k : CanonicalFilterStack, k ≠ .inr .remaining → k ≠ .inr .count → k ≠ .inr .output →
      (operationalBlockEval T s).stk k = u.stk k := by
    intro k hrem hcnt ho
    change (clearStackEval (.inr .remaining) v).stk k = u.stk k
    simp only [clearStackEval, Function.update_of_ne hrem]
    exact canonicalCombPrefix_extra _ _ k hcnt ho u
  have hcount' : (operationalBlockEval T s).stk (.inr .count) = [] := by
    change (clearStackEval (.inr .remaining) v).stk (.inr .count) = []
    simp only [clearStackEval, Function.update_of_ne (by decide :
      (Sum.inr CanonicalFilterPort.count : CanonicalFilterStack) ≠ .inr .remaining)]
    exact canonicalCombPrefix_count _ _ (by decide) u
  have hrem' : (operationalBlockEval T s).stk (.inr .remaining) = [] := by
    simp [operationalBlockEval, clearStackEval]
  have htype' : (operationalBlockEval T s).stk (.inr .typeIndex) = [] := by
    rw [hout _ (by decide) (by decide) (by decide)]; exact htype
  have hi' : RealTypeLoopInv L S I T B (operationalBlockEval T s) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact UnaryScanReady_of_stacks 0 L _ _ hi.scan
        (fun k => hout (.inl k) (by simp) (by simp) (by simp))
    · rw [hout _ (by decide) (by decide) (by decide)]; exact hi.query_empty
    · simp [htype', IsUnaryWord]
    · simp [htype']
    · rw [hout _ (by decide) (by decide) (by decide)]; exact hi.row_bound
    · rw [hout _ (by decide) (by decide) (by decide)]; exact hi.threshold_word
    · rw [hout _ (by decide) (by decide) (by decide)]; exact hi.temp_empty
    · simp [hrem']
    · rw [hout _ (by decide) (by decide) (by decide)]; exact hi.block_bound
  have hu' : RealTypeUnaryData (operationalBlockEval T s) := by
    refine ⟨?_, ?_, ?_⟩
    · change IsUnaryWord ((operationalBlockEval T s).stk (.inr .remaining))
      simp [hrem', IsUnaryWord]
    · change IsUnaryWord ((operationalBlockEval T s).stk (.inr .count))
      simp [hcount', IsUnaryWord]
    · change IsUnaryWord ((operationalBlockEval T s).stk (.inr .cost))
      rw [hout _ (by decide) (by decide) (by decide)]; exact hun.2.2
  refine ⟨n + ((q - 1 + 2) + (r + 1)), ?_, hall, hi', hu', htype', hcount', hrem', ?_, hf⟩
  · unfold operationalBlockBound; omega
  · rw [hout _ (by decide) (by decide) (by decide)]
    exact realTypeLoop_original_preserved L S I T B s hs

/- The looser uniform finish bound uses q<=S and remaining<=S, not an
unjustified original block interpretation of an arbitrary row selector.
For each genuine source block the earlier ORIGINAL exact byte/score
theorems still apply to this identical program. This is a stronger
operational contract needed by the full outer loop, not a new target.
-/

end PolytomyReductionModel
