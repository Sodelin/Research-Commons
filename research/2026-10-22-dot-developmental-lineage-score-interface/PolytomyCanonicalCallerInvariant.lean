/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Concrete caller decomposition and repeated-call data obligations for the
actual original real-type body. Stack-based invariant transport below is
only a logical lemma, not an operational control-conversion compiler.
-/
import PolytomyCanonicalMembershipGate

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {E F G : Type} [DecidableEq E]

def selectedCallerBase (s : CountdownStore (SelectedQueryCallerStack E) F) :
    CountdownStore (NumericStack UnaryScanPort) F := ⟨s.state, fun k => s.stk (.inl k)⟩

def selectedCallerExtra (s : CountdownStore (SelectedQueryCallerStack E) F) : E → List Bool :=
  fun k => s.stk (.inr k)

theorem selectedCaller_split (s : CountdownStore (SelectedQueryCallerStack E) F) :
    extraPortsStore (selectedCallerBase s) (selectedCallerExtra s) = s := by
  apply countdownStore_ext
  · rfl
  · funext k; cases k <;> rfl

theorem UnaryScanReady_of_stacks (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) F)
    (t : CountdownStore (NumericStack UnaryScanPort) G) (hs : UnaryScanReady C L s)
    (h : ∀ k, t.stk k = s.stk k) : UnaryScanReady C L t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [NumericLoopInv, h] using hs.numeric
  · rw [h]; exact hs.source_empty
  · intro k hk; rw [h]; exact hs.empty k hk
  · rw [h]; exact hs.original_bound

theorem realCanonicalType_base_data (p : CanonicalLeafLayout E) (rowPort : E) (C T : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (extra : E → List Bool)
    (k : NumericStack UnaryScanPort) :
    (selectedCallerBase (realCanonicalTypeResult p rowPort C T s extra)).stk k =
      (realBlockMembershipBase C T (p.port .value) rowPort s extra).stk k := by
  exact canonicalLeafGate_extra (callerLeafLayout p)
    (extraPortsStore (realBlockMembershipBase C T (p.port .value) rowPort s extra) extra) (.inl k)
    (by simp [callerLeafLayout]) (by simp [callerLeafLayout])
    (by simp [callerLeafLayout]) (by simp [callerLeafLayout])

theorem realCanonicalType_extra (p : CanonicalLeafLayout E) (rowPort : E) (C T : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (extra : E → List Bool)
    (k : E) (hkr : k ≠ p.port .remaining) (hkc : k ≠ p.port .count)
    (hkcost : k ≠ p.port .cost) (hko : k ≠ p.port .output) :
    (realCanonicalTypeResult p rowPort C T s extra).stk (.inr k) = extra k := by
  exact canonicalLeafGate_extra (callerLeafLayout p)
    (extraPortsStore (realBlockMembershipBase C T (p.port .value) rowPort s extra) extra) (.inr k)
    (by simpa [callerLeafLayout] using hkr) (by simpa [callerLeafLayout] using hkc)
    (by simpa [callerLeafLayout] using hkcost) (by simpa [callerLeafLayout] using hko)

theorem realCanonicalType_counter (p : CanonicalLeafLayout E) (rowPort : E) (C T : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (extra : E → List Bool) :
    (realCanonicalTypeResult p rowPort C T s extra).stk (.inr (p.port .value)) = extra (p.port .value) :=
  realCanonicalType_extra p rowPort C T s extra (p.port .value)
    (p.ne (by decide)) (p.ne (by decide)) (p.ne (by decide)) (p.ne (by decide))

theorem realCanonicalType_remaining_le (p : CanonicalLeafLayout E) (rowPort : E) (C T : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (extra : E → List Bool) :
    ((realCanonicalTypeResult p rowPort C T s extra).stk (.inr (p.port .remaining))).length ≤
      (extra (p.port .remaining)).length := by
  rw [realCanonicalTypeResult, canonicalLeafGate_data]
  split
  · rw [acceptedCanonicalLeaf_remaining]
    change (extra (p.port .remaining)).tail.length ≤ (extra (p.port .remaining)).length
    rw [List.length_tail]; omega
  · exact le_refl _

theorem realCanonicalType_ready (p : CanonicalLeafLayout E) (rowPort : E) (C L T : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady 0 L s)
    (extra : E → List Bool) (hC : extra (p.port .value) = List.replicate C true) :
    UnaryScanReady 0 L (selectedCallerBase (realCanonicalTypeResult p rowPort C T s extra)) ∧
      (realCanonicalTypeResult p rowPort C T s extra).stk (.inl (.inr .queries)) = [] ∧
      (realCanonicalTypeResult p rowPort C T s extra).stk (.inl (.inr .original)) = s.stk (.inr .original) := by
  obtain ⟨hr, hq, ho⟩ := copiedSelectedQuery_ready (p.port .value) rowPort C L s hs extra hC
  have hm : UnaryScanReady 0 L (realBlockMembershipBase C T (p.port .value) rowPort s extra) :=
    ⟨hr.numeric, hr.source_empty, hr.empty, hr.original_bound⟩
  refine ⟨UnaryScanReady_of_stacks 0 L _ _ hm (realCanonicalType_base_data p rowPort C T s extra), ?_, ?_⟩
  · change (selectedCallerBase (realCanonicalTypeResult p rowPort C T s extra)).stk (.inr .queries) = []
    rw [realCanonicalType_base_data]
    exact hq
  · change (selectedCallerBase (realCanonicalTypeResult p rowPort C T s extra)).stk (.inr .original) = _
    rw [realCanonicalType_base_data]
    exact ho

/- The type counter is reserved from both membership and accepted-leaf
writes. Remaining decreases or stays fixed. All original scan state is
fresh again. Row/threshold/block/temp words survive when their ports are
outside remaining/count/cost/output; a concrete finite layout will make
those exclusions explicit for the actual full descending loop.
-/

end PolytomyReductionModel
