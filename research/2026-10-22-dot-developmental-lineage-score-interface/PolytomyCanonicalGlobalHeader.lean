/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Physical original N,m,K extraction into reserved global caller ports.
These are ordinary finite-index Boolean stacks, not natural control.
-/
import PolytomyPreservingProductStore

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

inductive CanonicalGlobalPort where
  | universe | rowCount | budget | alphabet | markerThreshold | blockCounter
  deriving DecidableEq, Fintype

abbrev CanonicalGlobalStack := CanonicalFilterStack ⊕ CanonicalGlobalPort
abbrev CanonicalGlobalStore := CountdownStore CanonicalGlobalStack SelectedRowFrame

def canonicalGlobalBase (s : CanonicalGlobalStore) : CanonicalFilterStore :=
  ⟨s.state, fun k => s.stk (.inl k)⟩

def canonicalGlobalExtra (s : CanonicalGlobalStore) : CanonicalGlobalPort → List Bool :=
  fun k => s.stk (.inr k)

theorem canonicalGlobal_split (s : CanonicalGlobalStore) :
    extraPortsStore (canonicalGlobalBase s) (canonicalGlobalExtra s) = s := by
  apply countdownStore_ext
  · rfl
  · funext k; cases k <;> rfl

def globalScanPort (k : NumericStack UnaryScanPort) : CanonicalGlobalStack := .inl (.inl k)
def globalFilterPort (k : CanonicalFilterPort) : CanonicalGlobalStack := .inl (.inr k)

def canonicalGlobalHeaderPorts : InternalHeaderPorts CanonicalGlobalStack where
  source := globalScanPort (.inl .source)
  n := .inr .universe
  m := .inr .rowCount
  k := .inr .budget
  hsn := by decide
  hsm := by decide
  hsk := by decide
  hnm := by decide
  hnk := by decide
  hmk := by decide

def canonicalGlobalHeaderRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  copiedHeaderRoutine (globalScanPort (.inr .original)) (globalScanPort (.inr .copyTemp)) canonicalGlobalHeaderPorts

def canonicalGlobalHeaderEval (s : CanonicalGlobalStore) :=
  copiedHeaderEval (globalScanPort (.inr .original)) canonicalGlobalHeaderPorts s

theorem canonicalGlobalHeader_executes (L : ℕ) (s : CanonicalGlobalStore)
    (hs : UnaryScanReady 0 L (selectedCallerBase (canonicalGlobalBase s)))
    (hN : s.stk (.inr .universe) = []) (hM : s.stk (.inr .rowCount) = [])
    (hK : s.stk (.inr .budget) = []) :
    ∃ n ≤ 9 * L + 16,
      canonicalGlobalHeaderRoutine.Executes s (canonicalGlobalHeaderEval s) n ∧
      ((canonicalGlobalHeaderEval s).stk (globalScanPort (.inl .source))).length ≤ L ∧
      ((canonicalGlobalHeaderEval s).stk (.inr .universe)).length ≤ L ∧
      ((canonicalGlobalHeaderEval s).stk (.inr .rowCount)).length ≤ L ∧
      ((canonicalGlobalHeaderEval s).stk (.inr .budget)).length ≤ L := by
  obtain ⟨n, hn, he, ho, hsrc, hnu, hmu, hku⟩ := copiedHeader_executes
    (globalScanPort (.inr .original)) (globalScanPort (.inr .copyTemp)) canonicalGlobalHeaderPorts
    (by decide) (by decide) (by decide) s
    (hs.empty .copyTemp (by simp [scanWorkExtras])) hs.source_empty hN hM hK
  have hL := hs.original_bound
  exact ⟨n, by omega, he, hsrc.trans hL, hnu.trans hL, hmu.trans hL, hku.trans hL⟩

theorem canonicalGlobalHeader_values (L : ℕ) (s : CanonicalGlobalStore)
    (hs : UnaryScanReady 0 L (selectedCallerBase (canonicalGlobalBase s)))
    (hN : s.stk (.inr .universe) = []) (hM : s.stk (.inr .rowCount) = [])
    (hK : s.stk (.inr .budget) = []) (R : RawMSSCRecord)
    (hparse : readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R) :
    (canonicalGlobalHeaderEval s).state.2 = true ∧
      (canonicalGlobalHeaderEval s).stk (globalScanPort (.inl .source)) =
        encodeFramedList (encodeFramedList unaryFrame) R.rows ∧
      (canonicalGlobalHeaderEval s).stk (.inr .universe) = List.replicate R.N true ∧
      (canonicalGlobalHeaderEval s).stk (.inr .rowCount) = List.replicate R.declaredM true ∧
      (canonicalGlobalHeaderEval s).stk (.inr .budget) = List.replicate R.K true := by
  let u := wordDuplicateEval (globalScanPort (.inr .original)) (globalScanPort (.inl .source)) s
  have hu : u.stk (globalScanPort (.inl .source)) = s.stk (globalScanPort (.inr .original)) := by
    simp [u, wordDuplicateEval, hs.source_empty]
  apply internalHeader_complete_record_values canonicalGlobalHeaderPorts u
  · simpa [u, wordDuplicateEval, canonicalGlobalHeaderPorts, globalScanPort] using hN
  · simpa [u, wordDuplicateEval, canonicalGlobalHeaderPorts, globalScanPort] using hM
  · simpa [u, wordDuplicateEval, canonicalGlobalHeaderPorts, globalScanPort] using hK
  · change readNormalizedSource (u.stk (globalScanPort (.inl .source))) = some R
    rw [hu]; exact hparse

theorem canonicalGlobalHeader_extra (s : CanonicalGlobalStore) (k : CanonicalGlobalStack)
    (hsrc : k ≠ globalScanPort (.inl .source)) (hN : k ≠ .inr .universe)
    (hM : k ≠ .inr .rowCount) (hK : k ≠ .inr .budget) :
    (canonicalGlobalHeaderEval s).stk k = s.stk k :=
  copiedHeader_extra _ canonicalGlobalHeaderPorts k hsrc hN hM hK s

/- The source record is faithfully copied; complete original validity
is still a distinct premise/branch, not inferred from header success.
Actual product/alphabet/threshold/countdown creation and cleanup must
join this extraction before the global canonical block controller.
-/

end PolytomyReductionModel
