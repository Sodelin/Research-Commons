/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The COMPLETE original validator is now a concrete routine on the SAME
33 public ports and SAME five-bit control as the original constructor.
All extra output/parameter tapes and two caller flags are preserved.
No parse/validity premise is required for this validator call.
-/
import PolytomyControlFrameTransport
import PolytomyCleanOriginalCanonicalSerializer

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471Proofs

def selectedValidatorControlEquiv :
    CountdownState SelectedRowFrame ≃ CountdownState Bool × (Bool × Bool) where
  toFun := fun s => (((s.1.1.found, s.1.2), s.2), (s.1.1.chosen, s.1.1.active))
  invFun := fun v => ((⟨v.1.1.1, v.2.1, v.2.2⟩, v.1.1.2), v.1.2)
  left_inv := by rintro ⟨⟨⟨f, c, a⟩, g⟩, b⟩; rfl
  right_inv := by rintro ⟨⟨⟨f, g⟩, b⟩, ⟨c, a⟩⟩; rfl

def globalValidationOld (s : CanonicalGlobalStore) : CountdownStore (NumericStack UnaryScanPort) Bool :=
  ⟨(selectedValidatorControlEquiv s.state).1, fun k => s.stk (globalScanPort k)⟩

def globalValidationExpanded (s : CanonicalGlobalStore)
    (t : CountdownStore (NumericStack UnaryScanPort) Bool) : CountdownStore CanonicalGlobalStack Bool :=
  extraPortsStore (extraPortsStore t (fun k => s.stk (globalFilterPort k)))
    (fun k => s.stk (.inr k))

def globalValidationCallerFrame (s : CanonicalGlobalStore) : Bool × Bool :=
  (s.state.1.1.chosen, s.state.1.1.active)

def globalOriginalValidationBaseRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState Bool) :=
  extraPortsRoutine (E := CanonicalGlobalPort)
    (extraPortsRoutine (E := CanonicalFilterPort) originalUnaryValidationRoutine)

def globalOriginalValidationRoutine : Routine (fun _ : CanonicalGlobalStack => Bool) (CountdownState SelectedRowFrame) :=
  controlTransportRoutine globalOriginalValidationBaseRoutine selectedValidatorControlEquiv

def globalOriginalValidationEval (s : CanonicalGlobalStore) : CanonicalGlobalStore :=
  controlTransportStore selectedValidatorControlEquiv
    (globalValidationExpanded s (originalUnaryValidationEval (globalValidationOld s)))
    (globalValidationCallerFrame s)

theorem globalOriginalValidation_input (s : CanonicalGlobalStore) :
    controlTransportStore selectedValidatorControlEquiv
      (globalValidationExpanded s (globalValidationOld s)) (globalValidationCallerFrame s) = s := by
  apply countdownStore_ext
  · cases s with
    | mk state stk =>
        rcases state with ⟨⟨⟨f, c, a⟩, g⟩, b⟩
        rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

theorem globalOriginalValidation_old (s : CanonicalGlobalStore) (k : NumericStack UnaryScanPort) :
    (globalOriginalValidationEval s).stk (globalScanPort k) =
      (originalUnaryValidationEval (globalValidationOld s)).stk k := rfl

theorem globalOriginalValidation_filter (s : CanonicalGlobalStore) (k : CanonicalFilterPort) :
    (globalOriginalValidationEval s).stk (globalFilterPort k) = s.stk (globalFilterPort k) := rfl

theorem globalOriginalValidation_global (s : CanonicalGlobalStore) (k : CanonicalGlobalPort) :
    (globalOriginalValidationEval s).stk (.inr k) = s.stk (.inr k) := rfl

theorem globalOriginalValidation_caller (s : CanonicalGlobalStore) :
    (globalOriginalValidationEval s).state.1.1.chosen = s.state.1.1.chosen ∧
      (globalOriginalValidationEval s).state.1.1.active = s.state.1.1.active := ⟨rfl, rfl⟩

theorem globalOriginalValidation_executes (L : ℕ) (s : CanonicalGlobalStore)
    (hs : UnaryScanReady 0 L (canonicalGlobalNumeric s))
    (hq : s.stk (globalScanPort (.inr .queries)) = []) :
    ∃ n ≤ originalUnaryValidationBound L,
      globalOriginalValidationRoutine.Executes s (globalOriginalValidationEval s) n ∧
      UnaryScanReady 0 L (canonicalGlobalNumeric (globalOriginalValidationEval s)) ∧
      (globalOriginalValidationEval s).stk (globalScanPort (.inr .queries)) = [] ∧
      (globalOriginalValidationEval s).stk (globalScanPort (.inr .original)) =
        s.stk (globalScanPort (.inr .original)) ∧
      (globalOriginalValidationEval s).state.2 = originalUnaryValidity (s.stk (globalScanPort (.inr .original))) := by
  have hbase : UnaryScanReady 0 L (globalValidationOld s) :=
    UnaryScanReady_of_stacks 0 L _ _ hs (fun _ => rfl)
  obtain ⟨n, hn, he, hr, hc, hp, hf⟩ := originalUnaryValidation_executes L (globalValidationOld s) hbase hq
  have h1 := extraPorts_executes originalUnaryValidationRoutine (globalValidationOld s)
    (originalUnaryValidationEval (globalValidationOld s)) (fun k => s.stk (globalFilterPort k)) n he
  have h2 := extraPorts_executes (extraPortsRoutine (E := CanonicalFilterPort) originalUnaryValidationRoutine)
    _ _ (fun k : CanonicalGlobalPort => s.stk (.inr k)) n h1
  have h3 := controlTransport_executes globalOriginalValidationBaseRoutine selectedValidatorControlEquiv
    (globalValidationExpanded s (globalValidationOld s))
    (globalValidationExpanded s (originalUnaryValidationEval (globalValidationOld s)))
    (globalValidationCallerFrame s) n h2
  rw [globalOriginalValidation_input] at h3
  refine ⟨n, hn, h3, ?_, hc, hp, hf⟩
  exact UnaryScanReady_of_stacks 0 L _ _ hr (fun _ => rfl)

theorem originalUnaryValidity_true_iff (bits : List Bool) :
    originalUnaryValidity bits = true ↔
      ∃ R, readNormalizedSource bits = some R ∧ RawMSSCValid R := by
  cases hp : readNormalizedSource bits with
  | none => simp [originalUnaryValidity, hp]
  | some R => simp [originalUnaryValidity, hp, unaryRangeValid_eq_original, scanSourceValid_spec]

theorem globalOriginalValidation_success (L : ℕ) (s : CanonicalGlobalStore)
    (hs : UnaryScanReady 0 L (canonicalGlobalNumeric s))
    (hq : s.stk (globalScanPort (.inr .queries)) = [])
    (h : (globalOriginalValidationEval s).state.2 = true) :
    ∃ R, readNormalizedSource (s.stk (globalScanPort (.inr .original))) = some R ∧ RawMSSCValid R := by
  obtain ⟨n, hn, he, hr, hc, hp, hf⟩ := globalOriginalValidation_executes L s hs hq
  exact (originalUnaryValidity_true_iff _).mp (hf.symm.trans h)

/- This closes the ACTUAL control-interface gap, not the whole reduction.
The uniform bound is unchanged: 17L^4+44L^3+63L^2+90L+55. Its guard is
the ORIGINAL source validity test, even when N=0. The original special
cases must still be implemented downstream and cannot bypass this test.
Total standalone packaging, normalization composition, independent target
verification and compatible encoded-hardness/kernel checking remain open.
-/

end PolytomyReductionModel
