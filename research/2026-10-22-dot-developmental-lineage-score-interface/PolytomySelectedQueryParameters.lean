/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual caller-owned parameter copies before the complete selected query.
The original type/index words survive on added caller tapes; the copied
cap/selector are consumed by the query. All untouched caller data survive.
-/
import PolytomyCompleteSelectedQuery

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

abbrev SelectedQueryCallerStack (E : Type) := (NumericStack UnaryScanPort) ⊕ E

variable {E : Type} [DecidableEq E]

def selectedQueryPreparedBase (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame)
    (typeWord rowWord : List Bool) : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame :=
  ⟨s.state, Function.update (Function.update s.stk (.inl .cap) typeWord) (.inr .queries) rowWord⟩

def selectedQueryPrepareRoutine (typePort rowPort temp : E) :
    Routine (fun _ : SelectedQueryCallerStack E => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq
    (wordDuplicateRoutine (.inr typePort) (.inr temp) (.inl (.inl .cap)))
    (wordDuplicateRoutine (.inr rowPort) (.inr temp) (.inl (.inr .queries)))

def selectedQueryPrepareEval (typePort rowPort : E)
    (s : CountdownStore (SelectedQueryCallerStack E) SelectedRowFrame) :=
  wordDuplicateEval (.inr rowPort) (.inl (.inr .queries))
    (wordDuplicateEval (.inr typePort) (.inl (.inl .cap)) s)

theorem selectedQueryPrepare_executes (typePort rowPort temp : E)
    (htt : typePort ≠ temp) (hrt : rowPort ≠ temp)
    (s : CountdownStore (SelectedQueryCallerStack E) SelectedRowFrame)
    (ht : s.stk (.inr temp) = []) :
    (selectedQueryPrepareRoutine typePort rowPort temp).Executes s
      (selectedQueryPrepareEval typePort rowPort s)
      (3 * (s.stk (.inr typePort)).length + 3 * (s.stk (.inr rowPort)).length + 6) := by
  let u := wordDuplicateEval (.inr typePort) (.inl (.inl .cap)) s
  have h1 := wordDuplicate_executes (.inr typePort : SelectedQueryCallerStack E) (.inr temp)
    (.inl (.inl .cap)) (by simpa using htt) (by simp) (by simp) s ht
  have hu : u.stk (.inr temp) = [] := by simp [u, wordDuplicateEval, ht]
  have h2 := wordDuplicate_executes (.inr rowPort : SelectedQueryCallerStack E) (.inr temp)
    (.inl (.inr .queries)) (by simpa using hrt) (by simp) (by simp) u hu
  have hrow : u.stk (.inr rowPort) = s.stk (.inr rowPort) := by simp [u, wordDuplicateEval]
  rw [hrow] at h2
  have h := RoutineComposition.seq_executes _ _ h1 h2
  simpa only [selectedQueryPrepareRoutine, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem selectedQueryPrepare_effect (typePort rowPort : E)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame)
    (extra : E → List Bool) (hcap : s.stk (.inl .cap) = []) (hq : s.stk (.inr .queries) = []) :
    selectedQueryPrepareEval typePort rowPort (extraPortsStore s extra) =
      extraPortsStore (selectedQueryPreparedBase s (extra typePort) (extra rowPort)) extra := by
  apply countdownStore_ext
  · rfl
  · funext k
    cases k with
    | inl k =>
        by_cases hkcap : k = .inl .cap
        · subst k
          simp [selectedQueryPrepareEval, wordDuplicateEval, selectedQueryPreparedBase, extraPortsStore, hcap]
        · by_cases hkq : k = .inr .queries
          · subst k
            simp [selectedQueryPrepareEval, wordDuplicateEval, selectedQueryPreparedBase, extraPortsStore, hq]
          · simp [selectedQueryPrepareEval, wordDuplicateEval, selectedQueryPreparedBase, extraPortsStore, hkcap, hkq]
    | inr k => simp [selectedQueryPrepareEval, wordDuplicateEval, selectedQueryPreparedBase, extraPortsStore]

theorem selectedQueryPrepared_ready (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady 0 L s)
    (typeWord rowWord : List Bool) (htype : typeWord = List.replicate C true) :
    UnaryScanReady C L (selectedQueryPreparedBase s typeWord rowWord) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [selectedQueryPreparedBase] using hs.numeric.1
    · simpa [selectedQueryPreparedBase] using hs.numeric.2.1
    · simpa [selectedQueryPreparedBase] using hs.numeric.2.2.1
    · simp [selectedQueryPreparedBase, htype]
    · simpa [selectedQueryPreparedBase] using hs.numeric.2.2.2.2
  · simpa [selectedQueryPreparedBase] using hs.source_empty
  · intro k hk
    have hkq : k ≠ .queries := by intro h; subst k; simp [scanWorkExtras] at hk
    simpa [selectedQueryPreparedBase, hkq] using hs.empty k hk
  · simpa [selectedQueryPreparedBase] using hs.original_bound

def copiedSelectedQueryRoutine (typePort rowPort temp : E) :
    Routine (fun _ : SelectedQueryCallerStack E => Bool) (CountdownState SelectedRowFrame) :=
  RoutineComposition.seq (selectedQueryPrepareRoutine typePort rowPort temp)
    (extraPortsRoutine (E := E) selectedQueryRoutine)

def copiedSelectedQueryResult (C : ℕ) (typePort rowPort : E)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (extra : E → List Bool) :=
  extraPortsStore (selectedQueryEval C (selectedQueryPreparedBase s (extra typePort) (extra rowPort))) extra

theorem copiedSelectedQuery_executes (typePort rowPort temp : E)
    (htt : typePort ≠ temp) (hrt : rowPort ≠ temp) (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady 0 L s)
    (hq : s.stk (.inr .queries) = []) (extra : E → List Bool)
    (ht : extra temp = []) (hC : extra typePort = List.replicate C true) :
    ∃ n ≤ selectedQueryBound C L (extra rowPort).length + 3 * C + 3 * (extra rowPort).length + 6,
      (copiedSelectedQueryRoutine typePort rowPort temp).Executes (extraPortsStore s extra)
        (copiedSelectedQueryResult C typePort rowPort s extra) n ∧
      (copiedSelectedQueryResult C typePort rowPort s extra).state.2 =
        selectedQueryMember C (extra rowPort).length (s.stk (.inr .original)) ∧
      ∀ e, (copiedSelectedQueryResult C typePort rowPort s extra).stk (.inr e) = extra e := by
  let u := selectedQueryPreparedBase s (extra typePort) (extra rowPort)
  have hu := selectedQueryPrepared_ready C L s hs (extra typePort) (extra rowPort) hC
  have hcap : s.stk (.inl .cap) = [] := by simpa using hs.numeric.2.2.2.1
  have hcopy := selectedQueryPrepare_executes typePort rowPort temp htt hrt (extraPortsStore s extra) ht
  rw [selectedQueryPrepare_effect typePort rowPort s extra hcap hq] at hcopy
  have hcopylen : 3 * ((extraPortsStore s extra).stk (.inr typePort)).length +
      3 * ((extraPortsStore s extra).stk (.inr rowPort)).length + 6 =
      3 * C + 3 * (extra rowPort).length + 6 := by simp [extraPortsStore, hC]
  rw [hcopylen] at hcopy
  have hi : (u.stk (.inr .queries)).length ≤ (extra rowPort).length := by simp [u, selectedQueryPreparedBase]
  obtain ⟨n, hn, he, hready, hclean, hpres, hflag⟩ := selectedQuery_executes C L (extra rowPort).length u hu hi
  have hlift := extraPorts_executes selectedQueryRoutine u (selectedQueryEval C u) extra n he
  have hall := RoutineComposition.seq_executes _ _ hcopy hlift
  refine ⟨(3 * C + 3 * (extra rowPort).length + 6) + n, by omega, hall, ?_, fun _ => rfl⟩
  simpa [copiedSelectedQueryResult, extraPortsStore, u, selectedQueryPreparedBase] using hflag

theorem copiedSelectedQuery_ready (typePort rowPort : E) (C L : ℕ)
    (s : CountdownStore (NumericStack UnaryScanPort) SelectedRowFrame) (hs : UnaryScanReady 0 L s)
    (extra : E → List Bool) (hC : extra typePort = List.replicate C true) :
    UnaryScanReady 0 L (selectedQueryEval C (selectedQueryPreparedBase s (extra typePort) (extra rowPort))) ∧
      (selectedQueryEval C (selectedQueryPreparedBase s (extra typePort) (extra rowPort))).stk (.inr .queries) = [] ∧
      (selectedQueryEval C (selectedQueryPreparedBase s (extra typePort) (extra rowPort))).stk (.inr .original) =
        s.stk (.inr .original) := by
  let u := selectedQueryPreparedBase s (extra typePort) (extra rowPort)
  have hu := selectedQueryPrepared_ready C L s hs (extra typePort) (extra rowPort) hC
  obtain ⟨n, hn, he, hready, hclean, hpres, hflag⟩ := selectedQuery_executes C L (extra rowPort).length u hu
    (by simp [u, selectedQueryPreparedBase])
  exact ⟨hready, hclean, hpres⟩

/- Both parameters are physically copied. Their caller originals and
arbitrary other added tape contents survive; the callee's copies and
private scratch are clean at return. Complete original rawRowMember
threshold branches, actual finite-control integration and canonical
enumeration/arithmetic/serialization remain to join. No machine is run.
-/

end PolytomyReductionModel
