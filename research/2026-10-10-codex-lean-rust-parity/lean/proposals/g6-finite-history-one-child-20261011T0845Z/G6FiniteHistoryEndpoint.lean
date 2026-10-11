import G6NaturalCommonForestFactorization

/-!
Finite-history LAST endpoint bridge for the already defined original source
program. Contributor: Codex / lean_integration_successor, 11 October 2026.
UNCOMPILED SOURCE PROPOSAL. No compiler, parser or imported provider ran here.

The initializer is retained for the empty word. For a nonempty word, recordEnd
reads the existing Fin.last coordinate. The history and the endpoint program
use the same sourceProgramStep; no new process or history carrier is defined.
An arbitrary old label may remain correlated with the entering Code.
-/
namespace GProgram.G6.FiniteHistoryEndpoint

open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.PrivateRegisterHistory
open GProgram.G2.SourceFiniteHistory
open GProgram.G6.NaturalCommonForestFactorization
open scoped Classical

/-- Prepending the first endpoint does not change the final endpoint reader. -/
lemma recordEnd_cons {A : Type*} (n : Nat) (s d : A) (z : Fin n → A) :
    recordEnd (n + 1) s (Fin.cons d z) = recordEnd n d z := by
  cases n with
  | zero => simp only [recordEnd, Fin.last_zero, Fin.cons_zero]
  | succ n => simp only [recordEnd, Fin.cons_last]

/-- The Fin-history LAST reader follows the existing first-step bind. -/
theorem historyLaw_recordEnd_cons {S Op : Type*} (K : Op → S → PMF S)
    (op : Op) (ops : List Op) (s : S) :
    (historyLaw K (op :: ops) s).map (recordEnd (op :: ops).length s) =
      (K op s).bind (fun d => (historyLaw K ops d).map (recordEnd ops.length d)) := by
  rw [historyLaw, PMF.map_bind]
  congr 1
  funext d
  rw [PMF.map_comp]
  congr 1
  funext z
  exact recordEnd_cons ops.length s d z

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The LAST endpoint marginal of the actual finite source history is its
unchanged sourceProgram law, including the empty-word initial Code. -/
theorem actual_sourceHistory_recordEnd (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    (sourceHistoryLaw N r ops s).map (recordEnd ops.length s) =
      sourceProgram N r ops s := by
  change (historyLaw (sourceProgramStep N r) ops s).map (recordEnd ops.length s) = _
  induction ops generalizing s with
  | nil => simp only [historyLaw, PMF.pure_map, recordEnd, sourceProgram]
  | cons op ops ih =>
      rw [historyLaw_recordEnd_cons, sourceProgram]
      simp_rw [ih]

/-- Every supported finite history has a supported original program endpoint. -/
theorem actual_sourceHistory_recordEnd_support (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (s : Code N sample) (z : Fin ops.length → Code N sample)
    (hz : z ∈ (sourceHistoryLaw N r ops s).support) :
    recordEnd ops.length s z ∈ (sourceProgram N r ops s).support := by
  rw [← actual_sourceHistory_recordEnd N r ops s]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨z, hz, rfl⟩

/-- LAST projection preserves the old label and the actual entering Code.
The initial joint law is arbitrary; no entering independence is assumed. -/
theorem actual_initialized_recordEnd_law {Old : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (initial : PMF (Old × Code N sample)) :
    (initializedSourceHistory N r ops initial).map
        (fun a => (a.1, (a.2.1, recordEnd ops.length a.2.1 a.2.2))) =
      initial.bind (fun q => (sourceProgram N r ops q.2).map
        (fun d => (q.1, (q.2, d)))) := by
  rw [initializedSourceHistory, PMF.map_bind]
  congr 1
  funext q
  rw [PMF.map_comp]
  change (sourceHistoryLaw N r ops q.2).map
    ((fun d => (q.1, (q.2, d))) ∘ recordEnd ops.length q.2) = _
  rw [← PMF.map_comp, actual_sourceHistory_recordEnd N r ops q.2]

/-- Support extraction retains the same original initializer and old label. -/
theorem actual_initialized_recordEnd_support {Old : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (initial : PMF (Old × Code N sample))
    (a : Old × (Code N sample × (Fin ops.length → Code N sample)))
    (ha : a ∈ (initializedSourceHistory N r ops initial).support) :
    ∃ q ∈ initial.support, a.1 = q.1 ∧ a.2.1 = q.2 ∧
      recordEnd ops.length a.2.1 a.2.2 ∈ (sourceProgram N r ops q.2).support := by
  change a ∈ (initial.bind (fun q => (sourceHistoryLaw N r ops q.2).map
    (fun z => (q.1, (q.2, z))))).support at ha
  obtain ⟨q, hq, hqa⟩ := (PMF.mem_support_bind_iff _ _ _).mp ha
  obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hqa
  exact ⟨q, hq, rfl, rfl, actual_sourceHistory_recordEnd_support N r ops q.2 z hz⟩

/-- Any proved endpoint-support predicate transfers to the finite LAST reader.
This is support composition, not a desired-law or independence premise. -/
theorem actual_initialized_recordEnd_property {Old : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (initial : PMF (Old × Code N sample))
    (Q : Code N sample → Prop)
    (hQ : ∀ q ∈ initial.support, ∀ d ∈ (sourceProgram N r ops q.2).support, Q d)
    (a : Old × (Code N sample × (Fin ops.length → Code N sample)))
    (ha : a ∈ (initializedSourceHistory N r ops initial).support) :
    Q (recordEnd ops.length a.2.1 a.2.2) := by
  obtain ⟨q, hq, _, _, hd⟩ := actual_initialized_recordEnd_support N r ops initial a ha
  exact hQ q hq _ hd

#print axioms recordEnd_cons
#print axioms historyLaw_recordEnd_cons
#print axioms actual_sourceHistory_recordEnd
#print axioms actual_sourceHistory_recordEnd_support
#print axioms actual_initialized_recordEnd_law
#print axioms actual_initialized_recordEnd_support
#print axioms actual_initialized_recordEnd_property
end GProgram.G6.FiniteHistoryEndpoint
