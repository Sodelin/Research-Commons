import UnifiedLean.G6.PrivateRegisterProgram
import G2SourceFiniteHistory

/-!
UNCHECKED SAME-graph full endpoint-vector consumer. Every Code is erased,
including the initial Code, while a supplied correlated old label is retained.
This is the defined finite operation history, not the full physical marked
clock/pulse record. No desired history law is a scientific input.
Outside the active165 freeze. CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026.
-/
namespace UnifiedLean.G6.PrivateRegisterHistory
open Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.PrivateRegisterErasure
open UnifiedLean.G6.PrivateRegisterProgram
open GProgram.G2.SourceFiniteHistory
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_sourceHistory_erasure (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (P : Finset V)
    (ops : List (ProgramStep N)) :
    NoPrivateWordRead N P ops → ∀ s : Code N sample,
    (sourceHistoryLaw N r ops s).map (historyProjection (erasePrivateCode N P)) =
      sourceHistoryLaw N r ops (erasePrivateCode N P s) := by
  change NoPrivateWordRead N P ops → ∀ s,
    (historyLaw (sourceProgramStep N r) ops s).map
      (historyProjection (erasePrivateCode N P)) =
        historyLaw (sourceProgramStep N r) ops (erasePrivateCode N P s)
  induction ops with
  | nil =>
      intro _ s
      rw [historyLaw, historyLaw, PMF.pure_map]
      congr 1
      funext i
      exact Fin.elim0 i
  | cons op ops ih =>
      intro hops s
      have hhead : NoPrivateStepRead N P op := hops op List.mem_cons_self
      have htail : NoPrivateWordRead N P ops := by
        intro b hb
        exact hops b (List.mem_cons_of_mem op hb)
      rw [historyLaw, PMF.map_bind]
      have he (d : Code N sample) :
          ((historyLaw (sourceProgramStep N r) ops d).map (Fin.cons d)).map
            (historyProjection (erasePrivateCode N P)) =
          ((historyLaw (sourceProgramStep N r) ops d).map
            (historyProjection (erasePrivateCode N P))).map
              (Fin.cons (erasePrivateCode N P d)) := by
        rw [PMF.map_comp, PMF.map_comp]
        congr 1
        funext z i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      simp_rw [he, ih htail]
      change (sourceProgramStep N r op s).bind
        ((fun d : Code N sample =>
          (historyLaw (sourceProgramStep N r) ops d).map
            (fun z : Fin ops.length → Code N sample =>
              (Fin.cons d z : Fin (ops.length + 1) → Code N sample))) ∘
          erasePrivateCode N P) = _
      rw [← PMF.bind_map, actual_sourceProgramStep_erasure N r P op s hhead]
      rfl

/-- An arbitrary old label may be correlated with the actual initial Code;
the defined law retains both that Code and every future endpoint, even for
an empty operation word. No independence is assumed. -/
noncomputable def initializedSourceHistory {Old : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (initial : PMF (Old × Code N sample)) :
    PMF (Old × (Code N sample × (Fin ops.length → Code N sample))) :=
  initial.bind (fun a => (sourceHistoryLaw N r ops a.2).map
    (fun z => (a.1, (a.2, z))))

theorem actual_initialized_history_erasure {Old : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (P : Finset V) (ops : List (ProgramStep N)) (hops : NoPrivateWordRead N P ops)
    (initial : PMF (Old × Code N sample)) :
    (initializedSourceHistory N r ops initial).map
      (fun a => (a.1, (erasePrivateCode N P a.2.1,
        historyProjection (erasePrivateCode N P) a.2.2))) =
      initializedSourceHistory N r ops
        (initial.map (fun a => (a.1, erasePrivateCode N P a.2))) := by
  rw [initializedSourceHistory, PMF.map_bind]
  have hrow (a : Old × Code N sample) :
      ((sourceHistoryLaw N r ops a.2).map (fun z => (a.1, (a.2, z)))).map
        (fun b => (b.1, (erasePrivateCode N P b.2.1,
          historyProjection (erasePrivateCode N P) b.2.2))) =
      (sourceHistoryLaw N r ops (erasePrivateCode N P a.2)).map
        (fun z => (a.1, (erasePrivateCode N P a.2, z))) := by
    rw [PMF.map_comp]
    change (sourceHistoryLaw N r ops a.2).map
      ((fun z => (a.1, (erasePrivateCode N P a.2, z))) ∘
        historyProjection (erasePrivateCode N P)) = _
    rw [← PMF.map_comp, actual_sourceHistory_erasure N r P ops hops a.2]
  simp_rw [hrow]
  change initial.bind
    ((fun a : Old × Code N sample =>
      (sourceHistoryLaw N r ops a.2).map (fun z => (a.1, (a.2, z)))) ∘
      (fun a : Old × Code N sample => (a.1, erasePrivateCode N P a.2))) = _
  rw [← PMF.bind_map]
  rfl

theorem actual_erased_joint_history_readout {Old Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (P : Finset V) (ops : List (ProgramStep N)) (hops : NoPrivateWordRead N P ops)
    (initial : PMF (Old × Code N sample))
    (readout : Old × (Code N sample × (Fin ops.length → Code N sample)) → Obs) :
    (initializedSourceHistory N r ops initial).map
      (readout ∘ (fun a => (a.1, (erasePrivateCode N P a.2.1,
        historyProjection (erasePrivateCode N P) a.2.2)))) =
      (initializedSourceHistory N r ops
        (initial.map (fun a => (a.1, erasePrivateCode N P a.2)))).map readout := by
  rw [← PMF.map_comp, actual_initialized_history_erasure N r P ops hops initial]

#print axioms actual_sourceHistory_erasure
#print axioms actual_initialized_history_erasure
#print axioms actual_erased_joint_history_readout

end UnifiedLean.G6.PrivateRegisterHistory
