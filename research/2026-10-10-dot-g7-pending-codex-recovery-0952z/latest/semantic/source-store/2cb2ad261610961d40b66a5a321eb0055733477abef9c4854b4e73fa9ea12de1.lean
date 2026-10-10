import G7ProgramRelabelling

/-! Once-drawn original-register initialization for an actual mapped source
word. Contributor: dot, 2026-10-09. The final bind uses the inherited original
register PMF and initial code, with no desired-law premise. -/
namespace GProgram.G7.NaturalWordRelabelling
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source MeasureTheory
open GProgram.G7.OriginalRelabelling GProgram.G7.SnapshotRelabelling
open GProgram.G7.BoundaryRelabelling GProgram.G7.CoinReindexing
open GProgram.G7.ProgramRelabelling
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceInitializedCalendar
open scoped Classical
variable {V E W F Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable [Fintype Copy] [DecidableEq Copy]

theorem register_commutes (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (c : Hybrid N → Bool) :
    coinTransport v (originalRegister N c) =
      originalRegister (network N v e) (coinTransport (hybrids N v e) c) := by
  funext w
  simp only [coinTransport,originalRegister]
  have h : (network N v e).graph.IsHybrid w ↔ N.graph.IsHybrid (v.symm w) :=
    hybrid_iff N.graph v e w
  by_cases hw : N.graph.IsHybrid (v.symm w)
  · simp only [hw,h.mpr hw,dif_pos]
    rfl
  · simp [hw,mt h.mp hw]

theorem original_coin_pmf (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (p : HybridProbabilities N) :
    (originalRegisterMeasure N p).toPMF.map (coinTransport (hybrids N v e)) =
      (originalRegisterMeasure (network N v e) (inheritance N v e p)).toPMF := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (coinTransport (hybrids N v e))
    (originalRegisterMeasure N p).toPMF (original_coin_measure N v e p).measurable]
  simp only [Measure.toPMF_toMeasure]
  exact (original_coin_measure N v e p).map_eq

theorem register_pmf (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (p : HybridProbabilities N) :
    (originalRegisterPMF N p).map (coinTransport v) =
      originalRegisterPMF (network N v e) (inheritance N v e p) := by
  unfold originalRegisterPMF
  rw [PMF.map_comp]
  have hf : coinTransport v ∘ originalRegister N =
      originalRegister (network N v e) ∘ coinTransport (hybrids N v e) := by
    funext c
    exact register_commutes N v e c
  rw [hf,← PMF.map_comp,original_coin_pmf]

theorem initial_code (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (sample : Copy → X) (reg : V → Bool) :
    code N v e (initialCode N sample reg) =
      initialCode (network N v e) sample (coinTransport v reg) := by
  unfold initialCode
  rw [admittedCode_commutes]
  apply admitted_congr
  exact GProgram.G7.SourceStateRelabelling.initial_commutes N v e sample reg

/-- Actual unconditional finite-word source endpoint law. One original latent
register is drawn once and transported jointly, then reused for the whole word. -/
theorem initialized_word (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) :
    ((originalRegisterPMF N p).bind (fun reg =>
      sourceProgram N r ops (initialCode N sample reg))).map (code N v e) =
    (originalRegisterPMF (network N v e) (inheritance N v e p)).bind (fun reg =>
      sourceProgram (network N v e) (rates e r) (ops.map (programStep N v e))
        (initialCode (network N v e) sample reg)) := by
  rw [PMF.map_bind]
  simp_rw [program,initial_code]
  change (originalRegisterPMF N p).bind
    ((fun reg => sourceProgram (network N v e) (rates e r) (ops.map (programStep N v e))
      (initialCode (network N v e) sample reg)) ∘ coinTransport v) = _
  rw [← PMF.bind_map,register_pmf N v e p]

#print axioms register_pmf
#print axioms initial_code
#print axioms initialized_word
end GProgram.G7.NaturalWordRelabelling
