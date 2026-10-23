import G1OriginalWholeCausalView

/-! SOURCE-derived finite-phase K macro on the original Code carrier. Every
chosen representative lies in REAL original phase support. Only the complete
original UNRANKED causal row is identified; raw IDs/plane order may differ.
Contributor: dot, 2026-10-03. -/
namespace G1ActualSourceKMacroTransition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1ActualJointProgram G1ActualJointEpoch G1ActualJointOpaqueContext
open G1SameOriginalExteriorContinuation
open G1UnrankedSourceView G1UnrankedActualFuture G1UnrankedSingleExitLabel
open G1ActualUnrankedKMacro G1ActualKProductInsertion G1OriginalWholeCausalView
open G1ContextualForestReplacement
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- REAL support admission, rather than any fitted physical-state witness.
The fallback is unreachable on the derived product law's support. -/
noncomputable def realKRepresentative (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy)
    (phase : List (ProgramStep N)) (initial : Code N sample)
    (data : KExitData V E Copy) : Code N sample :=
  if h : ∃ d : Code N sample, d ∈ (sourceProgram N r phase initial).support ∧
      actualKExitData N inside outside d = data then Classical.choose h else initial

lemma representative_at_actual_data (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy)
    (phase : List (ProgramStep N)) (initial d : Code N sample)
    (hd : d ∈ (sourceProgram N r phase initial).support) :
    realKRepresentative N r inside outside phase initial (actualKExitData N inside outside d)
      ∈ (sourceProgram N r phase initial).support ∧
    actualKExitData N inside outside
      (realKRepresentative N r inside outside phase initial (actualKExitData N inside outside d)) =
      actualKExitData N inside outside d := by
  have hw : ∃ z : Code N sample, z ∈ (sourceProgram N r phase initial).support ∧
      actualKExitData N inside outside z = actualKExitData N inside outside d := ⟨d,hd,rfl⟩
  rw [realKRepresentative,dif_pos hw]
  exact Classical.choose_spec hw

lemma representative_whole_view (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (p : Location V E)
    (phase : List (ProgramStep N)) (initial d : Code N sample)
    (partition : inside ∪ outside = (state initial).live)
    (physical : ∀ z ∈ (sourceProgram N r phase initial).support, PhysicalKExit N inside outside p z)
    (hd : d ∈ (sourceProgram N r phase initial).support) :
    wholeOriginalView N
      (realKRepresentative N r inside outside phase initial (actualKExitData N inside outside d)) =
      wholeOriginalView N d := by
  let z := realKRepresentative N r inside outside phase initial (actualKExitData N inside outside d)
  obtain ⟨hz,hdata⟩ := representative_at_actual_data N r inside outside phase initial d hd
  have hK := congrArg Prod.fst hdata
  have ho := congrArg Prod.snd hdata
  have hreg : (state z).register = (state d).register := unranked_view_register _ _ ho
  have hv := actual_K_only_complete_exit_view (state z) (state d) z.property.forest d.property.forest
    inside outside p (physical z hz).1 (physical d hd).1 hK
    (physical z hz).2 (physical d hd).2 hreg ho
  rw [partition] at hv
  exact actual_supported_current_view_lifts_to_whole N r phase initial z d hz hd hv

/-- Actual independently initialized CURRENT-root K and actual concurrent
exterior law; Γ is retained in the exterior view and never resampled. -/
noncomputable def sourceKMacro (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy)
    (phase : List (ProgramStep N)) (initial : Code N sample)
    (hi : inside ⊆ (state initial).live) (ho : outside ⊆ (state initial).live) : PMF (Code N sample) :=
  (independentProduct (actualCurrentRootK N r phase initial inside hi)
    (actualExteriorUnrankedState N r phase initial outside ho)).map
      (realKRepresentative N r inside outside phase initial)

theorem actual_source_K_macro_whole_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (p : Location V E)
    (phase : List (ProgramStep N)) (initial : Code N sample)
    (hi : inside ⊆ (state initial).live) (ho : outside ⊆ (state initial).live)
    (partition : inside ∪ outside = (state initial).live)
    (sep : SeparatedAgenda N r inside outside phase initial)
    (physical : ∀ d ∈ (sourceProgram N r phase initial).support, PhysicalKExit N inside outside p d) :
    (sourceKMacro N r inside outside phase initial hi ho).map (wholeOriginalView N) =
      (sourceProgram N r phase initial).map (wholeOriginalView N) := by
  rw [sourceKMacro,←actual_K_exterior_interface_product N r inside outside phase initial hi ho sep,
    PMF.map_comp,PMF.map_comp]
  apply map_eq_of_eq_on_support
  intro d hd
  exact representative_whole_view N r inside outside p phase initial d partition physical hd

theorem actual_source_K_macro_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy)
    (phase : List (ProgramStep N)) (initial : Code N sample)
    (hi : inside ⊆ (state initial).live) (ho : outside ⊆ (state initial).live)
    (sep : SeparatedAgenda N r inside outside phase initial)
    {d : Code N sample} (hd : d ∈ (sourceKMacro N r inside outside phase initial hi ho).support) :
    d ∈ (sourceProgram N r phase initial).support := by
  rw [sourceKMacro,←actual_K_exterior_interface_product N r inside outside phase initial hi ho sep,
    PMF.map_comp] at hd
  obtain ⟨z,hz,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  rw [←he]
  exact (representative_at_actual_data N r inside outside phase initial z hz).1

#print axioms actual_source_K_macro_whole_row
#print axioms actual_source_K_macro_support
end G1ActualSourceKMacroTransition
