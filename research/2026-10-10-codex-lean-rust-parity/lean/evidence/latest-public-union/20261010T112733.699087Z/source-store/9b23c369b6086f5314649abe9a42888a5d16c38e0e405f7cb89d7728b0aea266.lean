import G1OriginalExteriorHistoryProduct

/-! The macro samples true K jointly with the complete actual exterior
checkpoint history, restores ALL original outside opaque descendant trees,
and chooses only a REAL supported original phase endpoint. -/
namespace G1ActualHistoryEnrichedKMacro
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1ActualJointProgram G1ActualJointOpaqueContext G1ActualJointStageHistory
open G1ActualJointEpoch
open G1ContextualForestReplacement G1UnrankedSourceView G1UnrankedActualFuture
open G1UnrankedSingleExitLabel G1ActualUnrankedKMacro G1ActualKProductInsertion
open G1UnrankedExteriorHistoryKInsertion G1OriginalWholeCausalView
open G1OriginalOpaqueExteriorView G1OriginalExteriorHistoryProduct
open G1SourceMacroComposition
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev KHistoryData (V E Copy : Type*) := Finset (UnrankedTree Copy) × List (UnrankedView V E Copy)

noncomputable def actualKHistoryData (N : RootedBinary V E X) {sample : Copy → X}
    (inside outside : Finset Copy) (initial : Code N sample) (tr : List (Code N sample)) :
    KHistoryData V E Copy :=
  (sourceUnrankedForest (state (tr.getLastD initial)) inside,exteriorHistory N outside tr)

noncomputable def realHistoryEndpoint (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy)
    (phase : List (ProgramStep N)) (initial : Code N sample) (data : KHistoryData V E Copy) : Code N sample :=
  if h : ∃ tr : List (Code N sample), tr ∈ (sourceStageHistory N r phase initial).support ∧
      actualKHistoryData N inside outside initial tr = data then (Classical.choose h).getLastD initial else initial

lemma endpoint_actual_history_spec (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy)
    (phase : List (ProgramStep N)) (initial : Code N sample) (tr : List (Code N sample))
    (ht : tr ∈ (sourceStageHistory N r phase initial).support) :
    ∃ chosen : List (Code N sample), chosen ∈ (sourceStageHistory N r phase initial).support ∧
      actualKHistoryData N inside outside initial chosen = actualKHistoryData N inside outside initial tr ∧
      realHistoryEndpoint N r inside outside phase initial (actualKHistoryData N inside outside initial tr) =
        chosen.getLastD initial := by
  have hw : ∃ chosen : List (Code N sample), chosen ∈ (sourceStageHistory N r phase initial).support ∧
      actualKHistoryData N inside outside initial chosen = actualKHistoryData N inside outside initial tr := ⟨tr,ht,rfl⟩
  rw [realHistoryEndpoint,dif_pos hw]
  exact ⟨Classical.choose hw,(Classical.choose_spec hw).1,(Classical.choose_spec hw).2,rfl⟩

lemma real_history_end_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (initial : Code N sample)
    (tr : List (Code N sample)) (ht : tr ∈ (sourceStageHistory N r phase initial).support) :
    tr.getLastD initial ∈ (sourceProgram N r phase initial).support := by
  rw [← actual_source_history_end N r phase initial]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨tr,ht,rfl⟩

theorem actual_history_endpoint_whole_view (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (p : Location V E)
    (phase : List (ProgramStep N)) (initial : Code N sample) (partition : inside ∪ outside = (state initial).live)
    (physical : ∀ d ∈ (sourceProgram N r phase initial).support, PhysicalKExit N inside outside p d)
    (tr : List (Code N sample)) (ht : tr ∈ (sourceStageHistory N r phase initial).support) :
    wholeOriginalView N (realHistoryEndpoint N r inside outside phase initial
      (actualKHistoryData N inside outside initial tr)) = wholeOriginalView N (tr.getLastD initial) := by
  obtain ⟨chosen,hchosen,hdata,he⟩ := endpoint_actual_history_spec N r inside outside phase initial tr ht
  rw [he]
  have hz := real_history_end_support N r phase initial chosen hchosen
  have hd := real_history_end_support N r phase initial tr ht
  have hK := congrArg Prod.fst hdata
  have ho := congrArg (fun v : KHistoryData V E Copy => v.2.getLastD
    (unrankedView (selectedView (state initial) outside))) hdata
  simp only [actualKHistoryData,exteriorHistory,List.getLastD_map] at ho
  have hreg := unranked_view_register _ _ ho
  have hv := actual_K_only_complete_exit_view _ _ (chosen.getLastD initial).property.forest
    (tr.getLastD initial).property.forest inside outside p (physical _ hz).1 (physical _ hd).1 hK
    (physical _ hz).2 (physical _ hd).2 hreg ho
  rw [partition] at hv
  exact actual_supported_current_view_lifts_to_whole N r phase initial _ _ hz hd hv

noncomputable def sourceKHistoryMacro (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (phase : List (ProgramStep N))
    (initial : Code N sample) (hi : inside ⊆ (state initial).live) :
    PMF (List (UnrankedView V E Copy) × Code N sample) :=
  (independentProduct (actualCurrentRootK N r phase initial inside hi)
    ((sourceStageHistory N r phase initial).map (exteriorHistory N outside))).map
      (fun data => (data.2.map (opaqueExteriorView (state initial) outside),
        realHistoryEndpoint N r inside outside phase initial data))

/-- The JOINT complete ORIGINAL exterior micro-checkpoint trajectory and
whole ORIGINAL final causal view have their actual source law. -/
theorem actual_history_enriched_K_macro_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (p : Location V E)
    (phase : List (ProgramStep N)) (initial : Code N sample) (hi : inside ⊆ (state initial).live)
    (partition : inside ∪ outside = (state initial).live)
    (sep : SeparatedAgenda N r inside outside phase initial)
    (physical : ∀ d ∈ (sourceProgram N r phase initial).support, PhysicalKExit N inside outside p d) :
    (sourceKHistoryMacro N r inside outside phase initial hi).map (fun v => (v.1,wholeOriginalView N v.2)) =
      (sourceStageHistory N r phase initial).map
        (fun tr => (originalExteriorHistory N initial outside tr,wholeOriginalView N (tr.getLastD initial))) := by
  rw [sourceKHistoryMacro,←actual_K_whole_exterior_history_product N r inside outside phase initial hi sep,
    PMF.map_comp,PMF.map_comp]
  apply map_eq_of_eq_on_support
  intro tr ht
  apply Prod.ext
  · exact actual_original_exterior_history_lift N r inside outside phase initial partition sep
      (fun d hd => (physical d hd).1) ht
  · exact actual_history_endpoint_whole_view N r inside outside p phase initial partition physical tr ht

theorem actual_history_enriched_K_macro_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (phase : List (ProgramStep N))
    (initial : Code N sample) (hi : inside ⊆ (state initial).live)
    (sep : SeparatedAgenda N r inside outside phase initial)
    {out : List (UnrankedView V E Copy) × Code N sample}
    (hout : out ∈ (sourceKHistoryMacro N r inside outside phase initial hi).support) :
    out.2 ∈ (sourceProgram N r phase initial).support := by
  rw [sourceKHistoryMacro,←actual_K_whole_exterior_history_product N r inside outside phase initial hi sep,
    PMF.map_comp] at hout
  obtain ⟨tr,ht,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  obtain ⟨chosen,hchosen,_,he⟩ := endpoint_actual_history_spec N r inside outside phase initial tr ht
  change realHistoryEndpoint N r inside outside phase initial (actualKHistoryData N inside outside initial tr)
    ∈ (sourceProgram N r phase initial).support
  rw [he]
  exact real_history_end_support N r phase initial chosen hchosen

#print axioms actual_history_enriched_K_macro_row
end G1ActualHistoryEnrichedKMacro
