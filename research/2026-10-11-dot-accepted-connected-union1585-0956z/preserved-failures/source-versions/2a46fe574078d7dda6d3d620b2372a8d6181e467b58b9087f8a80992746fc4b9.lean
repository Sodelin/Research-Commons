import G7SinglePopulationPolynomialKernel
import G1ActualUnrankedAncestralCompletion
import G1NonrootBigonKernel
import G4ActualCommonPrefixSelector

/-!
# Actual co-located COMMON suffix and the inherited completion readout

Contributor: dot (OpenAI), 2026-10-11. UNCOMPILED source assembly draft.
This ports part of the already accepted arbitrary-copy COMMON caterpillar
proof, not a new moment theorem or harmonicity principle. SourceCompletionHarmonic
and the original single-population pair-choice theorems are reused.

`rootRepresentation` is an internal canonical representative of the carried
forest for defining its completion reader. It is not a permitted experiment,
physical population move, or a claimed equality of unbinned histories.
The actual source operations remain unchanged throughout the statements.
-/
namespace DotG4.ActualColocatedCompletion
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceEmbeddedJumpLaw
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.G6.AncestralRateFree
open GProgram.G7.SinglePopulationPolynomialKernel
open G1UnrankedSourceView G1ActualUnrankedAncestralCompletion
open G1NonrootBigonKernel
open DotG4.ActualCommonPrefixSelector
open GProgram.G5.SafePrefixRouteBridge
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeParentRouting
open scoped Classical BigOperators NNReal
variable {V E Copy X Obs : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Same carried genealogy, ancestor map and bank; only an internal reader
representative places its current roots in the original ancestral population. -/
noncomputable def rootState (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : State V E Copy :=
  { state s with location := fun _ => .rootPopulation N.root }

lemma rootState_valid (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : SourceValid N sample (rootState N s) := by
  refine ⟨s.property.forest, ?_⟩
  intro x
  exact ⟨rfl, N.rooted (N.leaf (sample x))⟩

noncomputable def rootRepresentation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Code N sample :=
  admittedCode N sample (rootState N s) (rootState_valid N s)

@[simp] lemma rootRepresentation_live (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : (state (rootRepresentation N s)).live = (state s).live := rfl

@[simp] lemma rootRepresentation_ancestor (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : (state (rootRepresentation N s)).ancestor = (state s).ancestor := rfl

lemma rootRepresentation_genealogy (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) {x : Copy} (hx : x ∈ (state s).live) :
    (state (rootRepresentation N s)).genealogy x = (state s).genealogy x :=
  decode_encode_live_genealogy N.root (rootState N s) (rootState_valid N s).forest hx

lemma rootRepresentation_ancestral (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : AncestralRoot N (rootRepresentation N s) := by
  intro x
  exact decode_encode_copyLocation N.root (rootState N s)
    (rootState_valid N s).forest x

lemma rootRepresentation_selected (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) :
    selectedView (state (rootRepresentation N s)) keep =
      selectedView (rootState N s) keep :=
  decode_encode_selectedView N.root (rootState N s) (rootState_valid N s).forest keep

/-- Canonical reader representation forgets only population placement here;
equality is proved from the actual complete carried source data. -/
lemma rootRepresentation_eq_of_data (N : RootedBinary V E X) {sample : Copy → X}
    (s z : Code N sample) (hlive : (state s).live = (state z).live)
    (hancestor : (state s).ancestor = (state z).ancestor)
    (hgenealogy : ∀ x ∈ (state s).live, (state s).genealogy x = (state z).genealogy x)
    (hregister : (state s).register = (state z).register) :
    rootRepresentation N s = rootRepresentation N z := by
  apply Subtype.ext
  apply Snapshot.ext
  · exact hlive
  · exact hancestor
  · funext x
    by_cases hx : x ∈ (state s).live
    · have hz : x ∈ (state z).live := hlive ▸ hx
      simp only [rootRepresentation, admittedCode, encodeSnapshot, rootState,
        dif_pos hx, dif_pos hz]
      congr 1
      exact Subtype.ext (hgenealogy x hx)
    · have hz : x ∉ (state z).live := hlive ▸ hx
      simp only [rootRepresentation, admittedCode, encodeSnapshot, rootState,
        dif_neg hx, dif_neg hz]
  · funext x
    simp only [rootRepresentation, admittedCode, encodeSnapshot, rootState, hlive]
  · exact hregister

lemma rootRepresentation_transport (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (whereTo : Copy → Location V E) (event : SourceEvent V E Copy)
    (hs : SourceValid N sample (transport (state s) whereTo event)) :
    rootRepresentation N (admittedCode N sample (transport (state s) whereTo event) hs) =
      rootRepresentation N s := by
  apply rootRepresentation_eq_of_data
  · rfl
  · rfl
  · intro x hx
    exact decode_encode_live_genealogy N.root _ hs.forest hx
  · rfl

noncomputable def rootChoices (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i) :
    Choice N s ≃ Choice N (rootRepresentation N s) :=
  (populationChoices N s i hs).trans
    (populationChoices N (rootRepresentation N s) none (rootRepresentation_ancestral N s)).symm

@[simp] lemma rootChoices_pair (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i) (p : Choice N s) :
    (rootChoices N s i hs p).2.val = p.2.val := rfl

lemma rootRepresentation_destination (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (q : Option (Choice N s)) :
    rootRepresentation N (stepDestination N s q) =
      stepDestination N (rootRepresentation N s)
        ((Equiv.optionCongr (rootChoices N s i hs)) q) := by
  cases q with
  | none => rfl
  | some p =>
    have hp := population_pair_is_source_legal (state s) (originalPlace N p.1)
      (originalPlace_not_node N p.1) p.2.property
    apply Subtype.ext
    apply Snapshot.ext
    · rfl
    · rfl
    · funext x
      by_cases hx : x ∈ (state s).live.erase p.2.val.2
      · have hxlive := (Finset.mem_erase.mp hx).2
        have ha := rootRepresentation_genealogy N s hp.first_live
        have hb := rootRepresentation_genealogy N s hp.second_live
        have hg := rootRepresentation_genealogy N s hxlive
        simp [rootRepresentation, rootState, stepDestination, admittedCode,
          encodeSnapshot, state, decodeSnapshot, merge, rootChoices, populationChoices,
          hx, hxlive, hp.first_live, hp.second_live]
      · simp [rootRepresentation, rootState, stepDestination, admittedCode,
          encodeSnapshot, state, decodeSnapshot, merge, rootChoices, populationChoices, hx]
    · funext x
      by_cases hx : x ∈ (state s).live.erase p.2.val.2
      · have hlive := (Finset.mem_erase.mp hx).2
        simp [rootRepresentation, rootState, stepDestination, admittedCode,
          encodeSnapshot, state, decodeSnapshot, merge, rootChoices, populationChoices,
          hx, hlive]
      · simp [rootRepresentation, rootState, stepDestination, admittedCode,
          encodeSnapshot, state, decodeSnapshot, merge, rootChoices, populationChoices, hx]
    · rfl

lemma population_total_rate_card (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (i : Option E) (hs : CoLocated N s i) :
    totalRate N r s = (Fintype.card (Choice N s) : ℝ) * (pairRate r i / 2) := by
  unfold totalRate
  simp_rw [population_choice_rate N r s i hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The old ancestral rate cancellation applies to any one actual original
population; neither the forest nor the bank is replaced. -/
lemma population_jump_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (q : Option (Choice N s)) : jumpMass N r s q = ancestralChoiceMass N s q := by
  have hr : pairRate r i / 2 ≠ 0 := ne_of_gt (div_pos (pairRate_pos r i) (by norm_num))
  have hz : totalRate N r s = 0 ↔ Fintype.card (Choice N s) = 0 := by
    rw [population_total_rate_card N r s i hs, mul_eq_zero]
    simp only [hr, or_false, Nat.cast_eq_zero]
  cases q with
  | none => simp only [jumpMass, hz, ancestralChoiceMass]
  | some p =>
    letI : Nonempty (Choice N s) := ⟨p⟩
    have hc : (Fintype.card (Choice N s) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Choice N s) ≠ 0)
    rw [jumpMass, population_choice_rate N r s i hs p, population_total_rate_card N r s i hs]
    dsimp only [ancestralChoiceMass]
    field_simp [hc, hr]

lemma rootRepresentation_jump_choice (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (i : Option E) (hs : CoLocated N s i) :
    (sourceJumpChoice N r s).map (Equiv.optionCongr (rootChoices N s i hs)) =
      sourceJumpChoice N r (rootRepresentation N s) := by
  apply PMF.ext
  intro b
  obtain ⟨a, rfl⟩ := (Equiv.optionCongr (rootChoices N s i hs)).surjective b
  have hmap : ((sourceJumpChoice N r s).map (Equiv.optionCongr (rootChoices N s i hs)))
      ((Equiv.optionCongr (rootChoices N s i hs)) a) = sourceJumpChoice N r s a := by
    simp [PMF.map_apply]
  rw [hmap, sourceJumpChoice_apply, sourceJumpChoice_apply,
    population_jump_mass N r s i hs a,
    ancestral_jump_mass N r (rootRepresentation N s) (rootRepresentation_ancestral N s)]
  have hc := Fintype.card_congr (rootChoices N s i hs)
  cases a <;> simp [ancestralChoiceMass, hc]

theorem rootRepresentation_actual_jump (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (i : Option E) (hs : CoLocated N s i) :
    (sourceJumpStep N r s).map (rootRepresentation N) =
      sourceJumpStep N r (rootRepresentation N s) := by
  rw [sourceJumpStep, PMF.map_comp]
  have hf : rootRepresentation N ∘ stepDestination N s =
      stepDestination N (rootRepresentation N s) ∘ (Equiv.optionCongr (rootChoices N s i hs)) := by
    funext q
    exact rootRepresentation_destination N s i hs q
  rw [hf, ← PMF.map_comp, rootRepresentation_jump_choice]
  rfl

/-- Constructed actual ancestral readout of the same carried unranked forest.
The arbitrary readout retains the full view here, including the same bank. -/
noncomputable def completionReader (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (readout : UnrankedView V E Copy → Obs)
    (s : Code N sample) : PMF Obs :=
  (completionKernel N r (rootRepresentation N s)).map
    (fun d => readout (unrankedView (selectedView (state d) keep)))

lemma completionReader_actual_root (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (readout : UnrankedView V E Copy → Obs)
    (s : Code N sample) (hs : AncestralRoot N s) :
    completionReader N r keep readout s = (completionKernel N r s).map
      (fun d => readout (unrankedView (selectedView (state d) keep))) := by
  apply actual_unranked_completion_row N r keep (rootRepresentation N s) s
    (rootRepresentation_ancestral N s) hs
  rw [rootRepresentation_selected]
  apply congrArg unrankedView
  apply SelectedView.ext
  · rfl
  · funext x
    by_cases hx : x ∈ keep
    · simp only [selectedView, selectedLocation, if_pos hx, rootState, copyLocation]
      exact congrArg some (hs x).symm
    · simp only [selectedView, selectedLocation, if_neg hx]
  · rfl

lemma completionReader_jump_harmonic (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (readout : UnrankedView V E Copy → Obs)
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i) :
    (sourceJumpStep N r s).bind (completionReader N r keep readout) =
      completionReader N r keep readout s := by
  unfold completionReader
  calc
    _ = (((sourceJumpStep N r s).map (rootRepresentation N)).bind
        (completionKernel N r)).map
          (fun d => readout (unrankedView (selectedView (state d) keep))) := by
      rw [PMF.bind_map, PMF.map_bind]
      rfl
    _ = _ := by
      rw [rootRepresentation_actual_jump N r s i hs,
        completion_jump_harmonic N r (rootRepresentation N s) (rootRepresentation_ancestral N s)]

/-- Purely algebraic use of the old held-step proof. The actual completion
reader's jump equation is discharged below, not assumed in a source record. -/
lemma step_bind_of_jump_bind (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (F : Code N sample → PMF Obs)
    (hj : (sourceJumpStep N r s).bind F = F s) :
    (sourceStep N r s).bind F = F s := by
  apply PMF.ext
  intro z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [bind_probability_real, tsum_fintype, sourceStep_expectation, Fintype.sum_option]
  simp only [choiceMass]
  by_cases hz : totalRate N r s = 0
  · letI := choice_empty_of_zero_rate N r s hz
    simp [hz, stepDestination]
  · have he := congrArg (fun p : PMF Obs => (p z).toReal) hj
    rw [sourceJumpStep, PMF.bind_map, bind_probability_real, tsum_fintype,
      Fintype.sum_option] at he
    simp_rw [sourceJumpChoice_apply,
      ENNReal.toReal_ofReal (jumpMass_nonnegative N r s _)] at he
    simp only [jumpMass, if_neg hz, zero_mul, zero_add, Function.comp_apply] at he
    have hsums : (∑ p : Choice N s, choiceRate N r s p *
        (F (stepDestination N s (some p)) z).toReal) =
        totalRate N r s * (F s z).toReal := by
      simp_rw [div_mul_eq_mul_div] at he
      rw [← Finset.sum_div] at he
      exact ((div_eq_iff hz).mp he).trans (mul_comm _ _)
    change (1-totalRate N r s/globalRateBound (Copy := Copy) r)*
        (F s z).toReal +
        (∑ p : Choice N s, (choiceRate N r s p/globalRateBound (Copy := Copy) r)*
          (F (stepDestination N s (some p)) z).toReal) = _
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hsums]
    ring

def SharedLocation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Prop := ∃ p : Location V E, ∀ x, copyLocation (state s) x = p

lemma node_choice_empty (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (v : V) (hs : ∀ x, copyLocation (state s) x = .node v) :
    IsEmpty (Choice N s) := by
  refine ⟨fun p => ?_⟩
  have ha := (Finset.mem_offDiag.mp p.2.property).1
  obtain ⟨halive, haloc⟩ := Finset.mem_filter.mp ha
  have h := hs p.2.val.1
  change (state s).location ((state s).ancestor p.2.val.1) = _ at h
  rw [s.property.forest.representative _ halive] at h
  exact originalPlace_not_node N p.1 v (haloc.symm.trans h)

lemma jump_pure_of_empty (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) [IsEmpty (Choice N s)] :
    sourceJumpStep N r s = PMF.pure s := by
  have hz : totalRate N r s = 0 := by simp [totalRate]
  have hq : sourceJumpChoice N r s = PMF.pure none := by
    apply PMF.ext
    intro q
    cases q with
    | none => simp [sourceJumpChoice_apply, jumpMass, hz]
    | some p => exact isEmptyElim p
  rw [sourceJumpStep, hq, PMF.pure_map]
  rfl

theorem completionReader_actual_step [Nonempty Copy]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (readout : UnrankedView V E Copy → Obs)
    (s : Code N sample) (hs : SharedLocation N s) :
    (sourceStep N r s).bind (completionReader N r keep readout) =
      completionReader N r keep readout s := by
  apply step_bind_of_jump_bind
  obtain ⟨p, hp⟩ := hs
  cases p with
  | node v =>
    letI := node_choice_empty N s v hp
    rw [jump_pure_of_empty, PMF.pure_bind]
  | edge e => exact completionReader_jump_harmonic N r keep readout s (some e) hp
  | rootPopulation v =>
    obtain ⟨x⟩ := ‹Nonempty Copy›
    have hx := s.property.original_descendant x
    rw [hp x] at hx
    have hv : v = N.root := hx.1
    subst v
    exact completionReader_jump_harmonic N r keep readout s none hp

lemma step_preserves_shared_location (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : SharedLocation N s)
    {d : Code N sample} (hd : d ∈ (sourceStep N r s).support) : SharedLocation N d := by
  obtain ⟨p, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  obtain ⟨place, hp⟩ := hs
  refine ⟨place, fun x => ?_⟩
  rw [← he, actual_step_copy_population]
  exact hp x

theorem completionReader_actual_iteration [Nonempty Copy]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (readout : UnrankedView V E Copy → Obs)
    (n : Nat) (s : Code N sample) (hs : SharedLocation N s) :
    (sourceIteration N r n s).bind (completionReader N r keep readout) =
      completionReader N r keep readout s := by
  induction n generalizing s with
  | zero => simp [sourceIteration]
  | succ n ih =>
    rw [sourceIteration, PMF.bind_bind]
    calc
      _ = (sourceStep N r s).bind (completionReader N r keep readout) := by
        apply bind_congr_on_support
        intro d hd
        exact ih d (step_preserves_shared_location N r s hs hd)
      _ = _ := completionReader_actual_step N r keep readout s hs

theorem completionReader_actual_time [Nonempty Copy]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (readout : UnrankedView V E Copy → Obs)
    (t : ℝ≥0) (s : Code N sample) (hs : SharedLocation N s) :
    (sourceTimeKernel N r t s).bind (completionReader N r keep readout) =
      completionReader N r keep readout s := by
  rw [sourceTimeKernel, PMF.bind_bind]
  simp_rw [completionReader_actual_iteration N r keep readout _ s hs]
  exact PMF.bind_const _ _

lemma rootRepresentation_common_boundary (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (hb : CommonBoundary N b) (s : Code N sample) :
    rootRepresentation N (fixedRegisterBoundary N b s) = rootRepresentation N s := by
  cases b with
  | exit e => exact rootRepresentation_transport N s _ _ _
  | ordinary e hd => exact rootRepresentation_transport N s _ _ _
  | root => exact rootRepresentation_transport N s _ _ _
  | independent H gamma => exact False.elim hb
  | common H => exact rootRepresentation_transport N s _ _ _

lemma common_boundary_preserves_shared_location
    (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (s : Code N sample) (hs : SharedLocation N s) :
    SharedLocation N (fixedRegisterBoundary N b s) := by
  obtain ⟨p, hp⟩ := hs
  refine ⟨fixedBoundaryLocation N b (state s).register p, fun x => ?_⟩
  rw [fixedRegisterBoundary_copyLocation, hp x]

lemma program_step_preserves_shared_location
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (op : ProgramStep N) (hc : CommonStep N op) (s : Code N sample)
    (hs : SharedLocation N s) {d : Code N sample}
    (hd : d ∈ (sourceProgramStep N r op s).support) : SharedLocation N d := by
  cases op with
  | interval t =>
    obtain ⟨p, hp⟩ := hs
    exact ⟨p, fun x => (actual_time_copy_population N r t s hd x).trans (hp x)⟩
  | boundary b =>
    rw [sourceProgramStep, common_boundary_kernel N b hc s] at hd
    have he : d = fixedRegisterBoundary N b s := by
      simpa only [PMF.mem_support_pure_iff] using hd
    rw [he]
    exact common_boundary_preserves_shared_location N b s hs

lemma completionReader_actual_program_step [Nonempty Copy]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (readout : UnrankedView V E Copy → Obs)
    (op : ProgramStep N) (hc : CommonStep N op) (s : Code N sample)
    (hs : SharedLocation N s) :
    (sourceProgramStep N r op s).bind (completionReader N r keep readout) =
      completionReader N r keep readout s := by
  cases op with
  | interval t => exact completionReader_actual_time N r keep readout t s hs
  | boundary b =>
    rw [sourceProgramStep, common_boundary_kernel N b hc s, PMF.pure_bind]
    simp only [completionReader, rootRepresentation_common_boundary N b hc s]

/-- Every finite actual COMMON suffix preserves the constructed forest
completion reader, including tied node-boundary states and intervening holds. -/
theorem completionReader_actual_common_program [Nonempty Copy]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (readout : UnrankedView V E Copy → Obs)
    (ops : List (ProgramStep N)) (hc : CommonOnly N ops)
    (s : Code N sample) (hs : SharedLocation N s) :
    (sourceProgram N r ops s).bind (completionReader N r keep readout) =
      completionReader N r keep readout s := by
  induction ops generalizing s with
  | nil => simp [sourceProgram]
  | cons op ops ih =>
    have hhead : CommonStep N op := hc op List.mem_cons_self
    have htail : CommonOnly N ops := fun q hq => hc q (List.mem_cons_of_mem op hq)
    rw [sourceProgram, PMF.bind_bind]
    calc
      _ = (sourceProgramStep N r op s).bind (completionReader N r keep readout) := by
        apply bind_congr_on_support
        intro d hd
        exact ih htail d (program_step_preserves_shared_location N r op hhead s hs hd)
      _ = _ := completionReader_actual_program_step N r keep readout op hhead s hs

/-- Exact completed original source law, not an assumed terminal distribution.
The supplied root-support premise concerns the actual suffix states only. -/
theorem actual_common_suffix_completion [Nonempty Copy]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (readout : UnrankedView V E Copy → Obs)
    (ops : List (ProgramStep N)) (hc : CommonOnly N ops)
    (s : Code N sample) (hs : SharedLocation N s)
    (hroot : ∀ d ∈ (sourceProgram N r ops s).support, AncestralRoot N d) :
    ((sourceProgram N r ops s).bind (completionKernel N r)).map
      (fun d => readout (unrankedView (selectedView (state d) keep))) =
        completionReader N r keep readout s := by
  rw [PMF.map_bind]
  calc
    _ = (sourceProgram N r ops s).bind (completionReader N r keep readout) := by
      apply bind_congr_on_support
      intro d hd
      exact (completionReader_actual_root N r keep readout d (hroot d hd)).symm
    _ = _ := completionReader_actual_common_program N r keep readout ops hc s hs

/-- Physical root support is discharged for an actual initialized calendar
suffix. Only co-location at the supplied literal cut remains; its derivation
from the bank-specific first meeting is the next existing-proof binding. -/
theorem actual_initialized_common_suffix_completion [Nonempty Copy]
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool)
    (keep : Finset Copy) (readout : UnrankedView V E Copy → Obs)
    (past future : List (ProgramStep N))
    (hp : compiledCalendarProgram N C H gamma (fun _ => true) = past ++ future)
    (s : Code N sample)
    (hs : s ∈ (sourceProgram N r past (initialCode N sample (originalRegister N coin))).support)
    (hshared : SharedLocation N s) :
    ((sourceProgram N r future s).bind (completionKernel N r)).map
      (fun d => readout (unrankedView (selectedView (state d) keep))) =
        completionReader N r keep readout s := by
  have hc : CommonOnly N (past ++ future) := by
    rw [← hp]
    exact actual_common_calendar N C H gamma
  apply actual_common_suffix_completion N r keep readout future
    ((commonOnly_append N past future).mp hc).2 s hshared
  intro d hd
  apply initialized_original_calendar_ancestral_support N C sample (originalRegister N coin)
    H gamma (fun _ => true) r
  rw [hp, sourceProgram_append]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨s, hs, hd⟩

#print axioms rootRepresentation_actual_jump
#print axioms completionReader_actual_root
#print axioms completionReader_jump_harmonic
#print axioms completionReader_actual_common_program
#print axioms actual_initialized_common_suffix_completion
end DotG4.ActualColocatedCompletion
