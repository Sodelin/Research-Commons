import G6SelectedBinHistory
import G1KOnlyCurrentRootExitView
import G1FiniteTwoPortChain

/-!
Additive UNCOMPILED candidate, dot / OpenAI, 10 October 2026.
Protected constant-bin words retain their complete labelled forest and old
bins. The causal exit keeps the derived original population and register.
No positive-chain compression or COMMON mixture theorem is assumed here.
-/
namespace UnifiedLean.G6.ProtectedBinEndpoint
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G2.ActualPairCoalescence GProgram.G2.CalendarDecoration
open UnifiedLean.G6.BinHistory UnifiedLean.G6.SelectedBinHistory
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualCalendarCutContext
open G1ContextualForestReplacement G1UnrankedSourceView G1UnrankedSingleExitLabel
open G1KOnlyCurrentRootExitView G1FiniteTwoPortChain
open scoped Classical
variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem actual_iteration_relation_monotone (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (n : ℕ) (s d : Code N sample)
    (hd : d ∈ (sourceIteration N r n s).support) : RelationMonotone N s d := by
  induction n generalizing s with
  | zero =>
      have he : d = s := by simpa only [sourceIteration,PMF.mem_support_pure_iff] using hd
      subst d
      exact fun _ _ h => h
  | succ n ih =>
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      obtain ⟨p,_,hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      have hsz : RelationMonotone N s z := by
        rw [← hp]
        cases p with
        | none => exact fun _ _ h => h
        | some p => exact actual_destination_relation_monotone N s p
      exact fun x y h => ih z hdz x y (hsz x y h)

theorem actual_interval_relation_monotone (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : NNReal) (s d : Code N sample)
    (hd : d ∈ (sourceTimeKernel N r t s).support) : RelationMonotone N s d := by
  obtain ⟨n,_,hn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact actual_iteration_relation_monotone N r n s d hn

theorem actual_boundary_pair_iff (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) (s d : Code N sample)
    (hd : d ∈ (boundaryKernel N op s).support) (x y : Copy) :
    (state d).ancestor x = (state d).ancestor y ↔
      (state s).ancestor x = (state s).ancestor y := by
  have hm := (PMF.mem_support_map_iff
    (fun q : Code N sample => (selectedView (state q) Finset.univ).genealogy) _ _).mpr
      ⟨d,hd,rfl⟩
  rw [boundary_genealogy_law N op s Finset.univ] at hm
  have he := (PMF.mem_support_pure_iff _ _).mp hm
  rw [← selected_same_block (state d) d.property.forest Finset.univ
      (Finset.mem_univ x) (Finset.mem_univ y),
    ← selected_same_block (state s) s.property.forest Finset.univ
      (Finset.mem_univ x) (Finset.mem_univ y)]
  simp only [sameBlock,he]

theorem actual_program_step_relation_monotone (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (op : ProgramStep N)
    (s d : Code N sample) (hd : d ∈ (sourceProgramStep N r op s).support) :
    RelationMonotone N s d := by
  cases op with
  | interval t => exact actual_interval_relation_monotone N r t s d hd
  | boundary op => exact fun x y h => (actual_boundary_pair_iff N op s d hd x y).mpr h

theorem actual_program_relation_monotone (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (s d : Code N sample) (hd : d ∈ (sourceProgram N r ops s).support) :
    RelationMonotone N s d := by
  induction ops generalizing s with
  | nil =>
      have he : d = s := by simpa only [sourceProgram,PMF.mem_support_pure_iff] using hd
      subst d
      exact fun _ _ h => h
  | cons op ops ih =>
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact fun x y h => ih z hdz x y
        (actual_program_step_relation_monotone N r op s z hz x y h)

lemma actual_step_tag_update (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s d : Code N sample)
    (hd : d ∈ (sourceProgramStep N r op s).support)
    (tag : Tag) (B : Copy → Copy → Tag) :
    endpointStepTags N op tag s d B = tagUpdate N s d tag B := by
  cases op with
  | interval t => rfl
  | boundary op =>
      funext x y
      have he := actual_boundary_pair_iff N op s d hd x y
      simp only [endpointStepTags,tagUpdate]
      have hn : ¬ ((state s).ancestor x ≠ (state s).ancestor y ∧
          (state d).ancestor x = (state d).ancestor y) := fun h => h.1 (he.mp h.2)
      rw [if_neg hn]

section ActualBinLaw
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]

/-- Whole ACTUAL cut-free word. Old bins are carried, boundaries do not
merge, and every positive interval interior has the one protected tag. -/
theorem actual_constant_bin_word (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (tag : Tag) (s : Code N sample)
    (offset : ℝ) (B : Copy → Copy → Tag)
    (hword : wordBinContract N bin (ops.map (fun op => (op,tag))) offset) :
    calendarJoint N r bin hbin ops s offset B =
      (sourceProgram N r ops s).map (fun d => (d,tagUpdate N s d tag B)) := by
  induction ops generalizing s offset B with
  | nil =>
      rw [calendar_joint_nil,sourceProgram,PMF.pure_map,tag_update_self]
  | cons op ops ih =>
      have hh : stepBinContract N bin offset op tag := hword.1
      have ht : wordBinContract N bin (ops.map (fun op => (op,tag)))
          (segmentOffset N op offset) := hword.2
      rw [calendar_joint_cons,actual_segment_endpoint_tag_row N r bin hbin
        op tag s offset B hh,PMF.bind_map,sourceProgram,PMF.map_bind]
      apply bind_congr_on_support
      intro d hd
      change calendarJoint N r bin hbin ops d (segmentOffset N op offset)
        (endpointStepTags N op tag s d B) = _
      rw [ih d (segmentOffset N op offset) (endpointStepTags N op tag s d B) ht,
        actual_step_tag_update N r op s d hd tag B]
      apply map_eq_of_eq_on_support
      intro e he
      exact congrArg (fun M => (e,M))
        (same_bin_update_comp N s d e tag B
          (actual_program_step_relation_monotone N r op s d hd)
          (actual_program_relation_monotone N r ops d e he))

end ActualBinLaw

/-- Depends on labelled trees alone: no population, source ID, or latent bit. -/
noncomputable def forestSameBlock (F : Finset (UnrankedTree Copy)) (x y : Copy) : Prop :=
  y ∈ optionTreeLeaves (rootTreeAt F x)

theorem actual_forest_same_block (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (x y : Copy) :
    forestSameBlock (sourceUnrankedForest (state s) Finset.univ) x y ↔
      (state s).ancestor x = (state s).ancestor y := by
  have hw : ∃ q ∈ sourceUnrankedForest (state s) Finset.univ, x ∈ treeLeaves q :=
    (source_unranked_forest_covers (state s) s.property.forest Finset.univ x).mpr
      (Finset.mem_univ x)
  have ht : rootTreeAt (sourceUnrankedForest (state s) Finset.univ) x =
      optionUnranked ((selectedView (state s) Finset.univ).genealogy x) := by
    rw [rootTreeAt,dif_pos hw]
    exact (actual_unranked_subtree_from_forest (state s) s.property.forest
      Finset.univ x (Finset.mem_univ x) (Classical.choose hw)
      (Classical.choose_spec hw).1 (Classical.choose_spec hw).2).symm
  rw [forestSameBlock,ht,optionUnranked_leaves]
  exact selected_same_block (state s) s.property.forest Finset.univ
    (Finset.mem_univ x) (Finset.mem_univ y)

noncomputable def forestTagUpdate (F0 F : Finset (UnrankedTree Copy))
    (tag : Tag) (B : Copy → Copy → Tag) (x y : Copy) : Tag :=
  if ¬ forestSameBlock F0 x y ∧ forestSameBlock F x y then tag else B x y

theorem actual_forest_tag_update (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (tag : Tag) (B : Copy → Copy → Tag) :
    forestTagUpdate (sourceUnrankedForest (state s) Finset.univ)
      (sourceUnrankedForest (state d) Finset.univ) tag B = tagUpdate N s d tag B := by
  funext x y
  simp only [forestTagUpdate,actual_forest_same_block,tagUpdate]

/-- Observable decoder: its arguments contain no source-population IDs. -/
noncomputable def forestBinDecoder (F0 : Finset (UnrankedTree Copy))
    (tag : Tag) (B : Copy → Copy → Tag) (F : Finset (UnrankedTree Copy)) :=
  (F,forestTagUpdate F0 F tag B)

theorem actual_constant_bin_forest_law [Fintype Tag] [MeasurableSpace Tag]
    [MeasurableSingletonClass Tag] (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (tag : Tag) (s : Code N sample)
    (offset : ℝ) (B : Copy → Copy → Tag)
    (hword : wordBinContract N bin (ops.map (fun op => (op,tag))) offset) :
    (calendarJoint N r bin hbin ops s offset B).map
      (fun q => (sourceUnrankedForest (state q.1) Finset.univ,q.2)) =
      ((sourceProgram N r ops s).map
        (fun d => sourceUnrankedForest (state d) Finset.univ)).map
          (forestBinDecoder (sourceUnrankedForest (state s) Finset.univ) tag B) := by
  rw [actual_constant_bin_word N r bin hbin ops tag s offset B hword,
    PMF.map_comp,PMF.map_comp]
  congr 1
  funext d
  exact Prod.ext rfl (actual_forest_tag_update N s d tag B).symm

/-- The observation forgets population IDs; the CAUSAL continuation does not.
For an actual word, its sole original exit is derived and explicitly retained. -/
theorem actual_word_exit_reconstructed (N : RootedBinary V E X)
    {sample : Copy → X} (C : GProgram.G5.Calendar N.graph) (r : PositivePairRates E)
    (gamma : V → unitInterval) (common : V → Bool) {a b : V}
    (word : TwoPortWord N a b) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node a)
    (d : Code N sample)
    (hd : d ∈ (sourceProgram N r (wordProgram N C gamma common word) s).support) :
    currentRootExitView Finset.univ (.node b) (state s).register
      (sourceUnrankedForest (state d) Finset.univ) =
        unrankedView (selectedView (state d) Finset.univ) := by
  apply actual_current_root_exit_view (state d) d.property.forest Finset.univ
  · intro x _
    exact actual_word_exit_population N C r gamma common word s hinput hd
      ((state d).ancestor x) (d.property.forest.ancestor_live x)
  · exact actual_program_register_support N r (wordProgram N C gamma common word) s hd

#print axioms actual_constant_bin_word
#print axioms actual_constant_bin_forest_law
#print axioms actual_word_exit_reconstructed
end UnifiedLean.G6.ProtectedBinEndpoint
