import ClosedArmCarrier
import FinitePMFSemigroup

/-! Restrict only the selected panel's ACTUAL current edge. All original
outside choices remain in the source row. Cloud G3, 2026-10-08; UNCHECKED. -/
namespace CloudG3.ActualFixedEdgeRow
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.SourceStepGeneratorBinding UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.UnrankedGenealogyObservation
open G1OriginalEpochPanelSilence CloudG3.UnitArmGenerator CloudG3.ClosedArmCarrier
open scoped Classical BigOperators NNReal
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- ALL actual original choices preserve the selected panel's population,
including invisible/outside mergers and holding. No row-closure premise. -/
theorem actual_choice_preserves_edge_panel (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (keep : Finset Copy) (e : E)
    (hs : AtEdgePanel (state s) keep {e}) (p : Option (Choice N s)) :
    AtEdgePanel (state (stepDestination N s p)) keep {e} := by
  cases p with
  | none => exact hs
  | some p =>
      have hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
        (originalPlace_not_node N p.1) p.2.property
      have hview := merged_destination_selectedView N s keep p
      intro x hx
      have hp := congrArg (fun v : SelectedView V E Copy => v.population x) hview
      change selectedLocation (state (stepDestination N s (some p))) keep x =
        selectedLocation (merge (state s) p.2.val.1 p.2.val.2) keep x at hp
      rw [selectedLocation_merge_unchanged (state s) keep hm] at hp
      simp only [selectedLocation,if_pos hx] at hp
      obtain ⟨f,hf,hpop⟩ := hs x hx
      exact ⟨f,hf,(Option.some.inj hp).trans hpop⟩

abbrev EdgeCode (N : RootedBinary V E X) (sample : Copy → X) (keep : Finset Copy) (e : E) :=
  {s : Code N sample // AtEdgePanel (state s) keep {e}}

noncomputable instance edgeCodeFintype (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) (e : E) : Fintype (EdgeCode N sample keep e) := by
  unfold EdgeCode
  infer_instance

noncomputable def edgeDestination (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (e : E) (s : EdgeCode N sample keep e)
    (p : Option (Choice N s.val)) : EdgeCode N sample keep e :=
  ⟨stepDestination N s.val p,actual_choice_preserves_edge_panel N s.val keep e s.property p⟩

/-- A genuine normalized source row: full ORIGINAL choice law and actual
admitted destinations. Only their proved edge-panel property is carried. -/
noncomputable def edgeStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (e : E)
    (s : EdgeCode N sample keep e) : PMF (EdgeCode N sample keep e) :=
  (choicePMF N r s.val).map (edgeDestination N (sample := sample) keep e s)

theorem actual_edge_step_forget (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (e : E) (s : EdgeCode N sample keep e) :
    (edgeStep N (sample := sample) r keep e s).map Subtype.val = sourceStep N r s.val := by
  rw [edgeStep,PMF.map_comp]
  rfl

noncomputable def edgeForestProjection (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (e : E) (s : EdgeCode N sample keep e) : ArmForestIndex N sample keep :=
  armForestProjection N keep ⟨s.val,⟨e,s.property⟩⟩

/-- Actual typed step mass in the common admitted image, calculated from the
original normalized source expectation and the derived unit generator. -/
theorem actual_edge_arm_step_real (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (e : E)
    (s : EdgeCode N sample keep e) (v : ArmForestIndex N sample keep) :
    (((edgeStep N (sample := sample) r keep e s).map (edgeForestProjection N (sample := sample) keep e)) v).toReal =
      (if forestRegister (selectedView (state s.val) keep) = v.val then 1 else 0) +
        r.edge e * unitForestGenerator (selectedView (state s.val) keep) keep
          (fun q => if q = v.val then 1 else 0) / globalRateBound (Copy := Copy) r := by
  let rho : Code N sample → ((Copy → Option (UnrankedTree Copy)) × (V → Bool)) :=
    fun d => forestRegister (selectedView (state d) keep)
  have hraw : ((edgeStep N (sample := sample) r keep e s).map (fun d => rho d.val)) =
      (sourceStep N r s.val).map rho := by
    have h := congrArg (fun law : PMF (Code N sample) => law.map rho)
      (actual_edge_step_forget N (sample := sample) r keep e s)
    simpa only [PMF.map_comp,Function.comp_def] using h
  have hm : (((edgeStep N (sample := sample) r keep e s).map (edgeForestProjection N (sample := sample) keep e)) v).toReal =
      (((edgeStep N (sample := sample) r keep e s).map (fun d => rho d.val)) v.val).toReal := by
    rw [map_probability_real,map_probability_real]
    apply Finset.sum_congr rfl
    intro d _
    have heq : edgeForestProjection N (sample := sample) keep e d = v ↔ rho d.val = v.val := Subtype.ext_iff
    simp only [heq]
  rw [hm,hraw,map_probability_real]
  let F : ((Copy → Option (UnrankedTree Copy)) × (V → Bool)) → ℝ :=
    fun q => if q = v.val then 1 else 0
  change (∑ d : Code N sample, (sourceStep N r s.val d).toReal *
    (F ∘ forestRegister) (selectedView (state d) keep)) =
      F (forestRegister (selectedView (state s.val) keep)) +
        r.edge e * unitForestGenerator (selectedView (state s.val) keep) keep F /
          globalRateBound (Copy := Copy) r
  rw [sourceStep_expectation_eq_generator,
    actual_original_single_arm_generator N r s.val keep e s.property F]

noncomputable def edgeTime (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (e : E) (t : ℝ≥0)
    (s : EdgeCode N sample keep e) : PMF (EdgeCode N sample keep e) :=
  CloudG3.FinitePMFSemigroup.timeKernel (edgeStep N (sample := sample) r keep e)
    (globalClockRate (Copy := Copy) r) t s

lemma actual_edge_iteration_forget (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (e : E) (k : Nat)
    (s : EdgeCode N sample keep e) :
    (CloudG3.FinitePMFSemigroup.iteration (edgeStep N (sample := sample) r keep e) k s).map Subtype.val =
      sourceIteration N r k s.val := by
  induction k generalizing s with
  | zero => simp [CloudG3.FinitePMFSemigroup.iteration,sourceIteration,PMF.pure_map]
  | succ k ih =>
      rw [CloudG3.FinitePMFSemigroup.iteration,PMF.map_bind]
      simp_rw [ih]
      change (edgeStep N (sample := sample) r keep e s).bind (sourceIteration N r k ∘ Subtype.val) = _
      rw [← PMF.bind_map,actual_edge_step_forget]
      rfl

/-- The typed normalized time row is exactly the SAME original full kernel;
no desired interval law, posterior independence or outside-source erasure. -/
theorem actual_edge_time_forget (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (e : E) (t : ℝ≥0)
    (s : EdgeCode N sample keep e) :
    (edgeTime N (sample := sample) r keep e t s).map Subtype.val = sourceTimeKernel N r t s.val := by
  rw [edgeTime,CloudG3.FinitePMFSemigroup.timeKernel,sourceTimeKernel,PMF.map_bind]
  simp_rw [actual_edge_iteration_forget]

end CloudG3.ActualFixedEdgeRow
