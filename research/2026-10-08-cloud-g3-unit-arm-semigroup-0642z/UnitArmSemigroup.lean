import ActualFixedEdgeRow

/-! Concrete normalized unit forest/register operator and original edge
exposure instance. Cloud G3, 2026-10-08; compiler UNCHECKED. No exp law,
generator identity, source closure or target-preserving field is supplied. -/
namespace CloudG3.UnitArmSemigroup
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.MatrixProjectionExponential UnifiedLean.Source.UnrankedGenealogyObservation
open G1OriginalEpochPanelSilence CloudG3.UnitArmGenerator CloudG3.ClosedArmCarrier
open CloudG3.ActualFixedEdgeRow Matrix NormedSpace
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- Fixed POSITIVE original unit bank used only to construct the common unit
operator. Original physical r remains unchanged in its actual exposure theorem. -/
noncomputable def unitRates : PositivePairRates E :=
  ⟨fun _ => 1,by intro e; norm_num,1,by norm_num⟩

noncomputable def unitRepresentative (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : ArmForestIndex N sample keep) : SingleEdgeCode N sample keep :=
  Classical.choose v.property

lemma unit_representative_forest (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : ArmForestIndex N sample keep) :
    forestRegister (selectedView (state (unitRepresentative N (sample := sample) keep v).val) keep) = v.val :=
  Classical.choose_spec v.property

noncomputable def representativeEdge (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : ArmForestIndex N sample keep) : E :=
  Classical.choose (unitRepresentative N (sample := sample) keep v).property

noncomputable def representativeAtEdge (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : ArmForestIndex N sample keep) :
    EdgeCode N sample keep (representativeEdge N (sample := sample) keep v) :=
  ⟨(unitRepresentative N (sample := sample) keep v).val,Classical.choose_spec (unitRepresentative N (sample := sample) keep v).property⟩

/-- ACTUAL normalized original unit-bank row, projected to the closed admitted
image. Arbitrary original outside roots/choices remain in its representative.
Independence of that representative is proved below, not assumed. -/
noncomputable def unitStep (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : ArmForestIndex N sample keep) : PMF (ArmForestIndex N sample keep) :=
  (edgeStep N (sample := sample) unitRates keep (representativeEdge N (sample := sample) keep v) (representativeAtEdge N (sample := sample) keep v)).map
    (edgeForestProjection N (sample := sample) keep (representativeEdge N (sample := sample) keep v))

lemma unit_step_real (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (x y : ArmForestIndex N sample keep) :
    (unitStep N (sample := sample) keep x y).toReal = (if x = y then 1 else 0) +
      unitForestGenerator (selectedView (state (unitRepresentative N (sample := sample) keep x).val) keep) keep
        (fun q => if q = y.val then 1 else 0) / globalRateBound (Copy := Copy) (unitRates : PositivePairRates E) := by
  have h := actual_edge_arm_step_real N (sample := sample) unitRates keep (representativeEdge N (sample := sample) keep x)
    (representativeAtEdge N (sample := sample) keep x) y
  simpa only [unitStep,representativeAtEdge,unitRates,unit_representative_forest,one_mul,
    ← Subtype.ext_iff] using h

/-- SAME common unit row for EVERY admitted singleton-edge witness, without
relocating its hidden outside owners or assuming a kernel independence field. -/
theorem actual_unit_step_from_any_edge (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (e : E) (s : EdgeCode N sample keep e) :
    (edgeStep N (sample := sample) unitRates keep e s).map (edgeForestProjection N (sample := sample) keep e) =
      unitStep N (sample := sample) keep (edgeForestProjection N (sample := sample) keep e s) := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [actual_edge_arm_step_real,unit_step_real]
  have hforest : forestRegister (selectedView (state s.val) keep) =
      forestRegister (selectedView (state
        (unitRepresentative N (sample := sample) keep (edgeForestProjection N (sample := sample) keep e s)).val) keep) :=
    (unit_representative_forest N (sample := sample) keep (edgeForestProjection N (sample := sample) keep e s)).symm
  rw [unit_generator_factors_through_forest_register _ _ keep hforest
    (fun q => if q = y.val then 1 else 0)]
  have hdelta : (forestRegister (selectedView (state s.val) keep) = y.val) ↔
      edgeForestProjection N (sample := sample) keep e s = y := Subtype.ext_iff.symm
  simp only [unitRates,one_mul,hdelta]

noncomputable def unitTransition (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) : Matrix (ArmForestIndex N sample keep) (ArmForestIndex N sample keep) ℝ :=
  CloudG3.FinitePMFSemigroup.transition (unitStep N (sample := sample) keep)

noncomputable def unitGenerator (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) : Matrix (ArmForestIndex N sample keep) (ArmForestIndex N sample keep) ℝ :=
  CloudG3.FinitePMFSemigroup.generator (unitStep N (sample := sample) keep)
    (globalClockRate (Copy := Copy) (unitRates : PositivePairRates E))

/-- Concrete finite unit-generator entry is the derived original visible
block/graft generator, not a supplied matrix field. -/
theorem unit_generator_entry (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (x y : ArmForestIndex N sample keep) :
    unitGenerator N (sample := sample) keep x y =
      unitForestGenerator (selectedView (state (unitRepresentative N (sample := sample) keep x).val) keep) keep
        (fun q => if q = y.val then 1 else 0) := by
  unfold unitGenerator CloudG3.FinitePMFSemigroup.generator
  rw [Matrix.smul_apply,Matrix.sub_apply,CloudG3.FinitePMFSemigroup.transition,
    unit_step_real,Matrix.one_apply]
  let B := globalRateBound (Copy := Copy) (unitRates : PositivePairRates E)
  let K := unitForestGenerator (selectedView (state (unitRepresentative N (sample := sample) keep x).val) keep) keep
    (fun q => if q = y.val then 1 else 0)
  change B * ((if x = y then 1 else 0) + K/B - (if x = y then 1 else 0)) = K
  have hB : B ≠ 0 := (globalRateBound_positive (Copy := Copy) (unitRates : PositivePairRates E)).ne'
  field_simp [hB]
  ring

/-- Genuine normalized finite stochastic time row. Normalization comes from
actual original unitStep and Poisson PMFs, before any exponential identity. -/
noncomputable def unitTimeKernel (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (t : ℝ≥0) (x : ArmForestIndex N sample keep) :
    PMF (ArmForestIndex N sample keep) :=
  CloudG3.FinitePMFSemigroup.timeKernel (unitStep N (sample := sample) keep)
    (globalClockRate (Copy := Copy) (unitRates : PositivePairRates E)) t x

theorem unit_time_probability (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (t : ℝ≥0) (x y : ArmForestIndex N sample keep) :
    (unitTimeKernel N (sample := sample) keep t x y).toReal = (exp ((t : ℝ) • unitGenerator N (sample := sample) keep)) x y :=
  CloudG3.FinitePMFSemigroup.time_probability _ _ _ _ _

theorem unit_time_bind (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (a b : ℝ≥0) (x : ArmForestIndex N sample keep) :
    (unitTimeKernel N (sample := sample) keep a x).bind (unitTimeKernel N (sample := sample) keep b) = unitTimeKernel N (sample := sample) keep (a+b) x :=
  CloudG3.FinitePMFSemigroup.time_bind _ _ _ _ _

theorem unit_time_zero (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (x : ArmForestIndex N sample keep) :
    unitTimeKernel N (sample := sample) keep 0 x = PMF.pure x := CloudG3.FinitePMFSemigroup.time_zero _ _ _

noncomputable def edgeGenerator (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (e : E) :
    Matrix (EdgeCode N sample keep e) (EdgeCode N sample keep e) ℝ :=
  CloudG3.FinitePMFSemigroup.generator (edgeStep N (sample := sample) r keep e) (globalClockRate (Copy := Copy) r)

noncomputable def edgeProjectionMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (e : E) : Matrix (EdgeCode N sample keep e) (ArmForestIndex N sample keep) ℝ :=
  fun s v => if edgeForestProjection N (sample := sample) keep e s = v then 1 else 0

/-- The actual original rate bank and outside choices yield the concrete
rectangular generator identity at this ACTUAL selected edge. No Eq7, exp law,
source independence or generator-intertwining field is assumed. -/
theorem actual_edge_generator_intertwining (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (e : E) :
    edgeGenerator N (sample := sample) r keep e * edgeProjectionMatrix N (sample := sample) keep e =
      edgeProjectionMatrix N (sample := sample) keep e * (r.edge e • unitGenerator N (sample := sample) keep) := by
  ext s y
  have hleft : (CloudG3.FinitePMFSemigroup.transition (edgeStep N (sample := sample) r keep e) *
      edgeProjectionMatrix N (sample := sample) keep e) s y =
      (((edgeStep N (sample := sample) r keep e s).map (edgeForestProjection N (sample := sample) keep e)) y).toReal := by
    rw [Matrix.mul_apply]
    exact (map_probability_real (edgeStep N (sample := sample) r keep e s) (edgeForestProjection N (sample := sample) keep e) y).symm
  have hright : (edgeProjectionMatrix N (sample := sample) keep e * unitGenerator N (sample := sample) keep) s y =
      unitGenerator N (sample := sample) keep (edgeForestProjection N (sample := sample) keep e s) y := by
    simp [Matrix.mul_apply,edgeProjectionMatrix]
  unfold edgeGenerator CloudG3.FinitePMFSemigroup.generator
  rw [Matrix.smul_mul,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_smul]
  simp only [Matrix.smul_apply,Matrix.sub_apply]
  rw [hleft,hright,unit_generator_entry,actual_edge_arm_step_real]
  have hforest : forestRegister (selectedView (state s.val) keep) =
      forestRegister (selectedView (state
        (unitRepresentative N (sample := sample) keep (edgeForestProjection N (sample := sample) keep e s)).val) keep) :=
    (unit_representative_forest N (sample := sample) keep (edgeForestProjection N (sample := sample) keep e s)).symm
  have hK := unit_generator_factors_through_forest_register _ _ keep hforest
    (fun q => if q = y.val then 1 else 0)
  rw [← hK]
  have hdelta : (if forestRegister (selectedView (state s.val) keep) = y.val then (1 : ℝ) else 0) =
      edgeProjectionMatrix N (sample := sample) keep e s y := by
    simp only [edgeProjectionMatrix,Subtype.ext_iff]
    rfl
  rw [hdelta]
  let B := globalRateBound (Copy := Copy) r
  let K := unitForestGenerator (selectedView (state s.val) keep) keep
    (fun q => if q = y.val then 1 else 0)
  change B * (edgeProjectionMatrix N (sample := sample) keep e s y + r.edge e * K/B -
    edgeProjectionMatrix N (sample := sample) keep e s y) = r.edge e * K
  have hB : B ≠ 0 := (globalRateBound_positive (Copy := Copy) r).ne'
  field_simp [hB]
  ring

noncomputable def rateExposure (r : PositivePairRates E) (e : E) (t : ℝ≥0) : ℝ≥0 :=
  ⟨r.edge e * (t : ℝ),mul_nonneg (r.edge_pos e).le t.coe_nonneg⟩

/-- Exact actual normalized interval row on the common admitted forest image.
Positive physical original r is unchanged. λ is its edge rate × duration. -/
theorem actual_edge_time_arm_projection (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (e : E) (t : ℝ≥0)
    (s : EdgeCode N sample keep e) :
    (edgeTime N (sample := sample) r keep e t s).map (edgeForestProjection N (sample := sample) keep e) =
      unitTimeKernel N (sample := sample) keep (rateExposure r e t) (edgeForestProjection N (sample := sample) keep e s) := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [map_probability_real]
  simp_rw [edgeTime,CloudG3.FinitePMFSemigroup.time_probability]
  have hx := rectangular_scaled_exp_intertwining
    (edgeGenerator N (sample := sample) r keep e) (r.edge e • unitGenerator N (sample := sample) keep)
    (edgeProjectionMatrix N (sample := sample) keep e) (actual_edge_generator_intertwining N (sample := sample) r keep e) (t : ℝ)
  calc
    _ = (exp ((t : ℝ) • edgeGenerator N (sample := sample) r keep e) * edgeProjectionMatrix N (sample := sample) keep e) s y := rfl
    _ = (edgeProjectionMatrix N (sample := sample) keep e * exp ((t : ℝ) • (r.edge e • unitGenerator N (sample := sample) keep))) s y :=
      congrArg (fun M => M s y) hx
    _ = (exp ((rateExposure r e t : ℝ) • unitGenerator N (sample := sample) keep)) (edgeForestProjection N (sample := sample) keep e s) y := by
      have hscalar : (t : ℝ) • (r.edge e • unitGenerator N (sample := sample) keep) =
          (rateExposure r e t : ℝ) • unitGenerator N (sample := sample) keep := by
        simp only [smul_smul,rateExposure]
        congr 1
        exact mul_comm _ _
      rw [hscalar]
      simp [Matrix.mul_apply,edgeProjectionMatrix]
    _ = _ := (unit_time_probability N (sample := sample) keep (rateExposure r e t) _ _).symm

/-- Actual ORIGINAL interval readout, with every old rooted tree and the SAME
Γ. It is derived from the typed restriction's exact forget law and the proved
matrix/normalized row identity, not from a desired source/kernel premise. -/
theorem actual_original_edge_exposure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (e : E) (t : ℝ≥0)
    (s : Code N sample) (hs : AtEdgePanel (state s) keep {e}) :
    (sourceTimeKernel N r t s).map (fun d => forestRegister (selectedView (state d) keep)) =
      (unitTimeKernel N (sample := sample) keep (rateExposure r e t)
        (edgeForestProjection N (sample := sample) keep e ⟨s,hs⟩)).map Subtype.val := by
  let z : EdgeCode N sample keep e := ⟨s,hs⟩
  have h := congrArg (fun law : PMF (ArmForestIndex N sample keep) => law.map Subtype.val)
    (actual_edge_time_arm_projection N (sample := sample) r keep e t z)
  have hf := congrArg (fun law : PMF (Code N sample) => law.map
    (fun d => forestRegister (selectedView (state d) keep)))
    (actual_edge_time_forget N (sample := sample) r keep e t z)
  simp only [PMF.map_comp,Function.comp_def] at h hf
  exact hf.symm.trans h

end CloudG3.UnitArmSemigroup
