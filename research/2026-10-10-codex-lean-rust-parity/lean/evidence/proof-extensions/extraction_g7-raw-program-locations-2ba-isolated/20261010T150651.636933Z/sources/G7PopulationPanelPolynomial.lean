import G7WholeAncestorPanelCode

/-! Rational polynomial coordinates of the actual selected population marginal
of an arbitrary admitted full source state. -/
namespace GProgram.G7.PopulationPanelPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceEpochRenewal
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.SourceCrossCarrierEpoch
open GProgram.G7.SinglePopulationPolynomialKernel GProgram.G7.WholeAncestorPanelCode
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def imagePolynomial (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) {O : Type*} (f : Code N sample → O) (o : O) : Polynomial ℚ :=
  ∑ d : Code N sample, if f d = o then populationPolynomial N s d else 0

theorem actual_image_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    {O : Type*} (f : Code N sample → O) (o : O)
    (r : PositivePairRates E) (t : ℝ≥0) :
    Polynomial.eval₂ (Rat.castHom ℝ) (Real.exp (-pairRate r i * (t:ℝ)))
      (imagePolynomial N s f o) = ((sourceTimeKernel N r t s).map f o).toReal := by
  rw [map_probability_real]
  simp only [imagePolynomial, Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : f d = o
  · simp only [if_pos h, mul_one]
    exact actual_population_polynomial N s d i hs r t
  · simp [h]

noncomputable def panelPolynomial (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E)
    (o : JoinedIndex N sample (locationPanel (state s) (originalPlace N i))) : Polynomial ℚ :=
  imagePolynomial N
    (panelCode N s _ (locationPanel_closed (state s) s.property.forest (originalPlace N i)))
    (fun d => joinedProjection N _ (.inr d)) o

theorem actual_population_panel_polynomial (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (i : Option E)
    (o : JoinedIndex N sample (locationPanel (state s) (originalPlace N i)))
    (r : PositivePairRates E) (t : ℝ≥0) :
    Polynomial.eval₂ (Rat.castHom ℝ) (Real.exp (-pairRate r i * (t:ℝ)))
      (panelPolynomial N s i o) =
      ((sourceTimeKernel N r t s).map
        (fun d => joinedProjection N (locationPanel (state s) (originalPlace N i)) (.inl d)) o).toReal := by
  rw [actual_panel_epoch N r s _
    (locationPanel_closed (state s) s.property.forest (originalPlace N i)) t]
  exact actual_image_polynomial N _ i (panelCode_colocated N s i) _ o r t

lemma panelCode_location (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Location V E)
    (x : SelectedCopy (locationPanel (state s) p)) :
    copyLocation (state (panelCode N s _
      (locationPanel_closed (state s) s.property.forest p))) x = p := by
  change copyLocation (decodeSnapshot N.root (encodeSnapshot
    (restrictState (state s) s.property.forest (locationPanel (state s) p)
      (locationPanel_closed (state s) s.property.forest p))
    (restrictState_valid (state s) s.property.forest _ _))) x = _
  rw [decode_encode_copyLocation]
  exact (Finset.mem_filter.mp x.property).2

lemma node_choices_empty (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (v : V)
    (h : ∀ x, copyLocation (state s) x = .node v) : IsEmpty (Choice N s) := by
  refine ⟨fun p => ?_⟩
  have hp := Finset.mem_filter.mp (Finset.mem_offDiag.mp p.2.property).1
  have hr : (state s).ancestor p.2.val.1 = p.2.val.1 :=
    s.property.forest.representative _ hp.1
  have hx := h p.2.val.1
  change (state s).location ((state s).ancestor p.2.val.1) = _ at hx
  rw [hr] at hx
  exact originalPlace_not_node N p.1 v (hp.2.symm.trans hx)

theorem actual_node_epoch_identity (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (v : V)
    (h : ∀ x, copyLocation (state s) x = .node v)
    (r : PositivePairRates E) (t : ℝ≥0) :
    sourceTimeKernel N r t s = PMF.pure s := by
  letI := node_choices_empty N s v h
  apply PMF.ext
  intro d
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [actual_source_kernel_first_jump]
  by_cases he : s = d <;> simp [totalRate,PMF.pure_apply,he,eq_comm]

theorem actual_node_panel_identity (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (v : V) (r : PositivePairRates E) (t : ℝ≥0) :
    let keep := locationPanel (state s) (.node v)
    (sourceTimeKernel N r t s).map (fun d => joinedProjection N keep (.inl d)) =
      PMF.pure (joinedProjection N keep (.inl s)) := by
  dsimp only
  have hc := locationPanel_closed (state s) s.property.forest (.node v)
  rw [actual_panel_epoch N r s _ hc t,
    actual_node_epoch_identity N _ v (panelCode_location N s (.node v)) r t,PMF.pure_map]
  congr 1
  apply Subtype.ext
  exact (panelCode_view N s _ hc).symm

end GProgram.G7.PopulationPanelPolynomial
