import G6CompletedBinPolynomial
import ActualCompleteCutPattern

/-!
One rational polynomial table for each full original date/cut cell, evaluated
at the actual shared physical bank. This closes the literal word and initial
leaf-bin adapters for the actual infinitely completed source. The observation
corollary reads only the ordinary same-record unranked forest and bin matrix.
Contributor: dot / OpenAI, 10 October 2026. Uncompiled candidate.
-/
namespace UnifiedLean.G6.CellCompletedBinPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonExponential UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G7.SymbolicProgramPolynomial
open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.GeneratedNaturalChronology
open UnifiedLean.G6.OriginalCalendarSchema UnifiedLean.G6.StableCutSchema
open UnifiedLean.G6.StableFiniteCutSchema UnifiedLean.G6.ActualCompleteCutPattern
open UnifiedLean.G6.SelectedBinHistory UnifiedLean.G6.SelectedBinPolynomial
open UnifiedLean.G6.CompletedBinPolynomial UnifiedLean.G6.FiniteCutSourceWord
open CloudG6.NaturalCalendarPastAdmission CloudG6.NaturalPastCompleteObservation
open DotG6.GeneratedCompleteBinProxy
open scoped Classical BigOperators NNReal
variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Nonempty Copy]

/-- Every literal occurrence has a finite slot; boundary slots are unused by
polynomial interval variables. The shared Step and Symbol types are unchanged. -/
noncomputable def taggedSymbolAt (w : List (Step V E × Tag)) (i : Fin w.length) :
    Symbol (Fin w.length) V E × Tag :=
  ((match (w.get i).1 with
    | .interval _ _ => .interval i
    | .exit e => .exit e
    | .enter v => .enter v),(w.get i).2)

noncomputable def taggedSymbols (w : List (Step V E × Tag)) :
    List (Symbol (Fin w.length) V E × Tag) := List.ofFn (taggedSymbolAt w)

noncomputable def taggedDuration (N : RootedBinary V E X) (C : Calendar N.graph)
    (w : List (Step V E × Tag)) (i : Fin w.length) : ℝ≥0 :=
  Real.toNNReal ((w.get i).1.older.eval C.age - (w.get i).1.younger.eval C.age)

lemma actual_tagged_symbol_at (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (w : List (Step V E × Tag)) (i : Fin w.length) :
    (instantiateGamma N H (originalGamma p) common (taggedDuration N C w)
      (taggedSymbolAt w i).1,(taggedSymbolAt w i).2) =
      (instantiateStep N C H p common (w.get i).1,(w.get i).2) := by
  cases h : (w.get i).1 <;>
    simp only [taggedSymbolAt,h,instantiateGamma,instantiateStep,taggedDuration,Step.younger,Step.older]

/-- Exact syntactic bridge, retaining every boundary, tag, and interval. -/
theorem actual_tagged_symbols (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (w : List (Step V E × Tag)) :
    instantiateTagged N H (originalGamma p) common (taggedDuration N C w) (taggedSymbols w) =
      interpret N C H p common w := by
  simp only [instantiateTagged,taggedSymbols,List.map_ofFn,Function.comp_def,actual_tagged_symbol_at]
  change (List.ofFn (fun i : Fin w.length =>
    (instantiateStep N C H p common (w.get i).1,(w.get i).2))) =
      w.map (fun z => (instantiateStep N C H p common z.1,z.2))
  exact List.ofFn_getElem_eq_map w (fun z => (instantiateStep N C H p common z.1,z.2))

/-- The full event signature fixes each initial leaf's bin, including equality
with a cut. No nonnegative-age or zero-sampling-date hypothesis is introduced. -/
lemma actual_node_rank_bin_stable {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j))
    (sig : Signature V j) {age age' : V → ℝ}
    (h : Realizes cuts sig age) (h' : Realizes cuts sig age') (v : V) :
    rankBin (values cuts ks) (age v) = rankBin (values cuts ks) (age' v) := by
  apply Fin.ext
  rw [rank_bin_val,rank_bin_val]
  congr 1
  apply List.filter_congr
  intro q hq
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hq
  have hc := available_lt cuts sig h h' (a := .fixed (cuts k)) (b := .node v)
    ⟨.inr k,rfl⟩ ⟨.inl v,rfl⟩
  exact decide_eq_decide.mpr hc

lemma actual_initial_bins_stable (N : RootedBinary V E X) (C D : Calendar N.graph)
    (sample : Copy → X) {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j))
    (sig : Signature V (j+1))
    (hc : Realizes (completedCutBank cuts ks) sig C.age)
    (hd : Realizes (completedCutBank cuts ks) sig D.age) :
    (fun x y => rankBin (values cuts ks) (leafAgeMatrix N C sample x y)) =
      (fun x y => rankBin (values cuts ks) (leafAgeMatrix N D sample x y)) := by
  funext x y
  let P : List ℝ → Prop := fun qs =>
    rankBin qs (C.age (N.leaf (sample x))) = rankBin qs (D.age (N.leaf (sample x)))
  have hP : P (values (completedCutBank cuts ks) (ks.map Fin.succ)) :=
    actual_node_rank_bin_stable (completedCutBank cuts ks) (ks.map Fin.succ) sig hc hd (N.leaf (sample x))
  exact (congrArg P (completed_cut_bank_values cuts ks)).mp hP

/-- One table is shared throughout a full realized date/cut cell. Original
IDs, bank and COMMON flags remain unchanged, and final ancestral completion
is exact. All cut grammar and initial-bin facts are derived inside the proof. -/
theorem actual_cell_completed_bin_polynomial (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j))
    (sig : Signature V (j+1)) (hc : Realizes (completedCutBank cuts ks) sig C.age) :
    ∃ (w : List (Step V E × Fin ((values cuts ks).length+1)))
      (Q : SelectedTagged (Tag := Fin ((values cuts ks).length+1)) N sample →
        MvPolynomial (WordVariable N (Fin w.length)) ℚ),
      ∀ (D : Calendar N.graph), Realizes (completedCutBank cuts ks) sig D.age →
      ∀ (p : HybridProbabilities N) (r : PositivePairRates E)
        (b : SelectedTagged (Tag := Fin ((values cuts ks).length+1)) N sample),
        wordEval N r (originalGamma p) (taggedDuration N D w) (Q b) =
          (((naturalCompletedJoint N D sample p r (rankBin (values cuts ks))
            (rank_bin_measurable (values cuts ks))
            (compiledCalendarProgram N D H (originalGamma p) common)).map (projectTagged N)) b).toReal := by
  obtain ⟨w,hw⟩ := actual_complete_word_from_augmented_cell N C cuts ks sig hc
  refine ⟨w,completedBinPolynomial N
    (naturalBinPolynomial N sample H common (taggedSymbols w)
      (fun x y => rankBin (values cuts ks) (leafAgeMatrix N C sample x y)))
    (Fin.last (values cuts ks).length),?_⟩
  intro D hd p r b
  obtain ⟨_,href,hword⟩ := hw D hd H p common
  have hsyntax := actual_tagged_symbols N D H p common w
  have href' := href
  have hword' := hword
  rw [←hsyntax] at href' hword'
  rw [actual_initial_bins_stable N C D sample cuts ks sig hc hd]
  exact actual_natural_completed_bin_polynomial N D sample H p common r (values cuts ks)
    (taggedDuration N D w) (taggedSymbols w) href' hword' b

noncomputable def observedPolynomial {J O : Type*} [Fintype Tag]
    (N : RootedBinary V E X) {sample : Copy → X}
    (Q : SelectedTagged (Tag := Tag) N sample → MvPolynomial (WordVariable N J) ℚ)
    (readout : (Finset (UnrankedTree Copy) × (Copy → Copy → Tag)) → O) (o : O) :
    MvPolynomial (WordVariable N J) ℚ :=
  ∑ b, Q b * (if readout (selectedForestBins N b) = o then 1 else 0)

/-- A source-independent finite biological reader sees the ordinary same-record
forest/bin pair. It is not permitted to inspect raw Code or private registers. -/
theorem actual_cell_observed_bin_polynomial {O : Type*} (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) {j : ℕ} (cuts : Fin j → ℚ) (ks : List (Fin j))
    (sig : Signature V (j+1)) (hc : Realizes (completedCutBank cuts ks) sig C.age)
    (readout : (Finset (UnrankedTree Copy) ×
      (Copy → Copy → Fin ((values cuts ks).length+1))) → O) :
    ∃ (w : List (Step V E × Fin ((values cuts ks).length+1)))
      (Q : O → MvPolynomial (WordVariable N (Fin w.length)) ℚ),
      ∀ (D : Calendar N.graph), Realizes (completedCutBank cuts ks) sig D.age →
      ∀ (p : HybridProbabilities N) (r : PositivePairRates E) (o : O),
        wordEval N r (originalGamma p) (taggedDuration N D w) (Q o) =
          (((naturalCompletedJoint N D sample p r (rankBin (values cuts ks))
            (rank_bin_measurable (values cuts ks))
            (compiledCalendarProgram N D H (originalGamma p) common)).map
              (fun q => readout (sourceUnrankedForest (state q.1) Finset.univ,q.2))) o).toReal := by
  obtain ⟨w,Q,hQ⟩ := actual_cell_completed_bin_polynomial N C sample H common cuts ks sig hc
  refine ⟨w,observedPolynomial N Q readout,?_⟩
  intro D hd p r o
  have hmap : ((naturalCompletedJoint N D sample p r (rankBin (values cuts ks))
      (rank_bin_measurable (values cuts ks))
      (compiledCalendarProgram N D H (originalGamma p) common)).map (projectTagged N)).map
        (fun b => readout (selectedForestBins N b)) =
      (naturalCompletedJoint N D sample p r (rankBin (values cuts ks))
      (rank_bin_measurable (values cuts ks))
      (compiledCalendarProgram N D H (originalGamma p) common)).map
        (fun q => readout (sourceUnrankedForest (state q.1) Finset.univ,q.2)) := by
    rw [PMF.map_comp]
    rfl
  rw [←hmap,map_probability_real]
  simp only [observedPolynomial,wordEval,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [←hQ D hd p r b]
  by_cases h : readout (selectedForestBins N b) = o <;> simp [h,wordEval]

#print axioms actual_tagged_symbols
#print axioms actual_initial_bins_stable
#print axioms actual_cell_completed_bin_polynomial
#print axioms actual_cell_observed_bin_polynomial
end UnifiedLean.G6.CellCompletedBinPolynomial
