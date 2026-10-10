import G6SelectedBinPolynomial
import GeneratedCompleteBinProxy

/-!
Polynomial assembly for the original naturally initialized, infinitely
completed, finite-bin observation. It uses the actual complete-clock cut
identity, derived root support, and full selected-view/tagged-state rows.
Contributor: dot / OpenAI, 10 October 2026. Uncompiled candidate.
-/
namespace UnifiedLean.G6.CompletedBinPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonExponential UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompatibility
open CloudG3.ActualObservationCutRefinement
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open GProgram.G7.SymbolicProgramPolynomial GProgram.G7.SelectedCompletionPolynomial
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open UnifiedLean.G6.SelectedBinHistory UnifiedLean.G6.SelectedBinPolynomial
open UnifiedLean.G6.NaturalAncestralCutExtension UnifiedLean.G6.FiniteCutSourceWord
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualCalendarCutContext
open CloudG3.CompleteCalendarJointLaw
open CloudG6.NaturalCalendarPastAdmission CloudG6.NaturalPastCompleteObservation
open DotG6.UpperRateProxySupport DotG6.GeneratedCompleteBinProxy
open scoped Classical BigOperators NNReal
variable {J V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Nonempty Copy] [Fintype Tag]

noncomputable def tailRational (N : RootedBinary V E X) {sample : Copy → X}
    (tag : Tag) (a b : SelectedTagged (Tag := Tag) N sample) : ℚ :=
  ∑ d : SelectedIndex N sample Finset.univ, completionRational N a.1 d *
    (if (d,selectedTagUpdate N a.1 d tag a.2) = b then 1 else 0)

lemma actual_selected_tail_rational (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) (a b : SelectedTagged (Tag := Tag) N sample)
    (ha : FullRoot N a.1) :
    (tailRational N tag a b : ℝ) = (selectedJointTail N r tag a b).toReal := by
  rw [selectedJointTail,map_probability_real]
  simp only [tailRational,Rat.cast_sum,Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [actual_selected_completion_rational N a.1 d ha r]
  by_cases h : (d,selectedTagUpdate N a.1 d tag a.2) = b <;> simp [h]

noncomputable def completedBinPolynomial (N : RootedBinary V E X) {sample : Copy → X}
    (q : SelectedTagged (Tag := Tag) N sample → MvPolynomial (WordVariable N J) ℚ)
    (tag : Tag) (b : SelectedTagged (Tag := Tag) N sample) :
    MvPolynomial (WordVariable N J) ℚ :=
  ∑ a, q a * MvPolynomial.C (tailRational N tag a b)

/-- Generic finite sum assembly; the actual source consumer below derives
both the entering polynomial and its root support from the original calendar. -/
theorem actual_joint_completed_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (law : PMF (Code N sample × (Copy → Copy → Tag)))
    (hroot : ∀ q ∈ law.support, AncestralRoot N q.1)
    (q : SelectedTagged (Tag := Tag) N sample → MvPolynomial (WordVariable N J) ℚ)
    (r : PositivePairRates E) (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0)
    (hq : ∀ a, wordEval N r gamma dur (q a) = ((law.map (projectTagged N)) a).toReal)
    (tag : Tag) (b : SelectedTagged (Tag := Tag) N sample) :
    wordEval N r gamma dur (completedBinPolynomial N q tag b) =
      (((law.bind (jointTailKernel N r tag)).map (projectTagged N)) b).toReal := by
  rw [actual_joint_completion_projects N r tag law hroot,bind_probability_real,tsum_fintype]
  simp only [completedBinPolynomial,wordEval,MvPolynomial.eval₂_sum,MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C,Rat.coe_castHom]
  apply Finset.sum_congr rfl
  intro a _
  change wordEval N r gamma dur (q a) * (tailRational N tag a b : ℝ) = _
  rw [hq a]
  by_cases ha : a ∈ (law.map (projectTagged N)).support
  · obtain ⟨s,hs,he⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
    subst a
    rw [actual_selected_tail_rational N r tag _ b (actual_root_projection N s.1 (hroot s hs))]
  · have hz : (law.map (projectTagged N)) a = 0 := by
      simpa only [PMF.mem_support_iff,not_not] using ha
    simp [hz]

section ActualCalendar
variable [MeasurableSpace Tag] [MeasurableSingletonClass Tag]

/-- Root support is inherited from the actual complete original calendar and
preserved by its exposed ancestral interval. Old bins are not conditioned out. -/
lemma actual_extended_past_root (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (t : ℝ≥0)
    (q : Code N sample × (Copy → Copy → Tag))
    (hq : q ∈ (naturalPastJoint N C sample p r bin hbin
      (compiledCalendarProgram N C H (originalGamma p) common ++ [.interval t])).support) :
    AncestralRoot N q.1 := by
  obtain ⟨register,_,hq⟩ := (PMF.mem_support_bind_iff _ _ _).mp hq
  have hcode := (PMF.mem_support_map_iff Prod.fst _ q.1).mpr ⟨q,hq,rfl⟩
  rw [actual_calendar_joint_code] at hcode
  exact original_extended_ancestral_support N C sample H p common r register t hcode

/-- Actual complete finite-bin polynomial with an original-ID symbolic cut
word. The cut word grammar, not a probability law or root-support equality,
is the remaining adapter interface. Infinite completion retains old bins. -/
theorem actual_natural_completed_bin_polynomial (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (qs : List ℝ) (dur : J → ℝ≥0)
    (word : List (Symbol J V E × Fin (qs.length+1)))
    (href : CutRefines N (extendedOriginalOps N C H p common qs)
      (physicalOps N (instantiateTagged N H (originalGamma p) common dur word)))
    (hword : wordBinContract N (rankBin qs)
      (instantiateTagged N H (originalGamma p) common dur word) (firstOriginalDate N C))
    (b : SelectedTagged (Tag := Fin (qs.length+1)) N sample) :
    wordEval N r (originalGamma p) dur
      (completedBinPolynomial N
        (naturalBinPolynomial N sample H common word
          (fun x y => rankBin qs (leafAgeMatrix N C sample x y))) (Fin.last qs.length) b) =
      (((naturalCompletedJoint N C sample p r (rankBin qs) (rank_bin_measurable qs)
        (compiledCalendarProgram N C H (originalGamma p) common)).map (projectTagged N)) b).toReal := by
  have hc := actual_natural_arbitrary_last_cut N C sample H p common r
    (rankBin qs) (rank_bin_measurable qs) (lastCut qs) (Fin.last qs.length)
    (fun x hx => rank_bin_tail qs (lastCut qs) x (le_lastCut qs) hx)
  dsimp only at hc
  rw [hc]
  exact actual_joint_completed_polynomial N
    (naturalPastJoint N C sample p r (rankBin qs) (rank_bin_measurable qs)
      (extendedOriginalOps N C H p common qs))
    (fun q hq => actual_extended_past_root N C sample H p common r
      (rankBin qs) (rank_bin_measurable qs) _ q hq)
    _ r (originalGamma p) dur
    (fun a => actual_natural_clock_bin_polynomial N C sample H p common r
      (rankBin qs) (rank_bin_measurable qs) _ dur word href hword a)
    (Fin.last qs.length) b

end ActualCalendar
#print axioms actual_selected_tail_rational
#print axioms actual_joint_completed_polynomial
#print axioms actual_extended_past_root
#print axioms actual_natural_completed_bin_polynomial
end UnifiedLean.G6.CompletedBinPolynomial
