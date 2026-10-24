import ResearchCommons.MSCI.JC69Measurable
import G2RootedTimedOutputSupport
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! The actual original calendar/ancestral source followed by the SAME-tree
JC readout. A finite locus samples its whole source trace ONCE, then takes
the conditional site product inside that integral. The original registered
mixture is also taken ONCE. No arbitrary desired mixing law is a premise.

This constructs a source-trace channel. Descent to the unranked timed
observation, canonical MSci source/event coverage and reconstruction remain
separate. Nonempty original Copy is explicit; empty panels need no root.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69Source
open MeasureTheory ProbabilityTheory
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.FiniteSourceSnapshot
open GProgram.G2.LiteralMarkedClockTrace
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.CompleteDecoration
open GProgram.G2.CompleteTimedSupport GProgram.G2.RootedTimedOutputSupport
open GProgram.G2.FaithfulPairAgeDecoration GProgram.G2.ChronologicalDecoration
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Tree
open ResearchCommons.MSCI.JC69Observation ResearchCommons.MSCI.JC69Measurable
open scoped Classical BigOperators NNReal ENNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Nonempty Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- This is an existing live original representative, derived from validity.
On the actual completed one-root support every original copy has this root. -/
def selectedRoot (N : RootedBinary V E X) {sample : Copy → X}
    (d : Code N sample) : Copy :=
  (state d).ancestor (Classical.choice (inferInstance : Nonempty Copy))

theorem selected_root_live (N : RootedBinary V E X) {sample : Copy → X}
    (d : Code N sample) : selectedRoot N d ∈ (state d).live :=
  d.property.forest.ancestor_live _

def GoodPoint (N : RootedBinary V E X) {sample : Copy → X}
    (leafAge : Copy → ℝ) (z : Code N sample × (Copy → Copy → ℝ)) : Prop :=
  (state z.1).live.card ≤ 1 ∧ HasTimedBound leafAge z.2 (state z.1)

/-- A total probability kernel, with a fixed harmless value off the original
full-mass admitted set. The fallback is never a conditioning or renormalization
of the source. The same original matrix supplies every branch survival. -/
def conditionalKernel (N : RootedBinary V E X) {sample : Copy → X}
    (leafAge : Copy → ℝ) (z : Code N sample × (Copy → Copy → ℝ)) :
    PMF (Copy → Base) :=
  if h : GoodPoint N leafAge z then
    actualLabelledTreeKernel (state z.1) z.1.property.forest leafAge z.2
      (h.2.choose : ℝ) h.2.choose_spec (selectedRoot N z.1) (selected_root_live N z.1)
  else PMF.pure (fun _ => 0)

theorem conditional_kernel_probability (N : RootedBinary V E X)
    {sample : Copy → X} (leafAge : Copy → ℝ)
    (z : Code N sample × (Copy → Copy → ℝ)) (h : GoodPoint N leafAge z)
    (p : Copy → Base) :
    conditionalKernel N leafAge z p =
      ENNReal.ofReal (rootLikelihood ((state z.1).genealogy (selectedRoot N z.1))
        (clockSurvivals leafAge _ (decode z.2 _))
        (labelPattern ((state z.1).genealogy (selectedRoot N z.1)) p)) := by
  rw [conditionalKernel, dif_pos h]
  rw [← actual_original_label_probability (state z.1) z.1.property.forest h.1
    leafAge z.2 (h.2.choose : ℝ) h.2.choose_spec
    (selectedRoot N z.1) (selected_root_live N z.1) p]
  exact (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm

theorem conditional_mass_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (leafAge : Copy → ℝ) (p : Copy → Base) :
    Measurable (fun z : Code N sample × (Copy → Copy → ℝ) =>
      conditionalKernel N leafAge z p) := by
  classical
  apply measurable_from_prod_countable_right
  intro d
  have hg : Measurable (fun M : Copy → Copy → ℝ => GoodPoint N leafAge (d,M)) :=
    measurable_const.and ((has_timed_bound_joint_measurable N leafAge).comp
      (measurable_const.prodMk measurable_id))
  have hp := (decoded_probability_measurable leafAge
    ((state d).genealogy (selectedRoot N d))
    (labelPattern ((state d).genealogy (selectedRoot N d)) p)).ennreal_ofReal
  have hi := Measurable.ite hg.setOf hp
    (measurable_const : Measurable (fun _ : Copy → Copy → ℝ =>
      (PMF.pure (fun _ : Copy => (0 : Base)) p)))
  convert hi using 1
  funext M
  by_cases h : GoodPoint N leafAge (d,M)
  · rw [if_pos h]
    exact conditional_kernel_probability N leafAge (d,M) h p
  · simp only [conditionalKernel, dif_neg h, if_neg h]

/-- Sites share the SAME source point. Multiplication happens before the
source integral, including L=0. This is not a product of source mixtures. -/
def conditionalLocusKernel (L : ℕ) (N : RootedBinary V E X)
    {sample : Copy → X} (leafAge : Copy → ℝ)
    (z : Code N sample × (Copy → Copy → ℝ)) : PMF (Fin L → Copy → Base) :=
  PMF.ofFintype (fun p => ∏ j, conditionalKernel N leafAge z (p j)) (by
    rw [← Fintype.prod_sum]
    have hs : (∑ p : Copy → Base, conditionalKernel N leafAge z p) = 1 := by
      simpa only [tsum_fintype] using PMF.tsum_coe (conditionalKernel N leafAge z)
    simp only [hs, Finset.prod_const_one])

theorem conditional_locus_mass_measurable (L : ℕ) (N : RootedBinary V E X)
    {sample : Copy → X} (leafAge : Copy → ℝ) (p : Fin L → Copy → Base) :
    Measurable (fun z : Code N sample × (Copy → Copy → ℝ) =>
      conditionalLocusKernel L N leafAge z p) := by
  change Measurable (fun z => ∏ j, conditionalKernel N leafAge z (p j))
  exact Finset.measurable_prod Finset.univ (fun j _ =>
    conditional_mass_measurable N leafAge (p j))

/-- Exact ORIGINAL trace attachment and its SAME accumulated pair-age matrix.
The graph, agenda, entering register and actual ancestral clocks are retained. -/
def originalPoint (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (z : CompleteCalendarRecord N sample (compiledCalendarProgram N C H gamma common)) :
    Code N sample × (Copy → Copy → ℝ) :=
  (completeEnd N (compiledCalendarProgram N C H gamma common) z,
    completeMatrix N (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register) (firstOriginalDate N C)
      (fun x _ => C.age (N.leaf (sample x))) z)

omit [Nonempty Copy] in
theorem original_point_measurable (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) :
    Measurable (originalPoint N C sample register H gamma common) :=
  (complete_end_measurable N _).prodMk (complete_matrix_measurable N _ _ _ _)

theorem actual_original_point_support (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register),
      GoodPoint N (fun x => C.age (N.leaf (sample x)))
        (originalPoint N C sample register H gamma common z) := by
  filter_upwards [actual_original_complete_root_card N C sample register H gamma common r,
    actual_original_complete_timed_support N C sample register H gamma common r]
    with z hr ht
  exact ⟨hr,ht⟩

/-- Constructed probability law of a full finite locus on the ACTUAL complete
original calendar measure. No assumed output/source mixing equation enters. -/
def actualLocusLaw (L : ℕ) (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) : PMF (Fin L → Copy → Base) := by
  let ops := compiledCalendarProgram N C H gamma common
  let μ := completeCalendarTraceLaw N r ops (initialCode N sample register)
  letI : IsProbabilityMeasure μ := complete_calendar_trace_probability N r ops _
  let w := fun (p : Fin L → Copy → Base)
      (z : CompleteCalendarRecord N sample ops) =>
    conditionalLocusKernel L N (fun x => C.age (N.leaf (sample x)))
      (originalPoint N C sample register H gamma common z) p
  have hw (p : Fin L → Copy → Base) : Measurable (w p) :=
    (conditional_locus_mass_measurable L N _ p).comp
      (original_point_measurable N C sample register H gamma common)
  refine PMF.ofFintype (fun p => ∫⁻ z, w p z ∂μ) ?_
  calc
    (∑ p, ∫⁻ z, w p z ∂μ) = ∫⁻ z, ∑ p, w p z ∂μ :=
      (lintegral_finsetSum Finset.univ (fun p _ => hw p)).symm
    _ = ∫⁻ _ : CompleteCalendarRecord N sample ops, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_congr
      intro z
      simpa only [tsum_fintype] using PMF.tsum_coe
        (conditionalLocusKernel L N (fun x => C.age (N.leaf (sample x)))
          (originalPoint N C sample register H gamma common z))
    _ = 1 := by simp

theorem actual_source_locus_normalized (L : ℕ) (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) :
    (∑ p, actualLocusLaw L N C sample register H gamma common r p) = 1 := by
  simpa only [tsum_fintype] using
    PMF.tsum_coe (actualLocusLaw L N C sample register H gamma common r)

/-- On the actual source the fallback disappears almost surely. This is the
literal SAME-tree real-clock likelihood integral, with all site products
inside it and every original source parameter unchanged. -/
theorem actual_source_locus_integral (L : ℕ) (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (p : Fin L → Copy → Base) :
    actualLocusLaw L N C sample register H gamma common r p =
      ∫⁻ z, ∏ j, ENNReal.ofReal
        (rootLikelihood
          ((state (originalPoint N C sample register H gamma common z).1).genealogy
            (selectedRoot N (originalPoint N C sample register H gamma common z).1))
          (clockSurvivals (fun x => C.age (N.leaf (sample x))) _
            (decode (originalPoint N C sample register H gamma common z).2 _))
          (labelPattern
            ((state (originalPoint N C sample register H gamma common z).1).genealogy
              (selectedRoot N (originalPoint N C sample register H gamma common z).1)) (p j)))
      ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
        (initialCode N sample register) := by
  change (∫⁻ z, conditionalLocusKernel L N (fun x => C.age (N.leaf (sample x)))
    (originalPoint N C sample register H gamma common z) p
    ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register)) = _
  apply lintegral_congr_ae
  filter_upwards [actual_original_point_support N C sample register H gamma common r]
    with z hz
  change (∏ j, conditionalKernel N (fun x => C.age (N.leaf (sample x)))
    (originalPoint N C sample register H gamma common z) (p j)) = _
  apply Finset.prod_congr rfl
  intro j _
  exact conditional_kernel_probability N _ _ hz (p j)

/-- The entire original entering bank is mixed ONCE, outside the already
source-integrated locus. COMMON bits are not refreshed between cells/sites. -/
def registeredLocusLaw (L : ℕ) (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (ρ : PMF (V → Bool)) : PMF (Fin L → Copy → Base) :=
  ρ.bind (fun register => actualLocusLaw L N C sample register H gamma common r)

theorem registered_locus_probability (L : ℕ) (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (ρ : PMF (V → Bool)) (p : Fin L → Copy → Base) :
    registeredLocusLaw L N C sample H gamma common r ρ p =
      ∑ register : V → Bool, ρ register *
        actualLocusLaw L N C sample register H gamma common r p := by
  change (∑' register : V → Bool, ρ register *
    actualLocusLaw L N C sample register H gamma common r p) = _
  rw [tsum_fintype]

end ResearchCommons.MSCI.JC69Source
