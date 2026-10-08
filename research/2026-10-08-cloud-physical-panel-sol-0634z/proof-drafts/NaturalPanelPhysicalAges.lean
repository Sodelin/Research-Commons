import ActualPanelForestReadout
import NaturalCalendarPastAdmission
import CompleteCalendarBinReadout
import ActualCalendarCutContext

/-!
Cloud Sol /root/source_backend_review_sol, 8 October 2026.
Authored SOURCE/HAND; all new bodies compiler UNCHECKED/outside179.
Derives actual selected topology/pair bins from SAME initialized complete
physical record. No supplied desired law, old matrix correctness, independent
tag sampling or inverse bin/real-age decoder. Exact real ages are not observed.
-/
namespace CloudG6.NaturalPanelPhysicalAges

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.CompleteDecoration GProgram.G2.FaithfulPairAgeDecoration
open CloudG3.ActualCutJointLaw CloudG3.ActualCalendarCutContext
open CloudG3.CompleteCalendarBinReadout
open CloudG6.NaturalCalendarPastAdmission CloudG6.ActualPanelForestReadout
open scoped Classical

universe u v w x y
variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Physical fields come from the ACTUAL full initialized calendar/tail record,
not independently sampled or sorted ages/topology. Output contains only the
retained external labels, pruned unranked forest and selected pair AGE BINS. -/
noncomputable def physicalPanelFields (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (bin : ℝ → Tag)
    (ops : List (ProgramStep N)) (keep : Finset Copy)
    (z : CompleteCalendarRecord N sample ops) : RawPanelRecord keep Tag :=
  (sourceUnrankedForest (state (completeEnd N ops z)) keep,
    fun a b => bin (completeMatrix N ops (initialCode N sample register)
      (firstOriginalDate N C) (leafAgeMatrix N C sample) z a.val b.val))

/-- The literal endpoint Tag readout is exactly forward binning of its SAME
physical age matrix, and selected forest pruning is the actual source reader. -/
theorem initialized_complete_panel_readout (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (bin : ℝ → Tag)
    (ops : List (ProgramStep N)) (keep : Finset Copy)
    (z : CompleteCalendarRecord N sample ops) :
    endpointPanelReadout N keep
      (completeReadout N bin ops (initialCode N sample register) (firstOriginalDate N C)
        (fun a b => bin (leafAgeMatrix N C sample a b)) z) =
      physicalPanelFields N C sample register bin ops keep z := by
  apply Prod.ext
  · rfl
  · funext a b
    exact congrFun (congrFun
      (map_complete_matrix N bin ops (initialCode N sample register)
        (firstOriginalDate N C) (leafAgeMatrix N C sample) z).symm a.val) b.val

theorem physical_panel_fields_measurable (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (keep : Finset Copy) :
    Measurable (physicalPanelFields N C sample register bin ops keep) := by
  have hread : Measurable (endpointPanelReadout N (Tag := Tag) keep) := measurable_of_countable _
  have he : physicalPanelFields N C sample register bin ops keep =
      endpointPanelReadout N keep ∘ completeReadout N bin ops (initialCode N sample register)
        (firstOriginalDate N C) (fun a b => bin (leafAgeMatrix N C sample a b)) := by
    funext z
    exact (initialized_complete_panel_readout N C sample register bin ops keep z).symm
  rw [he]
  exact hread.comp (complete_readout_measurable N bin hbin ops (initialCode N sample register)
    (firstOriginalDate N C) (fun a b => bin (leafAgeMatrix N C sample a b)))

/-- Genuine physical measure pushforward of the ACTUAL initialized term in
the native panel law's once-drawn register mixture. No replacement law input. -/
theorem initialized_panel_physical_source_law (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N)) (keep : Finset Copy) :
    ((completedJoint N r bin hbin ops (initialCode N sample register)
      (firstOriginalDate N C) (fun a b => bin (leafAgeMatrix N C sample a b))).map
        (endpointPanelReadout N keep)).toMeasure =
      (completeCalendarTraceLaw N r ops (initialCode N sample register)).map
        (physicalPanelFields N C sample register bin ops keep) := by
  have hread : Measurable (endpointPanelReadout N (Tag := Tag) keep) := measurable_of_countable _
  rw [← PMF.toMeasure_map _ _ hread, completed_joint_toMeasure,
    Measure.map_map hread (complete_readout_measurable N bin hbin ops
      (initialCode N sample register) (firstOriginalDate N C)
      (fun a b => bin (leafAgeMatrix N C sample a b)))]
  apply congrArg (Measure.map · _)
  funext z
  exact initialized_complete_panel_readout N C sample register bin ops keep z

/-- Physical age semantics for every retained pair inside a SAME actual
terminal component, including ancestral tail grafts. The initializer's
decoration is DERIVED from the original leaf ages. No off-component age or
inverse bin claim is made. -/
theorem actual_initialized_panel_pair_age_bins (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (ops : List (ProgramStep N)) (keep : Finset Copy) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r ops (initialCode N sample register),
      ∀ l ∈ (state (completeEnd N ops z)).live,
        ∃ d : Decoration ((state (completeEnd N ops z)).genealogy l),
          ∀ a b : PanelCopy keep,
            a.val ∈ ((state (completeEnd N ops z)).genealogy l).leaves →
            b.val ∈ ((state (completeEnd N ops z)).genealogy l).leaves →
            (physicalPanelFields N C sample register bin ops keep z).2 a b =
              bin (pairAge (fun x => C.age (N.leaf (sample x)))
                ((state (completeEnd N ops z)).genealogy l) d a.val b.val) := by
  filter_upwards [actual_complete_tag_decoder N r bin (fun x => C.age (N.leaf (sample x)))
    ops (initialCode N sample register) (firstOriginalDate N C) (leafAgeMatrix N C sample)
    (actual_leaf_initialCode_decorates N C sample register)] with z hz
  intro l hl
  obtain ⟨d, hd, _⟩ := hz l hl
  refine ⟨d, ?_⟩
  intro a b ha hb
  exact congrArg bin (hd a.val ha b.val hb)

end CloudG6.NaturalPanelPhysicalAges
