import G6GuardedBinErasure

/-!
Additive UNCOMPILED candidate, dot / OpenAI, 10 October 2026.
Exact reuse of G1's actual unranked one-step law and G2's history transport.
A future spanning several bins retains its whole unranked endpoint vector.
Its causal interface retains original populations and the retained register.
-/
namespace UnifiedLean.G6.UnrankedBinContinuation
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G2.SourceFiniteHistory GProgram.G2.ActualPairCoalescence
open UnifiedLean.G6.BinHistory UnifiedLean.G6.GuardedBinErasure
open UnifiedLean.G6.PrivateRegisterErasure UnifiedLean.G6.PrivateRegisterCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open CloudG3.ActualObservationCutRefinement
open G1UnrankedSourceView G1UnrankedActualGenerator G1UnrankedActualFuture
open G1UnrankedSingleExitLabel
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualCalendarCutContext
open scoped Classical
variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def unrankedTagUpdate (a d : UnrankedView V E Copy)
    (tag : Tag) (B : Copy → Copy → Tag) (x y : Copy) : Tag :=
  if y ∉ optionTreeLeaves (a.genealogy x) ∧ y ∈ optionTreeLeaves (d.genealogy x)
    then tag else B x y

lemma actual_unranked_tag_update (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (tag : Tag) (B : Copy → Copy → Tag) :
    unrankedTagUpdate (unrankedProjection N Finset.univ s).val
      (unrankedProjection N Finset.univ d).val tag B = tagUpdate N s d tag B := by
  funext x y
  have hs := selected_same_block (state s) s.property.forest Finset.univ
    (Finset.mem_univ x) (Finset.mem_univ y)
  have hd := selected_same_block (state d) d.property.forest Finset.univ
    (Finset.mem_univ x) (Finset.mem_univ y)
  simp only [unrankedTagUpdate,unrankedProjection,unrankedView,
    optionUnranked_leaves,tagUpdate]
  simp only [sameBlock] at hs hd
  simp only [hs,hd]

noncomputable def unrankedStepTags (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (tag : Tag) (a d : UnrankedIndex N sample Finset.univ)
    (B : Copy → Copy → Tag) := match op with
  | .interval _ => unrankedTagUpdate a.val d.val tag B
  | .boundary _ => B

lemma actual_unranked_step_tags (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (tag : Tag) (s d : Code N sample) (B : Copy → Copy → Tag) :
    unrankedStepTags N op tag (unrankedProjection N Finset.univ s)
      (unrankedProjection N Finset.univ d) B = endpointStepTags N op tag s d B := by
  cases op with
  | interval t => exact actual_unranked_tag_update N s d tag B
  | boundary op => rfl

noncomputable def unrankedHistoryReadout (N : RootedBinary V E X) {sample : Copy → X} :
    (word : List (ProgramStep N × Tag)) → UnrankedIndex N sample Finset.univ →
    (Copy → Copy → Tag) → (Fin (physicalOps N word).length → UnrankedIndex N sample Finset.univ) →
      UnrankedIndex N sample Finset.univ × (Copy → Copy → Tag)
  | [],a,B,_ => (a,B)
  | q::word,a,B,h => by
      change (Fin ((physicalOps N word).length+1) → UnrankedIndex N sample Finset.univ) at h
      exact unrankedHistoryReadout N word (h 0)
        (unrankedStepTags N q.1 q.2 a (h 0) B) (Fin.tail h)

noncomputable def projectUnrankedTagged (N : RootedBinary V E X) {sample : Copy → X}
    (q : Code N sample × (Copy → Copy → Tag)) :=
  (unrankedProjection N Finset.univ q.1,q.2)

theorem actual_unranked_history_readout (N : RootedBinary V E X) {sample : Copy → X}
    (word : List (ProgramStep N × Tag)) (s : Code N sample) (B : Copy → Copy → Tag)
    (h : Fin (physicalOps N word).length → Code N sample) :
    projectUnrankedTagged N (endpointHistoryReadout N word s B h) =
      unrankedHistoryReadout N word (unrankedProjection N Finset.univ s) B
        (historyProjection (unrankedProjection N Finset.univ) h) := by
  induction word generalizing s B with
  | nil => rfl
  | cons q word ih =>
      rcases q with ⟨op,tag⟩
      change (Fin ((physicalOps N word).length+1) → Code N sample) at h
      change projectUnrankedTagged N (endpointHistoryReadout N word (h 0)
        (endpointStepTags N op tag s (h 0) B) (Fin.tail h)) =
          unrankedHistoryReadout N word (unrankedProjection N Finset.univ (h 0))
            (unrankedStepTags N op tag (unrankedProjection N Finset.univ s)
              (unrankedProjection N Finset.univ (h 0)) B)
            (Fin.tail (historyProjection (unrankedProjection N Finset.univ) h))
      rw [ih,actual_unranked_step_tags]
      rfl

noncomputable def unrankedObservedHistory (N : RootedBinary V E X) {sample : Copy → X}
    (word : List (ProgramStep N × Tag)) (a : UnrankedIndex N sample Finset.univ)
    (B : Copy → Copy → Tag)
    (h : Fin (physicalOps N word).length → UnrankedIndex N sample Finset.univ) :=
  let q := unrankedHistoryReadout N word a B h
  (unrankedViewForest q.1.val,q.2)

lemma actual_observed_unranked_history (N : RootedBinary V E X) {sample : Copy → X}
    (word : List (ProgramStep N × Tag)) (s : Code N sample) (B : Copy → Copy → Tag)
    (h : Fin (physicalOps N word).length → Code N sample) :
    observedHistory N word s B h =
      unrankedObservedHistory N word (unrankedProjection N Finset.univ s) B
        (historyProjection (unrankedProjection N Finset.univ) h) := by
  unfold unrankedObservedHistory
  rw [← actual_unranked_history_readout]
  apply Prod.ext
  · exact actual_unranked_view_forest _
  · rfl

/-- FULL actual finite history, retaining entering unranked state. The only
one-step law is G1's already proved original source projection. -/
theorem actual_unranked_observed_history_law (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (word : List (ProgramStep N × Tag))
    (s : Code N sample) (B : Copy → Copy → Tag) :
    (sourceHistoryLaw N r (physicalOps N word) s).map (observedHistory N word s B) =
      (historyLaw (unrankedProgramStep N r Finset.univ) (physicalOps N word)
        (unrankedProjection N Finset.univ s)).map
          (unrankedObservedHistory N word (unrankedProjection N Finset.univ s) B) := by
  have hp := history_projection (sourceProgramStep N r)
    (unrankedProgramStep N r Finset.univ) (unrankedProjection N Finset.univ)
    (actual_unranked_program_step N r Finset.univ) (physicalOps N word) s
  rw [← hp,PMF.map_comp]
  congr 1
  funext h
  exact actual_observed_unranked_history N word s B h

/-- Future cuts can differ: whole unranked history, rather than final endpoint
alone, supplies their bins. Original populations/register remain in the view. -/
theorem actual_unranked_bin_future [Fintype Tag] [MeasurableSpace Tag]
    [MeasurableSingletonClass Tag] (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (word : List (ProgramStep N × Tag)) (s z : Code N sample) (offset : ℝ)
    (B : Copy → Copy → Tag) (hword : wordBinContract N bin word offset)
    (hview : unrankedView (selectedView (state s) Finset.univ) =
      unrankedView (selectedView (state z) Finset.univ)) :
    (calendarJoint N r bin hbin (physicalOps N word) s offset B).map (observedEndpoint N) =
      (calendarJoint N r bin hbin (physicalOps N word) z offset B).map (observedEndpoint N) := by
  have he : unrankedProjection N Finset.univ s = unrankedProjection N Finset.univ z :=
    Subtype.ext hview
  rw [actual_calendar_joint_endpoint_history N r bin hbin word s offset B hword,
    actual_calendar_joint_endpoint_history N r bin hbin word z offset B hword,
    PMF.map_comp,PMF.map_comp]
  change (sourceHistoryLaw N r (physicalOps N word) s).map (observedHistory N word s B) =
    (sourceHistoryLaw N r (physicalOps N word) z).map (observedHistory N word z B)
  rw [actual_unranked_observed_history_law,actual_unranked_observed_history_law,he]

/-- Actual upper-guard suffix: equality of the ERASED unranked causal
interface suffices for every later forest/bin observer. All original outside
population IDs and all nonprivate register coordinates remain in this view. -/
theorem actual_guarded_unranked_bin_future [Fintype Tag] [MeasurableSpace Tag]
    [MeasurableSingletonClass Tag] (N : RootedBinary V E X) {sample : Copy → X}
    (C : GProgram.G5.Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (P : Finset V) (upper : V) (pre post : List ℝ)
    (hprivate : ∀ v ∈ P, C.age v < C.age upper)
    (hsplit : sortedOriginalDates N C = pre ++ C.age upper :: post)
    (bin : ℝ → Tag) (hbin : Measurable bin) (word : List (ProgramStep N × Tag))
    (href : CutRefines N
      (boundaryOperations N C H gamma common (C.age upper) ++
        calendarTail N C H gamma common (C.age upper) post) (physicalOps N word))
    (s z : Code N sample) (B : Copy → Copy → Tag)
    (hword : wordBinContract N bin word (C.age upper))
    (hview : unrankedView (selectedView (state (erasePrivateCode N P s)) Finset.univ) =
      unrankedView (selectedView (state (erasePrivateCode N P z)) Finset.univ)) :
    (calendarJoint N r bin hbin
      (boundaryOperations N C H gamma common (C.age upper) ++
        calendarTail N C H gamma common (C.age upper) post) s (C.age upper) B).map
          (observedEndpoint N) =
    (calendarJoint N r bin hbin
      (boundaryOperations N C H gamma common (C.age upper) ++
        calendarTail N C H gamma common (C.age upper) post) z (C.age upper) B).map
          (observedEndpoint N) := by
  let ops := boundaryOperations N C H gamma common (C.age upper) ++
    calendarTail N C H gamma common (C.age upper) post
  have row (d : Code N sample) :
      (calendarJoint N r bin hbin ops d (C.age upper) B).map (observedEndpoint N) =
        (calendarJoint N r bin hbin ops (erasePrivateCode N P d) (C.age upper) B).map
          (observedEndpoint N) := by
    rw [← actual_guarded_suffix_joint_erasure N C H gamma common r P upper pre post
      hprivate hsplit bin hbin word href d B hword,PMF.map_comp]
    congr 1
  rw [row s,row z]
  rw [cut_refines_actual_calendar_joint N r bin hbin href
      (erasePrivateCode N P s) (C.age upper) B,
    cut_refines_actual_calendar_joint N r bin hbin href
      (erasePrivateCode N P z) (C.age upper) B]
  exact actual_unranked_bin_future N r bin hbin word
    (erasePrivateCode N P s) (erasePrivateCode N P z) (C.age upper) B hword hview

#print axioms actual_guarded_unranked_bin_future

#print axioms actual_unranked_observed_history_law
#print axioms actual_unranked_bin_future
end UnifiedLean.G6.UnrankedBinContinuation
