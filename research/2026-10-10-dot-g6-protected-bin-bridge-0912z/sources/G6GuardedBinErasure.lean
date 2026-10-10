import G6ProtectedBinEndpoint
import NaturalCalendarPastAdmission

/-!
Additive UNCOMPILED candidate, dot / OpenAI, 10 October 2026.
Physical retained guards derive no-read before and after a deleted interior.
Every old bin is a same-record reader of erased ancestry, not a latent reader.
The erased future still carries all actual population IDs; infinite ancestral
completion uses the unchanged original jump law and also ignores these bits.
No graph surgery, positive compression, or normalized COMMON mixture is proved.
-/
namespace UnifiedLean.G6.GuardedBinErasure
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceEmbeddedJumpLaw UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.G6.BinHistory UnifiedLean.G6.PrivateRegisterErasure
open UnifiedLean.G6.PrivateRegisterSourceStep UnifiedLean.G6.PrivateRegisterProgram
open UnifiedLean.G6.PrivateRegisterHistory UnifiedLean.G6.PrivateRegisterCalendar
open UnifiedLean.G6.PrivateRegisterCalendarPrefix UnifiedLean.G6.ProtectedBinEndpoint
open GProgram.G2.SourceFiniteHistory GProgram.G2.CalendarDecoration
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualCalendarCutContext
open CloudG3.ActualObservationCutRefinement CloudG3.CompleteCalendarJointLaw
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open CloudG6.NaturalCalendarPastAdmission
open scoped Classical
variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def eraseTagged (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (q : Code N sample × (Copy → Copy → Tag)) :=
  (erasePrivateCode N P q.1,q.2)

noncomputable def observedEndpoint (N : RootedBinary V E X) {sample : Copy → X}
    (q : Code N sample × (Copy → Copy → Tag)) :=
  (sourceUnrankedForest (state q.1) Finset.univ,q.2)

theorem tag_update_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s d : Code N sample) (tag : Tag) (B : Copy → Copy → Tag) :
    tagUpdate N (erasePrivateCode N P s) (erasePrivateCode N P d) tag B =
      tagUpdate N s d tag B := rfl

/-- The accepted structural old-bin erasure proof, without its unused finite-Tag
section instance. No finiteness hypothesis is added to this deterministic reader. -/
theorem endpoint_history_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (word : List (ProgramStep N × Tag)) (s : Code N sample)
    (B : Copy → Copy → Tag) (h : Fin (physicalOps N word).length → Code N sample) :
    eraseTagged N P (endpointHistoryReadout N word s B h) =
      endpointHistoryReadout N word (erasePrivateCode N P s) B
        (historyProjection (erasePrivateCode N P) h) := by
  symm
  induction word generalizing s B with
  | nil => rfl
  | cons q word ih =>
      change Fin ((physicalOps N word).length + 1) → Code N sample at h
      change endpointHistoryReadout N word (erasePrivateCode N P (h 0))
        (endpointStepTags N q.1 q.2 (erasePrivateCode N P s)
          (erasePrivateCode N P (h 0)) B)
        (historyProjection (erasePrivateCode N P) (Fin.tail h)) = _
      have ht : endpointStepTags N q.1 q.2 (erasePrivateCode N P s)
          (erasePrivateCode N P (h 0)) B = endpointStepTags N q.1 q.2 s (h 0) B := by
        cases q.1 <;> rfl
      rw [ht]
      exact ih (h 0) _ (Fin.tail h)

theorem observed_endpoint_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (q : Code N sample × (Copy → Copy → Tag)) :
    observedEndpoint N (eraseTagged N P q) = observedEndpoint N q := rfl

noncomputable def observedHistory (N : RootedBinary V E X) {sample : Copy → X}
    (word : List (ProgramStep N × Tag)) (s : Code N sample) (B : Copy → Copy → Tag)
    (h : Fin (physicalOps N word).length → Code N sample) :=
  observedEndpoint N (endpointHistoryReadout N word s B h)

theorem observed_history_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (word : List (ProgramStep N × Tag)) (s : Code N sample)
    (B : Copy → Copy → Tag) (h : Fin (physicalOps N word).length → Code N sample) :
    observedHistory N word (erasePrivateCode N P s) B
      (historyProjection (erasePrivateCode N P) h) = observedHistory N word s B h := by
  unfold observedHistory
  rw [← endpoint_history_erasure,observed_endpoint_erasure]

section Calendar
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]

/-- Actual old and future bins commute with register erasure as one joint
law. The measurable observer is the actual marked-clock endpoint fold. -/
theorem actual_calendar_joint_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (P : Finset V) (bin : ℝ → Tag) (hbin : Measurable bin)
    (word : List (ProgramStep N × Tag)) (s : Code N sample) (offset : ℝ)
    (B : Copy → Copy → Tag) (hword : wordBinContract N bin word offset)
    (hread : NoPrivateWordRead N P (physicalOps N word)) :
    (calendarJoint N r bin hbin (physicalOps N word) s offset B).map (eraseTagged N P) =
      calendarJoint N r bin hbin (physicalOps N word) (erasePrivateCode N P s) offset B := by
  rw [actual_calendar_joint_endpoint_history N r bin hbin word s offset B hword,
    actual_calendar_joint_endpoint_history N r bin hbin word
      (erasePrivateCode N P s) offset B hword,PMF.map_comp]
  calc
    _ = ((sourceHistoryLaw N r (physicalOps N word) s).map
        (historyProjection (erasePrivateCode N P))).map
          (endpointHistoryReadout N word (erasePrivateCode N P s) B) := by
      rw [PMF.map_comp]
      congr 1
      funext h
      exact endpoint_history_erasure N P word s B h
    _ = _ := by rw [actual_sourceHistory_erasure N r P (physicalOps N word) hread s]

/-- The upper original guard discharges the no-read hypothesis, including
its complete tied boundary. Arbitrarily many later bin cuts are supported. -/
theorem actual_guarded_suffix_joint_erasure (N : RootedBinary V E X)
    {sample : Copy → X} (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (P : Finset V) (upper : V) (pre post : List ℝ)
    (hprivate : ∀ v ∈ P, C.age v < C.age upper)
    (hsplit : sortedOriginalDates N C = pre ++ C.age upper :: post)
    (bin : ℝ → Tag) (hbin : Measurable bin) (word : List (ProgramStep N × Tag))
    (href : CutRefines N
      (boundaryOperations N C H gamma common (C.age upper) ++
        calendarTail N C H gamma common (C.age upper) post) (physicalOps N word))
    (s : Code N sample) (B : Copy → Copy → Tag)
    (hword : wordBinContract N bin word (C.age upper)) :
    (calendarJoint N r bin hbin
      (boundaryOperations N C H gamma common (C.age upper) ++
        calendarTail N C H gamma common (C.age upper) post) s (C.age upper) B).map
          (eraseTagged N P) =
    calendarJoint N r bin hbin
      (boundaryOperations N C H gamma common (C.age upper) ++
        calendarTail N C H gamma common (C.age upper) post)
      (erasePrivateCode N P s) (C.age upper) B := by
  have hr := cutRefines_noPrivateWordRead N P href
    (actual_boundary_and_suffix_noPrivateWordRead N C H gamma common P
      (C.age upper) pre post hprivate hsplit)
  rw [cut_refines_actual_calendar_joint N r bin hbin href s (C.age upper) B,
    cut_refines_actual_calendar_joint N r bin hbin href
      (erasePrivateCode N P s) (C.age upper) B]
  exact actual_calendar_joint_erasure N r P bin hbin word s (C.age upper) B hword hr

end Calendar

/- The actual lower-prefix/old-bin independence theorem is imported directly:
NaturalCalendarPastAdmission.actual_guarded_private_seed_old_bin_product.
It already retains the FULL erased Code and old-bin matrix and derives the
no-read prefix from original physical guards. No duplicate theorem is added. -/

/-- Completion uses original winner fractions and destinations, none of which
reads any latent bit. This is independent of whether the bit was used earlier. -/
lemma actual_jump_choice_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (P : Finset V) (s : Code N sample) :
    sourceJumpChoice N r (erasePrivateCode N P s) = sourceJumpChoice N r s := by
  apply PMF.ext
  intro q
  change ENNReal.ofReal (jumpMass N r (erasePrivateCode N P s) q) =
    ENNReal.ofReal (jumpMass N r s q)
  cases q <;> rfl

lemma actual_jump_step_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (P : Finset V) (s : Code N sample) :
    (sourceJumpStep N r s).map (erasePrivateCode N P) =
      sourceJumpStep N r (erasePrivateCode N P s) := by
  have hd : erasePrivateCode N P ∘ stepDestination N s =
      stepDestination N (erasePrivateCode N P s) := by
    funext q
    cases q with
    | none => exact erase_actual_holding_destination N P s
    | some q => exact erase_actual_merger_destination N P s q
  unfold sourceJumpStep
  rw [PMF.map_comp,hd,actual_jump_choice_erasure]

theorem actual_ancestral_completion_erasure (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (P : Finset V)
    (n : ℕ) (s : Code N sample) :
    (ancestralCompletion N r n s).map (erasePrivateCode N P) =
      ancestralCompletion N r n (erasePrivateCode N P s) := by
  induction n generalizing s with
  | zero => simp only [ancestralCompletion,PMF.pure_map]
  | succ n ih =>
      rw [ancestralCompletion,PMF.map_bind]
      simp_rw [ih]
      change (sourceJumpStep N r s).bind
        (ancestralCompletion N r n ∘ erasePrivateCode N P) = _
      rw [← PMF.bind_map,actual_jump_step_erasure N r P s]
      rfl

theorem actual_joint_tail_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (P : Finset V) (tag : Tag)
    (q : Code N sample × (Copy → Copy → Tag)) :
    (jointTailKernel N r tag q).map (eraseTagged N P) =
      jointTailKernel N r tag (eraseTagged N P q) := by
  unfold jointTailKernel completionKernel
  dsimp only [eraseTagged]
  rw [← actual_ancestral_completion_erasure N r P (Fintype.card Copy) q.1,
    PMF.map_comp,PMF.map_comp]
  congr 1

/-- Infinite completion is the actual accepted jump-completion row. Its old
bins remain and its observable law does not recover an erased private bit. -/
theorem actual_joint_tail_observation_erasure (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (P : Finset V) (tag : Tag)
    (q : Code N sample × (Copy → Copy → Tag)) :
    (jointTailKernel N r tag q).map (observedEndpoint N) =
      (jointTailKernel N r tag (eraseTagged N P q)).map (observedEndpoint N) := by
  rw [← actual_joint_tail_erasure N r P tag q,PMF.map_comp]
  congr 1

/-- Append the same conditional completion to one correlated old-bin law.
The register erasure is joint and is never applied to separate marginals. -/
theorem actual_joint_completed_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (P : Finset V) (tag : Tag)
    (law : PMF (Code N sample × (Copy → Copy → Tag))) :
    (law.bind (jointTailKernel N r tag)).map (eraseTagged N P) =
      (law.map (eraseTagged N P)).bind (jointTailKernel N r tag) := by
  rw [PMF.map_bind,PMF.bind_map]
  congr 1
  funext q
  exact actual_joint_tail_erasure N r P tag q

#print axioms actual_joint_completed_erasure

#print axioms actual_guarded_suffix_joint_erasure
#print axioms actual_joint_tail_erasure
#print axioms actual_joint_tail_observation_erasure
end UnifiedLean.G6.GuardedBinErasure
