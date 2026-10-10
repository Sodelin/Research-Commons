import G1CanonicalBoundaryPrivateWordBinding

/-! Every full-calendar private coordinate has an explicit ORIGINAL operation
word, including only its physically active epochs. Its fused kernel is the
actual original local source program, on the fixed original inside carrier.
This is the precise source-word side of the remaining true-K block binding. -/
namespace G1CanonicalWholePrivateSourceWord
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler
open G1CanonicalOriginalNodeAsyncStep G1CanonicalOriginalEpochAsync G1CanonicalOriginalAdjacentRecordedRow
open G1CanonicalInitializedWholeCalendarHistory G1CanonicalWholeCalendarRecordedSuffix
open G1ActualOriginalUnrankedLocalKernel G1OriginalActorPrivateWordKernel
open G1PendingActorInterfaceCommutation G1FinitePendingActorPromotion G1PendingBaseCheckpointRecorder
open G1CanonicalActorKernelSourceBindings G1CanonicalBoundaryPrivateWordBinding
open G1ActiveCoreBridgeCohorts G1UnrankedSourceView
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def originalActorSourceSuffix (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) :
    ℝ → List ℝ → List (ProgramStep O.network)
  | date,[] => originalBoundaryPrivateWord O H D hD actor gamma common date
  | date,next::later => originalBoundaryPrivateWord O H D hD actor gamma common date ++
      (if actor ∈ canonicalDateActors T date then [.interval (Real.toNNReal (next-date))] else []) ++
      originalActorSourceSuffix O H D hD actor gamma common next later

noncomputable def originalActorSourceWord (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) :=
  match sortedOriginalDates O.network O.calendar with
  | [] => []
  | date::dates => originalActorSourceSuffix O H D hD actor gamma common date dates

/-- Exact equality of emitted kernel lists and the registry/rates/date-bound
actual ORIGINAL private operation word. Checkpoint recording adds no kernels. -/
theorem actual_calendar_suffix_private_source_kernel_list (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (date : ℝ) (dates : List ℝ) :
    ownerKernels actor (canonicalRecordedCalendarSuffix O H D hD sample gamma common r date dates) =
      (originalActorSourceSuffix O H D hD actor gamma common date dates).map
        (fun op => originalLocalRow O.network sample r (originalInsideCopies O sample (actorInput O D actor)) [op]) := by
  induction dates generalizing date with
  | nil => exact actual_whole_boundary_private_kernel_word O H D hD sample gamma common r actor date
  | cons next dates ih =>
    simp only [canonicalRecordedCalendarSuffix,canonicalRecordedBoundaryEpochOps,
      owner_kernels_append,owner_kernels_recorded_block]
    rw [actual_whole_boundary_private_kernel_word,actual_original_epoch_owner_kernel,ih]
    simp only [originalActorSourceSuffix,List.map_append]
    by_cases hm : actor ∈ canonicalDateActors T date <;> simp [hm,List.append_assoc]

/-- Every private kernel appearing in the whole original calendar is an actual
original inside source-operation kernel. No fitted synthetic edge rate, raw
representative equality, or supplied desired kernel is used. -/
theorem actual_whole_calendar_private_source_kernel_list (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) :
    ownerKernels actor (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r) =
      (originalActorSourceWord O H D hD actor gamma common).map
        (fun op => originalLocalRow O.network sample r (originalInsideCopies O sample (actorInput O D actor)) [op]) := by
  unfold canonicalRecordedWholeCalendarOps originalActorSourceWord
  cases sortedOriginalDates O.network O.calendar with
  | nil => rfl
  | cons date dates => exact actual_calendar_suffix_private_source_kernel_list O H D hD sample gamma common r actor date dates

theorem actual_whole_calendar_private_fused_source_row (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (actor : BridgeActor T) (value : UnrankedView O.Vertex O.Edge Copy) :
    actorWordKernel (ownerKernels actor (canonicalRecordedWholeCalendarOps O H D hD sample gamma common r)) value =
      originalLocalRow O.network sample r (originalInsideCopies O sample (actorInput O D actor))
        (originalActorSourceWord O H D hD actor gamma common) value := by
  rw [actual_whole_calendar_private_source_kernel_list,actual_original_source_private_word]

#print axioms actual_whole_calendar_private_source_kernel_list
#print axioms actual_whole_calendar_private_fused_source_row
end G1CanonicalWholePrivateSourceWord
