import G1OriginalActorPrivateWordKernel

/-! Actual private actor words are EXTRACTED from the literal original phase:
all original epochs remain, and outside-only boundaries are omitted solely
from the private coordinate. The full exterior compiler remains unchanged.
No desired private/source row equality is assumed. -/
namespace G1ActualPrivateOriginalWordExtraction
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceBoundaryKernels
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1OriginalSpanRegion G1OriginalSpanClosingPhase
open G1SpanRegionOriginalOperations G1OriginalEpochPanelCompression G1ExteriorBoundarySilence
open G1ActualJointProgram
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def privateStep (O : Source.{u,v,w} X) {a b : O.Vertex} (word : OriginalSpan O.network a b) :
    ProgramStep O.network → Bool
  | .interval _ => true
  | .boundary op => decide (SpanLocation O word (touchedPlace O.network op))

noncomputable def privateOriginalOps (O : Source.{u,v,w} X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (ops : List (ProgramStep O.network)) := ops.filter (privateStep O word)

lemma actual_excluded_original_step_frame (O : Source.{u,v,w} X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (s : Code O.network sample) (keep : Finset Copy)
    (hin : ∀ x ∈ keep, SpanLocation O word (copyLocation (state s) x)) (op : ProgramStep O.network)
    (hex : privateStep O word op = false) :
    (sourceProgramStep O.network r op s).map (projection O.network keep) = PMF.pure (projection O.network keep s) := by
  cases op with
  | interval t => cases hex
  | boundary op =>
    have hn : ¬ SpanLocation O word (touchedPlace O.network op) := of_decide_eq_false hex
    apply actual_untouched_boundary_law
    intro x hx heq
    exact hn (heq ▸ hin x hx)

/-- A complete actual private coordinate word is constructed by filtering
original operation sites; every omitted boundary is derived to be a full
labelled-state identity, including population and SAME register. -/
theorem actual_safe_private_original_row (O : Source.{u,v,w} X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (cut : O.Edge) (hend : EndsAt O cut word)
    (H : OriginalParentRegistry O.network) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (r : PositivePairRates O.Edge) (ops : List (ProgramStep O.network))
    (safe : ∀ op ∈ ops, EdgeSafeStep O.network H (fun h => gamma h.val) (fun h => common h.val) {cut} op)
    (s : Code O.network sample) (keep : Finset Copy)
    (hin : ∀ x ∈ keep, SpanLocation O word (copyLocation (state s) x)) :
    (sourceProgram O.network r ops s).map (projection O.network keep) =
      (sourceProgram O.network r (privateOriginalOps O word ops) s).map (projection O.network keep) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    have hs := safe op (List.mem_cons_self)
    have ht := fun q hq => safe q (List.mem_cons_of_mem op hq)
    have hrow (d : Code O.network sample) (hd : d ∈ (sourceProgramStep O.network r op s).support) :
        (sourceProgram O.network r ops d).map (projection O.network keep) =
          selectedProgram O.network r keep (privateOriginalOps O word ops) (projection O.network keep d) := by
      rw [ih ht d (actual_span_safe_step_support O word cut hend H gamma common r op hs s keep hin hd)]
      exact actual_source_program_projection O.network r keep _ d
    cases hp : privateStep O word op with
    | true =>
      have he : privateOriginalOps O word (op::ops) = op::privateOriginalOps O word ops := by
        simp [privateOriginalOps,hp]
      rw [he]
      simp only [sourceProgram,PMF.map_bind]
      apply bind_eq_of_eq_on_support
      intro d hd
      exact ih ht d (actual_span_safe_step_support O word cut hend H gamma common r op hs s keep hin hd)
    | false =>
      have he : privateOriginalOps O word (op::ops) = privateOriginalOps O word ops := by
        simp [privateOriginalOps,hp]
      rw [he]
      calc
        _ = (sourceProgramStep O.network r op s).bind (fun d =>
            selectedProgram O.network r keep (privateOriginalOps O word ops) (projection O.network keep d)) := by
          simp only [sourceProgram,PMF.map_bind]
          exact bind_eq_of_eq_on_support _ _ _ hrow
        _ = ((sourceProgramStep O.network r op s).map (projection O.network keep)).bind
            (selectedProgram O.network r keep (privateOriginalOps O word ops)) := by rw [PMF.bind_map]; rfl
        _ = selectedProgram O.network r keep (privateOriginalOps O word ops) (projection O.network keep s) := by
          rw [actual_excluded_original_step_frame O word r s keep hin op hp,PMF.pure_bind]
        _ = _ := (actual_source_program_projection O.network r keep _ s).symm

#print axioms actual_safe_private_original_row
end G1ActualPrivateOriginalWordExtraction
