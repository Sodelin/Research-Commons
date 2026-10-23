import UnifiedLean.G6.PrivateRegisterCalendar
import G1OriginatedNeutralSpanRegion
import G1OriginalExteriorCohort
import UnifiedLean.Source.SourceCompletedUnrankedTree
import UnifiedLean.Source.SourceCopyCarrierTransport

/-!
UNCOMPILED source candidate, existing G3 owner,22October2026.
The outside sample has no descendant taxon at a private span node. Derive
empty current-owner domains there, then actual full-program register erasure
even when its literal word contains those private COMMON operations.
The exterior evolves under its actual source kernels throughout.
-/
namespace G3OriginalExteriorRegisterErasure
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.SourceEmbeddedJumpLaw UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.G6.PrivateRegisterErasure UnifiedLean.G6.PrivateRegisterBoundary
open UnifiedLean.G6.PrivateRegisterProgram
open UnifiedLean.G6.PrivateRegisterSourceStep
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1OriginalSpanRegion
open G1OriginatedNeutralSpanRegion G1OriginalExteriorCohort
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Pure original graph/sample condition. No source-kernel equation or
absence-of-roots condition is a premise. -/
def NoPrivateTaxonReach (N : RootedBinary V E X) (P : Finset V) (sample : Copy → X) : Prop :=
  ∀ v ∈ P, ∀ x : Copy, ¬ N.graph.DReach v (N.leaf (sample x))

theorem actual_private_atNode_empty (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (hreach : NoPrivateTaxonReach N P sample)
    (s : Code N sample) (v : V) (hv : v ∈ P) : IsEmpty (AtNode (state s) v) := by
  refine ⟨fun l => ?_⟩
  have hl : l.val ∈ (state s).live ∧ (state s).location l.val = .node v := by
    simpa only [Finset.mem_filter] using l.property
  have hr := s.property.forest.representative l.val hl.1
  have hloc : copyLocation (state s) l.val = .node v := by
    change (state s).location ((state s).ancestor l.val) = .node v
    rw [hr]
    exact hl.2
  have hd := s.property.original_descendant l.val
  rw [hloc] at hd
  exact hreach v hv l.val hd

/-- A private COMMON bit can change its constant arm assignment, but its
actual current-owner domain is empty in EVERY valid outside Code. -/
theorem actual_boundary_erasure_of_no_private_taxon_reach (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (hreach : NoPrivateTaxonReach N P sample)
    (op : BoundaryOperation N) (s : Code N sample) :
    (boundaryKernel N op s).map (erasePrivateCode N P) =
      boundaryKernel N op (erasePrivateCode N P s) := by
  cases op with
  | exit e => exact actual_boundary_erasure N P (.exit e) s trivial
  | ordinary e hd => exact actual_boundary_erasure N P (.ordinary e hd) s trivial
  | root => exact actual_boundary_erasure N P .root s trivial
  | independent H gamma =>
      exact actual_boundary_erasure N P (.independent H gamma) s trivial
  | common H =>
      by_cases hH : H.hybrid ∈ P
      · have hc : (fun _ : AtNode (state s) H.hybrid => (state s).register H.hybrid) =
            (fun _ : AtNode (state (erasePrivateCode N P s)) H.hybrid =>
              (state (erasePrivateCode N P s)).register H.hybrid) := by
          funext l
          exact False.elim ((actual_private_atNode_empty N P sample hreach s H.hybrid hH).false l)
        simp only [boundaryKernel,PMF.pure_map,erase_pulseCode,hc]
      · exact actual_boundary_erasure N P (.common H) s hH

theorem actual_step_erasure_of_no_private_taxon_reach (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (hreach : NoPrivateTaxonReach N P sample)
    (r : PositivePairRates E) (op : ProgramStep N) (s : Code N sample) :
    (sourceProgramStep N r op s).map (erasePrivateCode N P) =
      sourceProgramStep N r op (erasePrivateCode N P s) := by
  cases op with
  | interval t => exact actual_sourceTimeKernel_erasure N r P t s
  | boundary b => exact actual_boundary_erasure_of_no_private_taxon_reach N P sample hreach b s

/-- Unlike the syntactic no-read theorem, this covers the actual outside
program THROUGH private pulses. Source validity supplies empty domains at
every intermediate Code, so no desired support invariant is assumed. -/
theorem actual_program_erasure_of_no_private_taxon_reach (N : RootedBinary V E X)
    (P : Finset V) (sample : Copy → X) (hreach : NoPrivateTaxonReach N P sample)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    (sourceProgram N r ops s).map (erasePrivateCode N P) =
      sourceProgram N r ops (erasePrivateCode N P s) := by
  induction ops generalizing s with
  | nil => simp only [sourceProgram,PMF.pure_map]
  | cons op ops ih =>
      rw [sourceProgram,PMF.map_bind]
      simp_rw [ih]
      change (sourceProgramStep N r op s).bind
        (sourceProgram N r ops ∘ erasePrivateCode N P) = _
      rw [← PMF.bind_map,actual_step_erasure_of_no_private_taxon_reach N P sample hreach r op s]
      rfl

/-- Existing actual Originated neutral-span theorem discharges hn at its
caller. Here the original outside-copy definition discharges the graph
condition, including an empty outside carrier and arbitrary copy census. -/
theorem neutral_span_outside_no_private_taxon_reach (O : Source X)
    {a b : O.Vertex} (word : OriginalSpan O.network a b)
    (hn : DescendantNeutral O word) (sample : Copy → X)
    (P : Finset O.Vertex) (hP : P ⊆ nodeRegion O word) :
    NoPrivateTaxonReach O.network P
      (selectedSample sample (originalOutsideCopies O sample a)) := by
  intro v hv x
  change ¬ O.network.graph.DReach v (O.network.leaf (sample x.val))
  intro hd
  have hinput := (hn v (hP hv) (sample x.val)).mp hd
  exact (Finset.mem_filter.mp x.property).2 hinput

theorem actual_outside_span_program_erasure (O : Source X) {a b : O.Vertex}
    (word : OriginalSpan O.network a b) (hn : DescendantNeutral O word)
    (sample : Copy → X) (P : Finset O.Vertex) (hP : P ⊆ nodeRegion O word)
    (r : PositivePairRates O.Edge) (ops : List (ProgramStep O.network))
    (s : Code O.network (selectedSample sample (originalOutsideCopies O sample a))) :
    (sourceProgram O.network r ops s).map (erasePrivateCode O.network P) =
      sourceProgram O.network r ops (erasePrivateCode O.network P s) :=
  actual_program_erasure_of_no_private_taxon_reach O.network P _
    (neutral_span_outside_no_private_taxon_reach O word hn sample P hP) r ops s

/-- Actual unranked endpoint forest discards the register by definition.
This is not permission to observe arbitrary hidden fields or marked clocks. -/
theorem actual_unranked_endpoint_erasure (N : RootedBinary V E X) (P : Finset V)
    (sample : Copy → X) (hreach : NoPrivateTaxonReach N P sample)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    (sourceProgram N r ops s).map (fun d => sourceUnrankedForest (state d) Finset.univ) =
    (sourceProgram N r ops (erasePrivateCode N P s)).map
      (fun d => sourceUnrankedForest (state d) Finset.univ) := by
  calc
    _ = ((sourceProgram N r ops s).map (erasePrivateCode N P)).map
        (fun d => sourceUnrankedForest (state d) Finset.univ) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by rw [actual_program_erasure_of_no_private_taxon_reach N P sample hreach r ops s]

#print axioms actual_private_atNode_empty
#print axioms actual_program_erasure_of_no_private_taxon_reach
#print axioms neutral_span_outside_no_private_taxon_reach
#print axioms actual_unranked_endpoint_erasure

/-- Real-merger jump probabilities use the unchanged actual pair catalogue
and rates, rather than uniformization holding probabilities. -/
theorem actual_jump_choice_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (P : Finset V) (s : Code N sample) :
    sourceJumpChoice N r (erasePrivateCode N P s) = sourceJumpChoice N r s := by
  apply PMF.ext
  intro q
  rw [sourceJumpChoice_apply,sourceJumpChoice_apply]
  cases q <;> rfl

theorem actual_jump_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (P : Finset V) (s : Code N sample) :
    (sourceJumpStep N r s).map (erasePrivateCode N P) =
      sourceJumpStep N r (erasePrivateCode N P s) := by
  have hd : erasePrivateCode N P ∘ stepDestination N s =
      stepDestination N (erasePrivateCode N P s) := by
    funext q
    cases q with
    | none => exact erase_actual_holding_destination N P s
    | some p => exact erase_actual_merger_destination N P s p
  unfold sourceJumpStep
  rw [PMF.map_comp,hd,actual_jump_choice_erasure N r P s]
  rfl

/-- The EXISTING finite ancestral completion, with its actual current-clock
winner jumps, commutes with register erasure for every natural jump budget. -/
theorem actual_ancestral_completion_erasure (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (P : Finset V) (n : Nat)
    (s : Code N sample) :
    (ancestralCompletion N r n s).map (erasePrivateCode N P) =
      ancestralCompletion N r n (erasePrivateCode N P s) := by
  induction n generalizing s with
  | zero => simp only [ancestralCompletion,PMF.pure_map]
  | succ n ih =>
      rw [ancestralCompletion,PMF.map_bind]
      simp_rw [ih]
      change (sourceJumpStep N r s).bind
        (ancestralCompletion N r n ∘ erasePrivateCode N P) = _
      rw [← PMF.bind_map,actual_jump_erasure N r P s]
      rfl

/-- The actual endpoint kernel used in naturalCompletedUnrankedLaw, without
the preceding actual calendar which is supplied separately at the caller. -/
noncomputable def actualCompletedUnrankedKernel (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :=
  (ancestralCompletion N r (Fintype.card Copy) s).map
    (fun d => sourceUnrankedForest (state d) Finset.univ)

theorem actual_completed_unranked_kernel_erasure (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (P : Finset V) (s : Code N sample) :
    actualCompletedUnrankedKernel N r s =
      actualCompletedUnrankedKernel N r (erasePrivateCode N P s) := by
  unfold actualCompletedUnrankedKernel
  calc
    _ = ((ancestralCompletion N r (Fintype.card Copy) s).map
        (erasePrivateCode N P)).map
        (fun d => sourceUnrankedForest (state d) Finset.univ) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by rw [actual_ancestral_completion_erasure N r P (Fintype.card Copy) s]

/-- A true no-read future followed by the ACTUAL ancestral/unranked kernel
is private-register blind. Existing actual calendar age/suffix theorems can
derive hops; this is not an arbitrary-register-blind-exterior premise. -/
theorem actual_completed_future_erasure (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (P : Finset V)
    (future : List (ProgramStep N)) (hops : NoPrivateWordRead N P future)
    (s : Code N sample) :
    (sourceProgram N r future s).bind (actualCompletedUnrankedKernel N r) =
      (sourceProgram N r future (erasePrivateCode N P s)).bind
        (actualCompletedUnrankedKernel N r) := by
  calc
    _ = ((sourceProgram N r future s).map (erasePrivateCode N P)).bind
        (actualCompletedUnrankedKernel N r) := by
      rw [PMF.bind_map]
      congr 1
      funext d
      exact actual_completed_unranked_kernel_erasure N r P d
    _ = _ := by rw [actual_sourceProgram_erasure N r P future hops s]

#print axioms actual_jump_erasure
#print axioms actual_ancestral_completion_erasure
#print axioms actual_completed_unranked_kernel_erasure
#print axioms actual_completed_future_erasure
end G3OriginalExteriorRegisterErasure
