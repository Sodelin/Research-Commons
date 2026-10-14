import Astra.PhysicalCommonStep
import Astra.PhysicalSpliceExternalMasks
import G1FiniteOriginalDecoratedCore

/-! Source-only finite protected equal-exposure physical iteration.
External primitive label domains are fixed parameters. Eligibility is the
literal local avoidance condition, not a desired reduced source/law/count.
The terminal source has no further eligible equal-exposure splice; neither
expanded dependency completeness nor the certificate size bound is asserted.
-/
namespace Astra.ProtectedPhysicalIteration

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1ActualTwoPortBlob G1BigonSpliceGraph G1ExactSemidirectedPartnerAdmission
open Astra.PhysicalCommonStep Astra.PhysicalSpliceRegistry
open Astra.PhysicalSpliceProtectedCoordinates Astra.PhysicalSpliceExternalMasks
open DotG4.WholeProfileDetermination
open scoped Classical

universe u v w a b c q k

/-- The same external label domains occur on every physical state. Label
injections name actual original primitive coordinates, not fitted parameters.
Expanded dependency completeness of these labels is a separate obligation. -/
structure MarkedSource (X : Type w) [Fintype X]
    (PV : Type a) (PE : Type b) (PH : Type c) where
  physical : PhysicalSource.{u,v,w} X
  vertices : PV → physical.source.Vertex
  vertices_injective : Function.Injective vertices
  edges : PE → physical.source.Edge
  edges_injective : Function.Injective edges
  hybrids : PH → Hybrid physical.source.network
  hybrids_injective : Function.Injective hybrids

variable {X : Type w} [Fintype X]
variable {PV : Type a} {PE : Type b} {PH : Type c}

/-- Only the cell and local eligibility data are stored. There is no target
source, law equality, size bound or conclusion-valued admissibility field. -/
structure EligibleCell (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) where
  blob : S.physical.source.network.graph.Blob
  nonroot : blob ≠ S.physical.source.network.graph.blobOf S.physical.source.network.root
  two_ports : Fintype.card (S.physical.source.network.BlobPort blob) = 2
  equal_exposure : EqualArmExposure S.physical blob nonroot two_ports
  vertex_avoid : ∀ z, S.vertices z ≠ (stepBigon S.physical blob nonroot two_ports).fragment.upper ∧
    S.vertices z ≠ (stepBigon S.physical blob nonroot two_ports).fragment.parents.hybrid
  edge_avoid : ∀ z, S.edges z ∉ G1BigonFootprint.removedEdges S.physical.source.network blob
    (stepBigon S.physical blob nonroot two_ports)
  hybrid_avoid : ∀ z, S.hybrids z ≠ removedHybrid S.physical.source.network blob
    (stepBigon S.physical blob nonroot two_ports)

/-- Construct the tuple and all three retained-label maps on the exact G1
splice. The tuple is independent of any future configuration or sample. -/
noncomputable def next (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (cell : EligibleCell S) : MarkedSource.{u,v,w,a,b,c} X PV PE PH where
  physical := physicalStep S.physical cell.blob cell.nonroot cell.two_ports
  vertices := vertexMap S.physical.source.network cell.blob
    (stepBigon S.physical cell.blob cell.nonroot cell.two_ports) S.vertices cell.vertex_avoid
  vertices_injective := vertexMap_injective S.physical.source.network cell.blob
    (stepBigon S.physical cell.blob cell.nonroot cell.two_ports) S.vertices cell.vertex_avoid
    S.vertices_injective
  edges := edgeMap S.physical.source.network cell.blob
    (stepBigon S.physical cell.blob cell.nonroot cell.two_ports) S.edges cell.edge_avoid
  edges_injective := edgeMap_injective S.physical.source.network cell.blob
    (stepBigon S.physical cell.blob cell.nonroot cell.two_ports) S.edges cell.edge_avoid
    S.edges_injective
  hybrids := hybridMap S.physical.source.network S.physical.source.cutChild cell.blob
    cell.nonroot (stepBigon S.physical cell.blob cell.nonroot cell.two_ports)
    S.hybrids cell.hybrid_avoid
  hybrids_injective := hybridMap_injective S.physical.source.network S.physical.source.cutChild
    cell.blob cell.nonroot (stepBigon S.physical cell.blob cell.nonroot cell.two_ports)
    S.hybrids cell.hybrid_avoid S.hybrids_injective

inductive MarkedStep : MarkedSource.{u,v,w,a,b,c} X PV PE PH →
    MarkedSource.{u,v,w,a,b,c} X PV PE PH → Prop
  | splice (S : MarkedSource X PV PE PH) (cell : EligibleCell S) : MarkedStep S (next S cell)

abbrev Steps := Relation.ReflTransGen (MarkedStep (X := X) (PV := PV) (PE := PE) (PH := PH))

def Reduced (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) : Prop :=
  ¬ Nonempty (EligibleCell S)

theorem next_graph_step (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (cell : EligibleCell S) :
    G1ActualGraphNormalization.Step S.physical.source (next S cell).physical.source :=
  physicalStep_is_step S.physical cell.blob cell.nonroot cell.two_ports

theorem next_strictly_smaller (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (cell : EligibleCell S) :
    Fintype.card (next S cell).physical.source.Vertex < Fintype.card S.physical.source.Vertex :=
  G1ActualGraphNormalization.actual_step_strictly_smaller (next_graph_step S cell)

theorem next_outer (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (cell : EligibleCell S)
    (hS : HasOuterSemidirectedPartner S.physical.source) :
    HasOuterSemidirectedPartner (next S cell).physical.source :=
  physicalStep_outer S.physical cell.blob cell.nonroot cell.two_ports hS

/-- Strong induction terminates on the actual physical vertex carrier. No
finite-horizon observation or supplied small representative is used. -/
theorem finite_eligible_normalization (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) :
    ∃ T : MarkedSource X PV PE PH, Steps S T ∧ Reduced T := by
  have aux : ∀ n : ℕ, ∀ S : MarkedSource X PV PE PH,
      Fintype.card S.physical.source.Vertex = n →
      ∃ T : MarkedSource X PV PE PH, Steps S T ∧ Reduced T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hn
      by_cases hr : Reduced S
      · exact ⟨S, Relation.ReflTransGen.refl, hr⟩
      · have hex : Nonempty (EligibleCell S) := by
          simpa only [Reduced, not_not] using hr
        obtain ⟨cell⟩ := hex
        have ht : Fintype.card (next S cell).physical.source.Vertex < n :=
          hn ▸ next_strictly_smaller S cell
        obtain ⟨T, hT, hrT⟩ := ih _ ht (next S cell) rfl
        exact ⟨T, (Relation.ReflTransGen.single (MarkedStep.splice S cell)).trans hT, hrT⟩
  exact aux _ S rfl

theorem steps_outer {S T : MarkedSource.{u,v,w,a,b,c} X PV PE PH}
    (steps : Steps S T) (hS : HasOuterSemidirectedPartner S.physical.source) :
    HasOuterSemidirectedPartner T.physical.source := by
  induction steps with
  | refl => exact hS
  | tail prior step ih =>
    cases step with
    | splice cell => exact next_outer _ cell ih

theorem steps_graph {S T : MarkedSource.{u,v,w,a,b,c} X PV PE PH}
    (steps : Steps S T) :
    G1ActualGraphNormalization.Steps S.physical.source T.physical.source := by
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | tail prior step ih =>
    cases step with
    | splice cell => exact ih.tail (next_graph_step _ cell)

/-- The selected G1 trace constructs genuine original-source recipes on the
same final graph. No arbitrary decoration is supplied. Binding marked PE
coordinates to its raw recipes still needs its own trace lemma. -/
theorem steps_original_provenance {S T : MarkedSource.{u,v,w,a,b,c} X PV PE PH}
    (steps : Steps S T) :
    ∃ D : G1DecoratedOriginalProvenance.Decoration S.physical.source T.physical.source,
      G1FiniteOriginalDecoratedCore.Originated S.physical.source S.physical.registry D := by
  exact G1FiniteOriginalDecoratedCore.actual_steps_construct_decorations
    S.physical.source S.physical.registry (steps_graph steps)
    (G1DecoratedOriginalProvenance.initialDecoration S.physical.source)
    G1FiniteOriginalDecoratedCore.Originated.initial

section ExternalRows
variable [DecidableEq X]

/-- Actual source-program forest PMF for a fixed external table, using none
on unmarked sites. No reduced-source-dependent configuration family appears. -/
noncomputable def externalForestLaw {Config Copy : Type*}
    [Fintype Config] [Fintype Copy] [DecidableEq Copy]
    (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (ν : PMF Config) (tables : Config → PH → Option Bool) (sample : Copy → X) :=
  randomizedFullForestLaw S.physical.source.network S.physical.source.calendar
    S.physical.registry S.physical.probabilities S.physical.rates ν
    (fun cfg => labelMask S.hybrids (tables cfg)) sample

theorem next_external_forest {Config Copy : Type*}
    [Fintype Config] [Fintype Copy] [DecidableEq Copy]
    (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (cell : EligibleCell S)
    (ν : PMF Config) (tables : Config → PH → Option Bool) (sample : Copy → X) :
    externalForestLaw (next S cell) ν tables sample = externalForestLaw S ν tables sample := by
  have h := physicalStep_randomized_forest S.physical cell.blob cell.nonroot cell.two_ports
    cell.equal_exposure ν (fun cfg => labelMask S.hybrids (tables cfg)) sample
  rw [splice_external_masks S.physical.source.network S.physical.source.cutChild cell.blob
    cell.nonroot (stepBigon S.physical cell.blob cell.nonroot cell.two_ports)
    S.hybrids S.hybrids_injective cell.hybrid_avoid tables] at h
  exact h

theorem steps_external_forest {Config Copy : Type*}
    [Fintype Config] [Fintype Copy] [DecidableEq Copy]
    {S T : MarkedSource.{u,v,w,a,b,c} X PV PE PH} (steps : Steps S T)
    (ν : PMF Config) (tables : Config → PH → Option Bool) (sample : Copy → X) :
    externalForestLaw T ν tables sample = externalForestLaw S ν tables sample := by
  induction steps with
  | refl => rfl
  | tail prior step ih =>
    cases step with
    | splice cell => exact (next_external_forest _ cell ν tables sample).trans ih

/-- One source and actual original provenance are chosen before every future
permitted external COMMON table and finite original-copy allocation. The
conclusion is eligible reducedness, not the certificate-derived size bound. -/
theorem one_eligible_representative
    (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (hS : HasOuterSemidirectedPartner S.physical.source) :
    ∃ T : MarkedSource X PV PE PH,
      ∃ D : G1DecoratedOriginalProvenance.Decoration S.physical.source T.physical.source,
      Steps S T ∧ Reduced T ∧
      G1FiniteOriginalDecoratedCore.Originated S.physical.source S.physical.registry D ∧
      HasOuterSemidirectedPartner T.physical.source ∧
      (∀ (Config : Type q) [Fintype Config] (Copy : Type k)
        [Fintype Copy] [DecidableEq Copy] (ν : PMF Config)
        (tables : Config → PH → Option Bool) (sample : Copy → X),
        externalForestLaw T ν tables sample = externalForestLaw S ν tables sample) := by
  obtain ⟨T, hT, hrT⟩ := finite_eligible_normalization S
  obtain ⟨D, hD⟩ := steps_original_provenance hT
  refine ⟨T, D, hT, hrT, hD, steps_outer hT hS, ?_⟩
  intro Config _ Copy _ _ ν tables sample
  exact steps_external_forest hT ν tables sample

end ExternalRows

-- Unexecuted future audit requests. No protected/certificate bound is claimed.
#print MarkedSource
#print EligibleCell
#print next
#check finite_eligible_normalization
#print axioms next_graph_step
#print axioms next_strictly_smaller
#print axioms next_outer
#print axioms finite_eligible_normalization
#print axioms steps_outer
#print axioms steps_graph
#print axioms steps_original_provenance
#print axioms next_external_forest
#print axioms steps_external_forest
#check one_eligible_representative
#print axioms one_eligible_representative

end Astra.ProtectedPhysicalIteration
