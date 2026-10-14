import Astra.ProtectedPhysicalIteration
import G1DecoratedSpliceConstruction

/-!
# Marked original recipes and primitive parameters along physical steps

Source-only, unselected and uncompiled. The decoration is constructed by the
selected G1 splice constructor on the actual marked trace. External label
domains remain fixed; no desired source, law or size bound is a premise.
This refines eligible normalization, not expanded-dependency completeness,
finite-code coverage or the certificate-bounded representative theorem.
-/

namespace Astra.ProtectedPhysicalTrace

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open G1ExactSemidirectedPartnerAdmission
open G1DecoratedOriginalProvenance G1DecoratedSpliceConstruction
open G1FiniteOriginalDecoratedCore
open Astra.PhysicalCommonStep Astra.PhysicalSpliceRates
open Astra.PhysicalSpliceProtectedCoordinates Astra.ProtectedPhysicalIteration
open scoped Classical

universe u v w a b c q k

variable {X : Type w} [Fintype X]
variable {PV : Type a} {PE : Type b} {PH : Type c}

/-- Binding to actual original primitive coordinates. These are hypotheses
about a supplied earlier decoration in the generalized induction, and derived
conclusions when that induction starts at the original source. -/
structure DecorationFrame (O S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (D : Decoration O.physical.source S.physical.source) : Prop where
  vertex_binding : ∀ z, D.vertex (S.vertices z) = O.vertices z
  raw_edge_binding : ∀ z, D.recipe (S.edges z) = Recipe.raw (O.edges z)

/-- Use precisely the selected original-source recipe construction for the
same extracted bigon used in next/physicalStep/G1.splice. -/
noncomputable def nextDecoration
    (O S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (D : Decoration O.physical.source S.physical.source) (cell : EligibleCell S) :
    Decoration O.physical.source (next S cell).physical.source :=
  normalizedSpliceDecoration O.physical.source S.physical.source D O.physical.registry
    cell.blob cell.nonroot cell.two_ports

theorem nextDecoration_vertex (O S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (D : Decoration O.physical.source S.physical.source) (cell : EligibleCell S) (z : PV) :
    (nextDecoration O S D cell).vertex ((next S cell).vertices z) =
      D.vertex (S.vertices z) := rfl

theorem nextDecoration_recipe (O S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (D : Decoration O.physical.source S.physical.source) (cell : EligibleCell S) (z : PE) :
    (nextDecoration O S D cell).recipe ((next S cell).edges z) =
      D.recipe (S.edges z) := rfl

theorem nextDecoration_originated (O S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (D : Decoration O.physical.source S.physical.source) (cell : EligibleCell S)
    (hD : Originated O.physical.source O.physical.registry D) :
    Originated O.physical.source O.physical.registry (nextDecoration O S D cell) :=
  Originated.splice D hD cell.blob cell.nonroot cell.two_ports

theorem nextDecoration_frame (O S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (D : Decoration O.physical.source S.physical.source) (cell : EligibleCell S)
    (hD : DecorationFrame O S D) :
    DecorationFrame O (next S cell) (nextDecoration O S D cell) := by
  constructor
  · intro z
    exact (nextDecoration_vertex O S D cell z).trans (hD.vertex_binding z)
  · intro z
    exact (nextDecoration_recipe O S D cell z).trans (hD.raw_edge_binding z)

/-- Generalized trace induction: retain the caller's original source and
already originated decoration, including its literal marked bindings. -/
theorem steps_extend_marked_decoration
    (O : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    {S T : MarkedSource.{u,v,w,a,b,c} X PV PE PH} (steps : Steps S T)
    (D : Decoration O.physical.source S.physical.source)
    (hD : Originated O.physical.source O.physical.registry D)
    (hframe : DecorationFrame O S D) :
    ∃ K : Decoration O.physical.source T.physical.source,
      Originated O.physical.source O.physical.registry K ∧ DecorationFrame O T K := by
  induction steps with
  | refl => exact ⟨D, hD, hframe⟩
  | @tail U W _ step ih =>
    obtain ⟨K, hK, hKF⟩ := ih
    cases step with
    | splice cell =>
      exact ⟨nextDecoration O U K cell, nextDecoration_originated O U K cell hK,
        nextDecoration_frame O U K cell hKF⟩

theorem initialDecoration_frame (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) :
    DecorationFrame S S (initialDecoration S.physical.source) := by
  constructor <;> intro z <;> rfl

/-- No decoration or recipe equality is supplied to this instantiated result. -/
theorem steps_construct_marked_decoration
    {S T : MarkedSource.{u,v,w,a,b,c} X PV PE PH} (steps : Steps S T) :
    ∃ D : Decoration S.physical.source T.physical.source,
      Originated S.physical.source S.physical.registry D ∧ DecorationFrame S T D :=
  steps_extend_marked_decoration S steps (initialDecoration S.physical.source)
    Originated.initial (initialDecoration_frame S)

/-- Literal numeric primitives on the same fixed external labels. Endpoint
dates are included separately from vertex labels, which need not name every
edge endpoint. No claim about unmarked ties or arbitrary constraints is made. -/
structure ParameterFrame (O S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) : Prop where
  vertex_age : ∀ z, S.physical.source.calendar.age (S.vertices z) =
    O.physical.source.calendar.age (O.vertices z)
  edge_rate : ∀ z, S.physical.rates.edge (S.edges z) = O.physical.rates.edge (O.edges z)
  edge_source_age : ∀ z,
    S.physical.source.calendar.age (S.physical.source.network.graph.source (S.edges z)) =
      O.physical.source.calendar.age (O.physical.source.network.graph.source (O.edges z))
  edge_target_age : ∀ z,
    S.physical.source.calendar.age (S.physical.source.network.graph.target (S.edges z)) =
      O.physical.source.calendar.age (O.physical.source.network.graph.target (O.edges z))
  hybrid_gamma : ∀ z, S.physical.probabilities.gamma (S.hybrids z) =
    O.physical.probabilities.gamma (O.hybrids z)
  ancestral_rate : S.physical.rates.ancestral = O.physical.rates.ancestral

theorem ParameterFrame.refl (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) :
    ParameterFrame S S := by
  constructor <;> first | (intro z; rfl) | rfl

theorem ParameterFrame.trans {O S T : MarkedSource.{u,v,w,a,b,c} X PV PE PH}
    (hOS : ParameterFrame O S) (hST : ParameterFrame S T) : ParameterFrame O T where
  vertex_age z := (hST.vertex_age z).trans (hOS.vertex_age z)
  edge_rate z := (hST.edge_rate z).trans (hOS.edge_rate z)
  edge_source_age z := (hST.edge_source_age z).trans (hOS.edge_source_age z)
  edge_target_age z := (hST.edge_target_age z).trans (hOS.edge_target_age z)
  hybrid_gamma z := (hST.hybrid_gamma z).trans (hOS.hybrid_gamma z)
  ancestral_rate := hST.ancestral_rate.trans hOS.ancestral_rate

/-- Every eligible step preserves these actual values by the existing
retained-coordinate and literal-rate theorems, not by a new fitted tuple. -/
theorem next_parameter_frame (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (cell : EligibleCell S) : ParameterFrame S (next S cell) := by
  constructor
  · intro z
    exact Astra.PhysicalSpliceProtectedCoordinates.vertex_age S.physical.source.network
      S.physical.source.cutChild cell.blob cell.nonroot
      (stepBigon S.physical cell.blob cell.nonroot cell.two_ports) S.physical.source.calendar
      S.vertices cell.vertex_avoid z
  · intro z
    exact Astra.PhysicalSpliceProtectedCoordinates.edge_rate S.physical.source.network
      cell.blob (stepBigon S.physical cell.blob cell.nonroot cell.two_ports)
      S.physical.source.calendar S.physical.rates S.edges cell.edge_avoid z
  · intro z
    exact Astra.PhysicalSpliceProtectedCoordinates.edge_source_age S.physical.source.network
      S.physical.source.cutChild cell.blob cell.nonroot
      (stepBigon S.physical cell.blob cell.nonroot cell.two_ports) S.physical.source.calendar
      S.edges cell.edge_avoid z
  · intro z
    exact Astra.PhysicalSpliceProtectedCoordinates.edge_target_age S.physical.source.network
      S.physical.source.cutChild cell.blob cell.nonroot
      (stepBigon S.physical cell.blob cell.nonroot cell.two_ports) S.physical.source.calendar
      S.edges cell.edge_avoid z
  · intro z
    exact Astra.PhysicalSpliceProtectedCoordinates.hybrid_gamma S.physical.source.network
      S.physical.source.cutChild cell.blob cell.nonroot
      (stepBigon S.physical cell.blob cell.nonroot cell.two_ports) S.physical.probabilities
      S.hybrids cell.hybrid_avoid z
  · exact Astra.PhysicalSpliceRates.ancestral_rate S.physical.source.network
      cell.blob (stepBigon S.physical cell.blob cell.nonroot cell.two_ports)
      S.physical.source.calendar S.physical.rates

theorem steps_parameter_frame {S T : MarkedSource.{u,v,w,a,b,c} X PV PE PH}
    (steps : Steps S T) : ParameterFrame S T := by
  induction steps with
  | refl => exact ParameterFrame.refl _
  | tail prior step ih =>
    cases step with
    | splice cell => exact ParameterFrame.trans ih (next_parameter_frame _ cell)

/-- The same terminal tuple and actual originated decoration have literal
marked recipes/parameters before every future permitted external COMMON row.
Eligible reducedness still supplies no protected/certificate cardinal bound. -/
theorem one_eligible_representative_with_frame [DecidableEq X]
    (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (hS : HasOuterSemidirectedPartner S.physical.source) :
    ∃ T : MarkedSource X PV PE PH,
      ∃ D : Decoration S.physical.source T.physical.source,
      Steps S T ∧ Reduced T ∧ Originated S.physical.source S.physical.registry D ∧
      DecorationFrame S T D ∧ ParameterFrame S T ∧
      HasOuterSemidirectedPartner T.physical.source ∧
      (∀ (Config : Type q) [Fintype Config] (Copy : Type k)
        [Fintype Copy] [DecidableEq Copy] (ν : PMF Config)
        (tables : Config → PH → Option Bool) (sample : Copy → X),
        externalForestLaw T ν tables sample = externalForestLaw S ν tables sample) := by
  obtain ⟨T, hT, hrT⟩ := finite_eligible_normalization S
  obtain ⟨D, hD, hframe⟩ := steps_construct_marked_decoration hT
  refine ⟨T, D, hT, hrT, hD, hframe, steps_parameter_frame hT, steps_outer hT hS, ?_⟩
  intro Config _ Copy _ _ ν tables sample
  exact steps_external_forest hT ν tables sample

-- Unexecuted requests for a future exact interface/axiom audit.
#print DecorationFrame
#print ParameterFrame
#check steps_extend_marked_decoration
#check one_eligible_representative_with_frame
#print axioms nextDecoration_vertex
#print axioms nextDecoration_recipe
#print axioms nextDecoration_originated
#print axioms nextDecoration_frame
#print axioms steps_extend_marked_decoration
#print axioms initialDecoration_frame
#print axioms steps_construct_marked_decoration
#print axioms ParameterFrame.refl
#print axioms ParameterFrame.trans
#print axioms next_parameter_frame
#print axioms steps_parameter_frame
#print axioms one_eligible_representative_with_frame

end Astra.ProtectedPhysicalTrace
