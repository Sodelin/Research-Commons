import G7OriginalAdmission
import Astra.ProtectedPhysicalTrace
import Mathlib.Data.Fintype.Sigma

/-!
Source-only finite code coverage for an actual marked source with a separately
proved hybrid bound. The finite carrier reuses the selected complete original
registry code and keeps fixed external PE/PH labels. No outer-admission oracle,
certificate-derived bound or unknown representative is assumed in a master
conclusion here: this is only the downstream code-coverage sublemma.
-/
namespace Astra.ProtectedFiniteCodeCoverage

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source
open UnifiedLean.Source.NativeParentRouting
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1ExactSemidirectedPartnerAdmission
open Astra.ProtectedPhysicalIteration Astra.ProtectedPhysicalTrace
open scoped Classical

universe u v w a b c

/-- Existing complete graph/ordered-registry code, with two fixed external
label maps. No graph occurrence or original parent bit is identified. -/
abbrev CodeWithLabels (X : Type w) (PE : Type b) (PH : Type c)
    [Fintype X] (r : Nat) :=
  GProgram.G7.OriginalFiniteEncoding.Code X (Fin r) ×
    (PE → Fin (edgeCount (Fintype.card X) r)) × (PH → Fin r)

/-- All bounded registry sizes, including zero hybrids, with the same taxon
and external label domains for every candidate. -/
abbrev BoundedCode (X : Type w) (PE : Type b) (PH : Type c)
    [Fintype X] (B : Nat) :=
  Σ rr : Fin (B + 1), CodeWithLabels X PE PH rr.val

variable {X : Type w} [Fintype X] [DecidableEq X]
variable {PV : Type a} {PE : Type b} {PH : Type c}
variable [Fintype PE] [Fintype PH]

/-- Only the selected binary/LSA/cut-child/complete-registry filter and
injective PE/PH labels. No outer, parameter or source-law test is hidden here. -/
def RegistryAndLabelsValid {B : Nat} (c : BoundedCode X PE PH B) : Prop :=
  c.2.1 ∈ (registeredBinaryCutChildCodes :
    Finset (GProgram.G7.OriginalFiniteEncoding.Code X (Fin c.1.val))) ∧
  Function.Injective c.2.2.1 ∧ Function.Injective c.2.2.2

noncomputable def boundedCodes (X : Type w) (PE : Type b) (PH : Type c)
    [Fintype X] [DecidableEq X] [Fintype PE] [Fintype PH] (B : Nat) :
    Finset (BoundedCode X PE PH B) :=
  Finset.univ.filter RegistryAndLabelsValid

/-- The actual source cardinality, not a guessed or partially named registry. -/
def boundedRank (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (B : Nat)
    (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) : Fin (B + 1) :=
  ⟨Fintype.card (Hybrid S.physical.source.network), Nat.lt_succ_of_le hB⟩

noncomputable def rankIDs (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (B : Nat)
    (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) :
    Fin (boundedRank S B hB).val ≃ Hybrid S.physical.source.network :=
  (Fintype.equivFin (Hybrid S.physical.source.network)).symm

/-- A cardinal-index normalization of the existing accepted edgeNumbering.
It does not use the unavailable provider's finiteEdgeNumbering declaration. -/
noncomputable def numberedEdges (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (B : Nat)
    (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) :
    S.physical.source.Edge ≃ Fin (edgeCount (Fintype.card X) (boundedRank S B hB).val) := by
  simpa only [Fintype.card_fin] using edgeNumbering S.physical.source.network (rankIDs S B hB)

noncomputable def edgeLabels (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (B : Nat)
    (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) :
    PE → Fin (edgeCount (Fintype.card X) (boundedRank S B hB).val) :=
  fun z => numberedEdges S B hB (S.edges z)

noncomputable def hybridLabels (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (B : Nat)
    (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) :
    PH → Fin (boundedRank S B hB).val :=
  fun z => (rankIDs S B hB).symm (S.hybrids z)

noncomputable def encoded (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (B : Nat)
    (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) : BoundedCode X PE PH B :=
  ⟨boundedRank S B hB,
    encode S.physical.source.network (rankIDs S B hB) S.physical.registry,
    edgeLabels S B hB, hybridLabels S B hB⟩

theorem edgeLabels_injective (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (B : Nat)
    (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) :
    Function.Injective (edgeLabels S B hB) :=
  (numberedEdges S B hB).injective.comp S.edges_injective

theorem hybridLabels_injective (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (B : Nat)
    (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) :
    Function.Injective (hybridLabels S B hB) :=
  (rankIDs S B hB).symm.injective.comp S.hybrids_injective

theorem encoded_valid (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (B : Nat)
    (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) :
    RegistryAndLabelsValid (encoded S B hB) :=
  ⟨every_registered_source_survives_filter S.physical.source.network (rankIDs S B hB)
      S.physical.registry S.physical.source.cutChild,
    edgeLabels_injective S B hB, hybridLabels_injective S B hB⟩

/-- Coverage of the exact actual source, registry and external label maps. -/
theorem encoded_mem (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (B : Nat)
    (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) :
    encoded S B hB ∈ boundedCodes X PE PH B :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, encoded_valid S B hB⟩

theorem encoded_edge_decode (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (B : Nat)
    (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) (z : PE) :
    (numberedEdges S B hB).symm ((encoded S B hB).2.2.1 z) = S.edges z :=
  (numberedEdges S B hB).symm_apply_apply (S.edges z)

theorem encoded_hybrid_decode (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (B : Nat)
    (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) (z : PH) :
    rankIDs S B hB ((encoded S B hB).2.2.2 z) = S.hybrids z :=
  (rankIDs S B hB).apply_symm_apply (S.hybrids z)

theorem encoded_raw_recipe {O S : MarkedSource.{u,v,w,a,b,c} X PV PE PH}
    (D : Decoration O.physical.source S.physical.source) (frame : DecorationFrame O S D)
    (B : Nat) (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) (z : PE) :
    D.recipe ((numberedEdges S B hB).symm ((encoded S B hB).2.2.1 z)) =
      Recipe.raw (O.edges z) := by
  rw [encoded_edge_decode]
  exact frame.raw_edge_binding z

/-- Trace-instantiated coverage builds the originated decoration and raw
marked bindings. The actual outer witness stays on S as a separate conjunct;
membership of arbitrary codes is not asserted to decide that predicate.
The separately proved actual-source bound hB remains this sublemma's input. -/
theorem trace_code_coverage {O S : MarkedSource.{u,v,w,a,b,c} X PV PE PH}
    (steps : Steps O S) (outer : HasOuterSemidirectedPartner O.physical.source)
    (B : Nat) (hB : Fintype.card (Hybrid S.physical.source.network) ≤ B) :
    ∃ D : Decoration O.physical.source S.physical.source,
      Originated O.physical.source O.physical.registry D ∧ DecorationFrame O S D ∧
      ParameterFrame O S ∧ HasOuterSemidirectedPartner S.physical.source ∧
      encoded S B hB ∈ boundedCodes X PE PH B ∧
      (∀ z, D.recipe ((numberedEdges S B hB).symm ((encoded S B hB).2.2.1 z)) =
        Recipe.raw (O.edges z)) ∧
      (∀ z, rankIDs S B hB ((encoded S B hB).2.2.2 z) = S.hybrids z) := by
  obtain ⟨D, hD, frame⟩ := steps_construct_marked_decoration steps
  exact ⟨D, hD, frame, steps_parameter_frame steps, steps_outer steps outer,
    encoded_mem S B hB, encoded_raw_recipe D frame B hB, encoded_hybrid_decode S B hB⟩

#print axioms encoded_valid
#print axioms encoded_mem
#print axioms encoded_raw_recipe
#print axioms trace_code_coverage

end Astra.ProtectedFiniteCodeCoverage
