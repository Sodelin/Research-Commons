import G7OriginalAdmission
import G6TwoTipChartFixture
import G7OriginalWordFixture

/-!
# The two named calendar sources are exact finite-code decodings

Contributor: Codex / lean_reuse_successor, 2026-10-10.
The fork literal below reuses the exact body of the older coefficient-smoke
candidate, SHA256 7137442eab121c30a486abe70efddbf401135b2a3a9cd0c051232a63ea207ff4.
That incomplete smoke package is not imported. Its incidence/root/taxon data
are identical to the accepted two-tip source; the source field proofs and
no-hybrid theorem are reused directly. The parallel code and registry already
come from the accepted original decoder, so only their named equalities and
original incoming-occurrence map are exposed here.

The exact three request inputs and old/new source bodies are authenticated in
rust/evidence/named-calendar-source-input-capture-1/RECEIPT.json, SHA256
025bf9aa31ff8762382e2144144bf47fe9620a0796531a764b432a138f8b08c4.
These are two fixed typed graph/registry carriers. No generic JSON/parser,
native validator, all-code census or labelled-planarity/cofacial admission
theorem is asserted. No source parameter, calendar, sample, coefficient or
timed-observation claim is inferred from structural equality. This consumer
is pending sole-scheduler kernel checking and complete owned audit.
-/

namespace GProgram.G7.NamedCalendarSourceAdmission

open Nanuq.Source
open GProgram.G7.OriginalAdmission
open UnifiedLean.Source.NativeParentRouting

abbrev N2 := UnifiedLean.G7.OriginalWordFixture.N2
abbrev NP := UnifiedLean.G7.OriginalWordFixture.NP

/-- Original edges 0 and 1, root 0 and taxon leaves 1 and 2; no hybrid IDs. -/
def forkCode : GProgram.G7.OriginalFiniteEncoding.Code (Fin 2) (Fin 0) :=
  ⟨fun _ => ⟨0, by decide⟩, fun e => e.succ, ⟨0, by decide⟩, fun x => x.succ,
    fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩

/-- Reuse every accepted source field, including reachability and LSA. -/
theorem fork_binaryValid : BinaryValid forkCode := by
  exact ⟨N2.leaf.injective, N2.at_least_two_taxa, N2.root_degrees,
    N2.leaf_degrees, N2.internal_degrees, N2.acyclic, N2.rooted, N2.least_stable⟩

theorem fork_registryValid : RegistryValid forkCode := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro v hv
    exact False.elim (UnifiedLean.G6.TwoTipChartFixture.noHybrid ⟨v, hv⟩)
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

theorem fork_cutChild : CutChild forkCode := by
  intro e he
  exact False.elim (UnifiedLean.G6.TwoTipChartFixture.noHybrid
    ⟨(codeGraph forkCode).source e, he⟩)

/-- Identical graph/root/taxon data; all source validity fields are proofs. -/
theorem fork_decodedSource_eq_N2 : sourceOfValid forkCode fork_binaryValid = N2 := by
  rfl

/-- Every registry on this fixed source is its accepted empty registry. -/
theorem registry2_unique (H : OriginalParentRegistry N2) :
    H = UnifiedLean.G7.OriginalWordFixture.registry2 := by
  cases H with
  | mk parents original_site =>
    have hp : parents = UnifiedLean.G7.OriginalWordFixture.registry2.parents := by
      funext h
      exact False.elim (UnifiedLean.G6.TwoTipChartFixture.noHybrid h)
    cases hp
    rfl

theorem fork_decodedRegistry_eq_registry2 :
    (fork_decodedSource_eq_N2 ▸
      decodedRegistry forkCode fork_binaryValid fork_registryValid) =
        UnifiedLean.G7.OriginalWordFixture.registry2 := by
  exact registry2_unique _

/-- NP is already the unchanged accepted code-to-source decoding. -/
theorem parallel_decodedSource_eq_NP :
    sourceOfValid UnifiedLean.G7.OriginalParallelEpochFixture.graphCode
      UnifiedLean.G7.OriginalParallelEpochFixture.graphCode_valid = NP := by
  rfl

theorem parallel_decodedRegistry_eq_named :
    decodedRegistry UnifiedLean.G7.OriginalParallelEpochFixture.graphCode
      UnifiedLean.G7.OriginalParallelEpochFixture.graphCode_valid
      UnifiedLean.G7.OriginalParallelEpochFixture.graphCode_registryValid =
        UnifiedLean.G7.OriginalParallelEpochFixture.registry := by
  rfl

theorem parallel_site_exact :
    (UnifiedLean.G7.OriginalParallelEpochFixture.ids (0 : Fin 1)).val = (3 : Fin 5) := by
  rfl

/-- False selects original edge 2; true selects distinct original edge 3. -/
theorem parallel_parent_exact (b : Bool) :
    UnifiedLean.G7.OriginalBoundaryFixture.parents.parent b =
      if b then (3 : Fin 5) else 2 := by
  exact UnifiedLean.G7.OriginalParallelEpochFixture.parentOccurrence_exact 0 b

#print axioms fork_binaryValid
#print axioms fork_registryValid
#print axioms fork_cutChild
#print axioms fork_decodedSource_eq_N2
#print axioms registry2_unique
#print axioms fork_decodedRegistry_eq_registry2
#print axioms parallel_decodedSource_eq_NP
#print axioms parallel_decodedRegistry_eq_named
#print axioms parallel_site_exact
#print axioms parallel_parent_exact

end GProgram.G7.NamedCalendarSourceAdmission
