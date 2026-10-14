import G1ActualGraphNormalization
import G1ExactSemidirectedPartnerAdmission
import G1ActualMarkedSemidirectedGalledAdmission
import Astra.PhysicalSpliceCommonLaw
import Astra.PhysicalSpliceControlledLaw

/-!
# One physical COMMON step on the exact existing G1 splice

Source-only proposal, unselected and uncompiled. The bundled graph/calendar
state is literally G1ActualGraphNormalization.Source; its successor is that
module's splice with the same extractedBigon and port-cardinality proof.
Ordered parents, strict probabilities and positive physical rates are built
from that source. No output graph, desired law, protected closure or bound is
supplied. This file proves no iteration or eligibility theorem.
-/

namespace Astra.PhysicalCommonStep

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1CutChildPorts G1ActualTwoPortBlob G1SplicedSourceAdmission
open G1ExactSemidirectedPartnerAdmission G1ActualMarkedSemidirectedGalledAdmission
open GProgram.G7.OriginalSurvivalCoverage
open DotG4.WholeProfileDetermination
open Astra.PhysicalSpliceRates Astra.PhysicalSpliceRegistry
open Astra.PhysicalSpliceCommonLaw Astra.PhysicalSpliceConfiguration
open Astra.PhysicalSpliceControlledLaw
open scoped Classical

universe u v w

/-- The actual G1 graph/cut-child/calendar source plus its physical tuple.
The ordered registry is retained as data, with no canonical parent sorting. -/
structure PhysicalSource (X : Type w) [Fintype X] where
  source : G1ActualGraphNormalization.Source.{u,v,w} X
  registry : OriginalParentRegistry source.network
  probabilities : HybridProbabilities source.network
  rates : PositivePairRates source.Edge

variable {X : Type w} [Fintype X]

/-- Exactly the extraction expression used by the selected G1 splice. -/
noncomputable def stepBigon (S : PhysicalSource.{u,v,w} X)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2) :
    ActualBlobBigon S.source.network b :=
  extractedBigon S.source.network S.source.cutChild b hb
    ((actual_quotient_port_card S.source.network b).symm.trans hp)

/-- This scalar premise is attached to the actual selected bigon. It is not
a desired law equality or a premise that every available splice satisfies it. -/
def EqualArmExposure (S : PhysicalSource.{u,v,w} X)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2) : Prop :=
  exposure S.source.network S.source.calendar S.rates
      (stepBigon S b hb hp).fragment.parents.parent0 =
    exposure S.source.network S.source.calendar S.rates
      (stepBigon S b hb hp).fragment.parents.parent1

/-- No new choice of graph or bigon: the source field is the selected G1
splice, and the other fields use precisely its original extracted cell. -/
noncomputable def physicalStep (S : PhysicalSource.{u,v,w} X)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2) : PhysicalSource.{u,v,w} X where
  source := G1ActualGraphNormalization.splice S.source b hb hp
  registry := splicedRegistry S.source.network S.source.cutChild b hb
    (stepBigon S b hb hp) S.registry
  probabilities := splicedProbabilities S.source.network S.source.cutChild b hb
    (stepBigon S b hb hp) S.probabilities
  rates := splicedRates S.source.network S.source.calendar S.rates b (stepBigon S b hb hp)

theorem physicalStep_source (S : PhysicalSource.{u,v,w} X)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2) :
    (physicalStep S b hb hp).source = G1ActualGraphNormalization.splice S.source b hb hp := rfl

theorem physicalStep_is_step (S : PhysicalSource.{u,v,w} X)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2) :
    G1ActualGraphNormalization.Step S.source (physicalStep S b hb hp).source :=
  G1ActualGraphNormalization.Step.splice S.source b hb hp

theorem physicalStep_vertex_decrement (S : PhysicalSource.{u,v,w} X)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2) :
    Fintype.card (physicalStep S b hb hp).source.Vertex + 2 = Fintype.card S.source.Vertex :=
  G1ActualGraphNormalization.actual_step_vertex_decrement (physicalStep_is_step S b hb hp)

theorem physicalStep_edge_decrement (S : PhysicalSource.{u,v,w} X)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2) :
    Fintype.card (physicalStep S b hb hp).source.Edge + 3 = Fintype.card S.source.Edge :=
  G1ActualGraphNormalization.actual_step_edge_decrement (physicalStep_is_step S b hb hp)

/-- Outer-labelled semidirected admission follows on this same actual output. -/
theorem physicalStep_outer (S : PhysicalSource.{u,v,w} X)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2)
    (hS : HasOuterSemidirectedPartner S.source) :
    HasOuterSemidirectedPartner (physicalStep S b hb hp).source :=
  actual_step_preserves_outer_semidirected_partner (physicalStep_is_step S b hb hp) hS

/-- The selected original marked-hybrid articulation criterion, without a
new galledness premise or a stronger drawing convention. -/
theorem physicalStep_outer_galled (S : PhysicalSource.{u,v,w} X)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2)
    (hS : HasOuterSemidirectedPartner S.source) :
    ∃ P : OuterSemidirectedPartner (physicalStep S b hb hp).source.network,
      BinaryGalledCriterion (physicalStep S b hb hp).source.network P.ports := by
  obtain ⟨P⟩ := physicalStep_outer S b hb hp hS
  exact ⟨P, actual_source_partner_has_galled_admission (physicalStep S b hb hp).source P⟩

section Laws

variable [DecidableEq X]
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

/-- Literal fixed-bank actual source-program forest law from the bundled tuple. -/
noncomputable def fixedForestLaw (S : PhysicalSource.{u,v,w} X)
    (sample : Copy → X) (coin : CommonSeed S.source.network) :
    PMF (Finset (UnrankedTree Copy)) :=
  fixedBankCommonForestLaw S.source.network S.source.calendar S.registry S.probabilities
    S.rates sample coin

noncomputable def naturalForestLaw (S : PhysicalSource.{u,v,w} X) (sample : Copy → X) :
    PMF (Finset (UnrankedTree Copy)) :=
  (originalRegisterMeasure S.source.network S.probabilities).toPMF.bind
    (fixedForestLaw S sample)

theorem physicalStep_fixed_forest (S : PhysicalSource.{u,v,w} X)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2)
    (heq : EqualArmExposure S b hb hp) (sample : Copy → X)
    (coin : CommonSeed S.source.network) :
    fixedForestLaw (physicalStep S b hb hp) sample
        (restrictBank S.source.network S.source.cutChild b hb (stepBigon S b hb hp) coin) =
      fixedForestLaw S sample coin :=
  fixed_bank_common_forest_splice S.source.network S.source.calendar S.registry S.probabilities
    S.source.cutChild b hb (stepBigon S b hb hp) S.rates heq sample coin

theorem physicalStep_natural_forest (S : PhysicalSource.{u,v,w} X)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2)
    (heq : EqualArmExposure S b hb hp) (sample : Copy → X) :
    naturalForestLaw (physicalStep S b hb hp) sample = naturalForestLaw S sample :=
  natural_common_forest_splice S.source.network S.source.calendar S.registry S.probabilities
    S.source.cutChild b hb (stepBigon S b hb hp) S.rates heq sample

/-- Actual controlled source-program PMFs with the derived mask pullback.
This algebraic equality does not authorize deletion of a protected site. -/
theorem physicalStep_controlled_forest (S : PhysicalSource.{u,v,w} X)
    (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2)
    (heq : EqualArmExposure S b hb hp) (mask : OriginalMask S.source.network)
    (sample : Copy → X) :
    controlledFullForestLaw (physicalStep S b hb hp).source.network
        (physicalStep S b hb hp).source.calendar (physicalStep S b hb hp).registry
        (physicalStep S b hb hp).probabilities (physicalStep S b hb hp).rates
        (restrictMask S.source.network S.source.cutChild b hb (stepBigon S b hb hp) mask) sample =
      controlledFullForestLaw S.source.network S.source.calendar S.registry S.probabilities
        S.rates mask sample :=
  controlledFullForestLaw_splice S.source.network S.source.calendar S.registry S.probabilities
    S.source.cutChild b hb (stepBigon S b hb hp) S.rates heq mask sample

/-- The same output tuple precedes every supplied whole configuration PMF,
its complete mask table, and the original labelled copy allocation. -/
theorem physicalStep_randomized_forest {Config : Type*} [Fintype Config]
    (S : PhysicalSource.{u,v,w} X) (b : S.source.network.graph.Blob)
    (hb : b ≠ S.source.network.graph.blobOf S.source.network.root)
    (hp : Fintype.card (S.source.network.BlobPort b) = 2)
    (heq : EqualArmExposure S b hb hp) (ν : PMF Config)
    (masks : Config → OriginalMask S.source.network) (sample : Copy → X) :
    randomizedFullForestLaw (physicalStep S b hb hp).source.network
        (physicalStep S b hb hp).source.calendar (physicalStep S b hb hp).registry
        (physicalStep S b hb hp).probabilities (physicalStep S b hb hp).rates ν
        (restrictMasks S.source.network S.source.cutChild b hb (stepBigon S b hb hp) masks) sample =
      randomizedFullForestLaw S.source.network S.source.calendar S.registry S.probabilities
        S.rates ν masks sample :=
  randomizedFullForestLaw_splice S.source.network S.source.calendar S.registry S.probabilities
    S.source.cutChild b hb (stepBigon S b hb hp) S.rates heq ν masks sample

end Laws

-- Unexecuted future type/axiom audit requests.
#print PhysicalSource
#print physicalStep
#check physicalStep_is_step
#check physicalStep_outer_galled
#check physicalStep_randomized_forest
#print axioms physicalStep_source
#print axioms physicalStep_is_step
#print axioms physicalStep_vertex_decrement
#print axioms physicalStep_edge_decrement
#print axioms physicalStep_outer
#print axioms physicalStep_outer_galled
#print axioms physicalStep_fixed_forest
#print axioms physicalStep_natural_forest
#print axioms physicalStep_controlled_forest
#print axioms physicalStep_randomized_forest

end Astra.PhysicalCommonStep
