import G4ProtectedCommonRepresentative
import StochasticAbstraction

/-!
# Original COMMON physical representatives in fresh-locus experiments

Contributor: dot (OpenAI), 16 October 2026.
SOURCE CANDIDATE ONLY: not compiled or independently reviewed.
Uses existing physical transport and stochastic experiment definitions; no new
generic adaptive-history induction, physical acquisition, or G3/G4 closure.
The generative experiment below explicitly resets at each complete locus.
-/

namespace DotG4.OriginalCommonFreshLocus

noncomputable section
open Nanuq.Source
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1ExactSemidirectedPartnerAdmission
open DotG4.ProtectedCommonRepresentative
open DotG4.WholeProfileDetermination

variable {Y : Type} [Fintype Y]

/-- Each action owns its finite copy/configuration carrier. Its only biological
readout is a declared stochastic channel of the completed unranked forest.
The full configuration is drawn jointly; its hidden label is not exposed. -/
structure CommonRow (O : PhysicalMarkedSource Y) (Out : Type) where
  Copy : Type
  copyFinite : Fintype Copy
  copyDecidable : DecidableEq Copy
  Config : Type
  configFinite : Fintype Config
  weights : PMF Config
  masks : Config → OriginalMask O.marked.source.network
  sample : Copy → Y
  channel : Finset (UnrankedTree Copy) → PMF Out

attribute [instance] CommonRow.copyFinite CommonRow.copyDecidable CommonRow.configFinite

def sourceResponse (O : PhysicalMarkedSource Y) {Out : Type}
    (row : CommonRow O Out) : PMF Out :=
  (randomizedFullForestLaw O.marked.source.network O.marked.source.calendar
    O.registry O.probabilities O.rates row.weights row.masks row.sample).bind row.channel

/-- The same original controls are pulled through ONE source-derived ID map.
No independently fitted PMF or free latent source is supplied. -/
def representativeResponse (O T : PhysicalMarkedSource Y)
    (J : Hybrid T.marked.source.network ↪ Hybrid O.marked.source.network)
    {Out : Type} (row : CommonRow O Out) : PMF Out :=
  (randomizedFullForestLaw T.marked.source.network T.marked.source.calendar
    T.registry T.probabilities T.rates row.weights
    (fun cfg h => row.masks cfg (J h)) row.sample).bind row.channel

/-- A fresh completed-locus draw. There is no latent state retained between
calls. Physical parameters remain in the fixed response function. -/
def resetKernel {Act Out : Type} (response : Act → PMF Out) :
    Act → Unit → PMF (Unit × Out) :=
  fun a _ => (response a).map (fun o => ((), o))

/-- The initial value is a common source-independent seed/sentinel. The
record contains actions and permitted outputs, never configuration/register
labels or internal genealogy states. -/
def transcript {Act Out : Type} (response : Act → PMF Out)
    (policy : StochasticAbstraction.Policy Out Act) (n : Nat)
    (initial : PMF Out) : PMF (List (Out × Act) × Out) :=
  (StochasticAbstraction.experimentLaw
    (StochasticAbstraction.sensorStep (resetKernel response))
    (StochasticAbstraction.observationPolicy Prod.snd policy) n
    (initial.map (fun o => ((), o)))).map (StochasticAbstraction.view Prod.snd)

/-- A source-specific composition: one physical tuple, one J, and provenance
are fixed before every future typed menu and adaptive protocol. The physical
transport theorem supplies the needed equality; it is not a hypothesis here.
Outer source admission is explicitly retained. COMMON only. -/
theorem physicalSteps_fresh_locus_transcripts
    (O T : PhysicalMarkedSource Y) (steps : PhysicalSteps O T)
    (outer : HasOuterSemidirectedPartner O.marked.source) :
    HasOuterSemidirectedPartner T.marked.source ∧
    ∃ J : Hybrid T.marked.source.network ↪ Hybrid O.marked.source.network,
    ∃ D : G1DecoratedOriginalProvenance.Decoration O.marked.source T.marked.source,
      PhysicalPrimitiveProvenance O T J D ∧
      (∀ h, J h ∈ O.marked.marks.hybrids ↔ h ∈ T.marked.marks.hybrids) ∧
      ∀ (Act Out : Type) (rows : Act → CommonRow O Out)
        (policy : StochasticAbstraction.Policy Out Act) (n : Nat) (initial : PMF Out),
        transcript (fun a => representativeResponse O T J (rows a)) policy n initial =
        transcript (fun a => sourceResponse O (rows a)) policy n initial := by
  refine ⟨markedSteps_outer (physicalSteps_marked steps) outer, ?_⟩
  obtain ⟨J, D, provenance, marks, laws⟩ := physicalSteps_complete_transport O T steps
  refine ⟨J, D, provenance, marks, ?_⟩
  intro Act Out rows policy n initial
  have responses : (fun a => representativeResponse O T J (rows a)) =
      (fun a => sourceResponse O (rows a)) := by
    funext a
    exact congrArg (fun p : PMF (Finset (UnrankedTree (rows a).Copy)) =>
      p.bind (rows a).channel)
      (laws (rows a).Copy (rows a).Config (rows a).weights (rows a).masks (rows a).sample)
  exact congrArg (fun r => transcript r policy n initial) responses

end
end DotG4.OriginalCommonFreshLocus
