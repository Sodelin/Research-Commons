import Astra.ProtectedPhysicalIteration
import Astra.PhysicalSpliceControlledLaw

/-! Source-only uniform original-hybrid transport along actual eligible steps.
The embedding is chosen from the actual trace before all future configuration
PMFs, mask tables and finite copy allocations. No data are extracted from a
Prop-valued trace into Type: the final construction is existential in Prop.
These are COMMON laws, not an INDEPENDENT or timed-law assertion. -/
namespace Astra.RetainedHybridTrace

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.OriginalFixedIDControls
open DotG4.WeightedOrdinaryTreeLaw DotG4.WholeProfileDetermination
open Astra.PhysicalCommonStep Astra.ProtectedPhysicalIteration
open Astra.PhysicalSpliceRegistry Astra.PhysicalSpliceConfiguration
open Astra.PhysicalSpliceProtectedCoordinates Astra.PhysicalSpliceExternalMasks
open Astra.PhysicalSpliceControlledLaw
open scoped Classical

universe u v w a b c q k
variable {X : Type w} [Fintype X] [DecidableEq X]
variable {PV : Type a} {PE : Type b} {PH : Type c}

/-- Literal retained-hybrid embedding for exactly the next physical tuple. -/
noncomputable def nextHybridEmbedding
    (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (cell : EligibleCell S) :
    Hybrid (next S cell).physical.source.network ↪ Hybrid S.physical.source.network :=
  retainedHybrid S.physical.source.network S.physical.source.cutChild cell.blob
    cell.nonroot (stepBigon S.physical cell.blob cell.nonroot cell.two_ports)

/-- A property of a specified injection, with every future row quantified
inside the property. The source tuple, original parent order and one whole ν
are retained; no user configuration distribution is factored or normalized. -/
structure Transport (S T : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (J : Hybrid T.physical.source.network ↪ Hybrid S.physical.source.network) : Prop where
  labels : ∀ z, J (T.hybrids z) = S.hybrids z
  gamma : ∀ h, T.physical.probabilities.gamma h = S.physical.probabilities.gamma (J h)
  tree : ∀ (Config : Type q) [Fintype Config] (ν : PMF Config)
    (masks : Config → OriginalMask S.physical.source.network),
    randomizedTreeLaw T.physical.source.network T.physical.source.calendar
        T.physical.registry T.physical.probabilities T.physical.rates ν
        (fun cfg h => masks cfg (J h)) =
      randomizedTreeLaw S.physical.source.network S.physical.source.calendar
        S.physical.registry S.physical.probabilities S.physical.rates ν masks
  forest : ∀ (Config : Type q) [Fintype Config] (Copy : Type k)
    [Fintype Copy] [DecidableEq Copy] (ν : PMF Config)
    (masks : Config → OriginalMask S.physical.source.network) (sample : Copy → X),
    randomizedFullForestLaw T.physical.source.network T.physical.source.calendar
        T.physical.registry T.physical.probabilities T.physical.rates ν
        (fun cfg h => masks cfg (J h)) sample =
      randomizedFullForestLaw S.physical.source.network S.physical.source.calendar
        S.physical.registry S.physical.probabilities S.physical.rates ν masks sample

theorem transport_refl (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) :
    Transport.{u,v,w,a,b,c,q,k} S S (Function.Embedding.refl _) := by
  constructor
  · intro z; rfl
  · intro h; rfl
  · intro Config _ ν masks; rfl
  · intro Config _ Copy _ _ ν masks sample; rfl

/-- The actual one-step laws are imported proofs; no desired-law premise is
added to the eligible cell. Equal arm exposure was already its local field. -/
theorem next_transport (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (cell : EligibleCell S) :
    Transport.{u,v,w,a,b,c,q,k} S (next S cell) (nextHybridEmbedding S cell) := by
  constructor
  · intro z
    exact hybridMap_original S.physical.source.network S.physical.source.cutChild
      cell.blob cell.nonroot (stepBigon S.physical cell.blob cell.nonroot cell.two_ports)
      S.hybrids cell.hybrid_avoid z
  · intro h
    exact splicedProbabilities_gamma S.physical.source.network S.physical.source.cutChild
      cell.blob cell.nonroot (stepBigon S.physical cell.blob cell.nonroot cell.two_ports)
      S.physical.probabilities h
  · intro Config _ ν masks
    exact randomizedTreeLaw_splice S.physical.source.network S.physical.source.calendar
      S.physical.registry S.physical.probabilities S.physical.source.cutChild
      cell.blob cell.nonroot (stepBigon S.physical cell.blob cell.nonroot cell.two_ports)
      S.physical.rates cell.equal_exposure ν masks
  · intro Config _ Copy _ _ ν masks sample
    exact physicalStep_randomized_forest S.physical cell.blob cell.nonroot cell.two_ports
      cell.equal_exposure ν masks sample

/-- Compose the same literal injection in the PH frame, gamma parameters and
both PMF laws. Pullback composition introduces no new configuration identity. -/
theorem Transport.trans
    {S T U : MarkedSource.{u,v,w,a,b,c} X PV PE PH}
    {J : Hybrid T.physical.source.network ↪ Hybrid S.physical.source.network}
    {K : Hybrid U.physical.source.network ↪ Hybrid T.physical.source.network}
    (hJ : Transport.{u,v,w,a,b,c,q,k} S T J)
    (hK : Transport.{u,v,w,a,b,c,q,k} T U K) :
    Transport.{u,v,w,a,b,c,q,k} S U (K.trans J) := by
  constructor
  · intro z
    change J (K (U.hybrids z)) = S.hybrids z
    rw [hK.labels, hJ.labels]
  · intro h
    exact (hK.gamma h).trans (hJ.gamma (K h))
  · intro Config _ ν masks
    exact (hK.tree Config ν (fun cfg h => masks cfg (J h))).trans (hJ.tree Config ν masks)
  · intro Config _ Copy _ _ ν masks sample
    exact (hK.forest Config Copy ν (fun cfg h => masks cfg (J h)) sample).trans
      (hJ.forest Config Copy ν masks sample)

/-- One actual retained-hybrid injection for the whole trace, before every
future ν, original mask program and finite labelled copy allocation. -/
theorem steps_retained_hybrid
    {S T : MarkedSource.{u,v,w,a,b,c} X PV PE PH} (steps : Steps S T) :
    ∃ J : Hybrid T.physical.source.network ↪ Hybrid S.physical.source.network,
      Transport.{u,v,w,a,b,c,q,k} S T J := by
  induction steps with
  | refl => exact ⟨Function.Embedding.refl _, transport_refl _⟩
  | tail prior step ih =>
    cases step with
    | splice cell =>
      obtain ⟨J, hJ⟩ := ih
      exact ⟨(nextHybridEmbedding _ cell).trans J, hJ.trans (next_transport _ cell)⟩

/-- The same fixed external PH table agrees pointwise under the trace
embedding, including none off the labelled image. This adds no new labels. -/
theorem Transport.external_mask
    {S T : MarkedSource.{u,v,w,a,b,c} X PV PE PH}
    {J : Hybrid T.physical.source.network ↪ Hybrid S.physical.source.network}
    (hJ : Transport.{u,v,w,a,b,c,q,k} S T J) (table : PH → Option Bool) :
    (fun h => labelMask S.hybrids table (J h)) = labelMask T.hybrids table :=
  labelMask_restrict J S.hybrids T.hybrids S.hybrids_injective hJ.labels table

-- Future type/axiom audit requests, not execution receipts.
#print Transport
#check steps_retained_hybrid
#print axioms next_transport
#print axioms Transport.trans
#print axioms steps_retained_hybrid
#print axioms Transport.external_mask

end Astra.RetainedHybridTrace
