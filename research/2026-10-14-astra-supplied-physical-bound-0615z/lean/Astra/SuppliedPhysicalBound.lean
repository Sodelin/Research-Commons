import Astra.TerminalPhysicalBudget
import Astra.ProtectedPhysicalTrace
import Astra.SuppliedCommonCertificates
import Astra.PhysicalSpliceControlledLaw

/-! Source-only supplied-certificate physical bound with fixed external IDs.
An actual possible realizer is universally quantified after the supplied
certificate and fixed PE/PH budget. Its representative is constructed before
every future permitted COMMON row. This does not recover provider0616, supply
finite-code coverage or decide exact physical feasibility. -/
namespace Astra.SuppliedPhysicalBound

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1ExactSemidirectedPartnerAdmission
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.OriginalFixedIDControls
open DotG4.WholeProfileDetermination
open DotG4.ActualObservableBankCertificate DotG4.ActualSparseCertificateExistence
open DotG4.ActualLegalPanelComb
open Astra.PhysicalCommonStep Astra.ProtectedPhysicalIteration
open Astra.PhysicalSpliceExternalMasks Astra.PhysicalSpliceControlledLaw
open Astra.ProtectedPhysicalTrace Astra.TerminalPhysicalBudget
open Astra.SuppliedCommonCertificates
open scoped Classical

universe u v w a b c q k
variable {X : Type w} [Fintype X] [DecidableEq X]
variable {PV : Type a} {PE : Type b} {PH : Type c}
variable [Fintype PV] [Fintype PE] [Fintype PH]

noncomputable def externalTreeLaw {Config : Type*} [Fintype Config]
    (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (ν : PMF Config) (tables : Config → PH → Option Bool) :=
  randomizedTreeLaw S.physical.source.network S.physical.source.calendar
    S.physical.registry S.physical.probabilities S.physical.rates ν
    (fun cfg => labelMask S.hybrids (tables cfg))

theorem next_external_tree {Config : Type*} [Fintype Config]
    (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH) (cell : EligibleCell S)
    (ν : PMF Config) (tables : Config → PH → Option Bool) :
    externalTreeLaw (next S cell) ν tables = externalTreeLaw S ν tables := by
  have h := randomizedTreeLaw_splice S.physical.source.network S.physical.source.calendar
    S.physical.registry S.physical.probabilities S.physical.source.cutChild
    cell.blob cell.nonroot (stepBigon S.physical cell.blob cell.nonroot cell.two_ports)
    S.physical.rates cell.equal_exposure ν (fun cfg => labelMask S.hybrids (tables cfg))
  rw [splice_external_masks S.physical.source.network S.physical.source.cutChild
    cell.blob cell.nonroot (stepBigon S.physical cell.blob cell.nonroot cell.two_ports)
    S.hybrids S.hybrids_injective cell.hybrid_avoid tables] at h
  exact h

theorem steps_external_tree {Config : Type*} [Fintype Config]
    {S T : MarkedSource.{u,v,w,a,b,c} X PV PE PH} (steps : Steps S T)
    (ν : PMF Config) (tables : Config → PH → Option Bool) :
    externalTreeLaw T ν tables = externalTreeLaw S ν tables := by
  induction steps with
  | refl => rfl
  | tail prior step ih =>
    cases step with
    | splice cell => exact (next_external_tree _ cell ν tables).trans ih

/-- Apply the same exact forest-law transport to the already defined padded
comb event. No new observable or unknown target value is requested. -/
theorem steps_legal_moment {Config : Type*} [Fintype Config]
    {S T : MarkedSource.{u,v,w,a,b,c} X PV PE PH} (steps : Steps S T)
    (ν : PMF Config) (tables : Config → PH → Option Bool) (i j : X) (level : Nat) :
    randomizedLegalCombMoment T.physical.source.network T.physical.source.calendar
        T.physical.registry T.physical.probabilities T.physical.rates ν
        (fun cfg => labelMask T.hybrids (tables cfg)) i j level =
      randomizedLegalCombMoment S.physical.source.network S.physical.source.calendar
        S.physical.registry S.physical.probabilities S.physical.rates ν
        (fun cfg => labelMask S.hybrids (tables cfg)) i j level := by
  have h := steps_external_forest steps ν tables (paddedSample level i j)
  unfold externalForestLaw at h
  unfold randomizedLegalCombMoment
  rw [h]

/-- The exact supplied certificate, unchanged external encoding and physical
trace give the accepted safe numeric bound. Expanded protection means every
fixed/tied/controlled dependency is already in PE/PH; the theorem does not
discover or certify adequacy of an arbitrary parser's declared-ID set.

PV is empty in this accepted specialization; endpoint dates are protected via
PE. The n>=4 domain is retained even though some intermediate lemmas are
stronger. No realizing source is asserted to exist by the supplied record. -/
theorem supplied_certificate_bounded_representative [IsEmpty PV]
    (cert : SuppliedCombCertificates X)
    (h : Nat) (hlabels : Fintype.card PE + Fintype.card PH ≤ h)
    (_hn : 4 ≤ Fintype.card X)
    (S : MarkedSource.{u,v,w,a,b,c} X PV PE PH)
    (houter : HasOuterSemidirectedPartner S.physical.source)
    {Config : Type q} [Fintype Config] (ν : PMF Config)
    (tables : Config → PH → Option Bool)
    (hmatch : ∀ i j level, level ∈ momentLevels (cert.level (i,j)) →
      randomizedLegalCombMoment S.physical.source.network S.physical.source.calendar
        S.physical.registry S.physical.probabilities S.physical.rates ν
        (fun cfg => labelMask S.hybrids (tables cfg)) i j level = cert.value (i,j) level) :
    ∃ T : MarkedSource X PV PE PH,
      ∃ D : Decoration S.physical.source T.physical.source,
      Steps S T ∧ Reduced T ∧ Originated S.physical.source S.physical.registry D ∧
      DecorationFrame S T D ∧ ParameterFrame S T ∧
      HasOuterSemidirectedPartner T.physical.source ∧
      Fintype.card (Hybrid T.physical.source.network) ≤ hybridBudget cert h ∧
      (∀ (Cfg : Type q) [Fintype Cfg] (μ : PMF Cfg)
        (controls : Cfg → PH → Option Bool), externalTreeLaw T μ controls = externalTreeLaw S μ controls) ∧
      (∀ (Cfg : Type q) [Fintype Cfg] (Copy : Type k)
        [Fintype Copy] [DecidableEq Copy] (μ : PMF Cfg)
        (controls : Cfg → PH → Option Bool) (sample : Copy → X),
        externalForestLaw T μ controls sample = externalForestLaw S μ controls sample) := by
  obtain ⟨T, hST, hrT⟩ := finite_eligible_normalization S
  obtain ⟨D, hD, hframe⟩ := steps_construct_marked_decoration hST
  have hm (i j : X) (level : Nat) (hl : level ∈ momentLevels (cert.level (i,j))) :
      randomizedLegalCombMoment T.physical.source.network T.physical.source.calendar
        T.physical.registry T.physical.probabilities T.physical.rates ν
        (fun cfg => labelMask T.hybrids (tables cfg)) i j level = cert.value (i,j) level :=
    (steps_legal_moment hST ν tables i j level).trans (hmatch i j level hl)
  obtain ⟨cfg, _, hcover⟩ := one_supported_configuration cert T.physical.source.network
    T.physical.source.calendar T.physical.registry T.physical.probabilities T.physical.rates
    ν (fun cfg => labelMask T.hybrids (tables cfg)) hm
  have hgrid (coin) (i j : X) :
      directedSurvival (maskedNormalizedTree T.physical.source.network T.physical.source.calendar
        T.physical.registry T.physical.rates (labelMask T.hybrids (tables cfg)) coin) i j ∈
        certificateGrid cert (i,j) := by
    rw [maskedNormalizedTree_survival T.physical.source.network T.physical.source.calendar
      T.physical.registry T.physical.probabilities T.physical.rates]
    exact hcover coin i j
  have hb := reduced_physical_hybrid_bound T hrT h hlabels (tables cfg)
    (certificateGrid cert) (supportCap cert) (certificateGrid_card_le cert) hgrid
  refine ⟨T, D, hST, hrT, hD, hframe, steps_parameter_frame hST,
    steps_outer hST houter, hb, ?_, ?_⟩
  · intro Cfg _ μ controls
    exact steps_external_tree hST μ controls
  · intro Cfg _ Copy _ _ μ controls sample
    exact steps_external_forest hST μ controls sample

#print externalTreeLaw
#print axioms next_external_tree
#print axioms steps_external_tree
#print axioms steps_legal_moment
#print axioms supplied_certificate_bounded_representative

end Astra.SuppliedPhysicalBound
