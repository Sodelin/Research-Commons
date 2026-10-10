import UnifiedLean.Source.SourceForestPulseTransport
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Natural original-current-root Bernoulli pulse under selected-label pruning

Contributor: dot, 2026-10-02. The library Bernoulli product measure is indexed
by the EXISTING actual live tokens at the ORIGINAL hybrid. Restricting to the
visible tokens and reindexing through the proved owner/block equivalence gives
exactly the natural selected-root Bernoulli law. With deterministic source pulse
commutation, the entire selected genealogy/population/register output measure
is equal. No fitted projected pulse or desired-law premise is supplied.
Calendar/continuous-time composition and full stochastic source law remain
separate. UnitInterval endpoints are supported by this general primitive;
admitted strict source parameters select its interior.
-/
namespace UnifiedLean.Source.SourceForestPulseMeasure
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.SourceForestPulseTransport
open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable def bitMeasure (gamma : unitInterval) : Measure Bool :=
  bernoulliMeasure true false gamma

noncomputable def independentCoinMeasure (Site : Type*) [Fintype Site]
    (gamma : unitInterval) : Measure (Site → Bool) :=
  Measure.pi (fun _ : Site => bitMeasure gamma)

instance bitMeasure_probability (gamma : unitInterval) :
    IsProbabilityMeasure (bitMeasure gamma) := by
  unfold bitMeasure
  infer_instance

instance independentCoinMeasure_probability (Site : Type*) [Fintype Site]
    (gamma : unitInterval) : IsProbabilityMeasure (independentCoinMeasure Site gamma) := by
  unfold independentCoinMeasure
  infer_instance

/-- Exact current-root marginalization is a standard product-measure theorem;
extra original live-owner coins are neither refitted nor independently redrawn. -/
theorem coin_restriction_measurePreserving {Site : Type*} [Fintype Site]
    (gamma : unitInterval) (visible : Site → Prop) [DecidablePred visible] :
    MeasurePreserving (fun c : Site → Bool => fun l : {l // visible l} => c l.val)
      (independentCoinMeasure Site gamma)
      (independentCoinMeasure {l // visible l} gamma) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : Site => bitMeasure gamma) visible
  have h2 := measurePreserving_fst
    (μ := Measure.pi (fun _ : {l // visible l} => bitMeasure gamma))
    (ν := Measure.pi (fun _ : {l // ¬ visible l} => bitMeasure gamma))
  exact h2.comp h1

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The actual current original representative coin law transports to the
intrinsic selected current-block law. No selected representative ID is assumed. -/
theorem induced_original_coin_measurePreserving (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) (gamma : unitInterval) :
    MeasurePreserving (inducedBlockCoin s hs keep node)
      (independentCoinMeasure (AtNode s node) gamma)
      (independentCoinMeasure (ViewBlockAtNode (selectedView s keep) keep node) gamma) := by
  have h1 := coin_restriction_measurePreserving gamma
    (fun l : AtNode s node => (selectedBlock s keep l.val).Nonempty)
  unfold independentCoinMeasure at h1 ⊢
  have he : (⇑(MeasurableEquiv.piCongrLeft
        (fun _ : ViewBlockAtNode (selectedView s keep) keep node => Bool)
        (visibleOwnerEquiv s hs keep node))) =
      (fun c : VisibleAtNode s keep node → Bool =>
        fun A : ViewBlockAtNode (selectedView s keep) keep node =>
          c ((visibleOwnerEquiv s hs keep node).symm A)) := by
    funext c A
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have h2 := measurePreserving_piCongrLeft
      (fun _ : ViewBlockAtNode (selectedView s keep) keep node => bitMeasure gamma)
      (visibleOwnerEquiv s hs keep node)
  rw [he] at h2
  exact h2.comp h1

/-- Mathematical output carriers have the discrete sigma algebra. This is
source-state measure encoding, not a physical observation/instrument claim. -/
local instance selectedView_measurable : MeasurableSpace (SelectedView V E Copy) := ⊤

noncomputable def originalPulseLaw {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy)
    (keep : Finset Copy) (gamma : unitInterval) : Measure (SelectedView V E Copy) :=
  (independentCoinMeasure (AtNode s H.hybrid) gamma).map
    (fun coin => selectedView (pulse H s coin) keep)

noncomputable def selectedPulseLaw {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (v : SelectedView V E Copy)
    (keep : Finset Copy) (gamma : unitInterval) : Measure (SelectedView V E Copy) :=
  (independentCoinMeasure (ViewBlockAtNode v keep H.hybrid) gamma).map
    (fun coin => projectedPulse H v keep coin)

/-- Whole selected output law at the actual original hybrid, arbitrary finite
copy panel and arbitrary natural coin parameter. CURRENT block coins are used;
already coalesced selected original copies are never given independent bits. -/
theorem actual_original_hybrid_pulse_projectivity {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (gamma : unitInterval) :
    originalPulseLaw H s keep gamma = selectedPulseLaw H (selectedView s keep) keep gamma := by
  let c := inducedBlockCoin s hs keep H.hybrid
  let out := fun q => projectedPulse H (selectedView s keep) keep q
  have hc : Measurable c := (induced_original_coin_measurePreserving s hs keep H.hybrid gamma).measurable
  have hout : Measurable out := measurable_of_countable out
  have hfun : (fun coin => selectedView (pulse H s coin) keep) = out ∘ c := by
    funext coin
    exact original_pulse_selected_view H s hs keep coin
  unfold originalPulseLaw selectedPulseLaw
  rw [hfun,← Measure.map_map hout hc]
  rw [(induced_original_coin_measurePreserving s hs keep H.hybrid gamma).map_eq]

#print axioms coin_restriction_measurePreserving
#print axioms induced_original_coin_measurePreserving
#print axioms actual_original_hybrid_pulse_projectivity
end UnifiedLean.Source.SourceForestPulseMeasure
