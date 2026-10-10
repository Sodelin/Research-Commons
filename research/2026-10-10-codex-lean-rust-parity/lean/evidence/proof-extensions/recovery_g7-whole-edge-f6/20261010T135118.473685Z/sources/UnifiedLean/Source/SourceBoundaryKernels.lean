import UnifiedLean.Source.SourceFiniteProjection
import UnifiedLean.Source.SourceForestPulseMeasure
import UnifiedLean.Source.SourceForestCommonPulse

/-!
# Actual finite original-node boundary kernels

Contributor: dot, 2026-10-02. Encodes the inherited actual edge exits, ordinary
indegree-one entries, ancestral root entry, CURRENT live-owner independent
Bernoulli pulse, and same-original-register COMMON pulse as finite source PMFs.
No target kernel/readout equality is an input field. The independent-pulse
selected law reuses the already-proved actual product-measure transport.
Calendar ordering and finite-time composition are subsequent original-source
assembly obligations. Selected genealogy/population/register views are internal.
-/
namespace UnifiedLean.Source.SourceBoundaryKernels
open Nanuq.Source GProgram.SourceForest MeasureTheory
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestPulseTransport
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceForestCommonPulse
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Each operation names a genuine ORIGINAL source operation; ordinary entries
retain the inherited indegree-one legality requirement. -/
inductive BoundaryOperation (N : RootedBinary V E X)
  | exit (edge : E)
  | ordinary (edge : E) (degree : N.graph.inDegree (N.graph.target edge) = 1)
  | root
  | independent (parents : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval)
  | common (parents : GProgram.G2.OriginalHybridParents N)

noncomputable def exitCode (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) : Code N sample :=
  admittedCode N sample (exitEdge N (state s) e) (exitEdge_source_valid N sample _ s.property e)

noncomputable def ordinaryCode (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) : Code N sample :=
  admittedCode N sample (enterEdge N (state s) e) (enterEdge_source_valid N sample _ s.property e)

noncomputable def rootCode (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Code N sample :=
  admittedCode N sample (enterRoot N (state s)) (enterRoot_source_valid N sample _ s.property)

noncomputable def pulseCode {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (coin : AtNode (state s) H.hybrid → Bool) : Code N sample :=
  admittedCode N sample (pulse H (state s) coin) (pulse_source_valid H sample _ s.property coin)

noncomputable def currentCoinPMF (Site : Type*) [Fintype Site]
    (gamma : unitInterval) : PMF (Site → Bool) := (independentCoinMeasure Site gamma).toPMF

/-- Exactly CURRENT AtNode owners, not independently re-coined original copies. -/
noncomputable def independentPulseKernel {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval)
    (s : Code N sample) : PMF (Code N sample) :=
  (currentCoinPMF (AtNode (state s) H.hybrid) gamma).map (pulseCode H s)

noncomputable def boundaryKernel (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) (s : Code N sample) : PMF (Code N sample) :=
  match op with
  | .exit e => PMF.pure (exitCode N s e)
  | .ordinary e _ => PMF.pure (ordinaryCode N s e)
  | .root => PMF.pure (rootCode N s)
  | .independent H gamma => independentPulseKernel H gamma s
  | .common H => PMF.pure (pulseCode H s (fun _ => (state s).register H.hybrid))

noncomputable def transportView (v : SelectedView V E Copy) (f : Location V E → Location V E) :
    SelectedView V E Copy :=
  ⟨v.genealogy,fun x => (v.population x).map f,v.register⟩

/-- Actual population transport commutes with full selected INTERNAL view. -/
theorem actual_population_transport_view (s : State V E Copy) (keep : Finset Copy)
    (f : Location V E → Location V E) (event : SourceEvent V E Copy) :
    selectedView (transport s (f ∘ s.location) event) keep = transportView (selectedView s keep) f := by
  apply SelectedView.ext
  · rfl
  · funext x
    by_cases hx : x ∈ keep <;> simp [selectedView,selectedLocation,transportView,
      transport,copyLocation,hx,Function.comp_apply]
  · rfl

noncomputable def exitLocation (N : RootedBinary V E X) (e : E) (p : Location V E) : Location V E :=
  if p = .edge e then .node (N.graph.source e) else p
noncomputable def ordinaryLocation (N : RootedBinary V E X) (e : E) (p : Location V E) : Location V E :=
  if p = .node (N.graph.target e) then .edge e else p
noncomputable def rootLocation (N : RootedBinary V E X) (p : Location V E) : Location V E :=
  if p = .node N.root then .rootPopulation N.root else p

lemma exitCode_view (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (e : E) :
    selectedView (state (exitCode N s e)) keep =
      transportView (selectedView (state s) keep) (exitLocation N e) := by
  rw [show selectedView (state (exitCode N s e)) keep = selectedView (exitEdge N (state s) e) keep from
    decode_encode_selectedView N.root _ (exitEdge_source_valid N sample _ s.property e).forest keep]
  exact actual_population_transport_view _ keep (exitLocation N e) (.edgeExit e)

lemma ordinaryCode_view (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (e : E) :
    selectedView (state (ordinaryCode N s e)) keep =
      transportView (selectedView (state s) keep) (ordinaryLocation N e) := by
  rw [show selectedView (state (ordinaryCode N s e)) keep = selectedView (enterEdge N (state s) e) keep from
    decode_encode_selectedView N.root _ (enterEdge_source_valid N sample _ s.property e).forest keep]
  exact actual_population_transport_view _ keep (ordinaryLocation N e) (.ordinaryEntry e)

lemma rootCode_view (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) :
    selectedView (state (rootCode N s)) keep =
      transportView (selectedView (state s) keep) (rootLocation N) := by
  rw [show selectedView (state (rootCode N s)) keep = selectedView (enterRoot N (state s)) keep from
    decode_encode_selectedView N.root _ (enterRoot_source_valid N sample _ s.property).forest keep]
  exact actual_population_transport_view _ keep (rootLocation N) (.rootEntry N.root)

lemma pulseCode_view {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (keep : Finset Copy)
    (coin : AtNode (state s) H.hybrid → Bool) :
    selectedView (state (pulseCode H s coin)) keep = selectedView (pulse H (state s) coin) keep :=
  decode_encode_selectedView N.root _ (pulse_source_valid H sample _ s.property coin).forest keep

local instance viewMeasurable : MeasurableSpace (SelectedView V E Copy) := ⊤

/-- The constructed finite-code PMF has precisely the existing ACTUAL original
current-owner product-measure pulse output, not a fitted selected distribution. -/
theorem independent_pulse_kernel_view_measure {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval)
    (s : Code N sample) (keep : Finset Copy) :
    ((independentPulseKernel H gamma s).map (fun d => selectedView (state d) keep)).toMeasure =
      selectedPulseLaw H (selectedView (state s) keep) keep gamma := by
  rw [independentPulseKernel,PMF.map_comp]
  have hfun : (fun d : Code N sample => selectedView (state d) keep) ∘ pulseCode H s =
      (fun coin => selectedView (pulse H (state s) coin) keep) := by
    funext coin
    exact pulseCode_view H s keep coin
  rw [hfun,← PMF.toMeasure_map _ _ (measurable_of_countable _),
    currentCoinPMF,Measure.toPMF_toMeasure]
  exact actual_original_hybrid_pulse_projectivity H (state s) s.property.forest keep gamma

/-- Even when invisible source roots exist, the same original-register COMMON
pulse preserves the complete selected view through actual finite source coding. -/
theorem common_boundary_kernel_view {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (keep : Finset Copy) :
    (boundaryKernel N (.common H) s).map (fun d => selectedView (state d) keep) =
      PMF.pure (selectedCommonPulse H (selectedView (state s) keep) keep) := by
  rw [boundaryKernel,PMF.pure_map,pulseCode_view]
  congr 1
  exact actual_common_pulse_pruning H (state s) s.property.forest keep

#print axioms boundaryKernel
#print axioms actual_population_transport_view
#print axioms independent_pulse_kernel_view_measure
#print axioms common_boundary_kernel_view
end UnifiedLean.Source.SourceBoundaryKernels
