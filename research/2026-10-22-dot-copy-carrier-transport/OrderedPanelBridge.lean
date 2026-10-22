import CopyCarrierTransport
import G7WholeAncestorPanelCode
import G7EffectivePanelJoin

/- dot, 2026-10-22. Unelaborated source proposal.
Instantiation at the original ancestor-closed panel Code, not a new source law.
The supplied enumeration must still be identified with the actual native list. -/
namespace Dot.OrderedPanelBridge
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.WholeAncestorPanelCode
open GProgram.G7.PopulationForestReassembly
open GProgram.G7.ConstructivePanelJoin
open GProgram.G7.EffectivePanelJoin

variable {V E X A B : Type*}
variable [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B]
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

def view (e : A ≃ B) (v : SelectedView V E A) : SelectedView V E B where
  genealogy y := (v.genealogy (e.symm y)).map (mapLabels e)
  population y := v.population (e.symm y)
  register := v.register

theorem view_inverse (e : A ≃ B) (v : SelectedView V E A) :
    view e.symm (view e v) = v := by
  apply SelectedView.ext
  · funext x
    simp only [view, Equiv.symm_symm, Equiv.symm_apply_apply, Option.map_map]
    cases h : v.genealogy x with
    | none => rfl
    | some t => simp [Dot.CopyCarrierTransport.labels_inverse]
  · funext x
    simp [view]
  · rfl

theorem full_view_transport (e : A ≃ B) (s : State V E A) :
    selectedView (Dot.CopyCarrierTransport.state e s) Finset.univ =
      view e (selectedView s Finset.univ) := by
  apply SelectedView.ext
  · funext y
    simp [view, Dot.CopyCarrierTransport.state, selectedView, selectedGenealogy,
      full_prune]
  · funext y
    simp [view, Dot.CopyCarrierTransport.state, selectedView, selectedLocation,
      copyLocation]
  · rfl

theorem code_full_view_transport (N : RootedBinary V E X) (e : A ≃ B)
    {sample : A → X} (s : Code N sample) :
    selectedView (state (Dot.CopyCarrierTransport.code N e s)) Finset.univ =
      view e (selectedView (state s) Finset.univ) := by
  change selectedView (decode N.root (Dot.CopyCarrierTransport.code N e s).val)
      Finset.univ = view e (selectedView (decode N.root s.val) Finset.univ)
  rw [Dot.CopyCarrierTransport.code_state]
  exact full_view_transport e _

/-- Original panel Code, represented in the exact local ordered-list carrier. -/
noncomputable def localPanelCode (N : RootedBinary V E X) {sample : A → X}
    (s : Code N sample) (keep : Finset A) (hc : AncestorClosed (state s) keep)
    {m : Nat} (e : Fin m ≃ SelectedCopy keep) :
    Code N ((selectedSample sample keep) ∘ e) :=
  Dot.CopyCarrierTransport.code N e.symm (panelCode N s keep hc)

/-- Snapshot identity, retaining canonical option fields of the original panel.
This exposes the exact constructor to compare against native restriction. -/
theorem localPanelCode_snapshot (N : RootedBinary V E X) {sample : A → X}
    (s : Code N sample) (keep : Finset A) (hc : AncestorClosed (state s) keep)
    {m : Nat} (e : Fin m ≃ SelectedCopy keep) :
    (localPanelCode N s keep hc e).val =
      Dot.CopyCarrierTransport.snapshot e.symm
        (encodeSnapshot (restrictState (state s) s.property.forest keep hc)
          (restrictState_valid (state s) s.property.forest keep hc)) := rfl

/-- Return the local selected view to the original IDs, then use the original
subtype lift. The result is the exact original panel view. -/
theorem localPanelCode_view (N : RootedBinary V E X) {sample : A → X}
    (s : Code N sample) (keep : Finset A) (hc : AncestorClosed (state s) keep)
    {m : Nat} (e : Fin m ≃ SelectedCopy keep) :
    liftView keep (view e
      (selectedView (state (localPanelCode N s keep hc e)) Finset.univ)) =
      selectedView (state s) keep := by
  unfold localPanelCode
  rw [code_full_view_transport]
  have h := view_inverse e.symm
    (selectedView (state (panelCode N s keep hc)) Finset.univ)
  simp only [Equiv.symm_symm] at h
  rw [h]
  exact (panelCode_view N s keep hc).symm

variable [FinEnum V] [FinEnum E]

/-- Per-destination polynomial transport in the actual original panel API.
This does not discard any original admitted destination. -/
theorem localPanelCode_coefficients (N : RootedBinary V E X) {sample : A → X}
    (s : Code N sample) (keep : Finset A) (hc : AncestorClosed (state s) keep)
    {m : Nat} (e : Fin m ≃ SelectedCopy keep)
    [FinEnum (SelectedCopy keep)] (fuel : Nat)
    (d : Code N (selectedSample sample keep)) :
    exprPolynomial (coefficients N fuel (panelCode N s keep hc) d) =
      exprPolynomial (coefficients N fuel (localPanelCode N s keep hc e)
        (Dot.CopyCarrierTransport.code N e.symm d)) :=
  Dot.CopyCarrierTransport.coefficients_polynomial_transport N e.symm fuel _ d

/-- The actual original polynomial's prescribed cardinality horizon equals
the native local carrier size m; no horizon truncation premise is introduced. -/
theorem localPanelCode_populationPolynomial (N : RootedBinary V E X) {sample : A → X}
    (s : Code N sample) (keep : Finset A) (hc : AncestorClosed (state s) keep)
    {m : Nat} (e : Fin m ≃ SelectedCopy keep)
    [FinEnum (SelectedCopy keep)] (d : Code N (selectedSample sample keep)) :
    populationPolynomial N (panelCode N s keep hc) d =
      exprPolynomial (coefficients N m (localPanelCode N s keep hc e)
        (Dot.CopyCarrierTransport.code N e.symm d)) := by
  have h := localPanelCode_coefficients N s keep hc e
    (Fintype.card (SelectedCopy keep)) d
  have hcard : Fintype.card (SelectedCopy keep) = m := by
    simpa using (Fintype.card_congr e).symm
  rw [coefficients_polynomial] at h
  simpa only [hcard] using h

/-- Inverse view transport applies to every local destination, not merely the
entering panel. -/
theorem restored_view (N : RootedBinary V E X) (e : A ≃ B)
    {sample : B → X} (s : Code N sample) :
    view e (selectedView (state (Dot.CopyCarrierTransport.code N e.symm s))
      Finset.univ) = selectedView (state s) Finset.univ := by
  rw [code_full_view_transport]
  simpa only [Equiv.symm_symm] using
    view_inverse e.symm (selectedView (state s) Finset.univ)

/-- One actual constructive join, expressed entirely through the corresponding
local ordered-carrier destination views. The inherited join uses the LEFT
register; equality with a native shared-register join needs its support fact. -/
theorem joinedCode_local_views (N : RootedBinary V E X) {sample : A → X}
    [FinEnum A] (keep : Finset A)
    {m n : Nat} (e : Fin m ≃ SelectedCopy keep)
    (f : Fin n ≃ SelectedCopy (Finset.univ \ keep))
    (a : Code N (selectedSample sample keep))
    (b : Code N (selectedSample sample (Finset.univ \ keep))) :
    selectedView (state (joinedCode N keep a b)) Finset.univ =
      joinViews keep
        (liftView keep (view e (selectedView
          (state (Dot.CopyCarrierTransport.code N e.symm a)) Finset.univ)))
        (liftView (Finset.univ \ keep) (view f (selectedView
          (state (Dot.CopyCarrierTransport.code N f.symm b)) Finset.univ))) := by
  rw [restored_view, restored_view, joinedCode_eq_joinCode, joinCode_view]

end Dot.OrderedPanelBridge
