import G1OriginalEpochRecomposition

/-!
# Exterior-only original boundaries leave the COMPLETE inside view unchanged

Contributor: dot, 2026-10-03. Absence is a physical condition on original
population/node locations. Identity is proved from actual boundary operations,
fresh current-owner coin support and the same original COMMON register.
The actual exterior source continues to process the boundary.
-/
namespace G1ExteriorBoundarySilence
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryProjection
open G1ActualJointBoundary G1ContextualForestReplacement
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def touchedPlace (N : RootedBinary V E X) : BoundaryOperation N → Location V E
  | .exit e => .edge e
  | .ordinary e _ => .node (N.graph.target e)
  | .root => .node N.root
  | .independent H _ => .node H.hybrid
  | .common H => .node H.hybrid

def PanelAbsent (N : RootedBinary V E X) (op : BoundaryOperation N)
    (s : State V E Copy) (keep : Finset Copy) : Prop :=
  ∀ x ∈ keep, copyLocation s x ≠ touchedPlace N op

lemma untouched_transport_view (s : State V E Copy) (keep : Finset Copy)
    (f : Location V E → Location V E) (hf : ∀ x ∈ keep, f (copyLocation s x) = copyLocation s x) :
    transportView (selectedView s keep) f = selectedView s keep := by
  apply SelectedView.ext
  · rfl
  · funext x
    by_cases hx : x ∈ keep
    · simp [transportView,selectedView,selectedLocation,hx,hf x hx]
    · simp [transportView,selectedView,selectedLocation,hx]
  · rfl

/-- Every ACTUAL supported original boundary realization retains the whole
inside labelled genealogy/population/register view when inside is absent. -/
theorem actual_untouched_boundary_panel (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) (s : Code N sample) (keep : Finset Copy)
    (habsent : PanelAbsent N op (state s) keep) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N op s).support) : projection N keep d = projection N keep s := by
  cases op with
  | exit e =>
      have he : d = exitCode N s e := by simpa [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d
      apply Subtype.ext
      change selectedView (state (exitCode N s e)) keep = _
      rw [exitCode_view]
      apply untouched_transport_view
      intro x hx
      exact if_neg (habsent x hx)
  | ordinary e degree =>
      have he : d = ordinaryCode N s e := by simpa [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d
      apply Subtype.ext
      change selectedView (state (ordinaryCode N s e)) keep = _
      rw [ordinaryCode_view]
      apply untouched_transport_view
      intro x hx
      exact if_neg (habsent x hx)
  | root =>
      have he : d = rootCode N s := by simpa [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d
      apply Subtype.ext
      change selectedView (state (rootCode N s)) keep = _
      rw [rootCode_view]
      apply untouched_transport_view
      intro x hx
      exact if_neg (habsent x hx)
  | common H =>
      have he : d = pulseCode H s (fun _ => (state s).register H.hybrid) := by
        simpa [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d
      exact actual_pulse_untouched_panel N H s keep habsent _
  | independent H gamma =>
      obtain ⟨coin,_,hc⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
      rw [← hc]
      exact actual_pulse_untouched_panel N H s keep habsent coin

theorem actual_untouched_boundary_law (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) (s : Code N sample) (keep : Finset Copy)
    (habsent : PanelAbsent N op (state s) keep) :
    (boundaryKernel N op s).map (projection N keep) = PMF.pure (projection N keep s) := by
  rw [map_eq_of_eq_on_support _ _ (fun _ => projection N keep s)
    (fun d hd => actual_untouched_boundary_panel N op s keep habsent hd)]
  exact PMF.map_const _ _

theorem actual_selected_untouched_boundary (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) (s : Code N sample) (keep : Finset Copy)
    (habsent : PanelAbsent N op (state s) keep) :
    selectedBoundary N keep op (projection N keep s) = PMF.pure (projection N keep s) := by
  rw [← actual_boundary_projection]
  exact actual_untouched_boundary_law N op s keep habsent

#print axioms actual_untouched_boundary_law
end G1ExteriorBoundarySilence
