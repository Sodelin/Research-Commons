import G1ActualJointEpoch
import UnifiedLean.Source.SourceProgramTransport

/-! Actual original pulses and deterministic transports at a separated
interface. Contributor: dot, 2026-10-03. COMMON uses the same retained register;
private coins are the inherited iid law on actual CURRENT owners. -/
namespace G1ActualJointBoundary
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceBoundaryKernels
open G1ContextualForestReplacement G1JointSeparatedSourceGeometry G1ActualJointGenerator G1ActualJointEpoch
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma independentProduct_pure {A B : Type*} (a : A) (b : B) :
    independentProduct (PMF.pure a) (PMF.pure b) = PMF.pure (a,b) := by
  simp [independentProduct,PMF.pure_bind,PMF.pure_map]

lemma pair_map_product_of_constant_right {Z A B : Type*} (p : PMF Z)
    (f : Z → A) (g : Z → B) (b : B) (hg : ∀ z ∈ p.support, g z = b) :
    p.map (fun z => (f z,g z)) = independentProduct (p.map f) (p.map g) := by
  have hmap : p.map g = PMF.pure b := by
    rw [map_eq_of_eq_on_support p g (fun _ => b) hg]
    exact PMF.map_const _ _
  rw [hmap,independentProduct]
  simp only [PMF.pure_map,PMF.bind_map,Function.comp_def]
  change p.map (fun z => (f z,g z)) = p.map (fun z => (f z,b))
  exact map_eq_of_eq_on_support _ _ _ (fun z hz => congrArg (fun c => (f z,c)) (hg z hz))

lemma pair_map_product_of_constant_left {Z A B : Type*} (p : PMF Z)
    (f : Z → A) (g : Z → B) (a : A) (hf : ∀ z ∈ p.support, f z = a) :
    p.map (fun z => (f z,g z)) = independentProduct (p.map f) (p.map g) := by
  have hmap : p.map f = PMF.pure a := by
    rw [map_eq_of_eq_on_support p f (fun _ => a) hf]
    exact PMF.map_const _ _
  rw [hmap,independentProduct,PMF.pure_bind,PMF.map_comp]
  exact map_eq_of_eq_on_support _ _ _ (fun z hz => congrArg (fun c => (c,g z)) (hf z hz))

lemma separated_panels_not_at_same_node (s : State V E Copy) (inside outside : Finset Copy)
    (hsep : PopulationSeparated s inside outside) (node : V) :
    (∀ x ∈ inside, copyLocation s x ≠ .node node) ∨
      (∀ y ∈ outside, copyLocation s y ≠ .node node) := by
  by_cases hi : ∀ x ∈ inside, copyLocation s x ≠ .node node
  · exact Or.inl hi
  · right
    push_neg at hi
    obtain ⟨x,hx,hxl⟩ := hi
    intro y hy hyl
    exact hsep x hx y hy (hxl.trans hyl.symm)

lemma actual_pulse_untouched_panel (N : RootedBinary V E X) {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (keep : Finset Copy)
    (hnode : ∀ x ∈ keep, copyLocation (state s) x ≠ .node H.hybrid)
    (coin : AtNode (state s) H.hybrid → Bool) :
    projection N keep (pulseCode H s coin) = projection N keep s := by
  apply Subtype.ext
  change selectedView (state (pulseCode H s coin)) keep = selectedView (state s) keep
  rw [pulseCode_view]
  apply SelectedView.ext
  · rfl
  · funext x
    by_cases hx : x ∈ keep
    · have hn := hnode x hx
      change (state s).location ((state s).ancestor x) ≠ .node H.hybrid at hn
      simp [selectedView,selectedLocation,pulse,transport,copyLocation,hx,hn]
    · simp [selectedView,selectedLocation,hx]
  · rfl

/-- The original boundary's complete two-panel PMF factors. For private
routing, population separation means only one panel can occupy this original
hybrid, so all coins affecting it remain fresh CURRENT-owner source coins. -/
theorem actual_separated_joint_boundary_law (N : RootedBinary V E X) {sample : Copy → X}
    (inside outside : Finset Copy) (op : BoundaryOperation N) (s : Code N sample)
    (hsep : PopulationSeparated (state s) inside outside) :
    (boundaryKernel N op s).map (jointProjection N inside outside) =
      independentProduct ((boundaryKernel N op s).map (projection N inside))
        ((boundaryKernel N op s).map (projection N outside)) := by
  cases op with
  | exit e => simp [boundaryKernel,PMF.pure_map,jointProjection,independentProduct_pure]
  | ordinary e degree => simp [boundaryKernel,PMF.pure_map,jointProjection,independentProduct_pure]
  | root => simp [boundaryKernel,PMF.pure_map,jointProjection,independentProduct_pure]
  | common H => simp [boundaryKernel,PMF.pure_map,jointProjection,independentProduct_pure]
  | independent H gamma =>
      obtain hnode | hnode := separated_panels_not_at_same_node (state s) inside outside hsep H.hybrid
      · apply pair_map_product_of_constant_left _ _ _ (projection N inside s)
        intro d hd
        obtain ⟨coin,_,hc⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
        rw [← hc]
        exact actual_pulse_untouched_panel N H s inside hnode coin
      · apply pair_map_product_of_constant_right _ _ _ (projection N outside s)
        intro d hd
        obtain ⟨coin,_,hc⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
        rw [← hc]
        exact actual_pulse_untouched_panel N H s outside hnode coin

#print axioms actual_separated_joint_boundary_law
end G1ActualJointBoundary
