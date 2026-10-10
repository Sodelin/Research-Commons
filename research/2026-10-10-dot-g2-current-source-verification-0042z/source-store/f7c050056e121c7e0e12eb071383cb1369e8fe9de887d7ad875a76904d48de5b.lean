import UnifiedLean.Source.SourceCalendarCompiler

/-!
# Actual original-node/location movements of compiled boundary kernels

Contributor: dot, 2026-10-02. Establishes the location facts needed to admit the
constructed graph/calendar agenda physically. The formulas are derived from
existing actual source operations and exact snapshot decoding. CURRENT owners,
original parent edge IDs, root identity and outside-node invariance are retained;
there is no supplied desired location/clock law field.
-/
namespace UnifiedLean.Source.SourceBoundaryLocations
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceCalendarCompiler
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma exitCode_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) (x : Copy) :
    copyLocation (state (exitCode N s e)) x = exitLocation N e (copyLocation (state s) x) := by
  rw [show copyLocation (state (exitCode N s e)) x = copyLocation (exitEdge N (state s) e) x from
    decode_encode_copyLocation N.root _ (exitEdge_source_valid N sample _ s.property e).forest x]
  rfl

lemma ordinaryCode_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) (x : Copy) :
    copyLocation (state (ordinaryCode N s e)) x = ordinaryLocation N e (copyLocation (state s) x) := by
  rw [show copyLocation (state (ordinaryCode N s e)) x = copyLocation (enterEdge N (state s) e) x from
    decode_encode_copyLocation N.root _ (enterEdge_source_valid N sample _ s.property e).forest x]
  rfl

lemma rootCode_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (x : Copy) :
    copyLocation (state (rootCode N s)) x = rootLocation N (copyLocation (state s) x) := by
  rw [show copyLocation (state (rootCode N s)) x = copyLocation (enterRoot N (state s)) x from
    decode_encode_copyLocation N.root _ (enterRoot_source_valid N sample _ s.property).forest x]
  rfl

/-- A parent pulse changes only CURRENT roots at its actual original hybrid. -/
theorem actual_pulse_code_location {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (coin : AtNode (state s) H.hybrid → Bool) (x : Copy) :
    (copyLocation (state s) x = .node H.hybrid → ∃ b : Bool,
      copyLocation (state (pulseCode H s coin)) x = .edge (H.parent b)) ∧
    (copyLocation (state s) x ≠ .node H.hybrid →
      copyLocation (state (pulseCode H s coin)) x = copyLocation (state s) x) := by
  rw [show copyLocation (state (pulseCode H s coin)) x = copyLocation (pulse H (state s) coin) x from
    decode_encode_copyLocation N.root _ (pulse_source_valid H sample _ s.property coin).forest x]
  constructor
  · intro hx
    let owner : AtNode (state s) H.hybrid :=
      ⟨(state s).ancestor x,⟨s.property.forest.ancestor_live x,hx⟩⟩
    refine ⟨coin owner,?_⟩
    exact pulse_routes_current_ancestor H (state s) coin owner
  · intro hx
    have hp : ¬ ((state s).ancestor x ∈ (state s).live ∧
        (state s).location ((state s).ancestor x) = .node H.hybrid) := fun h => hx h.2
    simp only [copyLocation,pulse,transport,dif_neg hp]

/-- A node boundary leaves every other location untouched; at the node it
enters a genuine incoming original edge, or the original ancestral root. -/
def NodeMovement (N : RootedBinary V E X) (v : V)
    (old new : Location V E) : Prop :=
  if old = .node v then
    if v = N.root then new = .rootPopulation N.root
    else ∃ e : E, N.graph.target e = v ∧ new = .edge e
  else new = old

lemma parent_move_is_node_movement (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (hy : Hybrid N) (hr : hy.val ≠ N.root)
    {old new : Location V E}
    (hp : (old = .node (H.parents hy).hybrid → ∃ b : Bool, new = .edge ((H.parents hy).parent b)) ∧
      (old ≠ .node (H.parents hy).hybrid → new = old)) : NodeMovement N hy.val old new := by
  unfold NodeMovement
  by_cases hn : old = .node hy.val
  · rw [if_pos hn,if_neg hr]
    obtain ⟨b,hb⟩ := hp.1 (by rw [H.original_site]; exact hn)
    exact ⟨(H.parents hy).parent b,registry_parent_target N H hy b,hb⟩
  · rw [if_neg hn]
    exact hp.2 (by rw [H.original_site]; exact hn)

/-- All positive-mass actual compiled node destinations satisfy the physical
original-parent movement, including both routing regimes and repeated samples. -/
theorem actual_original_node_kernel_movement (N : RootedBinary V E X)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N (originalNodeOperation N H gamma common v) s).support) (x : Copy) :
    NodeMovement N v (copyLocation (state s) x) (copyLocation (state d) x) := by
  by_cases hr : v = N.root
  · simp only [originalNodeOperation,dif_pos hr,boundaryKernel,PMF.mem_support_pure_iff] at hd
    subst d
    rw [rootCode_copyLocation]
    subst v
    unfold NodeMovement rootLocation
    by_cases hn : copyLocation (state s) x = .node N.root <;> simp [hn]
  · by_cases hh : N.graph.IsHybrid v
    · cases hc : common ⟨v,hh⟩ with
      | false =>
          simp only [originalNodeOperation,dif_neg hr,dif_pos hh,hc,Bool.false_eq_true,
            if_false,boundaryKernel,independentPulseKernel] at hd
          obtain ⟨coin,_,hcoin⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
          rw [← hcoin]
          exact parent_move_is_node_movement N H ⟨v,hh⟩ hr
            (actual_pulse_code_location (H.parents ⟨v,hh⟩) s coin x)
      | true =>
          simp only [originalNodeOperation,dif_neg hr,dif_pos hh,hc,if_true,
            boundaryKernel,PMF.mem_support_pure_iff] at hd
          subst d
          exact parent_move_is_node_movement N H ⟨v,hh⟩ hr
            (actual_pulse_code_location (H.parents ⟨v,hh⟩) s _ x)
    · simp only [originalNodeOperation,dif_neg hr,dif_neg hh,
        boundaryKernel,PMF.mem_support_pure_iff] at hd
      subst d
      rw [ordinaryCode_copyLocation]
      let e := (defaultSelector N).edge ⟨v,hr⟩
      have he : N.graph.target e = v := (defaultSelector N).target _
      change NodeMovement N v (copyLocation (state s) x) (ordinaryLocation N e (copyLocation (state s) x))
      unfold NodeMovement ordinaryLocation
      rw [he]
      by_cases hn : copyLocation (state s) x = .node v
      · rw [if_pos hn,if_pos hn,if_neg hr]
        exact ⟨e,he,rfl⟩
      · simp only [if_neg hn]

#print axioms exitCode_copyLocation
#print axioms actual_pulse_code_location
#print axioms parent_move_is_node_movement
#print axioms actual_original_node_kernel_movement
end UnifiedLean.Source.SourceBoundaryLocations
