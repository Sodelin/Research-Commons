import G2EventualPathReadout

/-!
The pair-age observer is tied to actual original source ancestry and grafts.
Contributor: dot (OpenAI), 6 October 2026.
A real merger creates exactly the cross-operand pair relations; demographic
routing/boundaries retain the entire genealogy readout. These facts support
the chronological threshold proof, without postulating a timed law.
-/
namespace GProgram.G2.ActualPairCoalescence
set_option backward.isDefEq.respectTransparency false
open GProgram.SourceForest Nanuq.Source GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceStepGeneratorBinding
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def sameBlock (v : SelectedView V E Copy) (x y : Copy) : Prop :=
  y ∈ Genealogy.optionLeaves (v.genealogy x)

lemma selected_same_block (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {x y : Copy} (hx : x ∈ keep) (hy : y ∈ keep) :
    sameBlock (selectedView s keep) x y ↔ s.ancestor x = s.ancestor y := by
  simp only [sameBlock,selectedView,selectedGenealogy,if_pos hx,Genealogy.prune_leaves,
    Finset.mem_inter,hy,and_true]
  exact (hs.leaf_fiber (s.ancestor x) (hs.ancestor_live x) y).trans eq_comm

lemma merger_pair_relation (s : State V E Copy) (a b x y : Copy) (hab : a ≠ b) :
    (merge s a b).ancestor x = (merge s a b).ancestor y ↔
      s.ancestor x = s.ancestor y ∨
      (s.ancestor x = a ∧ s.ancestor y = b) ∨
      (s.ancestor x = b ∧ s.ancestor y = a) := by
  simp only [merge]
  by_cases hx : s.ancestor x = b <;> by_cases hy : s.ancestor y = b <;>
    simp_all [eq_comm]

lemma selected_merger_pair_birth (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a b x y : Copy} (hm : LegalMerge s a b)
    (hx : x ∈ keep) (hy : y ∈ keep) :
    sameBlock (selectedView (merge s a b) keep) x y ↔
      sameBlock (selectedView s keep) x y ∨
      (x ∈ (s.genealogy a).leaves ∧ y ∈ (s.genealogy b).leaves) ∨
      (x ∈ (s.genealogy b).leaves ∧ y ∈ (s.genealogy a).leaves) := by
  rw [selected_same_block _ (merge_valid s hs hm) keep hx hy,
    selected_same_block s hs keep hx hy,merger_pair_relation s a b x y hm.different]
  simp only [hs.leaf_fiber a hm.first_live,hs.leaf_fiber b hm.second_live]

/-- Source code normalization does not replace the pair's ancestry. -/
theorem actual_destination_pair_birth (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (p : Choice N s) {x y : Copy}
    (hx : x ∈ keep) (hy : y ∈ keep) :
    sameBlock (selectedView (state (stepDestination N s (some p))) keep) x y ↔
      sameBlock (selectedView (state s) keep) x y ∨
      (x ∈ ((state s).genealogy p.2.val.1).leaves ∧ y ∈ ((state s).genealogy p.2.val.2).leaves) ∨
      (x ∈ ((state s).genealogy p.2.val.2).leaves ∧ y ∈ ((state s).genealogy p.2.val.1).leaves) := by
  rw [merged_destination_selectedView]
  exact selected_merger_pair_birth (state s) s.property.forest keep
    (population_pair_is_source_legal (state s) (originalPlace N p.1)
      (originalPlace_not_node N p.1) p.2.property) hx hy

lemma transport_same_block (v : SelectedView V E Copy)
    (f : Location V E → Location V E) (x y : Copy) :
    sameBlock (transportView v f) x y ↔ sameBlock v x y := Iff.rfl

lemma pulse_same_block {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (keep : Finset Copy) (coin : AtNode (state s) H.hybrid → Bool) (x y : Copy) :
    sameBlock (selectedView (state (pulseCode H s coin)) keep) x y ↔
      sameBlock (selectedView (state s) keep) x y := by
  rw [pulseCode_view]
  rfl

/-- Every admitted boundary preserves all genealogies, for each current-owner
coin realization, including COMMON register-directed routing. -/
theorem boundary_genealogy_law (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) (s : Code N sample) (keep : Finset Copy) :
    (boundaryKernel N op s).map (fun d => (selectedView (state d) keep).genealogy) =
      PMF.pure (selectedView (state s) keep).genealogy := by
  cases op with
  | exit e => simp only [boundaryKernel,PMF.pure_map,exitCode_view,transportView]
  | ordinary e h => simp only [boundaryKernel,PMF.pure_map,ordinaryCode_view,transportView]
  | root => simp only [boundaryKernel,PMF.pure_map,rootCode_view,transportView]
  | common H =>
      simp only [boundaryKernel,PMF.pure_map,pulseCode_view]
      rfl
  | independent H gamma =>
      rw [boundaryKernel,independentPulseKernel,PMF.map_comp]
      have hf : (fun a => (selectedView (state (pulseCode H s a)) keep).genealogy) =
          fun _ => (selectedView (state s) keep).genealogy := by
        funext a
        rw [pulseCode_view]
        rfl
      change PMF.map (fun a => (selectedView (state (pulseCode H s a)) keep).genealogy) _ = _
      rw [hf]
      exact PMF.map_const _ _

#print axioms actual_destination_pair_birth
#print axioms boundary_genealogy_law
end GProgram.G2.ActualPairCoalescence
