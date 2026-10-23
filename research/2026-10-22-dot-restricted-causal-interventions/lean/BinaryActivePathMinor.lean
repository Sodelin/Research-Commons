import BinaryWitnessCircuit

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Geometry-to-circuit join for the finite binary atomic-completeness minor.
The conditioning slice and endpoint equations are proved from the actual
minimum path, chosen disjoint activation branches, original-arrow gates,
and derived finite-DAG rank. They are not additional theorem premises.

Classical mathematical attribution: Geiger--Verma--Pearl atomic
completeness, as used constructively by Meek (1995), Lemmas 9 and 11.
This is not a novelty claim, a successful Lean build, or the full shared
positive selected soft-intervention faithfulness theorem (D1--D6).
-/

namespace RestrictedCausal.ProbabilitySource

open SelectedWalk WeakInducing VertexActivePaths CanonicalSelection LatentRoots
open InducingSeparation OriginalProjection BinaryCPT

universe u

namespace BinaryWitnessGeometry

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem ordinary_constant_value (g : BinaryWitnessGeometry V) (t : Bool)
    (vertex : V) (ordinary : g.ordinary vertex) : g.circuit.value (fun _ => t) vertex = t :=
  g.circuit.constant_value_on_copy_region g.ordinary g.ordinary_gate_classification t vertex ordinary

theorem collider_selected_zero (g : BinaryWitnessGeometry V) (bits : g.SourceIndex → Bool)
    {b : V} (collider : TraceCollider g.arrow g.main b)
    (matching : Matches g.conditioned (fun _ => false) (g.circuit.value bits)) :
    g.circuit.value bits b = false := by
  let index : g.ColliderIndex := ⟨b, collider⟩
  exact g.circuit.selected_copy_forces_zero bits g.conditioned
    (g.branch_copy_route index) (g.branch index).shortest.endpoint matching

theorem ordinary_adjacent_equal (g : BinaryWitnessGeometry V) (bits : g.SourceIndex → Bool)
    {a b : V} (next : NextOn g.main a b)
    (notA : ¬ TraceCollider g.arrow g.main a) (notB : ¬ TraceCollider g.arrow g.main b) :
    g.circuit.value bits a = g.circuit.value bits b := by
  have adjacent := route_next_edge g.minimal.1.1 a b next
  rcases arrow_adjacent_directions g.arrow adjacent with forward | backward
  · exact (g.circuit.copy_value bits
      (g.gate_main_copy ⟨next.members.2, notB⟩ ⟨Or.inl next, forward⟩)).symm
  · exact g.circuit.copy_value bits
      (g.gate_main_copy ⟨next.members.1, notA⟩ ⟨Or.inr next, backward⟩)

theorem selected_forces_constant_bits (g : BinaryWitnessGeometry V) (bits : g.SourceIndex → Bool)
    (matching : Matches g.conditioned (fun _ => false) (g.circuit.value bits)) :
    bits = (fun _ => false) ∨ bits = (fun _ => true) := by
  apply g.circuit.all_source_bits_constant bits (TraceCollider g.arrow g.main) g.start g.vertices
  · intro i
    exact ⟨i.property.1, i.property.2.1⟩
  · exact g.start_ordinary.2
  · intro front last equation
    change ¬ TraceCollider g.arrow (g.start :: g.vertices) last
    rw [equation]
    exact trace_last_not_collider g.arrow front last (by rw [← equation]; exact g.simple)
  · exact allPairs_of_next _ g.main (fun a b next =>
      trace_collider_isolated g.arrow g.acyclic g.simple next)
  · exact allPairs_of_next _ g.main (fun a b next notA notB =>
      g.ordinary_adjacent_equal bits next notA notB)
  · apply allTriples_of_triple
    intro a b c occurrence collider
    obtain ⟨leftEdge, rightEdge, leftRank, rightRank, gate⟩ := g.gate_collider_xor occurrence collider
    exact g.circuit.zero_xor_equal_inputs bits a b c leftEdge rightEdge leftRank rightRank gate
      (g.collider_selected_zero bits collider matching)

theorem collider_constant_zero (g : BinaryWitnessGeometry V) (t : Bool)
    {b : V} (collider : TraceCollider g.arrow g.main b) : g.circuit.value (fun _ => t) b = false := by
  obtain ⟨a, c, occurrence, left, right⟩ := collider
  have parentA : MainParent g.arrow g.main a b := ⟨Or.inl occurrence.left, left⟩
  have parentC : MainParent g.arrow g.main c b := ⟨Or.inr occurrence.right, right⟩
  have ordinaryA : g.ordinary a := ⟨occurrence.left.members.1,
    mainParent_ordinary g.arrow g.acyclic g.simple parentA⟩
  have ordinaryC : g.ordinary c := ⟨occurrence.right.members.2,
    mainParent_ordinary g.arrow g.acyclic g.simple parentC⟩
  obtain ⟨leftEdge, rightEdge, leftRank, rightRank, gate⟩ :=
    g.gate_collider_xor occurrence ⟨a, c, occurrence, left, right⟩
  exact g.circuit.equal_constant_xor_zero a b c leftEdge rightEdge leftRank rightRank gate t
    (g.ordinary_constant_value t a ordinaryA) (g.ordinary_constant_value t c ordinaryC)

theorem branch_constant_zero (g : BinaryWitnessGeometry V) (t : Bool)
    (b : g.ColliderIndex) (vertex : V) (member : vertex ∈ b.val :: (g.branch b).vertices) :
    g.circuit.value (fun _ => t) vertex = false := by
  obtain ⟨prefix, route⟩ := (g.branch_copy_route b).prefix_of_mem member
  exact (g.circuit.copy_route_value (fun _ => t) route).trans (g.collider_constant_zero t b.property)

theorem constants_match_conditioning (g : BinaryWitnessGeometry V) (t : Bool) :
    Matches g.conditioned (fun _ => false) (g.circuit.value (fun _ => t)) := by
  classical
  intro vertex selected
  by_cases onMain : vertex ∈ g.main
  · have collider : TraceCollider g.arrow g.main vertex := by
      by_contra ordinary
      exact g.ordinary_outside_conditioning ⟨onMain, ordinary⟩ selected
    exact g.collider_constant_zero t collider
  · by_cases hasParent : ∃ p, g.BranchParent p vertex
    · obtain ⟨parent, b, next⟩ := hasParent
      exact g.branch_constant_zero t b vertex next.members.2
    · have off : g.circuit.gate vertex = .off := by
        simp only [circuit, gate, dif_neg onMain, dif_neg hasParent]
      rw [BoundaryCircuit.value, off]

theorem constant_slice (g : BinaryWitnessGeometry V) (bits : g.SourceIndex → Bool) :
    Matches g.conditioned (fun _ => false) (g.circuit.value bits) ↔
      bits = (fun _ => false) ∨ bits = (fun _ => true) := by
  constructor
  · exact g.selected_forces_constant_bits bits
  · rintro (allFalse | allTrue)
    · rw [allFalse]; exact g.constants_match_conditioning false
    · rw [allTrue]; exact g.constants_match_conditioning true

theorem constant_endpoints (g : BinaryWitnessGeometry V) (t : Bool) :
    g.circuit.value (fun _ => t) g.start = t ∧ g.circuit.value (fun _ => t) g.finish = t :=
  ⟨g.ordinary_constant_value t g.start g.start_ordinary,
    g.ordinary_constant_value t g.finish g.finish_ordinary⟩

theorem actual_minor_nonzero (g : BinaryWitnessGeometry V) :
    minorPolynomial g.arrow g.start g.finish g.conditioned (fun _ => false) ≠ 0 :=
  g.circuit.minor_ne_zero_of_constant_slice g.start g.finish g.conditioned (fun _ => false)
    g.distinct g.startOutside g.finishOutside g.constant_slice g.constant_endpoints

/-- The root subtype cannot be empty, even for a collider-free path. No
unused root indices are introduced: every index is its own actual fair
source and an ordinary main-path vertex. -/
theorem source_index_nonempty (g : BinaryWitnessGeometry V) : Nonempty g.SourceIndex := by
  classical
  by_contra empty
  have functionsEqual : (fun _ : g.SourceIndex => false) = (fun _ => true) := by
    funext i
    exact (empty ⟨i⟩).elim
  have endpoints := (g.constant_endpoints false).1
  rw [functionsEqual, (g.constant_endpoints true).1] at endpoints
  cases endpoints

end BinaryWitnessGeometry

/-- Exact finite binary-CPT nonzero-minor supplier. No circuit, rank,
branch-disjointness, slice, endpoint, Gaussian, or faithfulness premise is
added to the actual finite-DAG connection statement. The displayed zero
conditioning assignment is a boundary witness slice, not a claim about
an arbitrary selected slice or the later common positive parameter point.

Source-only/unelaborated: this declaration has NOT been compiler checked.
-/
theorem binary_active_path_minor_nonzero {V : Type u} [Fintype V] [DecidableEq V]
    (D : V → V → Prop) (acyclic : ∀ a xs, Route D a xs a → xs = [])
    (x y : V) (C : Finset V) (different : x ≠ y) (xOutside : x ∉ C) (yOutside : y ∉ C)
    (connected : ActiveConnection (arrowGraph D) (fun v => v ∈ C) x y) :
    BinaryCPT.minorPolynomial D x y C (fun _ => false) ≠ 0 := by
  obtain ⟨vertices, minimal⟩ := exists_collider_minimal (arrowGraph D)
    (arrow_single_edges D acyclic) (fun v => v ∈ C) x y connected
  let geometry : BinaryWitnessGeometry V :=
    ⟨D, acyclic, C, x, y, different, xOutside, yOutside, vertices, minimal⟩
  exact geometry.actual_minor_nonzero

end RestrictedCausal.ProbabilitySource
