import ClosestFirstArrowPotential

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Recover the actual boundary incidences from retained physical traces. These
lemmas discharge the unchanged-neighbor-status premises of the equal-length
potential calculation; they do not assume them as a graph-adapter axiom.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open DiscriminatingStatus AncestralShortcutGeometry WeakInducing

universe u

theorem terminal_label_unique {V : Type u} (front back : List V) (a b : V)
    (equation : front ++ [a] = back ++ [b]) : a = b := by
  have reversed := congrArg List.reverse equation
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at reversed
  exact (List.cons.inj reversed).1

theorem penultimate_label_unique {V : Type u} (front back : List V) (p q a : V)
    (equation : front ++ [p, a] = back ++ [q, a]) : p = q := by
  have reversed := congrArg List.reverse equation
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.cons_append] at reversed
  exact (List.cons.inj (List.cons.inj reversed).2).1

theorem retained_arm_terminal {V : Type u} {R : Arrival V → Arrival V → Prop}
    (x : V) {a : Arrival V} {states : List (Arrival V)}
    (arm : Route R ⟨x, none⟩ states a) {front : List V} {last : V}
    (equation : (⟨x, none⟩ :: states).map Arrival.vertex = front ++ [last]) : a.vertex = last := by
  obtain ⟨before, ends⟩ := arm.full_list_ends
  have «trace» := congrArg (List.map Arrival.vertex) ends
  simp only [List.map_append, List.map_cons, List.map_nil] at «trace»
  exact terminal_label_unique (before.map Arrival.vertex) front a.vertex last («trace».symm.trans equation)

/-- Recover the last real incoming edge, with the actual arrival mark,
from a two-vertex suffix of the arm's physical trace. -/
theorem retained_arm_last_edge {V : Type u} (G : MarkedGraph V) (Z : V → Prop)
    (x p : V) {a : Arrival V} {states : List (Arrival V)}
    (arm : Route (RealStep G Z) ⟨x, none⟩ states a) (front : List V)
    (equation : (⟨x, none⟩ :: states).map Arrival.vertex = front ++ [p, a.vertex]) :
    ∃ «left» incoming, G.edge p a.vertex «left» incoming ∧ a.incoming = some incoming := by
  have nonempty : states ≠ [] := by
    intro empty
    have lengths := congrArg List.length equation
    simp only [empty, List.length_map, List.length_cons, List.length_nil, List.length_append] at lengths
    omega
  obtain ⟨before, «prefix», «split», route, lastStep⟩ := arm.split_last nonempty
  obtain ⟨dropped, ends⟩ := route.full_list_ends
  have originalEnds : (⟨x, none⟩ :: states).map Arrival.vertex =
      dropped.map Arrival.vertex ++ [before.vertex, a.vertex] := by
    have mapped := congrArg (fun nodes => (nodes ++ [a]).map Arrival.vertex) ends
    simpa only [«split», List.map_cons, List.map_append, List.map_nil, List.cons_append,
      List.append_assoc, List.nil_append] using mapped
  have label : before.vertex = p := penultimate_label_unique (dropped.map Arrival.vertex) front
    before.vertex p a.vertex (originalEnds.symm.trans equation)
  obtain ⟨«left», incoming, edge, mark, _⟩ := lastStep
  exact ⟨«left», incoming, by simpa only [label] using edge, mark⟩

theorem stopped_boundary_vertex_status {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (p d : V)
    {a b : Arrival V} {«left» incoming : Mark}
    (previous : G.edge p a.vertex «left» incoming) (arrival : a.incoming = some incoming)
    (boundary : RealStep G Z a b) (stopped : ¬ StrictParentStep G d a b)
    (headB : b.incoming = some .head) (child : Directed G b.vertex d)
    (adjacent : Adjacent G a.vertex d) :
    Collider G p a.vertex b.vertex ↔ Collider G p a.vertex d := by
  obtain ⟨outgoing, received, edge, mark, active⟩ := boundary
  have receivedHead : received = .head := Option.some.inj (mark.symm.trans headB)
  subst received
  have stoppedVertex : ¬ (Collider G p a.vertex b.vertex ∧ Directed G a.vertex d) := by
    rintro ⟨collider, parent⟩
    have heads := (collider_iff_chosen_marks G single p a.vertex b.vertex
      «left» incoming outgoing .head previous edge).mp collider
    apply stopped
    refine ⟨⟨outgoing, .head, edge, mark, ?_⟩, arrival.trans (congrArg some heads.1)⟩
    simpa only [arrival] using (show incoming = .head ∧ outgoing = .head ∧
      Directed G a.vertex d from ⟨heads.1, heads.2, parent⟩)
  obtain ⟨_, _, status⟩ := stopping_boundary_status G laws single previous
    ⟨outgoing, edge⟩ child adjacent stoppedVertex
  exact status

/-- Supply every left-neighbor status required by the literal replacement
potential theorem directly from the actual retained arm and its stopping
edge. Endpoint cases require no spurious collider condition. -/
theorem retained_left_status {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (x d : V)
    {a b : Arrival V} {states : List (Arrival V)}
    (arm : Route (RealStep G Z) ⟨x, none⟩ states a)
    (boundary : RealStep G Z a b) (stopped : ¬ StrictParentStep G d a b)
    (headB : b.incoming = some .head) (child : Directed G b.vertex d)
    (adjacent : Adjacent G a.vertex d) :
    ∀ front p q, (⟨x, none⟩ :: states).map Arrival.vertex = front ++ [p, q] →
      (Collider G p q b.vertex ↔ Collider G p q d) := by
  intro front p q equation
  have label : a.vertex = q := retained_arm_terminal x arm (front := front ++ [p]) (by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using equation)
  have finalTrace : (⟨x, none⟩ :: states).map Arrival.vertex = front ++ [p, a.vertex] := by
    simpa only [label] using equation
  obtain ⟨«left», incoming, edge, arrival⟩ := retained_arm_last_edge G Z x p arm front finalTrace
  simpa only [label] using stopped_boundary_vertex_status G laws single Z p d edge arrival
    boundary stopped headB child adjacent

end RestrictedCausal.VertexActivePaths
