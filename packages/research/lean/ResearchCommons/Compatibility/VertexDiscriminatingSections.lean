import ActivePathReversal

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Exact vertex-list adapters and a typed discriminating witness. In particular
the penultimate vertex a in the discriminated triple (a,b,c) is retained,
not merely a path ending at b. No full MAG-equivalence theorem is assumed.
-/

namespace RestrictedCausal.SelectedWalk.Route

universe u

theorem split_append {V : Type u} {R : V → V → Prop} («prefix» suffix : List V)
    {a b : V} (h : Route R a («prefix» ++ suffix) b) :
    ∃ middle, Route R a «prefix» middle ∧ Route R middle suffix b := by
  induction «prefix» generalizing a with
  | nil => exact ⟨a, .nil a, h⟩
  | cons «next» rest ih =>
      cases h with
      | cons step tail =>
          obtain ⟨middle, «first», last⟩ := ih tail
          exact ⟨middle, .cons step «first», last⟩

end RestrictedCausal.SelectedWalk.Route

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget DiscriminatingStatus
open AncestralShortcutGeometry
open SourceSelection (AncestorOf)

universe u v

theorem split_map_append {A : Type u} {B : Type v} (f : A → B) («prefix» suffix : List B)
    (xs : List A) (h : xs.map f = «prefix» ++ suffix) :
    ∃ «first» last, xs = «first» ++ last ∧ «first».map f = «prefix» ∧ last.map f = suffix := by
  induction «prefix» generalizing xs with
  | nil => exact ⟨[], xs, rfl, rfl, h⟩
  | cons b rest ih =>
      cases xs with
      | nil => cases h
      | cons a as =>
          have eq : f a :: as.map f = b :: (rest ++ suffix) := h
          obtain ⟨head, tail⟩ := List.cons.inj eq
          obtain ⟨«first», last, original, firstTrace, lastTrace⟩ := ih as tail
          refine ⟨a :: «first», last, ?_, ?_, lastTrace⟩
          · simpa only [List.cons_append, original]
          · simpa only [List.map_cons, head, firstTrace]

/-- Data of one literal discriminating path for the specified triple.
Its prefix parent vertices are nonempty, all full-path vertices are distinct,
and the terminal edge and endpoint nonadjacency are explicitly present. -/
structure DiscriminatingWitness {V : Type u} (G : MarkedGraph V) (a b c : V) where
  start : V
  before : Arrival V
  terminal : Arrival V
  parents : List (Arrival V)
  before_vertex : before.vertex = a
  terminal_vertex : terminal.vertex = b
  parent_prefix : Route (ColliderParentStep G c) ⟨start, none⟩ parents before
  last_parent_step : ColliderParentStep G c before terminal
  terminal_adjacent : Adjacent G b c
  nonempty : parents ≠ []
  simple : (((⟨start, none⟩ :: (parents ++ [terminal])).map Arrival.vertex) ++ [c]).Nodup
  nonadjacent : ¬ Adjacent G start c

theorem DiscriminatingWitness.prefix {V : Type u} {G : MarkedGraph V} {a b c : V}
    (w : DiscriminatingWitness G a b c) :
    Route (ColliderParentStep G c) ⟨w.start, none⟩ (w.parents ++ [w.terminal]) w.terminal :=
  w.parent_prefix.append (.cons w.last_parent_step (.nil _))

def DiscriminatingWitness.vertices {V : Type u} {G : MarkedGraph V} {a b c : V}
    (w : DiscriminatingWitness G a b c) : List V :=
  ((⟨w.start, none⟩ :: (w.parents ++ [w.terminal])).map Arrival.vertex) ++ [c]

/-- Literal contiguous occurrence, not merely an arbitrary path or a
subsequence. This is the interval datum needed by the order-dependency proof. -/
def DiscriminatingWitness.OccursOn {V : Type u} {G : MarkedGraph V} {a b c : V}
    (w : DiscriminatingWitness G a b c) (path : List V) : Prop :=
  ∃ front back, path = front ++ w.vertices ++ back

theorem left_section_from_tail_decomposition {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (x z a b c : V)
    («prefix» suffix : List V) {xs : List V} (minimal : Shortest G Z x z xs)
    (decomposition : xs = «prefix» ++ [a, b, c] ++ suffix)
    (notStart : ¬ Z x) (good : Z a ∧ Directed G a c) :
    ∃ w : DiscriminatingWitness G a b c, w.OccursOn (x :: xs) := by
  obtain ⟨last, states, route, «trace», nodup⟩ := vertex_path_realization G single Z x z minimal.1
  have mapped : states.map Arrival.vertex = «prefix» ++ (a :: b :: c :: suffix) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using «trace».trans decomposition
  obtain ⟨front, remainder, stateSplit, frontTrace, remainderTrace⟩ :=
    split_map_append Arrival.vertex «prefix» (a :: b :: c :: suffix) states mapped
  cases remainder with
  | nil => cases remainderTrace
  | cons qa remaining =>
      obtain ⟨qaVertex, firstTrace⟩ := List.cons.inj remainderTrace
      cases remaining with
      | nil => cases firstTrace
      | cons qb remaining =>
          obtain ⟨qbVertex, secondTrace⟩ := List.cons.inj firstTrace
          cases remaining with
          | nil => cases secondTrace
          | cons qc back =>
              obtain ⟨qcVertex, backTrace⟩ := List.cons.inj secondTrace
              rw [stateSplit] at route
              obtain ⟨middle, frontRoute, restRoute⟩ := route.split_append front (qa :: qb :: qc :: back)
              cases restRoute with
              | cons toA tailA =>
                  cases tailA with
                  | cons ab tailB =>
                      cases tailB with
                      | cons bc backRoute =>
                          have sourceTrace : ((front ++ [qa]) ++ [qb, qc] ++ back).map Arrival.vertex = xs := by
                            have eq : ((front ++ [qa]) ++ [qb, qc] ++ back) = states := by
                              rw [stateSplit]
                              simp only [List.append_assoc, List.cons_append, List.nil_append]
                            rw [eq]
                            exact «trace»
                          have sourceMinimal : Shortest G Z x z
                              (((front ++ [qa]) ++ [qb, qc] ++ back).map Arrival.vertex) := by
                            rw [sourceTrace]
                            exact minimal
                          have sourceGood : ParentConditioned G Z qc.vertex qa := by
                            simpa only [ParentConditioned, qaVertex, qcVertex] using good
                          have lastAdjacent : Adjacent G b c := by
                            obtain ⟨outgoing, incoming, edge, _, _⟩ := bc
                            exact ⟨outgoing, incoming, by simpa only [qbVertex, qcVertex] using edge⟩
                          obtain ⟨start, nodes, fullPrefix, simple, nonadjacent, length,
                              parents, nodesEq, parentPrefix, parentLast, dropped, occurrence⟩ :=
                            extract_left_discriminating_section G laws single Z x z
                              (frontRoute.append (.cons toA (.nil qa))) ab bc backRoute sourceMinimal notStart sourceGood
                          have nonempty : parents ≠ [] := by
                            intro nil
                            rw [nodesEq, nil] at length
                            simp only [List.nil_append, List.length_cons, List.length_nil] at length
                            omega
                          refine ⟨{
                            start := start
                            before := qa
                            terminal := qb
                            parents := parents
                            before_vertex := qaVertex
                            terminal_vertex := qbVertex
                            parent_prefix := ?_
                            last_parent_step := ?_
                            terminal_adjacent := lastAdjacent
                            nonempty := nonempty
                            simple := ?_
                            nonadjacent := ?_
                          }, ?_⟩
                          · simpa only [qcVertex] using parentPrefix
                          · simpa only [qcVertex] using parentLast
                          · simpa only [nodesEq, qcVertex] using simple
                          · simpa only [qcVertex] using nonadjacent
                          · refine ⟨dropped, back.map Arrival.vertex, ?_⟩
                            simpa only [DiscriminatingWitness.vertices, nodesEq, qcVertex, sourceTrace] using occurrence

theorem left_section_from_vertex_decomposition {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (x z a b c : V)
    («prefix» suffix : List V) {xs : List V} (minimal : Shortest G Z x z xs)
    (decomposition : x :: xs = «prefix» ++ [a, b, c] ++ suffix)
    (notStart : ¬ Z x) (good : Z a ∧ Directed G a c) :
    ∃ w : DiscriminatingWitness G a b c, w.OccursOn (x :: xs) := by
  cases «prefix» with
  | nil =>
      have eq : x :: xs = a :: (b :: c :: suffix) := by
        simpa only [List.nil_append, List.cons_append] using decomposition
      have head := (List.cons.inj eq).1
      exact (notStart (head.symm ▸ good.1)).elim
  | cons «first» rest =>
      have eq : x :: xs = «first» :: (rest ++ [a, b, c] ++ suffix) := by
        simpa only [List.cons_append] using decomposition
      exact left_section_from_tail_decomposition G laws single Z x z a b c rest suffix minimal
        (List.cons.inj eq).2 notStart good

structure ThreeSection {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (x z a b c : V) where
  «first» : Arrival V
  middle : Arrival V
  third : Arrival V
  front : List (Arrival V)
  back : List (Arrival V)
  last : Option Mark
  first_vertex : «first».vertex = a
  middle_vertex : middle.vertex = b
  third_vertex : third.vertex = c
  «prefix» : Route (RealStep G Z) ⟨x, none⟩ front «first»
  first_step : RealStep G Z «first» middle
  second_step : RealStep G Z middle third
  suffix : Route (RealStep G Z) third back ⟨z, last⟩
  shortest : Shortest G Z x z ((front ++ [middle, third] ++ back).map Arrival.vertex)

theorem realize_tail_three_section {V : Type u} (G : MarkedGraph V) (single : SingleEdges G)
    (Z : V → Prop) (x z a b c : V) («prefix» suffix : List V) {xs : List V}
    (minimal : Shortest G Z x z xs) (decomposition : xs = «prefix» ++ [a, b, c] ++ suffix) :
    Nonempty (ThreeSection G Z x z a b c) := by
  obtain ⟨last, states, route, «trace», _⟩ := vertex_path_realization G single Z x z minimal.1
  have mapped : states.map Arrival.vertex = «prefix» ++ (a :: b :: c :: suffix) := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using «trace».trans decomposition
  obtain ⟨front, remainder, stateSplit, _, remainderTrace⟩ :=
    split_map_append Arrival.vertex «prefix» (a :: b :: c :: suffix) states mapped
  cases remainder with
  | nil => cases remainderTrace
  | cons qa remaining =>
      obtain ⟨qaVertex, firstTrace⟩ := List.cons.inj remainderTrace
      cases remaining with
      | nil => cases firstTrace
      | cons qb remaining =>
          obtain ⟨qbVertex, secondTrace⟩ := List.cons.inj firstTrace
          cases remaining with
          | nil => cases secondTrace
          | cons qc back =>
              obtain ⟨qcVertex, _⟩ := List.cons.inj secondTrace
              rw [stateSplit] at route
              obtain ⟨middle, frontRoute, restRoute⟩ := route.split_append front (qa :: qb :: qc :: back)
              cases restRoute with
              | cons toA tailA =>
                  cases tailA with
                  | cons ab tailB =>
                      cases tailB with
                      | cons bc backRoute =>
                          refine ⟨{
                            «first» := qa
                            middle := qb
                            third := qc
                            front := front ++ [qa]
                            back := back
                            last := last
                            first_vertex := qaVertex
                            middle_vertex := qbVertex
                            third_vertex := qcVertex
                            «prefix» := frontRoute.append (.cons toA (.nil qa))
                            first_step := ab
                            second_step := bc
                            suffix := backRoute
                            shortest := ?_
                          }⟩
                          have eq : ((front ++ [qa]) ++ [qb, qc] ++ back) = states := by
                            rw [stateSplit]
                            simp only [List.append_assoc, List.cons_append, List.nil_append]
                          rw [eq, «trace»]
                          exact minimal

theorem realize_three_section {V : Type u} (G : MarkedGraph V) (single : SingleEdges G)
    (Z : V → Prop) (x z a b c : V) («prefix» suffix : List V) {xs : List V}
    (minimal : Shortest G Z x z xs) (decomposition : x :: xs = «prefix» ++ [a, b, c] ++ suffix) :
    Nonempty (ThreeSection G Z x z a b c) := by
  cases «prefix» with
  | cons «first» rest =>
      have eq : x :: xs = «first» :: (rest ++ [a, b, c] ++ suffix) := by
        simpa only [List.cons_append] using decomposition
      exact realize_tail_three_section G single Z x z a b c rest suffix minimal (List.cons.inj eq).2
  | nil =>
      have eq : x :: xs = a :: (b :: c :: suffix) := by
        simpa only [List.nil_append, List.cons_append] using decomposition
      obtain ⟨startEq, tailEq⟩ := List.cons.inj eq
      obtain ⟨last, states, route, «trace», _⟩ := vertex_path_realization G single Z x z minimal.1
      have mapped : states.map Arrival.vertex = b :: c :: suffix := «trace».trans tailEq
      cases states with
      | nil => cases mapped
      | cons qb remaining =>
          obtain ⟨qbVertex, remainingTrace⟩ := List.cons.inj mapped
          cases remaining with
          | nil => cases remainingTrace
          | cons qc back =>
              obtain ⟨qcVertex, _⟩ := List.cons.inj remainingTrace
              cases route with
              | cons ab tail =>
                  cases tail with
                  | cons bc suffixRoute =>
                      refine ⟨{
                        «first» := ⟨x, none⟩
                        middle := qb
                        third := qc
                        front := []
                        back := back
                        last := last
                        first_vertex := startEq
                        middle_vertex := qbVertex
                        third_vertex := qcVertex
                        «prefix» := .nil _
                        first_step := ab
                        second_step := bc
                        suffix := suffixRoute
                        shortest := ?_
                      }⟩
                      simpa only [List.nil_append, List.cons_append, «trace»] using minimal

theorem shortest_vertex_chord_conditioned_parent {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (x z a b c : V)
    («prefix» suffix : List V) {xs : List V} (minimal : Shortest G Z x z xs)
    (decomposition : x :: xs = «prefix» ++ [a, b, c] ++ suffix) (chord : Adjacent G a c) :
    (Z a ∧ Directed G a c) ∨ (Z c ∧ Directed G c a) := by
  obtain ⟨«section»⟩ := realize_three_section G single Z x z a b c «prefix» suffix minimal decomposition
  obtain ⟨«left», «right», edge⟩ := chord
  have marked : G.edge «section».first.vertex «section».third.vertex «left» «right» := by
    simpa only [«section».first_vertex, «section».third_vertex] using edge
  have long : 1 < ([«section».middle, «section».third] : List (Arrival V)).length := by simp only [List.length_cons, List.length_nil]; omega
  have result := shortest_chord_conditioned_parent G laws single Z x z «section».prefix
    (.cons «section».first_step (.cons «section».second_step (.nil «section».third))) «section».suffix long marked «section».shortest
  simpa only [«section».first_vertex, «section».third_vertex] using result

/-- Full dual-orientation discriminating-section existence for every shielded
triple on a shortest active path. The two possible orientations refer to the
same original graph and the same specified triple, not a weaker summary. -/
theorem shortest_shielded_triple_discriminated {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (x z a b c : V)
    («prefix» suffix : List V) {xs : List V} (minimal : Shortest G Z x z xs)
    (decomposition : x :: xs = «prefix» ++ [a, b, c] ++ suffix)
    (notStart : ¬ Z x) (notEnd : ¬ Z z) (chord : Adjacent G a c) :
    (∃ w : DiscriminatingWitness G a b c, w.OccursOn (x :: xs)) ∨
      (∃ w : DiscriminatingWitness G c b a, w.OccursOn (x :: xs).reverse) := by
  rcases shortest_vertex_chord_conditioned_parent G laws single Z x z a b c «prefix» suffix minimal decomposition chord with
      «left» | «right»
  · exact Or.inl (left_section_from_vertex_decomposition G laws single Z x z a b c
      «prefix» suffix minimal decomposition notStart «left»)
  · obtain ⟨ys, reversed, «trace», _⟩ := reverse_shortest_path G single laws.symmetric Z x z minimal
    have reversedDecomposition : z :: ys = suffix.reverse ++ [c, b, a] ++ «prefix».reverse := by
      rw [«trace», decomposition]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.append_assoc, List.cons_append, List.nil_append]
    obtain ⟨w, occurs⟩ := left_section_from_vertex_decomposition G laws single Z z x c b a
      suffix.reverse «prefix».reverse reversed reversedDecomposition notEnd «right»
    exact Or.inr ⟨w, «trace» ▸ occurs⟩

end RestrictedCausal.VertexActivePaths
