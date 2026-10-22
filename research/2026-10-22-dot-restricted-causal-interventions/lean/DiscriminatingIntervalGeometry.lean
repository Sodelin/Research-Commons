import LiteralMAGInducingChains

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Graphical exclusion of two-cycles for indexed discriminating sections.
The data retain an actual discriminating witness, its oriented neighboring
positions, and the actual collider-parent incidences at every interior
position. This module proves the graphical contradiction from that data;
constructing these data from the contiguous list witness remains explicit
downstream work. No acyclicity or MAG-equivalence field is assumed.
-/

namespace RestrictedCausal.DiscriminatingIntervalGeometry

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection HPLTarget
open InducingSeparation DiscriminatingStatus VertexActivePaths
open LiteralMAGInducingChains IntervalDependency

universe u v w

def Interior (start center position : Nat) : Prop :=
  (start < position ∧ position < center) ∨ (center < position ∧ position < start)

/-- Both orientations are retained. `parents` and `colliders` describe the
actual finite section, not a claimed order or invariance property. -/
structure IndexedWitness {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (vertex : Nat → X) (center : Nat) where
  start : Nat
  before : Nat
  finish : Nat
  orientation :
    (start < center ∧ before + 1 = center ∧ finish = center + 1) ∨
    (center < start ∧ before = center + 1 ∧ finish + 1 = center)
  witness : DiscriminatingWitness (mag D) (vertex before) (vertex center) (vertex finish)
  start_vertex : witness.start = vertex start
  parents : ∀ i, Interior start center i → Directed (mag D) (vertex i) (vertex finish)
  colliders : ∀ i, Interior start center i →
    Collider (mag D) (vertex (i - 1)) (vertex i) (vertex (i + 1))

theorem collider_reverse {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {a b c : X} (collider : Collider (mag D) a b c) :
    Collider (mag D) c b a := by
  obtain ⟨left, right, first, last⟩ := collider
  exact ⟨right, left, mag_symmetric D b c .head right last,
    mag_symmetric D a b left .head first⟩

theorem indexed_terminal_collider {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (vertex : Nat → X) {center : Nat}
    (w : IndexedWitness D vertex center)
    (collider : Collider (mag D) (vertex (center - 1)) (vertex center) (vertex (center + 1))) :
    Collider (mag D) (vertex w.before) (vertex center) (vertex w.finish) := by
  rcases w.orientation with left | right
  · have before : w.before = center - 1 := by omega
    simpa only [before, left.2.2] using collider
  · have finish : w.finish = center - 1 := by omega
    simpa only [right.2.1, finish] using collider_reverse D collider

/-- If the two discriminating starts reach beyond one another's centers,
there are exactly two boundary cases and one strict-interior case. At a
boundary the terminal collider would be ancestral to its nonadjacent start;
in the strict case the two terminal vertices would be parents of each other.
All three contradictions are proved using the actual original source's MAG. -/
theorem mutual_interior_impossible {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (vertex : Nat → X) {a b : Nat}
    (wa : IndexedWitness D vertex a) (wb : IndexedWitness D vertex b)
    (ab : Interior wb.start b a) (ba : Interior wa.start a b) : False := by
  classical
  have ordered : a < b ∨ b < a := by rcases ab with h | h <;> omega
  suffices forward : ∀ (a b : Nat), a < b →
      ∀ (wa : IndexedWitness D vertex a) (wb : IndexedWitness D vertex b),
        Interior wb.start b a → Interior wa.start a b → False by
    rcases ordered with less | greater
    · exact forward a b less wa wb ab ba
    · exact forward b a greater wb wa ba ab
  intro a b less wa wb ab ba
  have startB : wb.start < a := by rcases ab with h | h <;> omega
  have startA : b < wa.start := by rcases ba with h | h <;> omega
  have orientedB : wb.before + 1 = b ∧ wb.finish = b + 1 := by
    rcases wb.orientation with h | h <;> omega
  have orientedA : wa.before = a + 1 ∧ wa.finish + 1 = a := by
    rcases wa.orientation with h | h <;> omega
  have leftBoundary : wb.start ≤ wa.finish := by omega
  have rightBoundary : wb.finish ≤ wa.start := by omega
  by_cases leftEqual : wb.start = wa.finish
  · have bCollider := indexed_terminal_collider D vertex wb (wa.colliders b ba)
    have parent := wa.parents b ba
    have toStart : Directed (mag D) (vertex b) wb.witness.start := by
      rw [wb.start_vertex, leftEqual]
      exact parent
    exact discriminating_collider_not_reach_start D wb.witness bCollider
      ⟨[wb.witness.start], .cons toStart (.nil _)⟩
  · by_cases rightEqual : wa.start = wb.finish
    · have aCollider := indexed_terminal_collider D vertex wa (wb.colliders a ab)
      have parent := wb.parents a ab
      have toStart : Directed (mag D) (vertex a) wa.witness.start := by
        rw [wa.start_vertex, rightEqual]
        exact parent
      exact discriminating_collider_not_reach_start D wa.witness aCollider
        ⟨[wa.witness.start], .cons toStart (.nil _)⟩
    · have inB : Interior wb.start b wa.finish := Or.inl ⟨by omega, by omega⟩
      have inA : Interior wa.start a wb.finish := Or.inr ⟨by omega, by omega⟩
      have first := wb.parents wa.finish inB
      have last := wa.parents wb.finish inA
      have impossible := mag_no_directed_cycle D (vertex wa.finish)
        [vertex wb.finish, vertex wa.finish] (.cons first (.cons last (.nil _)))
      cases impossible

/-- The actual graphical exclusion discharges, rather than assumes, the
two-cycle premise of the finite interval contraction theorem. The only
remaining adapter here is extraction of `IndexedWitness` data from a chosen
contiguous discriminating section of the actual simple path. -/
theorem indexed_dependencies_acyclic {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (vertex : Nat → X) (active : Nat → Prop)
    (chosen : ∀ i, active i → IndexedWitness D vertex i)
    (start : Nat → Nat) (matches : ∀ i (hi : active i), start i = (chosen i hi).start) :
    ∀ a xs, Route (RestrictedBetween active start) a xs a → xs = [] := by
  apply restricted_between_acyclic active start
  intro a b ha hb ab ba
  have first : Interior (chosen b hb).start b a := by
    simpa only [Interior, BetweenStart, matches b hb] using ab
  have second : Interior (chosen a ha).start a b := by
    simpa only [Interior, BetweenStart, matches a ha] using ba
  exact mutual_interior_impossible D vertex (chosen a ha) (chosen b hb) first second

end RestrictedCausal.DiscriminatingIntervalGeometry
