import BinaryTrekDecomposition

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

D1 graphical soundness infrastructure: an ancestral moral route avoiding
the conditioning vertices yields an actual original-DAG active connection.
The endpoint-ancestor collider shortcut and active-walk loop reduction are
the existing proof bodies, not an assumed moralization equivalence.
Actual finite probability marginalization/global Markov remains separate.
-/

namespace RestrictedCausal.ProbabilitySource

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open SourceSelection (AncestorOf)

universe u

theorem raw_arrow_mixed_laws {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) : MixedLaws (arrowGraph D) := by
  constructor
  · exact arrow_graph_symm D
  · intro a ma mb edge
    rcases edge with ⟨loop, _, _⟩ | ⟨loop, _, _⟩ <;>
      have «impossible» := acyclic a [a] (.cons loop (.nil a)) <;> cases «impossible»
  · intro a b edge
    rcases edge with ⟨_, _, «impossible»⟩ | ⟨_, «impossible», _⟩ <;> exact Mark.noConfusion «impossible»

def MoralStep {V : Type u} (D : V → V → Prop) (A C : V → Prop) (a b : V) : Prop :=
  A a ∧ A b ∧ ¬ C a ∧ ¬ C b ∧
    (D a b ∨ D b a ∨ ∃ child, A child ∧ D a child ∧ D b child)

theorem outside_ancestral_departure {V : Type u} (C A : V → Prop) (a : V)
    (ancestral : A a) (outside : ¬ C a) (incoming : Option Mark) (outgoing : Mark) :
    DepartureAllowed C A a incoming outgoing := by
  cases incoming with
  | none => trivial
  | some previous =>
      by_cases collider : previous = .head ∧ outgoing = .head
      · simpa only [DepartureAllowed, ActiveAt, if_pos collider] using ancestral
      · simpa only [DepartureAllowed, ActiveAt, if_neg collider] using outside

theorem moral_step_relaxed {V : Type u} (D : V → V → Prop) (A C : V → Prop)
    {a b : V} (step : MoralStep D A C a b) (incoming : Option Mark) :
    ∃ last vertices, Route (Transition (arrowGraph D) C A) ⟨a, incoming⟩ vertices ⟨b, last⟩ := by
  rcases step with ⟨aAncestral, bAncestral, aOutside, bOutside, forward | backward | married⟩
  · exact ⟨some .head, [⟨b, some .head⟩], .cons
      ⟨.tail, .head, Or.inl ⟨forward, rfl, rfl⟩, rfl,
        outside_ancestral_departure C A a aAncestral aOutside incoming .tail⟩ (.nil _)⟩
  · exact ⟨some .tail, [⟨b, some .tail⟩], .cons
      ⟨.head, .tail, Or.inr ⟨backward, rfl, rfl⟩, rfl,
        outside_ancestral_departure C A a aAncestral aOutside incoming .head⟩ (.nil _)⟩
  · obtain ⟨child, childAncestral, «left», «right»⟩ := married
    refine ⟨some .tail, [⟨child, some .head⟩, ⟨b, some .tail⟩], .cons ?_ (.cons ?_ (.nil _))⟩
    · exact ⟨.tail, .head, Or.inl ⟨«left», rfl, rfl⟩, rfl,
        outside_ancestral_departure C A a aAncestral aOutside incoming .tail⟩
    · exact ⟨.head, .tail, Or.inr ⟨«right», rfl, rfl⟩, rfl,
        by simpa [ActiveAt] using childAncestral⟩

theorem moral_route_relaxed {V : Type u} (D : V → V → Prop) (A C : V → Prop)
    {a b : V} {vertices : List V} (route : Route (MoralStep D A C) a vertices b) :
    ∀ incoming, ∃ last states,
      Route (Transition (arrowGraph D) C A) ⟨a, incoming⟩ states ⟨b, last⟩ := by
  induction route with
  | nil a => intro incoming; exact ⟨incoming, [], .nil _⟩
  | cons step tail ih =>
      intro incoming
      obtain ⟨middleMark, «prefix», «first»⟩ := moral_step_relaxed D A C step incoming
      obtain ⟨last, suffix, remaining⟩ := ih middleMark
      exact ⟨last, «prefix» ++ suffix, «first».append remaining⟩

/-- Classical moralization direction needed for global Markov soundness:
if a moral path survived deleting C, it would contradict d-separation. -/
theorem ancestral_moral_route_is_active {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (C : V → Prop) (x y : V)
    {vertices : List V}
    (route : Route (MoralStep D (AncestorOf (arrowGraph D) (EndpointCondition C x y)) C) x vertices y) :
    ActiveConnection (arrowGraph D) C x y := by
  obtain ⟨last, states, relaxed⟩ := moral_route_relaxed D _ C route none
  exact endpoint_relaxed_connection (arrowGraph D) (raw_arrow_mixed_laws D acyclic) C x y relaxed

theorem ancestral_parent_closed {V : Type u} (D : V → V → Prop) (K : V → Prop)
    {parent child : V} (edge : D parent child) (ancestral : AncestorOf (arrowGraph D) K child) :
    AncestorOf (arrowGraph D) K parent := by
  obtain ⟨last, ⟨vertices, route⟩, terminal⟩ := ancestral
  exact ⟨last, ⟨child :: vertices, .cons ((arrow_directed_exact D parent child).mpr edge) route⟩, terminal⟩

def FamilyVertex {V : Type u} (D : V → V → Prop) (child vertex : V) : Prop := vertex = child ∨ D vertex child

/-- Any two unconditioned members of one ancestral CPT's family are
morally adjacent. Consequently that factor cannot straddle two different
components after deleting C. This statement keeps its original child and
original parent arrows; it does not introduce a factorization premise. -/
theorem family_vertices_morally_adjacent {V : Type u} (D : V → V → Prop) (K C : V → Prop)
    {child a b : V} (ancestral : AncestorOf (arrowGraph D) K child)
    («first» : FamilyVertex D child a) (second : FamilyVertex D child b)
    (different : a ≠ b) (aOutside : ¬ C a) (bOutside : ¬ C b) :
    MoralStep D (AncestorOf (arrowGraph D) K) C a b := by
  have allAncestral : ∀ v, FamilyVertex D child v → AncestorOf (arrowGraph D) K v := by
    intro v h
    rcases h with same | parent
    · exact same.symm ▸ ancestral
    · exact ancestral_parent_closed D K parent ancestral
  refine ⟨allAncestral a «first», allAncestral b second, aOutside, bOutside, ?_⟩
  rcases «first» with atChild | parentA <;> rcases second with atChildB | parentB
  · exact (different (atChild.trans atChildB.symm)).elim
  · subst a
    exact Or.inr (Or.inl parentB)
  · subst b
    exact Or.inl parentA
  · exact Or.inr (Or.inr ⟨child, ancestral, parentA, parentB⟩)

end RestrictedCausal.ProbabilitySource
