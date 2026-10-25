import MarkedActiveWalks

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual original-source walks realizing one literal MAG edge, with the two
boundary conditions needed for concatenation along an active MAG path:
heads at conditioned endpoints, and tails at nonancestor endpoints whose
MAG incidence is a tail. Unknown latent/selection carriers and the original
marked target remain unchanged. The full two-way MAG representation and MEC
criterion are not claimed by this local realization component.
-/

namespace RestrictedCausal.EdgeWalks

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation FramedWalk RefinedSeparator IndicatorAncestry HPLTarget
open SourceSelection (AncestorOf)

universe u v w

theorem selected_condition_nonlatent {X : Type u} {S : Type v} {L : Type w}
    (Z : X → Prop) (a : SourceVertex X S L) (h : SelectedCondition Z a) : Nonlatent a := by
  cases a with
  | inl r => trivial
  | inr l => exact h.elim

theorem head_started_marked {V : Type u} (G : MarkedGraph V) (C A : V → Prop)
    (x y : V) (hne : x ≠ y) (hx : C x) {last : Option Mark} {xs : List (Arrival V)}
    (h : Route (Transition G C A) ⟨x, some .head⟩ xs ⟨y, last⟩) :
    ∃ «right», MarkedRoute G C A x y .head «right» := by
  cases xs with
  | nil =>
      cases h
      exact (hne rfl).elim
  | cons «next» rest =>
      cases h with
      | cons «first» tail =>
          obtain ⟨outgoing, incoming, edge, hmark, active⟩ := «first»
          have hout := (ActiveWalkReduction.conditioned_active_heads hx active).2
          subst outgoing
          obtain ⟨«right», hright⟩ := ActiveWalkReduction.some_arrival_preserved tail ⟨incoming, hmark⟩
          have nextEq : «next» = ⟨«next».vertex, some incoming⟩ := Arrival.eq_of_fields rfl hmark
          have endEq : last = some «right» := hright
          exact ⟨«right», «next».vertex, incoming, rest, edge, by
            rw [← nextEq, ← endEq]
            exact tail⟩

/-- If x is conditioned and its MAG endpoint is a head, every unactivated
inducing collider can only require a shortcut toward y: ancestry to x is
already ancestry to the conditioning set. The head-started route therefore
retains an actual head at x. -/
theorem one_conditioned_head_walk {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (Z : X → Prop) (h : InducingPath D x y)
    (hx : Z x) (head : ¬ TailFlag D x y) :
    ∃ «right», MarkedRoute (arrowGraph D.arrow) (SelectedCondition Z)
      (AncestorOf (arrowGraph D.arrow) (SelectedCondition Z))
      (Observed x) (Observed y) .head «right» := by
  obtain ⟨«left», «right», marked⟩ := inducing_marked_route D x y h
  have hleft := marked_inducing_left_head D x y marked head
  subst «left»
  let C := SelectedCondition (S := S) (L := L) Z
  let E : SourceVertex X S L → Prop := fun v => v = Observed y
  have hAnc : ∀ a, EndpointAncestor D x y a →
      AncestorOf (arrowGraph D.arrow) (fun v => E v ∨ C v) a := by
    intro a ha
    apply ancestor_mono (C := EndpointSelection x y) (fun v hv => ?_) ha
    rcases hv with hxv | hyv | hsv
    · right
      simpa only [hxv] using (show C (Observed x) from hx)
    · exact Or.inl hyv
    · exact Or.inr (selected_condition_contains_selection Z v hsv)
  have relaxed := marked.mono (selected_condition_nonlatent Z) hAnc
  have activeAtStart : ActiveAt C (AncestorOf (arrowGraph D.arrow) (fun v => E v ∨ C v))
      (Observed x) .head .head := by
    have ha : AncestorOf (arrowGraph D.arrow) (fun v => E v ∨ C v) (Observed x) :=
      ⟨Observed x, ⟨[], .nil _⟩, Or.inr hx⟩
    simpa [ActiveAt] using ha
  obtain ⟨xs, hr⟩ := relaxed.with_arrival activeAtStart
  obtain ⟨endpoint, hend, last, ys, actual⟩ := relaxed_route_hits (arrowGraph D.arrow) C E
    hr rfl (some .head) [] (.nil _) (Or.inl rfl)
  change endpoint = Observed y at hend
  have actual' : Route (RealStep (arrowGraph D.arrow) C)
      ⟨Observed x, some .head⟩ ys ⟨Observed y, last⟩ := by simpa only [hend] using actual
  apply head_started_marked (arrowGraph D.arrow) C (AncestorOf (arrowGraph D.arrow) C)
    (Observed x) (Observed y) ?_ hx actual'
  intro heq
  exact h.1 (Sum.inl.inj (Sum.inl.inj heq))

/-- Protected heads at every conditioned endpoint. If both endpoints are
conditioned, all inducing colliders are already activated, so the original
endpoint-marked route itself is used. Otherwise only the opposite endpoint
can cause a directed shortcut. -/
theorem inducing_walk_conditioned_heads {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (Z : X → Prop) (h : InducingPath D x y)
    (headX : Z x → ¬ TailFlag D x y) (headY : Z y → ¬ TailFlag D y x) :
    ∃ «left» «right», MarkedRoute (arrowGraph D.arrow) (SelectedCondition Z)
      (AncestorOf (arrowGraph D.arrow) (SelectedCondition Z))
      (Observed x) (Observed y) «left» «right» ∧
      (Z x → «left» = .head) ∧ (Z y → «right» = .head) := by
  classical
  by_cases hx : Z x
  · by_cases hy : Z y
    · obtain ⟨«left», «right», marked⟩ := inducing_marked_route D x y h
      have hl := marked_inducing_left_head D x y marked (headX hx)
      have hr := marked_inducing_right_head D x y marked (headY hy)
      have hAnc : ∀ a, EndpointAncestor D x y a →
          AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) a := by
        intro a ha
        apply ancestor_mono (C := EndpointSelection x y) (fun v hv => ?_) ha
        rcases hv with hxv | hyv | hsv
        · simpa only [hxv] using
            (show SelectedCondition (S := S) (L := L) Z (Observed x) from hx)
        · simpa only [hyv] using
            (show SelectedCondition (S := S) (L := L) Z (Observed y) from hy)
        · exact selected_condition_contains_selection Z v hsv
      exact ⟨«left», «right», marked.mono (selected_condition_nonlatent Z) hAnc,
        fun _ => hl, fun _ => hr⟩
    · obtain ⟨«right», marked⟩ := one_conditioned_head_walk D x y Z h hx (headX hx)
      exact ⟨.head, «right», marked, fun _ => rfl, fun h => (hy h).elim⟩
  · by_cases hy : Z y
    · obtain ⟨«left», marked⟩ := one_conditioned_head_walk D y x Z (inducing_symm D h) hy (headY hy)
      exact ⟨«left», .head, marked.reverse (arrow_graph_symm D.arrow), fun h => (hx h).elim, fun _ => rfl⟩
    · obtain ⟨last, xs, route, _⟩ := (inducing_implies_inseparable D x y h).2 Z hx hy
      obtain ⟨«left», «right», marked⟩ := marked_of_distinct_route (arrowGraph D.arrow)
        (SelectedCondition Z) (AncestorOf (arrowGraph D.arrow) (SelectedCondition Z))
        (Observed x) (Observed y) (fun eq => h.1 (Sum.inl.inj (Sum.inl.inj eq))) route
      exact ⟨«left», «right», marked, fun h => (hx h).elim, fun h => (hy h).elim⟩

theorem directed_head_arrival_route {V : Type u} (G : MarkedGraph V) (C : V → Prop)
    {a b : V} {xs : List V} (h : Route (Directed G) a xs b) (hn : ¬ AncestorOf G C a) :
    ∃ ys, Route (RealStep G C) ⟨a, some .head⟩ ys ⟨b, some .head⟩ := by
  revert hn
  induction h with
  | nil a => intro _; exact ⟨[], .nil _⟩
  | @cons a «next» b rest edge tail ih =>
      intro hn
      obtain ⟨ys, hy⟩ := ih (not_ancestor_successor edge hn)
      refine ⟨⟨«next», some .head⟩ :: ys, .cons ⟨.tail, .head, edge, rfl, ?_⟩ hy⟩
      simpa [ActiveAt] using not_ancestor_condition hn

theorem directed_tail_head_walk {V : Type u} (G : MarkedGraph V) (C : V → Prop)
    {a b : V} (hne : a ≠ b) (h : Reach G a b) (hn : ¬ AncestorOf G C a) :
    MarkedRoute G C (AncestorOf G C) a b .tail .head := by
  obtain ⟨xs, hp⟩ := h
  cases hp with
  | nil => exact (hne rfl).elim
  | cons edge tail =>
      obtain ⟨ys, hy⟩ := directed_head_arrival_route G C tail (not_ancestor_successor edge hn)
      exact ⟨_, .head, ys, edge, hy⟩

theorem selection_ancestor_condition_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x : X) (h : SelectionAncestor D x) :
    AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) := by
  obtain ⟨s, hp⟩ := h
  exact ⟨.inl (.inr s), hp, trivial⟩

theorem nonancestor_tail_reach {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X)
    (hx : ¬ AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) (Observed x))
    (tail : TailFlag D x y) : Reach (arrowGraph D.arrow) (Observed x) (Observed y) := by
  rcases tail with h | h
  · exact h
  · exact (hx (selection_ancestor_condition_ancestor D Z x h)).elim

theorem nonancestor_tail_opposite_not_tail {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X) (hne : x ≠ y)
    (hx : ¬ AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) (Observed x))
    (tail : TailFlag D x y) : ¬ TailFlag D y x := by
  have forward := nonancestor_tail_reach D Z x y hx tail
  rintro (back | selected)
  · have eq := reach_antisymm_of_acyclic (arrowGraph D.arrow) (source_directed_acyclic D) forward back
    exact hne (Sum.inl.inj (Sum.inl.inj eq))
  · exact hx (selection_ancestor_condition_ancestor D Z x (selection_ancestor_predecessor D forward selected))

def BoundaryCompatible {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x : X) (magMark rawMark : Mark) : Prop :=
  (Z x → rawMark = .head) ∧
  (¬ AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) →
    magMark = .tail → rawMark = .tail)

/-- Every literal MAG edge has a same-source active walk satisfying both
boundary rules. The two conditional-head premises are exactly what an
active MAG path supplies at internal vertices, and legal endpoint exclusion
supplies at its endpoints. No complete graph-level representation is assumed. -/
theorem mag_edge_boundary_walk {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (Z : X → Prop) (x y : X) (mx my : Mark)
    (edge : (mag D).edge x y mx my) (headX : Z x → mx = .head) (headY : Z y → my = .head) :
    ∃ «left» «right», MarkedRoute (arrowGraph D.arrow) (SelectedCondition Z)
      (AncestorOf (arrowGraph D.arrow) (SelectedCondition Z))
      (Observed x) (Observed y) «left» «right» ∧
      BoundaryCompatible D Z x mx «left» ∧ BoundaryCompatible D Z y my «right» := by
  classical
  by_cases leftTail : ¬ AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) ∧ mx = .tail
  · have flag : TailFlag D x y := (endpoint_tail_iff D x y).mp (by simpa only [leftTail.2] using edge.2.1)
    have reach := nonancestor_tail_reach D Z x y leftTail.1 flag
    have opposite := nonancestor_tail_opposite_not_tail D Z x y edge.1.1 leftTail.1 flag
    have marked := directed_tail_head_walk (arrowGraph D.arrow) (SelectedCondition Z)
      (fun eq => edge.1.1 (Sum.inl.inj (Sum.inl.inj eq))) reach leftTail.1
    refine ⟨.tail, .head, marked, ⟨?_, fun _ _ => rfl⟩, ⟨fun _ => rfl, ?_⟩⟩
    · intro hz
      exact (not_ancestor_condition leftTail.1 hz).elim
    · intro _ hmy
      exact (opposite ((endpoint_tail_iff D y x).mp (by simpa only [hmy] using edge.2.2))).elim
  · by_cases rightTail : ¬ AncestorOf (arrowGraph D.arrow) (SelectedCondition Z) (Observed y) ∧ my = .tail
    · have flag : TailFlag D y x := (endpoint_tail_iff D y x).mp (by simpa only [rightTail.2] using edge.2.2)
      have reach := nonancestor_tail_reach D Z y x rightTail.1 flag
      have opposite := nonancestor_tail_opposite_not_tail D Z y x edge.1.1.symm rightTail.1 flag
      have marked := directed_tail_head_walk (arrowGraph D.arrow) (SelectedCondition Z)
        (fun eq => edge.1.1.symm (Sum.inl.inj (Sum.inl.inj eq))) reach rightTail.1
      refine ⟨.head, .tail, marked.reverse (arrow_graph_symm D.arrow),
        ⟨fun _ => rfl, ?_⟩, ⟨?_, fun _ _ => rfl⟩⟩
      · intro _ hmx
        exact (opposite ((endpoint_tail_iff D x y).mp (by simpa only [hmx] using edge.2.1))).elim
      · intro hz
        exact (not_ancestor_condition rightTail.1 hz).elim
    · have hx : Z x → ¬ TailFlag D x y := by
        intro hz
        exact (endpoint_head_iff D x y).mp (by simpa only [headX hz] using edge.2.1)
      have hy : Z y → ¬ TailFlag D y x := by
        intro hz
        exact (endpoint_head_iff D y x).mp (by simpa only [headY hz] using edge.2.2)
      obtain ⟨«left», «right», marked, hl, hr⟩ := inducing_walk_conditioned_heads D x y Z edge.1 hx hy
      exact ⟨«left», «right», marked, ⟨hl, fun hn hm => (leftTail ⟨hn, hm⟩).elim⟩,
        ⟨hr, fun hn hm => (rightTail ⟨hn, hm⟩).elim⟩⟩

end RestrictedCausal.EdgeWalks
