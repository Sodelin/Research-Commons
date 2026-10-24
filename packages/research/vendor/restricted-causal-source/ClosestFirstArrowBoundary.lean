import ClosestFirstArrowGeometry

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual finite stopping-boundary extraction for the closest-path first-arrow
argument. The predicate is on the departure incidence, not just the arrival
mark: the outgoing head and parent arrow must BOTH be present. Thus a
conditioned-parent surrogate is not silently substituted for the classical
collider-parent scan. Attribution: Ali--Richardson--Spirtes (2009), Lemma 3.25.
-/

namespace RestrictedCausal.SelectedWalk.Route

universe u

theorem last_bad_step {V : Type u} {R : V → V → Prop} (Good : V → V → Prop)
    {p q : V} {xs : List V} (route : Route R p xs q) :
    Route (fun a b => R a b ∧ Good a b) p xs q ∨
      ∃ a b front rest, xs = front ++ (b :: rest) ∧
        Route R p front a ∧ R a b ∧ ¬ Good a b ∧
        Route (fun v w => R v w ∧ Good v w) b rest q := by
  classical
  induction route with
  | nil p => exact Or.inl (.nil p)
  | @cons p «next» q rest step tail ih =>
      rcases ih with goodTail | ⟨a, b, front, suffix, equation, before, boundary, bad, after⟩
      · by_cases good : Good p «next»
        · exact Or.inl (.cons ⟨step, good⟩ goodTail)
        · exact Or.inr ⟨p, «next», [], rest, rfl, .nil p, step, good, goodTail⟩
      · exact Or.inr ⟨a, b, «next» :: front, suffix,
          by simpa only [List.cons_append, equation], .cons step before, boundary, bad, after⟩

end RestrictedCausal.SelectedWalk.Route

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open DiscriminatingStatus AncestralShortcutGeometry WeakInducing

universe u

def StrictParentStep {V : Type u} (G : MarkedGraph V) (d : V) (p q : Arrival V) : Prop :=
  ColliderParentStep G d p q ∧ p.incoming = some .head

theorem strict_parent_route_forget {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (d : V)
    {p q : Arrival V} {xs : List (Arrival V)}
    (route : Route (fun a b => RealStep G Z a b ∧ StrictParentStep G d a b) p xs q) :
    Route (ColliderParentStep G d) p xs q := by
  induction route with
  | nil p => exact .nil p
  | cons step tail ih => exact .cons step.2.1 ih

/-- Root arrival is not a collider, so the actual finite scan necessarily
stops. The returned decomposition retains the old complete prefix, not
merely a subsequence or an independently chosen discriminating witness. -/
theorem extract_first_arrow_boundary {V : Type u} (G : MarkedGraph V) (Z : V → Prop)
    (x d : V) {b : Arrival V} {«prefix» : List (Arrival V)}
    (before : Route (RealStep G Z) ⟨x, none⟩ «prefix» b)
    (incoming : b.incoming = some .head) :
    ∃ a «next» front rest, «prefix» = front ++ («next» :: rest) ∧
      Route (RealStep G Z) ⟨x, none⟩ front a ∧ RealStep G Z a «next» ∧
      ¬ StrictParentStep G d a «next» ∧
      Route (fun p q => RealStep G Z p q ∧ StrictParentStep G d p q) «next» rest b := by
  rcases before.last_bad_step (StrictParentStep G d) with all | boundary
  · cases all with
    | nil => cases incoming
    | cons step tail => cases step.2.2
  · exact boundary

theorem boundary_next_head {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (d : V)
    {«next» b : Arrival V} {rest : List (Arrival V)}
    (after : Route (fun p q => RealStep G Z p q ∧ StrictParentStep G d p q) «next» rest b)
    (lastHead : b.incoming = some .head) : «next».incoming = some .head := by
  cases after with
  | nil => exact lastHead
  | cons step tail => exact step.2.2

theorem boundary_next_parent {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (d : V)
    {«next» b : Arrival V} {rest : List (Arrival V)}
    (after : Route (fun p q => RealStep G Z p q ∧ StrictParentStep G d p q) «next» rest b)
    (lastParent : Directed G b.vertex d) : Directed G «next».vertex d := by
  cases after with
  | nil => exact lastParent
  | cons step tail =>
      obtain ⟨outgoing, incoming, edge, mark, details⟩ := step.2.1
      have all : Mark.head = .head ∧ outgoing = .head ∧ Directed G «next».vertex d := by
        simpa only [step.2.2] using details
      exact all.2.2

/-- Adjacency at the actual stopping boundary gives an active replacement
departure to d. For a head replacement, an old tail would create a forbidden
ancestral triangle. For a tail replacement, an old collider-parent would
contradict the defining stopping condition. Root endpoints are explicit. -/
theorem stopped_boundary_replacement {V : Type u} (G : MarkedGraph V)
    (laws : AncestralLaws G) (single : SingleEdges G) (Z : V → Prop) (d : V)
    {a «next» b : Arrival V} {rest : List (Arrival V)}
    (boundary : RealStep G Z a «next») (stopped : ¬ StrictParentStep G d a «next»)
    (after : Route (fun p q => RealStep G Z p q ∧ StrictParentStep G d p q) «next» rest b)
    (lastHead : b.incoming = some .head) (lastParent : Directed G b.vertex d)
    (adjacent : Adjacent G a.vertex d) :
    ∃ outgoing, G.edge a.vertex d outgoing .head ∧
      DepartureAllowed Z (SourceSelection.AncestorOf G Z) a.vertex a.incoming outgoing := by
  have nextHead := boundary_next_head G Z d after lastHead
  have nextParent := boundary_next_parent G Z d after lastParent
  obtain ⟨oldOut, oldIn, oldEdge, oldMark, oldActive⟩ := boundary
  have oldInHead : oldIn = .head := Option.some.inj (oldMark.symm.trans nextHead)
  subst oldIn
  obtain ⟨newOut, newIn, newEdge⟩ := adjacent
  have newInHead := head_directed_triangle G laws oldEdge nextParent newEdge
  subst newIn
  refine ⟨newOut, newEdge, ?_⟩
  cases arrival : a.incoming with
  | none => trivial
  | some previous =>
      have oldReady : ActiveAt Z (SourceSelection.AncestorOf G Z) a.vertex previous oldOut := by
        simpa only [arrival] using oldActive
      change ActiveAt Z (SourceSelection.AncestorOf G Z) a.vertex previous newOut
      cases newOut with
      | head =>
          have oldOutHead : oldOut = .head := by
            cases oldOut with
            | head => rfl
            | tail =>
                exact (laws.head_not_ancestor a.vertex d .head newEdge
                  ⟨[«next».vertex, d], .cons oldEdge (.cons nextParent (.nil d))⟩).elim
          simpa only [oldOutHead] using oldReady
      | tail =>
          have notOldCollider : ¬ (previous = .head ∧ oldOut = .head) := by
            intro both
            apply stopped
            refine ⟨⟨oldOut, .head, oldEdge, oldMark, ?_⟩, ?_⟩
            · simpa only [arrival] using (show previous = .head ∧ oldOut = .head ∧
                Directed G a.vertex d from ⟨both.1, both.2, newEdge⟩)
            · exact arrival.trans (congrArg some both.1)
          have outside : ¬ Z a.vertex := by
            simpa only [ActiveAt, if_neg notOldCollider] using oldReady
          simpa [ActiveAt] using outside

end RestrictedCausal.VertexActivePaths
