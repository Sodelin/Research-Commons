import ShortestPathStatusInvariance

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The directed-tail part of the closest-path ancestry argument. A minimum
directed route to Z has only unshielded triples. Once its first arrow is
preserved, every later arrow is forced by the shared-separator unshielded
status and the actual incoming head. The first-arrow closest-path lemma is
deliberately not a premise silently promoted to a completed theorem.
Classical attribution: Ali--Richardson--Spirtes (2009), Lemma 3.26 and
Corollary 3.27; those exact primary-source proofs were re-inspected.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation HPLTarget
open DiscriminatingStatus AncestralShortcutGeometry WeakInducing

universe u

structure MinimumDirectedPath {V : Type u} (G : MarkedGraph V) (Z : V → Prop)
    (start : V) (vertices : List V) (finish : V) : Prop where
  route : Route (Directed G) start vertices finish
  endpoint : Z finish
  minimal : ∀ last xs, Route (Directed G) start xs last → Z last → vertices.length ≤ xs.length

theorem minimum_directed_path_exists {V : Type u} (G : MarkedGraph V) (Z : V → Prop) (b : V)
    (ancestor : SourceSelection.AncestorOf G Z b) :
    ∃ vertices finish, MinimumDirectedPath G Z b vertices finish ∧
      vertices.length = directedDistance G Z b := by
  obtain ⟨⟨finish, vertices, route, endpoint, length⟩, bound⟩ := directedDistance_spec G Z b ancestor
  exact ⟨vertices, finish, ⟨route, endpoint, fun last xs route endpoint => by
    rw [length]
    exact bound xs.length ⟨last, xs, route, endpoint, rfl⟩⟩, length⟩

theorem directed_triangle_shortcut {V : Type u} (G : MarkedGraph V) (laws : AncestralLaws G)
    {a b c : V} (first : Directed G a b) (last : Directed G b c)
    (adjacent : Adjacent G a c) : Directed G a c := by
  obtain ⟨left, right, edge⟩ := adjacent
  have rightHead := head_directed_triangle G laws first last edge
  subst right
  cases left with
  | tail => exact edge
  | head =>
      exact (laws.head_not_ancestor a c .head edge ⟨[b, c], .cons first (.cons last (.nil c))⟩).elim

theorem minimum_directed_tail {V : Type u} (G : MarkedGraph V) (Z : V → Prop)
    {a b finish : V} {vertices : List V}
    (path : MinimumDirectedPath G Z a (b :: vertices) finish) :
    MinimumDirectedPath G Z b vertices finish := by
  cases path.route with
  | cons first tail =>
      refine ⟨tail, path.endpoint, ?_⟩
      intro last xs route endpoint
      have bound := path.minimal last (b :: xs) (.cons first route) endpoint
      simp only [List.length_cons] at bound
      omega

theorem minimum_directed_unshielded {V : Type u} (G : MarkedGraph V) (laws : AncestralLaws G)
    (Z : V → Prop) {start finish : V} {vertices : List V}
    (path : MinimumDirectedPath G Z start vertices finish) :
    AllTriples (fun a _ c => ¬ Adjacent G a c) (start :: vertices) := by
  induction vertices generalizing start with
  | nil => trivial
  | cons b vertices ih =>
      cases vertices with
      | nil => trivial
      | cons c rest =>
          constructor
          · intro adjacent
            cases path.route with
            | cons first tail =>
                cases tail with
                | cons last suffix =>
                    have shortcut := directed_triangle_shortcut G laws first last adjacent
                    have bound := path.minimal finish (c :: rest) (.cons shortcut suffix) path.endpoint
                    simp only [List.length_cons] at bound
                    omega
          · exact ih (minimum_directed_tail G Z path)

theorem directed_two_step_simple {V : Type u} (G : MarkedGraph V) (laws : AncestralLaws G)
    {a b c : V} (first : Directed G a b) (last : Directed G b c) :
    ([a, b, c] : List V).Nodup := by
  have ab : a ≠ b := by intro same; subst b; exact laws.irreflexive a .tail .head first
  have bc : b ≠ c := by intro same; subst c; exact laws.irreflexive b .tail .head last
  have ac : a ≠ c := by
    intro same
    subst c
    have impossible := laws.acyclic a [b, a] (.cons first (.cons last (.nil a)))
    cases impossible
  simp [ab, bc, ac]

theorem head_noncollider_forces_directed {V : Type u} (H : MarkedGraph V) (laws : AncestralLaws H)
    {a b c : V} {m : Mark} (incoming : H.edge a b m .head)
    (adjacent : Adjacent H b c) (noncollider : ¬ Collider H a b c) : Directed H b c := by
  obtain ⟨left, right, edge⟩ := adjacent
  have leftTail : left = .tail := by
    cases left with
    | tail => rfl
    | head => exact (noncollider ⟨m, right, incoming, edge⟩).elim
  subst left
  cases right with
  | head => exact edge
  | tail => exact (laws.undirected_no_heads b c a m edge (laws.symmetric a b m .head incoming)).elim

theorem unshielded_directed_step_transfers {V : Type u} (G H : MarkedGraph V)
    (lawsG : AncestralLaws G) (lawsH : AncestralLaws H)
    (singleG : SingleEdges G) (singleH : SingleEdges H)
    (skeleton : ∀ a b, Adjacent G a b ↔ Adjacent H a b) (shared : SharedSeparators G H)
    {a b c : V} (firstG : Directed G a b) (lastG : Directed G b c)
    (firstH : Directed H a b) (nonadjacent : ¬ Adjacent G a c) : Directed H b c := by
  have simple := directed_two_step_simple G lawsG firstG lastG
  have distinct : a ≠ c := by
    intro same
    apply (List.nodup_cons.mp simple).1
    exact List.mem_cons_of_mem _ (by simpa only [List.mem_singleton] using same)
  have status := shared_separators_unshielded G H singleG singleH skeleton shared a b c distinct
    ⟨.tail, .head, firstG⟩ ⟨.tail, .head, lastG⟩ nonadjacent simple
  have sourceNoncollider : ¬ Collider G a b c := by
    intro collider
    have marks := (collider_iff_chosen_marks G singleG a b c .tail .head .tail .head firstG lastG).mp collider
    cases marks.2
  have targetNoncollider : ¬ Collider H a b c := fun collider => sourceNoncollider (status.mpr collider)
  exact head_noncollider_forces_directed H lawsH firstH
    ((skeleton b c).mp ⟨.tail, .head, lastG⟩) targetNoncollider

theorem directed_tail_transfers {V : Type u} (G H : MarkedGraph V)
    (lawsG : AncestralLaws G) (lawsH : AncestralLaws H)
    (singleG : SingleEdges G) (singleH : SingleEdges H)
    (skeleton : ∀ a b, Adjacent G a b ↔ Adjacent H a b) (shared : SharedSeparators G H)
    {p q : V} {vertices : List V} (route : Route (Directed G) p vertices q) :
    ∀ a, Directed G a p → Directed H a p →
      AllTriples (fun x _ z => ¬ Adjacent G x z) (a :: p :: vertices) →
      Route (Directed H) p vertices q := by
  induction route with
  | nil p => intro _ _ _ _; exact .nil p
  | @cons p next q rest step tail ih =>
      intro a firstG firstH unshielded
      have nextH := unshielded_directed_step_transfers G H lawsG lawsH singleG singleH skeleton shared
        firstG step firstH unshielded.1
      exact .cons nextH (ih p step nextH unshielded.2)

/-- The exact remaining closest-path obligation is the first arrow. Once it
is supplied, the entire minimum directed path reaches the SAME z in Z in H.
This theorem does not assert that every arbitrary first arrow is invariant. -/
theorem minimum_directed_path_transfers_from_first {V : Type u} (G H : MarkedGraph V)
    (lawsG : AncestralLaws G) (lawsH : AncestralLaws H)
    (singleG : SingleEdges G) (singleH : SingleEdges H)
    (skeleton : ∀ a b, Adjacent G a b ↔ Adjacent H a b) (shared : SharedSeparators G H)
    (Z : V → Prop) {start first finish : V} {rest : List V}
    (path : MinimumDirectedPath G Z start (first :: rest) finish)
    (firstH : Directed H start first) :
    Route (Directed H) start (first :: rest) finish ∧ SourceSelection.AncestorOf H Z start := by
  have unshielded := minimum_directed_unshielded G lawsG Z path
  cases path.route with
  | cons firstG tail =>
      have targetTail := directed_tail_transfers G H lawsG lawsH singleG singleH skeleton shared
        tail start firstG firstH unshielded
      have target : Route (Directed H) start (first :: rest) finish := .cons firstH targetTail
      exact ⟨target, finish, ⟨first :: rest, target⟩, path.endpoint⟩

end RestrictedCausal.VertexActivePaths
