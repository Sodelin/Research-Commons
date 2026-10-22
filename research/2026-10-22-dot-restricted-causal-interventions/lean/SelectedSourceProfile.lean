import CanonicalSelectionProfile

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. Not elaborated or kernel checked.
Pinned Lean v4.33.1 / mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

B2 and explicit portions of B5/B9: extract the profile from an arbitrary
selected mixed graph; lift every marked virtual edge through its actual
selection component; show exact profile behavior under one named soft root.

The original DAG-to-selected-mixed-graph projection is NOT assumed as a field.
Its proof is still required in Layer A/B1. Selection types are arbitrary here;
no finite latent or selector bound is imposed on the original carrier.
-/

namespace RestrictedCausal.SourceSelection

open SelectedWalk CanonicalSelection

universe u v

/-- The actual post-latent-projection data: an observed mixed graph, marked
observed/selected incidences, and bidirected edges among selection vertices. -/
structure SelectedGraph (X : Type u) (S : Type v) where
  observed : MarkedGraph X
  boundary : X → Mark → S → Prop
  selectionEdge : S → S → Prop
  selection_symm : ∀ {s t}, selectionEdge s t → selectionEdge t s

def graph {X : Type u} {S : Type v} (H : SelectedGraph X S) :
    MarkedGraph (Sum X S) where
  edge a b ma mb := match a, b with
    | .inl x, .inl y => H.observed.edge x y ma mb
    | .inl x, .inr s => H.boundary x ma s ∧ mb = .head
    | .inr s, .inl x => H.boundary x mb s ∧ ma = .head
    | .inr s, .inr t => H.selectionEdge s t ∧ ma = .head ∧ mb = .head

def isSelected {X : Type u} {S : Type v} : Sum X S → Prop
  | .inl _ => False
  | .inr _ => True

theorem selection_heads {X : Type u} {S : Type v} (H : SelectedGraph X S) :
    SelectionHeads (graph H) isSelected := by
  intro a b ma mb hedge
  cases a with
  | inl x =>
      cases b with
      | inl y => exact ⟨False.elim, False.elim⟩
      | inr s => exact ⟨False.elim, fun _ => hedge.2⟩
  | inr s =>
      cases b with
      | inl y => exact ⟨fun _ => hedge.2, False.elim⟩
      | inr t => exact ⟨fun _ => hedge.2.1, fun _ => hedge.2.2⟩

def Component {X : Type u} {S : Type v} (H : SelectedGraph X S) (s t : S) : Prop :=
  ∃ xs, Route H.selectionEdge s xs t

theorem Component.symm {X : Type u} {S : Type v} {H : SelectedGraph X S}
    {s t : S} (h : Component H s t) : Component H t s := by
  obtain ⟨xs, hx⟩ := h
  exact hx.reverse_exists H.selection_symm

def Parent {X : Type u} {S : Type v} (H : SelectedGraph X S) (x : X) : Prop :=
  ∃ s, H.boundary x .tail s

def Bridge {X : Type u} {S : Type v} (H : SelectedGraph X S)
    (x : X) (mx : Mark) (y : X) (my : Mark) : Prop :=
  x ≠ y ∧ ∃ s t, H.boundary x mx s ∧ Component H s t ∧ H.boundary y my t

def profile {X : Type u} {S : Type v} (H : SelectedGraph X S) : Profile X where
  observed := H.observed
  parent := Parent H
  bridge := Bridge H
  bridge_ne := fun h => h.1
  bridge_symm := by
    rintro x mx y my ⟨hne, s, t, hx, hst, hy⟩
    exact ⟨hne.symm, t, s, hy, hst.symm, hx⟩
  bridge_tails := by
    rintro x mx y my ⟨_, s, t, hx, _, hy⟩
    constructor
    · intro hm
      subst mx
      exact ⟨s, hx⟩
    · intro hm
      subst my
      exact ⟨t, hy⟩

/-- Incidence arrivals inside a selected block always carry a head. -/
def selectedArrival {X : Type u} {S : Type v} (s : S) : Arrival (Sum X S) :=
  ⟨.inr s, some .head⟩

def observedArrival {X : Type u} {S : Type v} (x : X) (m : Option Mark) :
    Arrival (Sum X S) := ⟨.inl x, m⟩

/-- Consume precisely the initial consecutive selected block. The returned
equation records the original list, not just endpoint reachability, so later
contraction can inherit the original observed-vertex distinctness. -/
theorem split_selected_prefix {X : Type u} {S : Type v} (H : SelectedGraph X S)
    {C A : Sum X S → Prop} {s : S} {xs : List (Arrival (Sum X S))}
    {y : X} {lastMark : Option Mark}
    (h : Route (Transition (graph H) C A) (selectedArrival s) xs
      (observedArrival y lastMark)) :
    ∃ t selectedVertices x m rest,
      Route H.selectionEdge s selectedVertices t ∧
      H.boundary x m t ∧
      Route (Transition (graph H) C A) (observedArrival x (some m)) rest
        (observedArrival y lastMark) ∧
      xs = selectedVertices.map selectedArrival ++
        observedArrival x (some m) :: rest := by
  induction xs generalizing s with
  | nil => cases h
  | cons next xs ih =>
      cases h with
      | cons hstep htail =>
          rcases next with ⟨nextVertex, nextMark⟩
          cases nextVertex with
          | inl x =>
              obtain ⟨outgoing, incoming, hedge, hmark, _⟩ := hstep
              change nextMark = some incoming at hmark
              subst nextMark
              exact ⟨s, [], x, incoming, xs, .nil s, hedge.1, htail, rfl⟩
          | inr t =>
              obtain ⟨outgoing, incoming, hedge, hmark, _⟩ := hstep
              have hm : nextMark = some .head :=
                hmark.trans (congrArg some hedge.2.2)
              subst nextMark
              obtain ⟨r, vs, x, m, rest, htr, hboundary, hrest, heq⟩ := ih htail
              refine ⟨r, t :: vs, x, m, rest, .cons hedge.1 htr,
                hboundary, hrest, ?_⟩
              simpa only [List.map_cons, List.cons_append] using
                congrArg (List.cons (selectedArrival t)) heq

theorem lift_selection_route {X : Type u} {S : Type v} (H : SelectedGraph X S)
    {C A : Sum X S → Prop} (selected_active : ∀ s, A (.inr s))
    {s t : S} {xs : List S} (h : Route H.selectionEdge s xs t) :
    Route (Transition (graph H) C A) (selectedArrival s)
      (xs.map selectedArrival) (selectedArrival t) := by
  induction h with
  | nil s => exact .nil (selectedArrival s)
  | @cons s t r xs hst htr ih =>
      apply Route.cons _ ih
      refine ⟨.head, .head, ⟨hst, rfl, rfl⟩, rfl, ?_⟩
      simpa [selectedArrival, ActiveAt] using selected_active s

/-- Every compressed marked pair has a concrete lifted active block. Its only
observed vertices are its two endpoints. The chosen incoming mark at the
left endpoint is retained, so bow choices and collider activity are not lost. -/
theorem lift_bridge {X : Type u} {S : Type v} (H : SelectedGraph X S)
    {C A : Sum X S → Prop} (selected_active : ∀ s, A (.inr s))
    {x y : X} {mx my : Mark} {previous : Option Mark}
    (hbridge : Bridge H x mx y my)
    (left_active : match previous with
      | none => True
      | some m => ActiveAt C A (.inl x) m mx) :
    ∃ selectedStates : List (Arrival (Sum X S)),
      (∀ p ∈ selectedStates, isSelected p.vertex) ∧
      Route (Transition (graph H) C A) ⟨.inl x, previous⟩
        (selectedStates ++ [⟨.inl y, some my⟩]) ⟨.inl y, some my⟩ := by
  obtain ⟨_, s, t, hx, ⟨xs, hst⟩, hy⟩ := hbridge
  let middle := selectedArrival s :: xs.map selectedArrival
  have hfirst : Transition (graph H) C A ⟨.inl x, previous⟩ (selectedArrival s) :=
    ⟨mx, .head, ⟨hx, rfl⟩, rfl, left_active⟩
  have hlast : Transition (graph H) C A (selectedArrival t) ⟨.inl y, some my⟩ := by
    refine ⟨.head, my, ⟨hy, rfl⟩, rfl, ?_⟩
    simpa [selectedArrival, ActiveAt] using selected_active t
  refine ⟨middle, ?_, ?_⟩
  · intro p hp
    rcases List.mem_cons.mp hp with hps | hp
    · subst p
      trivial
    · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
      trivial
  · exact (Route.cons hfirst (lift_selection_route H selected_active hst)).append
      (.cons hlast (.nil _))

/-- The compressed edge explicitly remembers the two marks and the departure
activity. It is either one old observed edge or one entire selection block. -/
def CompressedTransition {X : Type u} {S : Type v} (H : SelectedGraph X S)
    (C A : Sum X S → Prop) (p q : Arrival (Sum X S)) : Prop :=
  ∃ x y outgoing incoming,
    p.vertex = .inl x ∧ q.vertex = .inl y ∧
    q.incoming = some incoming ∧
    (match p.incoming with
      | none => True
      | some previous => ActiveAt C A p.vertex previous outgoing) ∧
    (H.observed.edge x y outgoing incoming ∨ Bridge H x outgoing y incoming)

def observedValue {X : Type u} {S : Type v} (p : Arrival (Sum X S)) : Option X :=
  match p.vertex with
  | .inl x => some x
  | .inr _ => none

theorem noObservedRepeat_iff_trace_nodup {X : Type u} {S : Type v}
    (xs : List (Arrival (Sum X S))) :
    NoObservedRepeat isSelected xs ↔ (xs.filterMap observedValue).Nodup := by
  unfold NoObservedRepeat
  rw [List.Nodup, List.pairwise_filterMap]
  apply List.Pairwise.iff_of_mem
  intro p q _ _
  rcases p with ⟨pv, pm⟩
  rcases q with ⟨qv, qm⟩
  cases pv <;> cases qv <;> simp [observedValue, isSelected]

theorem selected_trace_nil {X : Type u} {S : Type v}
    {xs : List (Arrival (Sum X S))}
    (h : ∀ p ∈ xs, isSelected p.vertex) : xs.filterMap observedValue = [] := by
  revert h
  induction xs with
  | nil => intro h; rfl
  | cons p ps ih =>
      intro h
      have hp := h p List.mem_cons_self
      have ht : ∀ q ∈ ps, isSelected q.vertex :=
        fun q hq => h q (List.mem_cons_of_mem _ hq)
      rcases p with ⟨pv, pm⟩
      cases pv with
      | inl x => exact hp.elim
      | inr s => simpa [observedValue] using ih ht

theorem lift_compressed_step {X : Type u} {S : Type v} (H : SelectedGraph X S)
    {C A : Sum X S → Prop} (selected_active : ∀ s, A (.inr s))
    {p q : Arrival (Sum X S)} (h : CompressedTransition H C A p q) :
    ∃ selectedStates : List (Arrival (Sum X S)),
      (∀ r ∈ selectedStates, isSelected r.vertex) ∧
      Route (Transition (graph H) C A) p (selectedStates ++ [q]) q := by
  obtain ⟨x, y, outgoing, incoming, hp, hq, hmark, hactive, hedge⟩ := h
  rcases p with ⟨pv, pm⟩
  rcases q with ⟨qv, qm⟩
  change pv = .inl x at hp
  change qv = .inl y at hq
  change qm = some incoming at hmark
  subst pv
  subst qv
  subst qm
  rcases hedge with hdirect | hbridge
  · refine ⟨[], ?_, .cons ?_ (.nil _)⟩
    · intro r hr
      cases hr
    · exact ⟨outgoing, incoming, hdirect, rfl, hactive⟩
  · exact lift_bridge H selected_active hbridge hactive

/-- B5 lifting with an exact observed trace invariant, not an assertion that
independently chosen selection-component paths are already jointly simple. -/
theorem lift_compressed_route {X : Type u} {S : Type v} (H : SelectedGraph X S)
    {C A : Sum X S → Prop} (selected_active : ∀ s, A (.inr s))
    {p q : Arrival (Sum X S)} {xs : List (Arrival (Sum X S))}
    (h : Route (CompressedTransition H C A) p xs q) :
    ∃ ys, Route (Transition (graph H) C A) p ys q ∧
      ys.filterMap observedValue = xs.filterMap observedValue := by
  induction h with
  | nil p => exact ⟨[], .nil p, rfl⟩
  | @cons p q r xs hpq hqr ih =>
      obtain ⟨middle, hm, hblock⟩ := lift_compressed_step H selected_active hpq
      obtain ⟨ys, hy, htrace⟩ := ih
      refine ⟨(middle ++ [q]) ++ ys, hblock.append hy, ?_⟩
      calc
        ((middle ++ [q]) ++ ys).filterMap observedValue =
            [q].filterMap observedValue ++ ys.filterMap observedValue := by
          simp only [List.filterMap_append, selected_trace_nil hm, List.nil_append]
        _ = [q].filterMap observedValue ++ xs.filterMap observedValue := by rw [htrace]
        _ = (q :: xs).filterMap observedValue := by rw [← List.filterMap_append]; rfl

/-- A distinct-observed compressed route is realized by a simple active
physical path after the proved B6 reduction; selected repetitions are allowed
during lifting and are not hidden under a false simple-path assumption. -/
theorem compressed_route_realizes_simple {X : Type u} {S : Type v}
    (H : SelectedGraph X S) {C A : Sum X S → Prop}
    (selected_active : ∀ s, A (.inr s))
    {x y : X} {lastMark : Option Mark} {xs : List (Arrival (Sum X S))}
    (h : Route (CompressedTransition H C A) (observedArrival x none) xs
      (observedArrival y lastMark))
    (hobs : NoObservedRepeat isSelected (observedArrival x none :: xs)) :
    ∃ ys, Route (Transition (graph H) C A) (observedArrival x none) ys
      (observedArrival y lastMark) ∧
      ((observedArrival x none :: ys).map Arrival.vertex).Nodup := by
  obtain ⟨ys, hy, htrace⟩ := lift_compressed_route H selected_active h
  have hobslift : NoObservedRepeat isSelected (observedArrival x none :: ys) := by
    apply (noObservedRepeat_iff_trace_nodup _).mpr
    have hs := (noObservedRepeat_iff_trace_nodup _).mp hobs
    change (x :: ys.filterMap observedValue).Nodup
    rw [htrace]
    exact hs
  obtain ⟨zs, hz, hsimple, _⟩ :=
    selected_walk_to_simple_path (selection_heads H) (fun hfalse => hfalse) hy hobslift
  exact ⟨zs, hz, hsimple⟩

/-- Strong induction is justified by the actual tail length. The output is
an ordered sublist of the original arrivals, not a newly invented path. -/
private theorem contract_aux {X : Type u} {S : Type v} (H : SelectedGraph X S)
    {C A : Sum X S → Prop} (n : Nat) :
    ∀ (x : X) (previous : Option Mark) (xs : List (Arrival (Sum X S)))
      (y : X) (lastMark : Option Mark), xs.length = n →
      Route (Transition (graph H) C A) (observedArrival x previous) xs
        (observedArrival y lastMark) →
      NoObservedRepeat isSelected (observedArrival x previous :: xs) →
      ∃ ys, Route (CompressedTransition H C A) (observedArrival x previous) ys
        (observedArrival y lastMark) ∧ ys <+ xs := by
  refine Nat.strongRecOn n ?_
  intro n ih x previous xs y lastMark hlen h hobs
  cases xs with
  | nil =>
      cases h
      exact ⟨[], .nil _, List.Sublist.refl _⟩
  | cons next rest =>
      cases h with
      | cons hstep htail =>
          rcases next with ⟨nextVertex, nextMark⟩
          cases nextVertex with
          | inl z =>
              have hlt : rest.length < n := by
                simp only [List.length_cons] at hlen
                omega
              have hobstail : NoObservedRepeat isSelected
                  (observedArrival z nextMark :: rest) := List.Pairwise.of_cons hobs
              obtain ⟨ys, hy, hsub⟩ :=
                ih rest.length hlt z nextMark rest y lastMark rfl htail hobstail
              obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hstep
              have hc : CompressedTransition H C A (observedArrival x previous)
                  (observedArrival z nextMark) :=
                ⟨x, z, outgoing, incoming, rfl, rfl, hmark, hactive, Or.inl hedge⟩
              exact ⟨observedArrival z nextMark :: ys, .cons hc hy,
                hsub.cons_cons _⟩
          | inr s =>
              obtain ⟨outgoing, incoming, hedge, hmark, hactive⟩ := hstep
              have hm : nextMark = some .head := hmark.trans (congrArg some hedge.2)
              subst nextMark
              obtain ⟨t, vs, z, m, tail, hselected, hboundary, hrest, heq⟩ :=
                split_selected_prefix H htail
              have hlt : tail.length < n := by
                rw [heq] at hlen
                simp only [List.length_cons, List.length_append, List.length_map] at hlen
                omega
              have hmem : observedArrival z (some m) ∈ selectedArrival s :: rest := by
                rw [heq]
                exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
              have hne : x ≠ z := by
                intro hxz
                exact (List.rel_of_pairwise_cons hobs hmem) (congrArg Sum.inl hxz)
              have hsubtail : (observedArrival z (some m) :: tail) <+
                  (observedArrival x previous :: selectedArrival s :: rest) := by
                rw [heq]
                exact ((List.sublist_append_right (vs.map selectedArrival)
                  (observedArrival z (some m) :: tail)).cons _).cons _
              have hobstail : NoObservedRepeat isSelected
                  (observedArrival z (some m) :: tail) := hobs.sublist hsubtail
              obtain ⟨ys, hy, hsub⟩ :=
                ih tail.length hlt z (some m) tail y lastMark rfl hrest hobstail
              have hbridge : Bridge H x outgoing z m :=
                ⟨hne, s, t, hedge.1, ⟨vs, hselected⟩, hboundary⟩
              have hc : CompressedTransition H C A (observedArrival x previous)
                  (observedArrival z (some m)) :=
                ⟨x, z, outgoing, m, rfl, rfl, rfl, hactive, Or.inr hbridge⟩
              have hs : (observedArrival z (some m) :: ys) <+ rest := by
                rw [heq]
                exact (hsub.cons_cons _).trans (List.sublist_append_right _ _)
              exact ⟨observedArrival z (some m) :: ys, .cons hc hy,
                hs.cons (selectedArrival s)⟩

/-- B4: contract every consecutive selection block, preserving observed local
marks, activity and endpoint labels. Original observed distinctness is kept
by the returned sublist and may be transported with `Pairwise.sublist`. -/
theorem contract_active_route {X : Type u} {S : Type v} (H : SelectedGraph X S)
    {C A : Sum X S → Prop} {x y : X} {previous lastMark : Option Mark}
    {xs : List (Arrival (Sum X S))}
    (h : Route (Transition (graph H) C A) (observedArrival x previous) xs
      (observedArrival y lastMark))
    (hobs : NoObservedRepeat isSelected (observedArrival x previous :: xs)) :
    ∃ ys, Route (CompressedTransition H C A) (observedArrival x previous) ys
      (observedArrival y lastMark) ∧ ys <+ xs :=
  contract_aux H xs.length x previous xs y lastMark rfl h hobs

/-- Named root augmentation changes only H_X; boundary incidences and the
entire selection-component relation remain the same. This is soft root
augmentation, not hard deletion of incoming arrows. -/
def augmentObserved {X : Type u} (G : MarkedGraph X) (target : X) :
    MarkedGraph (Option X) where
  edge a b ma mb := match a, b with
    | some x, some y => G.edge x y ma mb
    | none, some y => y = target ∧ ma = .tail ∧ mb = .head
    | some x, none => x = target ∧ ma = .head ∧ mb = .tail
    | none, none => False

def augment {X : Type u} {S : Type v} (H : SelectedGraph X S) (target : X) :
    SelectedGraph (Option X) S where
  observed := augmentObserved H.observed target
  boundary x m s := match x with
    | none => False
    | some x => H.boundary x m s
  selectionEdge := H.selectionEdge
  selection_symm := H.selection_symm

theorem augment_parent_old {X : Type u} {S : Type v} (H : SelectedGraph X S)
    (target x : X) : (profile (augment H target)).parent (some x) ↔ (profile H).parent x :=
  Iff.rfl

theorem augment_parent_root {X : Type u} {S : Type v} (H : SelectedGraph X S)
    (target : X) : ¬ (profile (augment H target)).parent none := by
  rintro ⟨s, h⟩
  exact h

theorem augment_bridge_old {X : Type u} {S : Type v} (H : SelectedGraph X S)
    (target x y : X) (mx my : Mark) :
    (profile (augment H target)).bridge (some x) mx (some y) my ↔
      (profile H).bridge x mx y my := by
  change (some x ≠ some y ∧ _) ↔ (x ≠ y ∧ _)
  simp only [ne_eq, Option.some.injEq]

theorem augment_bridge_root_left {X : Type u} {S : Type v}
    (H : SelectedGraph X S) (target : X) (y : Option X) (mx my : Mark) :
    ¬ (profile (augment H target)).bridge none mx y my := by
  rintro ⟨_, s, t, h, _, _⟩
  exact h

theorem augment_bridge_root_right {X : Type u} {S : Type v}
    (H : SelectedGraph X S) (target : X) (x : Option X) (mx my : Mark) :
    ¬ (profile (augment H target)).bridge x mx none my := by
  rintro ⟨_, s, t, _, _, h⟩
  exact h

end RestrictedCausal.SourceSelection
