import Mathlib.Data.List.Nodup

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. Not elaborated, executed, or kernel checked.

Read-only API pin: Lean v4.33.1; mathlib
0df444a360eaa60ab8c11dca51a86af692955474.
This package does NOT import the separately hosted Lean 4.35 G7 provider.
Porting and full dependency checking remain explicit integration obligations.

This is a proof-bearing component of B6 in FULL-CLAIM-FORMALIZATION-HANDOFF.md,
not the full selected causal theorem. No graph-compression axiom is assumed.
The graph is bow-aware: each transition carries two chosen endpoint marks.
The source proof is classical existence, not an evaluated erasure algorithm.
-/

namespace RestrictedCausal.SelectedWalk

universe u

/-- `xs` contains every vertex after the starting vertex, including the end. -/
inductive Route {α : Type u} (R : α → α → Prop) : α → List α → α → Prop
  | nil (a : α) : Route R a [] a
  | cons {a b c : α} {xs : List α} (step : R a b)
      (tail : Route R b xs c) : Route R a (b :: xs) c

namespace Route

variable {α : Type u} {R : α → α → Prop}

theorem append {a b c : α} {xs ys : List α}
    (h : Route R a xs b) (k : Route R b ys c) :
    Route R a (xs ++ ys) c := by
  induction h with
  | nil => exact k
  | cons hstep htail ih => exact .cons hstep ih

theorem reverse_exists (symmetric : ∀ {a b}, R a b → R b a)
    {a b : α} {xs : List α} (h : Route R a xs b) :
    ∃ ys, Route R b ys a := by
  induction h with
  | nil a => exact ⟨[], .nil a⟩
  | @cons a b c xs hab hbc ih =>
      obtain ⟨ys, hy⟩ := ih
      exact ⟨_, hy.append (.cons (symmetric hab) (.nil a))⟩

/-- A vertex occurring on a route starts a genuine suffix route to its end. -/
theorem suffix_of_mem {a b x : α} {xs : List α}
    (h : Route R a xs b) (hx : x ∈ a :: xs) :
    ∃ ys, Route R x ys b ∧ (x :: ys) <+ (a :: xs) := by
  revert hx
  induction h with
  | nil a =>
      intro hx
      have hxa : x = a := by simpa only [List.mem_singleton] using hx
      subst x
      exact ⟨[], .nil a, List.Sublist.refl _⟩
  | @cons a b c xs hab hbc ih =>
      intro hx
      rcases List.mem_cons.mp hx with hxa | hx
      · subst x
        exact ⟨b :: xs, .cons hab hbc, List.Sublist.refl _⟩
      · obtain ⟨ys, hy, hsub⟩ := ih hx
        exact ⟨ys, hy, hsub.cons a⟩

/-- Finite loop erasure for any relation, preserving both indexed endpoints.
The induction is on the original route, not an assumed shortest-path oracle. -/
theorem exists_simple_subroute {a b : α} {xs : List α}
    (h : Route R a xs b) :
    ∃ ys, Route R a ys b ∧ (a :: ys).Nodup ∧ (a :: ys) <+ (a :: xs) := by
  classical
  induction h with
  | nil a =>
      exact ⟨[], .nil a, List.nodup_singleton a, List.Sublist.refl _⟩
  | @cons a b c xs hab hbc ih =>
      obtain ⟨ys, hy, hnd, hsub⟩ := ih
      by_cases ha : a ∈ b :: ys
      · obtain ⟨zs, hz, hzsub⟩ := hy.suffix_of_mem ha
        exact ⟨zs, hz, hnd.sublist hzsub,
          (hzsub.trans hsub).cons a⟩
      · exact ⟨b :: ys, .cons hab hy, List.Nodup.cons ha hnd,
          hsub.cons_cons a⟩

/-- A literal prefix-loop-suffix splice; no transitivity of `R` is assumed. -/
theorem erase_return_segment {a s b : α} {prefix loop suffix : List α}
    (hp : Route R a prefix s) (_hl : Route R s loop s)
    (hs : Route R s suffix b) : Route R a (prefix ++ suffix) b :=
  hp.append hs

theorem erased_vertices_sublist {a : α} (prefix loop suffix : List α) :
    (a :: (prefix ++ suffix)) <+ (a :: (prefix ++ (loop ++ suffix))) :=
  ((List.sublist_append_right loop suffix).append_left prefix).cons_cons a

end Route

inductive Mark
  | tail
  | head
  deriving DecidableEq

/-- Incidences, not merely adjacent vertices, are retained, so bows are allowed. -/
structure MarkedGraph (V : Type u) where
  edge : V → V → Mark → Mark → Prop

structure Arrival (V : Type u) where
  vertex : V
  incoming : Option Mark

theorem Arrival.eq_of_fields {V : Type u} {p q : Arrival V}
    (hv : p.vertex = q.vertex) (hm : p.incoming = q.incoming) : p = q := by
  cases p
  cases q
  cases hv
  cases hm
  rfl

/-- `C` is the conditioned set and `A` its ancestor set in the application.
No ancestry theorem is assumed or hidden in this local definition. -/
def ActiveAt {V : Type u} (C A : V → Prop) (v : V) (incoming outgoing : Mark) : Prop :=
  if incoming = .head ∧ outgoing = .head then A v else ¬ C v

/-- A step checks activity at its departure, except at the initial `none` arrival.
The terminal arrival has no outgoing step, so its activity is not checked. -/
def Transition {V : Type u} (G : MarkedGraph V) (C A : V → Prop)
    (p q : Arrival V) : Prop :=
  ∃ outgoing incoming,
    G.edge p.vertex q.vertex outgoing incoming ∧
    q.incoming = some incoming ∧
    match p.incoming with
    | none => True
    | some previous => ActiveAt C A p.vertex previous outgoing

/-- At a selected splice both retained incidences are heads and the collider is
active because the selected vertex belongs to the conditioning ancestor set. -/
theorem selected_splice_active {V : Type u} {C A S : V → Prop}
    (selected_active : ∀ v, S v → A v) {v : V} (hv : S v) :
    ActiveAt C A v .head .head := by
  simpa [ActiveAt] using selected_active v hv

/-- Selected incidences point into the selected vertex. The application derives
this property from latent projection of a DAG with selection sinks (B1). -/
def SelectionHeads {V : Type u} (G : MarkedGraph V) (S : V → Prop) : Prop :=
  ∀ x y left right, G.edge x y left right →
    (S x → left = .head) ∧ (S y → right = .head)

/-- Every selected occurrence of an active route has the same arrival mark.
The initial endpoint is required to satisfy this too; an observed start gives
that premise vacuously. -/
theorem selected_arrival_marks {V : Type u} {G : MarkedGraph V}
    {C A S : V → Prop} (heads : SelectionHeads G S)
    {p q : Arrival V} {xs : List (Arrival V)}
    (h : Route (Transition G C A) p xs q)
    (initial : S p.vertex → p.incoming = some .head) :
    ∀ r ∈ p :: xs, S r.vertex → r.incoming = some .head := by
  revert initial
  induction h with
  | nil p =>
      intro initial r hr
      have hrp : r = p := by simpa only [List.mem_singleton] using hr
      subst r
      exact initial
  | @cons p q r xs hpq hqr ih =>
      intro initial z hz
      rcases List.mem_cons.mp hz with hzp | hz
      · subst z
        exact initial
      · apply ih _ z hz
        intro hq
        obtain ⟨outgoing, incoming, hedge, hmark, _⟩ := hpq
        exact hmark.trans (congrArg some ((heads _ _ _ _ hedge).2 hq))

/-- No repeated observed vertex: if two successive-in-order occurrences have
the same physical vertex, that vertex is selected. This is weaker than asserting
the entire lifted walk is simple, and is exactly the B5 lifting invariant. -/
def NoObservedRepeat {V : Type u} (S : V → Prop) (xs : List (Arrival V)) : Prop :=
  xs.Pairwise (fun p q => p.vertex = q.vertex → S p.vertex)

/-- State simplicity plus selected incoming heads turns into physical-vertex
simplicity. It does not confuse different mark choices on a bow. -/
theorem vertex_nodup {V : Type u} {S : V → Prop} {xs : List (Arrival V)}
    (hnd : xs.Nodup) (hobs : NoObservedRepeat S xs)
    (marks : ∀ p ∈ xs, S p.vertex → p.incoming = some .head) :
    (xs.map Arrival.vertex).Nodup := by
  apply List.pairwise_map.mpr
  apply (List.Pairwise.and hnd hobs).imp_of_mem
  intro p q hp hq hpair heq
  have hsp : S p.vertex := hpair.2 heq
  have hsq : S q.vertex := heq ▸ hsp
  exact hpair.1 (Arrival.eq_of_fields heq
    ((marks p hp hsp).trans (marks q hq hsq).symm))

/-- B6, in explicit bow-aware arrival semantics: a finite lifted active walk
with an observed starting endpoint and no repeated observed occurrence has an active
simple physical-vertex path with the same endpoints. Nothing about MAGs,
source compression, a hidden-size bound, or a decoder is assumed here. -/
theorem selected_walk_to_simple_path {V : Type u} {G : MarkedGraph V}
    {C A S : V → Prop} (heads : SelectionHeads G S)
    {x : V} {q : Arrival V} {xs : List (Arrival V)}
    (hx : ¬ S x)
    (h : Route (Transition G C A) ⟨x, none⟩ xs q)
    (hobs : NoObservedRepeat S (⟨x, none⟩ :: xs)) :
    ∃ ys,
      Route (Transition G C A) ⟨x, none⟩ ys q ∧
      ((⟨x, none⟩ :: ys).map Arrival.vertex).Nodup ∧
      (⟨x, none⟩ :: ys) <+ (⟨x, none⟩ :: xs) := by
  obtain ⟨ys, hy, hnd, hsub⟩ := h.exists_simple_subroute
  have marks := selected_arrival_marks heads h (fun hs => (hx hs).elim)
  refine ⟨ys, hy, vertex_nodup hnd (hobs.sublist hsub) ?_, hsub⟩
  intro p hp hs
  exact marks p (hsub.subset hp) hs

end RestrictedCausal.SelectedWalk
