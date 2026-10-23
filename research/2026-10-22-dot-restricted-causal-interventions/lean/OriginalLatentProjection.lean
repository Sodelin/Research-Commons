import CommonSelectedIndicatorSource

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
Classical latent projection, not a new projection theory: genuine original DAG
data, arbitrary original latent carrier, projected laws and selection heads.
The general original d/m-separation equivalence is still a separate obligation.
-/

namespace RestrictedCausal.OriginalProjection

open SelectedWalk CanonicalSelection LatentRoots

universe u v w

abbrev SourceVertex (X : Type u) (S : Type v) (L : Type w) := Sum (Sum X S) L

structure SourceDAG (X : Type u) (S : Type v) (L : Type w) where
  arrow : SourceVertex X S L → SourceVertex X S L → Prop
  acyclic : ∀ a xs, Route arrow a xs a → xs = []
  selection_sink : ∀ s b, ¬ arrow (.inl (.inr s)) b

def arrowGraph {V : Type u} (D : V → V → Prop) : MarkedGraph V where
  edge a b ma mb := (D a b ∧ ma = .tail ∧ mb = .head) ∨
    (D b a ∧ ma = .head ∧ mb = .tail)

theorem arrow_graph_symm {V : Type u} (D : V → V → Prop)
    (a b : V) (ma mb : Mark) (h : (arrowGraph D).edge a b ma mb) :
    (arrowGraph D).edge b a mb ma := by
  rcases h with ⟨hd, hma, hmb⟩ | ⟨hd, hma, hmb⟩
  · exact Or.inr ⟨hd, hmb, hma⟩
  · exact Or.inl ⟨hd, hmb, hma⟩

theorem tail_edge_forward {V : Type u} (D : V → V → Prop)
    {a b : V} {mb : Mark} (h : (arrowGraph D).edge a b .tail mb) :
    D a b ∧ mb = .head := by
  rcases h with ⟨hd, _, hmb⟩ | ⟨_, hbad, _⟩
  · exact ⟨hd, hmb⟩
  · exact Mark.noConfusion hbad

theorem sink_incidence_head {V : Type u} (D : V → V → Prop)
    {a b : V} {ma mb : Mark} (hs : ∀ z, ¬ D a z)
    (h : (arrowGraph D).edge a b ma mb) : ma = .head := by
  rcases h with ⟨hd, _⟩ | ⟨_, hma, _⟩
  · exact (hs b hd).elim
  · exact hma

theorem noncollider_snoc {V : Type u} {G : MarkedGraph V}
    {a b c : V} {ma incoming outgoing mc : Mark} {mids : List V}
    (h : NoncolliderRoute G a ma mids b incoming) (edge : G.edge b c outgoing mc)
    (active : ¬ (incoming = .head ∧ outgoing = .head)) :
    NoncolliderRoute G a ma (mids ++ [b]) c mc := by
  induction h with
  | single «first» => exact .step «first» active (.single edge)
  | step «first» hn tail ih => exact .step «first» hn ih

theorem noncollider_reverse {V : Type u} {G : MarkedGraph V}
    (symmetric : ∀ a b ma mb, G.edge a b ma mb → G.edge b a mb ma)
    {a b : V} {ma mb : Mark} {mids : List V}
    (h : NoncolliderRoute G a ma mids b mb) :
    NoncolliderRoute G b mb mids.reverse a ma := by
  induction h with
  | single hedge => exact .single (symmetric _ _ _ _ hedge)
  | step hedge hn tail ih =>
      rw [List.reverse_cons]
      exact noncollider_snoc ih (symmetric _ _ _ _ hedge)
        (fun hc => hn ⟨hc.2, hc.1⟩)

/-- Starting with a tail forces every edge of a noncollider path to point
forward. This supplies no-tail-tail and the original directed-path witness. -/
theorem noncollider_tail_path {V : Type u} (D : V → V → Prop)
    {a b : V} {ma mb : Mark} {mids : List V}
    (h : NoncolliderRoute (arrowGraph D) a ma mids b mb) :
    ma = .tail → mb = .head ∧ Route D a (mids ++ [b]) b := by
  induction h with
  | single hedge =>
      intro hma
      subst ma
      obtain ⟨hd, hmb⟩ := tail_edge_forward D hedge
      exact ⟨hmb, .cons hd (.nil _)⟩
  | @step a b c ma incoming outgoing mc mids hedge hn tail ih =>
      intro hma
      subst ma
      obtain ⟨hd, hin⟩ := tail_edge_forward D hedge
      have hout : outgoing = .tail := by
        cases outgoing with
        | tail => rfl
        | head => exact (hn ⟨hin, rfl⟩).elim
      obtain ⟨hmc, hp⟩ := ih hout
      exact ⟨hmc, .cons hd hp⟩

theorem noncollider_start_sink {V : Type u} (D : V → V → Prop)
    {a b : V} {ma mb : Mark} {mids : List V}
    (h : NoncolliderRoute (arrowGraph D) a ma mids b mb) (hs : ∀ z, ¬ D a z) : ma = .head := by
  cases h with
  | single hedge => exact sink_incidence_head D hs hedge
  | step hedge _ _ => exact sink_incidence_head D hs hedge

theorem noncollider_end_sink {V : Type u} (D : V → V → Prop)
    {a b : V} {ma mb : Mark} {mids : List V}
    (h : NoncolliderRoute (arrowGraph D) a ma mids b mb) (hs : ∀ z, ¬ D b z) : mb = .head :=
  noncollider_start_sink D (noncollider_reverse (arrow_graph_symm D) h) hs

/-- The original latent set is unbounded here. All retained X and S vertices
are kept; projection only permits latent internal vertices. -/
def projection {X : Type u} {S : Type v} {L : Type w} (D : SourceDAG X S L) :
    MarkedGraph (Sum X S) where
  edge a b ma mb := a ≠ b ∧ ∃ latent : List L,
    NoncolliderRoute (arrowGraph D.arrow) (.inl a) ma
      (latent.map (fun l => Sum.inr l : L → SourceVertex X S L)) (.inl b) mb

theorem projection_symm {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (a b : Sum X S) (ma mb : Mark)
    (h : (projection D).edge a b ma mb) : (projection D).edge b a mb ma := by
  obtain ⟨hne, latent, hp⟩ := h
  refine ⟨hne.symm, latent.reverse, ?_⟩
  rw [List.map_reverse]
  exact noncollider_reverse (arrow_graph_symm D.arrow) hp

theorem projection_mixed_laws {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : MixedLaws (projection D) := by
  constructor
  · exact projection_symm D
  · rintro a ma mb ⟨hne, _⟩
    exact hne rfl
  · rintro a b ⟨_, latent, hp⟩
    have hbad := (noncollider_tail_path D.arrow hp rfl).1
    exact Mark.noConfusion hbad

theorem projected_selection_heads {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : SelectionHeads (projection D) SourceSelection.isSelected := by
  intro a b ma mb hedge
  obtain ⟨_, latent, hp⟩ := hedge
  constructor
  · intro hs
    cases a with
    | inl x => exact hs.elim
    | inr s => exact noncollider_start_sink D.arrow hp (D.selection_sink s)
  · intro hs
    cases b with
    | inl y => exact hs.elim
    | inr s => exact noncollider_end_sink D.arrow hp (D.selection_sink s)

theorem projection_route_lift {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) {a b : Sum X S} {xs : List (Sum X S)}
    (h : Route (Directed (projection D)) a xs b) :
    ∃ ys, Route D.arrow (.inl a) ys (.inl b) ∧ xs.length ≤ ys.length := by
  induction h with
  | nil a => exact ⟨[], .nil _, Nat.le_refl _⟩
  | @cons a b c xs hab hbc ih =>
      obtain ⟨_, latent, hpath⟩ := hab
      have hfirst := (noncollider_tail_path D.arrow hpath rfl).2
      obtain ⟨ys, hy, hlength⟩ := ih
      refine ⟨_, hfirst.append hy, ?_⟩
      simp only [List.length_append, List.length_map, List.length_singleton, List.length_cons]
      omega

theorem projection_directed_acyclic {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : DirectedAcyclic (projection D) := by
  intro a xs h
  obtain ⟨ys, hy, hlength⟩ := projection_route_lift D h
  have hnil := D.acyclic (.inl a) ys hy
  rw [hnil] at hlength
  cases xs with
  | nil => rfl
  | cons x xs => simp only [List.length_cons, List.length_nil] at hlength; omega

/-- Extract the actual selected-mixed representation from this original DAG's
projection. No selection-head or acyclicity field is assumed on this adapter. -/
def extracted {X : Type u} {S : Type v} {L : Type w} (D : SourceDAG X S L) :
    SourceSelection.SelectedGraph X S where
  observed := { edge := fun x y mx my => (projection D).edge (.inl x) (.inl y) mx my }
  boundary x mx s := (projection D).edge (.inl x) (.inr s) mx .head
  selectionEdge s t := (projection D).edge (.inr s) (.inr t) .head .head
  selection_symm := by
    intro s t h
    exact projection_symm D _ _ _ _ h

theorem extracted_edge_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (a b : Sum X S) (ma mb : Mark) :
    (SourceSelection.graph (extracted D)).edge a b ma mb ↔ (projection D).edge a b ma mb := by
  cases a with
  | inl x =>
      cases b with
      | inl y => exact Iff.rfl
      | inr s =>
          constructor
          · rintro ⟨h, rfl⟩
            exact h
          · intro h
            have hm := ((projected_selection_heads D) _ _ _ _ h).2 trivial
            exact ⟨hm ▸ h, hm⟩
  | inr s =>
      cases b with
      | inl y =>
          constructor
          · rintro ⟨h, rfl⟩
            exact projection_symm D _ _ _ _ h
          · intro h
            have hm := ((projected_selection_heads D) _ _ _ _ h).1 trivial
            subst ma
            exact ⟨projection_symm D _ _ _ _ h, rfl⟩
      | inr t =>
          constructor
          · rintro ⟨h, rfl, rfl⟩
            exact h
          · intro h
            obtain ⟨hma, hmb⟩ := (projected_selection_heads D) _ _ _ _ h
            have ha := hma trivial
            have hb := hmb trivial
            subst ma
            subst mb
            exact ⟨h, rfl, rfl⟩

theorem extracted_graph_eq {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : SourceSelection.graph (extracted D) = projection D :=
  ProfileRegistry.markedGraph_eq (extracted_edge_iff D)

theorem extracted_observed_laws {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : MixedLaws (extracted D).observed := by
  have laws := projection_mixed_laws D
  exact ⟨fun x y mx my h => laws.symmetric (.inl x) (.inl y) mx my h,
    fun x mx my => laws.irreflexive (.inl x) mx my,
    fun x y => laws.no_tail_tail (.inl x) (.inl y)⟩

theorem extracted_observed_acyclic {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : DirectedAcyclic (extracted D).observed := by
  intro x xs h
  have hp := h.map (fun x => Sum.inl x : X → Sum X S) (fun _ _ hab => hab)
  have hempty := projection_directed_acyclic D (.inl x) _ hp
  cases xs with
  | nil => rfl
  | cons x xs => cases hempty

/-- The actual extracted source belongs to the same finite full-profile
registry used by the canonical construction. No bound on original L or S is
assumed. The bridge from original d-separation to this route projection has
not been silently bundled into this elementary membership theorem. -/
def originalProfile {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) : ProfileRegistry.AdmissibleProfile X :=
  ⟨SourceSelection.profile (extracted D), extracted_observed_laws D,
    extracted_observed_acyclic D⟩

end RestrictedCausal.OriginalProjection
