import OriginalProjectionContraction


/- Pinned-context proof variant: expose the SAME identity maps/simplification,
or eliminate the existing impossible Sum equality. All original theorem and
source/graph/conditioning hypotheses and conclusion semantics remain. -/
/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.
Actual original-source named-root augmentation and latent projection commute.
Original observed, selected and latent carriers are preserved, not reselected.
-/

namespace RestrictedCausal.OriginalProjection

open SelectedWalk CanonicalSelection LatentRoots GraphEquivalence

universe u v w

def oldRetained {X : Type u} {S : Type v} : Sum X S → Sum (Option X) S
  | .inl x => .inl (some x)
  | .inr s => .inr s

def oldSource {X : Type u} {S : Type v} {L : Type w} :
    SourceVertex X S L → SourceVertex (Option X) S L
  | .inl r => .inl (oldRetained r)
  | .inr l => .inr l

def sourceIndicatorEquiv {X : Type u} {S : Type v} {L : Type w} :
    SourceVertex (Option X) S L ≃ Option (SourceVertex X S L) where
  toFun a := match a with
    | .inl (.inl none) => none
    | .inl (.inl (some x)) => some (.inl (.inl x))
    | .inl (.inr s) => some (.inl (.inr s))
    | .inr l => some (.inr l)
  invFun b := match b with
    | none => .inl (.inl none)
    | some a => oldSource a
  left_inv a := by
    rcases a with ((x | s) | l)
    · cases x <;> rfl
    · rfl
    · rfl
  right_inv b := by
    rcases b with _ | ((x | s) | l) <;> rfl

theorem indicator_equiv_oldSource {X : Type u} {S : Type v} {L : Type w}
    (a : SourceVertex X S L) : sourceIndicatorEquiv (oldSource a) = some a := by
  rcases a with ((x | s) | l) <;> rfl

theorem oldRetained_injective {X : Type u} {S : Type v} :
    Function.Injective (oldRetained (X := X) (S := S)) := by
  intro a b h
  have hp := congrArg SourceSelection.selectedIndicatorVertexEquiv h
  have hsome : some a = some b := by
    cases a <;> cases b <;> exact hp
  exact Option.some.inj hsome

def augmentedArrow {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (target : X) :
    SourceVertex (Option X) S L → SourceVertex (Option X) S L → Prop :=
  fun a b => AddIndicator D.arrow (.inl (.inl target))
    (sourceIndicatorEquiv a) (sourceIndicatorEquiv b)

def augmentSource {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (target : X) : SourceDAG (Option X) S L where
  arrow := augmentedArrow D target
  acyclic := by
    intro a xs h
    have hp := h.map sourceIndicatorEquiv (fun _ _ hab => hab)
    have hempty := add_indicator_acyclic D.arrow (.inl (.inl target)) D.acyclic _ _ hp
    cases xs with
    | nil => rfl
    | cons x xs => cases hempty
  selection_sink := by
    intro s b
    exact indicator_preserves_sink D.arrow (.inl (.inl target)) (.inl (.inr s))
      (D.selection_sink s) (sourceIndicatorEquiv b)

theorem old_source_arrow_exact {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (target : X) (a b : SourceVertex X S L) :
    (augmentSource D target).arrow (oldSource a) (oldSource b) ↔ D.arrow a b := by
  change AddIndicator D.arrow (.inl (.inl target))
    (sourceIndicatorEquiv (oldSource a)) (sourceIndicatorEquiv (oldSource b)) ↔ _
  rw [indicator_equiv_oldSource, indicator_equiv_oldSource]
  exact Iff.rfl

theorem old_source_marked_exact {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (target : X) (a b : SourceVertex X S L) (ma mb : Mark) :
    (arrowGraph D.arrow).edge a b ma mb ↔
      (arrowGraph (augmentSource D target).arrow).edge (oldSource a) (oldSource b) ma mb :=
  or_congr (and_congr (old_source_arrow_exact D target a b).symm Iff.rfl)
    (and_congr (old_source_arrow_exact D target b a).symm Iff.rfl)

theorem noncollider_map {V : Type u} {W : Type v} {G : MarkedGraph V} {K : MarkedGraph W}
    (f : V → W) (hf : ∀ a b ma mb, G.edge a b ma mb → K.edge (f a) (f b) ma mb)
    {a b : V} {ma mb : Mark} {mids : List V} (h : NoncolliderRoute G a ma mids b mb) :
    NoncolliderRoute K (f a) ma (mids.map f) (f b) mb := by
  induction h with
  | single hedge => exact .single (hf _ _ _ _ hedge)
  | step hedge hn tail ih => exact .step (hf _ _ _ _ hedge) hn ih

theorem noncollider_pullback {V : Type u} {W : Type v}
    {G : MarkedGraph V} {K : MarkedGraph W} (f : V → W)
    (hf : ∀ a b ma mb, K.edge (f a) (f b) ma mb → G.edge a b ma mb)
    {a b : V} {ma mb : Mark} (mids : List V)
    (h : NoncolliderRoute K (f a) ma (mids.map f) (f b) mb) :
    NoncolliderRoute G a ma mids b mb := by
  induction mids generalizing a ma with
  | nil =>
      cases h with
      | single hedge => exact .single (hf _ _ _ _ hedge)
  | cons z zs ih =>
      cases h with
      | step hedge hn tail => exact .step (hf _ _ _ _ hedge) hn (ih tail)

theorem projected_old_edge_exact {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (target : X) (a b : Sum X S) (ma mb : Mark) :
    (projection (augmentSource D target)).edge (oldRetained a) (oldRetained b) ma mb ↔
      (projection D).edge a b ma mb := by
  constructor
  · rintro ⟨hne, latent, hp⟩
    have hne' : a ≠ b := fun h => hne (congrArg oldRetained h)
    have hp' : NoncolliderRoute (arrowGraph (augmentSource D target).arrow)
        (oldSource (.inl a)) ma
        ((latent.map (fun l => Sum.inr l : L → SourceVertex X S L)).map oldSource)
        (oldSource (.inl b)) mb := by
      simpa only [List.map_map, Function.comp_def, oldSource] using hp
    exact ⟨hne', latent, noncollider_pullback oldSource
      (fun a b ma mb h => (old_source_marked_exact D target a b ma mb).mpr h) _ hp'⟩
  · rintro ⟨hne, latent, hp⟩
    have hne' : oldRetained a ≠ oldRetained b := fun h => hne (oldRetained_injective h)
    have hp' := noncollider_map oldSource
      (fun a b ma mb h => (old_source_marked_exact D target a b ma mb).mp h) hp
    refine ⟨hne', latent, ?_⟩
    simpa only [List.map_map, Function.comp_def, oldSource] using hp'

/-- The original indicator has exactly its named observed child at the source
level. This also forbids beginning a latent-only interior from the indicator. -/
theorem indicator_raw_edge {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (target : X) (b : SourceVertex (Option X) S L) (ma mb : Mark) :
    (arrowGraph (augmentSource D target).arrow).edge (.inl (.inl none)) b ma mb ↔
      b = .inl (.inl (some target)) ∧ ma = .tail ∧ mb = .head := by
  constructor
  · rintro (⟨h, hma, hmb⟩ | ⟨h, _, _⟩)
    · have hb := (indicator_sole_child D.arrow (.inl (.inl target)) (sourceIndicatorEquiv b)).mp h
      have heq : b = .inl (.inl (some target)) := sourceIndicatorEquiv.injective hb
      exact ⟨heq, hma, hmb⟩
    · exact (indicator_no_parent D.arrow (.inl (.inl target)) (sourceIndicatorEquiv b) h).elim
  · rintro ⟨rfl, rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl, rfl⟩

theorem projected_indicator_edge {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (target : X) (b : Sum (Option X) S) (ma mb : Mark) :
    (projection (augmentSource D target)).edge (.inl none) b ma mb ↔
      b = .inl (some target) ∧ ma = .tail ∧ mb = .head := by
  constructor
  · rintro ⟨_, latent, hp⟩
    cases latent with
    | nil =>
        cases hp with
        | single hedge =>
            obtain ⟨hb, hma, hmb⟩ := (indicator_raw_edge D target (.inl b) ma mb).mp hedge
            exact ⟨Sum.inl.inj hb, hma, hmb⟩
    | cons l ls =>
        cases hp with
        | step hedge _ _ =>
            have hbad := ((indicator_raw_edge D target (.inr l) _ _).mp hedge).1
            cases hbad
  · rintro ⟨rfl, rfl, rfl⟩
    refine ⟨?_, [], .single ((indicator_raw_edge D target _ _ _).mpr ⟨rfl, rfl, rfl⟩)⟩
    intro hbad
    exact Option.noConfusion (Sum.inl.inj hbad)

theorem projection_augment_option {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (target : X) (a b : WithBot (Sum X S)) (ma mb : Mark) :
    (projection (augmentSource D target)).edge
      (SourceSelection.selectedIndicatorVertexEquiv.symm a)
      (SourceSelection.selectedIndicatorVertexEquiv.symm b) ma mb ↔
      (LatentRoots.augmentGraph (projection D) (.inl target)).edge a b ma mb := by
  cases a with
  | none =>
      cases b with
      | none => exact ⟨fun h => h.1 rfl, False.elim⟩
      | some b =>
          change (projection (augmentSource D target)).edge (.inl none) (oldRetained b) ma mb ↔
            (b = .inl target ∧ ma = .tail ∧ mb = .head)
          rw [projected_indicator_edge]
          constructor
          · rintro ⟨hb, hma, hmb⟩
            exact ⟨oldRetained_injective hb, hma, hmb⟩
          · rintro ⟨rfl, hma, hmb⟩
            exact ⟨rfl, hma, hmb⟩
  | some a =>
      cases b with
      | none =>
          change (projection (augmentSource D target)).edge (oldRetained a) (.inl none) ma mb ↔
            (a = .inl target ∧ ma = .head ∧ mb = .tail)
          constructor
          · intro h
            have hr := projection_symm (augmentSource D target) _ _ _ _ h
            obtain ⟨ha, hmb, hma⟩ := (projected_indicator_edge D target (oldRetained a) mb ma).mp hr
            exact ⟨oldRetained_injective ha, hma, hmb⟩
          · rintro ⟨rfl, hma, hmb⟩
            have hr := (projected_indicator_edge D target (oldRetained (.inl target)) mb ma).mpr
              ⟨rfl, hmb, hma⟩
            exact projection_symm (augmentSource D target) _ _ _ _ hr
      | some b => exact projected_old_edge_exact D target a b ma mb

def original_projection_indicator_equiv {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (target : X) :
    MarkedEquiv (projection (augmentSource D target))
      (LatentRoots.augmentGraph (projection D) (.inl target)) where
  toEquiv := SourceSelection.selectedIndicatorVertexEquiv
  edge a b ma mb := by
    have h := projection_augment_option D target (SourceSelection.selectedIndicatorVertexEquiv a)
      (SourceSelection.selectedIndicatorVertexEquiv b) ma mb
    simpa only [Equiv.symm_apply_apply] using h

/-- Literal marked-graph equality on all augmented observed/selection labels.
The original latent variables and selection vertices remain the same ones. -/
theorem projection_augmentation_exact {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (target : X) :
    projection (augmentSource D target) = SourceSelection.graph (SourceSelection.augment (extracted D) target) := by
  apply ProfileRegistry.markedGraph_eq
  intro a b ma mb
  have hp := (original_projection_indicator_equiv D target).edge a b ma mb
  have he := (SourceSelection.selectedIndicatorGraphEquiv (extracted D) target).edge a b ma mb
  rw [extracted_graph_eq D] at he
  exact hp.trans he.symm

end RestrictedCausal.OriginalProjection
