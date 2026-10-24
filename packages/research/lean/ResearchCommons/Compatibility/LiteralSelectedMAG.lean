import InducingPathSeparation

/- Pinned-context proof compatibility: expose the SAME original condition
functions and actual canonical indicator equivalence before rewriting.
All original source/target/latent/selection hypotheses and statements remain. -/

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Literal HPL Definition 2: inducing-path adjacency and original-DAG ancestral
endpoint marks. The preceding source theorem proves the inducing/inseparable
bridge. No skeleton or generic mixed-graph summary is substituted for this
marked target. Ancestral-graph validity, its full m-separation representation
and the complete MAG-equivalence certificate remain further proof obligations.
-/

namespace RestrictedCausal.HPLTarget

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open GraphEquivalence

universe u v w v' w'

def SelectionAncestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x : X) : Prop :=
  ∃ s : S, Reach (arrowGraph D.arrow) (Observed x) (.inl (.inr s))

def TailFlag {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : Prop :=
  Reach (arrowGraph D.arrow) (Observed x) (Observed y) ∨ SelectionAncestor D x

def EndpointMark {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) (m : Mark) : Prop :=
  (m = .tail ∧ TailFlag D x y) ∨ (m = .head ∧ ¬ TailFlag D x y)

/-- The four endpoint combinations are exactly HPL Definition 2(a)--(d). -/
def mag {X : Type u} {S : Type v} {L : Type w} (D : SourceDAG X S L) :
    MarkedGraph X where
  edge x y mx my := InducingPath D x y ∧ EndpointMark D x y mx ∧ EndpointMark D y x my

theorem mag_no_self_edge {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x : X) (mx my : Mark) : ¬ (mag D).edge x x mx my :=
  fun h => h.1.1 rfl

/-- Explicit premises for target transport between genuine DAGs. This is not
an assumed original-source adapter: the canonical instance is constructed
below from the completed graph-source proof bodies. -/
structure SourcePreserves {X : Type u} {S : Type v} {L : Type w}
    {S' : Type v'} {L' : Type w'} (D : SourceDAG X S L) (E : SourceDAG X S' L') : Prop where
  connection : ∀ Z x y,
    ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) (Observed y) ↔
      ActiveConnection (arrowGraph E.arrow) (SelectedCondition Z) (Observed x) (Observed y)
  observed_ancestry : ∀ x y,
    Reach (arrowGraph D.arrow) (Observed x) (Observed y) ↔
      Reach (arrowGraph E.arrow) (Observed x) (Observed y)
  selection_ancestry : ∀ x, SelectionAncestor D x ↔ SelectionAncestor E x

theorem SourcePreserves.inducing {X : Type u} {S : Type v} {L : Type w}
    {S' : Type v'} {L' : Type w'} {D : SourceDAG X S L} {E : SourceDAG X S' L'}
    (h : SourcePreserves D E) (x y : X) : InducingPath D x y ↔ InducingPath E x y := by
  rw [inducing_iff_inseparable, inducing_iff_inseparable]
  constructor
  · rintro ⟨hne, hp⟩
    exact ⟨hne, fun Z hx hy => (h.connection Z x y).mp (hp Z hx hy)⟩
  · rintro ⟨hne, hp⟩
    exact ⟨hne, fun Z hx hy => (h.connection Z x y).mpr (hp Z hx hy)⟩

theorem SourcePreserves.mark {X : Type u} {S : Type v} {L : Type w}
    {S' : Type v'} {L' : Type w'} {D : SourceDAG X S L} {E : SourceDAG X S' L'}
    (h : SourcePreserves D E) (x y : X) (m : Mark) :
    EndpointMark D x y m ↔ EndpointMark E x y m := by
  have hflag : TailFlag D x y ↔ TailFlag E x y :=
    or_congr (h.observed_ancestry x y) (h.selection_ancestry x)
  exact or_congr (and_congr Iff.rfl hflag) (and_congr Iff.rfl (not_congr hflag))

theorem SourcePreserves.mag_eq {X : Type u} {S : Type v} {L : Type w}
    {S' : Type v'} {L' : Type w'} {D : SourceDAG X S L} {E : SourceDAG X S' L'}
    (h : SourcePreserves D E) : mag D = mag E := by
  apply ProfileRegistry.markedGraph_eq
  intro x y mx my
  exact and_congr (h.inducing x y) (and_congr (h.mark x y mx) (h.mark y x my))

/-- One actual finite-size source, not a tuple of independently realized
indicator MAGs. Original selection/latent carriers remain unrestricted. -/
def canonicalSource {X : Type u} {S : Type v} {L : Type w} [LinearOrder X]
    (D : SourceDAG X S L) [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] :
    SourceDAG X (Selector (sourceProfile D)) (Root (canonicalRetainedGraph D)) where
  arrow := Arrow (canonicalRetainedGraph D)
  acyclic := root_expansion_acyclic (canonicalRetainedGraph D)
    (SourceSelection.selected_directed_acyclic (SourceSelection.canonical (sourceProfile D))
      (extracted_observed_acyclic D))
  selection_sink := SourceSelection.canonical_dag_selection_sinks (sourceProfile D)

theorem canonical_baseline_preserves {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] :
    SourcePreserves D (canonicalSource D) where
  connection Z x y := by
    simpa only [canonicalSource, SelectedCondition, retainedCondition, liftCondition,
      dagGraph, arrowGraph] using original_canonical_baseline_connection D Z x y
  observed_ancestry := original_canonical_baseline_observed_ancestry D
  selection_ancestry := original_canonical_baseline_selection_ancestry D

def canonicalIndicatorEquiv {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] (target : X) :
    MarkedEquiv (arrowGraph (augmentSource (canonicalSource D) target).arrow)
      (indicatorGraph (canonicalRetainedGraph D) (.inl target)) where
  toEquiv := sourceIndicatorEquiv
  edge _ _ _ _ := Iff.rfl

private theorem canonical_indicator_equiv_apply
    {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] (target : X)
    (a : SourceVertex (Option X) (Selector (sourceProfile D))
      (Root (canonicalRetainedGraph D))) :
    (canonicalIndicatorEquiv D target).toEquiv a = sourceIndicatorEquiv a := rfl

theorem canonical_indicator_condition {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] (Z : Option X → Prop)
    (a : SourceVertex (Option X) (Selector (sourceProfile D)) (Root (canonicalRetainedGraph D))) :
    SelectedCondition Z a ↔
      indicatorCondition (SourceSelection.augmentedSelectedCondition Z) (sourceIndicatorEquiv a) := by
  rcases a with ((x | s) | l)
  · cases x <;> exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl

theorem canonical_indicator_observed_label {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] (x : Option X) :
    sourceIndicatorEquiv (Observed x : SourceVertex (Option X) (Selector (sourceProfile D))
      (Root (canonicalRetainedGraph D))) =
      indicatorRetained (SourceSelection.selectedIndicatorObserved x) := by
  cases x <;> rfl

theorem canonical_indicator_preserves {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] (target : X) :
    SourcePreserves (augmentSource D target) (augmentSource (canonicalSource D) target) where
  connection Z x y := by
    have h := (canonicalIndicatorEquiv D target).active_iff (canonical_indicator_condition D Z)
      (Observed x) (Observed y)
    simp only [canonical_indicator_equiv_apply, canonical_indicator_observed_label] at h
    exact (original_canonical_indicator_connection D target Z x y).trans h.symm
  observed_ancestry x y := by
    have h := (canonicalIndicatorEquiv D target).reach_iff (Observed x) (Observed y)
    simp only [canonical_indicator_equiv_apply, canonical_indicator_observed_label] at h
    exact (original_canonical_indicator_observed_ancestry D target x y).trans h.symm
  selection_ancestry x := by
    have last : (∃ s : Selector (sourceProfile D),
        Reach (indicatorGraph (canonicalRetainedGraph D) (.inl target))
          (indicatorRetained (SourceSelection.selectedIndicatorObserved x)) (some (.inl (.inr s)))) ↔
        SelectionAncestor (augmentSource (canonicalSource D) target) x := by
      have one (s : Selector (sourceProfile D)) :=
        (canonicalIndicatorEquiv D target).reach_iff (Observed x) (.inl (.inr s))
      simp only [canonical_indicator_equiv_apply, canonical_indicator_observed_label] at one
      exact ⟨fun ⟨s, hs⟩ => ⟨s, (one s).mpr hs⟩,
        fun ⟨s, hs⟩ => ⟨s, (one s).mp hs⟩⟩
    exact (original_canonical_indicator_selection_ancestry D target x).trans last

/-- Literal labeled, marked MAG preservation for the baseline and EVERY
separate single-indicator augmentation of the same canonical source. -/
theorem canonical_all_mags {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] :
    mag D = mag (canonicalSource D) ∧
      ∀ target : X, mag (augmentSource D target) = mag (augmentSource (canonicalSource D) target) :=
  ⟨(canonical_baseline_preserves D).mag_eq, fun t => (canonical_indicator_preserves D t).mag_eq⟩

abbrev CombinedVertex (X : Type u) (T : X → Prop) := Sum X {x : X // T x}

def sliceLabel {X : Type u} {T : X → Prop} (target : {x : X // T x}) :
    Option X → CombinedVertex X T
  | none => .inr target
  | some x => .inl x

def OwnTargetPair {X : Type u} {T : X → Prop} (a b : CombinedVertex X T) : Prop :=
  ∃ t : {x : X // T x}, (a = .inr t ∧ b = .inl t.val) ∨ (a = .inl t.val ∧ b = .inr t)

/-- Literal union of the separate augmented MAG edge sets, followed by
deletion only of each indicator's own-target edge (HPL equations (2) and the
TCM definition). All observed labels are retained. If T is empty the literal
union has no edges; the baseline remains in the separate equivalence
certificate. No unannounced observational extension of TCM is introduced. -/
def tcm {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (T : X → Prop) : MarkedGraph (CombinedVertex X T) where
  edge a b ma mb := ¬ OwnTargetPair a b ∧ ∃ t : {x : X // T x}, ∃ x y : Option X,
    sliceLabel t x = a ∧ sliceLabel t y = b ∧ (mag (augmentSource D t.val)).edge x y ma mb

theorem tcm_eq_of_all_mags {X : Type u} {S : Type v} {L : Type w}
    {S' : Type v'} {L' : Type w'} (D : SourceDAG X S L) (E : SourceDAG X S' L')
    (T : X → Prop) (h : ∀ t : {x : X // T x}, mag (augmentSource D t.val) = mag (augmentSource E t.val)) :
    tcm D T = tcm E T := by
  apply ProfileRegistry.markedGraph_eq
  intro a b ma mb
  constructor
  · rintro ⟨hn, t, x, y, hx, hy, hedge⟩
    exact ⟨hn, t, x, y, hx, hy, by simpa only [h t] using hedge⟩
  · rintro ⟨hn, t, x, y, hx, hy, hedge⟩
    exact ⟨hn, t, x, y, hx, hy, by simpa only [h t] using hedge⟩

theorem canonical_literal_tcm {X : Type u} {S : Type v} {L : Type w}
    [LinearOrder X] (D : SourceDAG X S L)
    [LinearOrder (CanonicalSelection.Vertex (sourceProfile D))] (T : X → Prop) :
    tcm D T = tcm (canonicalSource D) T :=
  tcm_eq_of_all_mags D (canonicalSource D) T (fun t => (canonical_all_mags D).2 t.val)

end RestrictedCausal.HPLTarget
