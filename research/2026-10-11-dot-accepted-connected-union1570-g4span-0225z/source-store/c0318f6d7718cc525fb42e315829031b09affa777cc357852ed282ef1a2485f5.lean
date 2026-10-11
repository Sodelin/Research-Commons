import G5FairSharpnessTargets
import UnifiedLean.Source.SourceCompletedUnrankedTree
import UnifiedLean.Source.SourceCopyCarrierTransport

/-!
# Exact ordinary one-copy calendar observation of the actual source
Contributor: dot / OpenAI, 2026-10-03.
For one original gene copy, a complete ordinary rooted calendar genealogy has
one original-labelled leaf at its sampling age and no internal merger times.
The no-merger statement and leaf identity are proved from ACTUAL legal source
transitions and valid source genealogy states below. Hidden original
population/routing IDs and silent source boundary movements are not observed.
The output map is applied to the inherited natural original-source law, not
to an independently supplied fitted one-tip law. No general multi-copy timed
law is inferred from this exact singleton specialization.
-/
namespace GProgram.G5.Sharpness
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.NativeFairCurrentPosition
open UnifiedLean.Source.FiniteGenealogyEncoding UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCopyCarrierTransport
open scoped Classical

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- Positive rates never create a one-copy merger: the source requires two
DIFFERENT current live copies for every actual Kingman merger. -/
lemma singleton_source_has_no_legal_merge (s : State V E (Fin 1)) (a b : Fin 1) :
    ¬ LegalMerge s a b := by
  intro h
  exact h.different (Subsingleton.elim a b)

/-- Every actual one-copy clock competitor catalogue is EMPTY, at every
admitted original-source state. There are no hidden merger times to erase. -/
lemma singleton_source_clock_catalogue_empty (N : RootedBinary V E X)
    {sample : Fin 1 → X} (s : Code N sample) : IsEmpty (Choice N s) := by
  refine ⟨fun p => ?_⟩
  exact (Finset.mem_offDiag.mp p.2.property).2.2 (Subsingleton.elim _ _)

/-- No binary internal node fits a valid genealogy on one original copy. -/
lemma wellLabelled_singleton_genealogy (t : Genealogy (Fin 1)) (ht : t.WellLabelled) :
    t = .leaf 0 := by
  have hb := wellLabelled_height_below_copy_cap t ht
  cases t with
  | leaf x => exact congrArg Genealogy.leaf (Subsingleton.elim x 0)
  | graft a b =>
      simp only [genealogyHeight,Fintype.card_fin] at hb
      omega

omit [DecidableEq E] in
lemma actual_singleton_genealogy (N : RootedBinary V E X) {sample : Fin 1 → X}
    (s : Code N sample) : (state s).genealogy ((state s).ancestor 0) = .leaf 0 := by
  apply wellLabelled_singleton_genealogy
  exact s.property.forest.wellLabelled _ (s.property.forest.ancestor_live 0)

/-- Full rooted labelled calendar genealogy syntax. EVERY internal merger
node has its calendar age; source population/routing IDs do not occur. -/
inductive CalendarGenealogy (Copy : Type*)
  | leaf (copy : Copy) (samplingAge : ℝ)
  | merger (calendarAge : ℝ) (left right : CalendarGenealogy Copy)

def CalendarGenealogy.erase : CalendarGenealogy Copy → Genealogy Copy
  | .leaf c _ => .leaf c
  | .merger _ a b => .graft a.erase b.erase

def CalendarGenealogy.CorrectLeafAges (sampledAge : Copy → ℝ) : CalendarGenealogy Copy → Prop
  | .leaf c t => t = sampledAge c
  | .merger _ a b => a.CorrectLeafAges sampledAge ∧ b.CorrectLeafAges sampledAge

def CalendarGenealogy.mapLabels (f : A → B) : CalendarGenealogy A → CalendarGenealogy B
  | .leaf c t => .leaf (f c) t
  | .merger t a b => .merger t (a.mapLabels f) (b.mapLabels f)

/-- Completeness of the singleton calendar encoding, rather than an arbitrary
coarser observation quotient: ANY well-labelled full timed genealogy on the
one-copy carrier has NO merger/internal node, and its only remaining age is
exactly the original sample age. No internal ages have been forgotten. -/
theorem canonical_singleton_calendar_genealogy_complete (sampledAge : ℝ)
    (t : CalendarGenealogy (Fin 1)) (ht : t.erase.WellLabelled)
    (hs : t.CorrectLeafAges (fun _ => sampledAge)) :
    t = .leaf 0 sampledAge := by
  have hshape := wellLabelled_singleton_genealogy t.erase ht
  cases t with
  | leaf c age =>
      have hc : c = 0 := Subsingleton.elim _ _
      have ha : age = sampledAge := hs
      subst c; subst age; rfl
  | merger age a b => cases hshape

abbrev SingletonCalendarGenealogy (X : Type*) := CalendarGenealogy X

/-- Actual one-copy observer reads the inherited recorded source genealogy,
relabels its ORIGINAL copy, and dates its leaf with the source's own calendar.
An internal-node case is impossible by the proved source invariant. -/
noncomputable def singletonCalendarReadout (N : RootedBinary V E X) (C : Calendar N.graph)
    (x : X) (s : Code N (fun _ : Fin 1 => x)) : Option (SingletonCalendarGenealogy X) :=
  match h : (state s).genealogy ((state s).ancestor 0) with
  | .leaf _ => some (.leaf x (C.age (N.leaf x)))
  | .graft _ _ => False.elim (by
      have hh := actual_singleton_genealogy N s
      rw [h] at hh
      cases hh)

omit [DecidableEq E] in
lemma singletonCalendarReadout_exact (N : RootedBinary V E X) (C : Calendar N.graph)
    (x : X) (s : Code N (fun _ : Fin 1 => x)) :
    singletonCalendarReadout N C x s = some (.leaf x (C.age (N.leaf x))) := by
  unfold singletonCalendarReadout
  split
  · rfl
  · rename_i a b h
    have hh := actual_singleton_genealogy N s
    rw [h] at hh
    cases hh

/-- Merely the canonical LOCAL recorder rules: it records the actual source
merger topology and dates ORIGINAL leaves correctly. No desired law equality,
root rate/age readout or lack of internal nodes is an assumed field. -/
structure CanonicalSingletonRecorder (N : RootedBinary V E X) (C : Calendar N.graph) (x : X) where
  tree : Code N (fun _ : Fin 1 => x) → CalendarGenealogy (Fin 1)
  actual_topology : ∀ s, (tree s).erase = (state s).genealogy ((state s).ancestor 0)
  original_leaf_dates : ∀ s, (tree s).CorrectLeafAges (fun _ => C.age (N.leaf x))

/-- EVERY canonical full timed singleton recorder has exactly our value. This
is the formal binding to ordinary merger-topology+calendar-time readout. -/
theorem every_canonical_singleton_recorder_is_exact (N : RootedBinary V E X) (C : Calendar N.graph)
    (x : X) (R : CanonicalSingletonRecorder N C x) (s : Code N (fun _ : Fin 1 => x)) :
    some ((R.tree s).mapLabels (fun _ : Fin 1 => x)) = singletonCalendarReadout N C x s := by
  have ht : (R.tree s).erase.WellLabelled := by
    rw [R.actual_topology]
    exact s.property.forest.wellLabelled _ (s.property.forest.ancestor_live 0)
  rw [canonical_singleton_calendar_genealogy_complete _ _ ht (R.original_leaf_dates s)]
  rw [singletonCalendarReadout_exact]
  rfl

/-- Genuine ordinary one-copy rooted CALENDAR law. The source graph, calendar,
register prior, inheritance mechanism and positive original clocks are all
passed to the inherited actual original-source law. -/
noncomputable def singletonCalendarLaw (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (common : Bool) (x : X) : PMF (Option (SingletonCalendarGenealogy X)) :=
  (naturalCompletedLaw N C (fun _ : Fin 1 => x) H p (fun _ => common) r).map
    (singletonCalendarReadout N C x)

/-- Derived exact law, with actual original-source sampling age and label.
All silent routing/clock information is integrated out through the source. -/
theorem actual_singleton_calendar_law (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (common : Bool) (x : X) :
    singletonCalendarLaw N C H p r common x =
      PMF.pure (some (CalendarGenealogy.leaf x (C.age (N.leaf x)))) := by
  unfold singletonCalendarLaw
  have hf : singletonCalendarReadout N C x =
      Function.const (Code N (fun _ : Fin 1 => x)) (some (CalendarGenealogy.leaf x (C.age (N.leaf x)))) := by
    funext s
    exact singletonCalendarReadout_exact N C x s
  rw [hf,PMF.map_const]

/-- Any full timed recorder satisfying only the canonical observation rules
has the SAME source-pushforward law. Thus the law is independent of an
encoding choice, rather than a narrower ad hoc readout. -/
theorem canonical_singleton_calendar_observation_binding (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (common : Bool) (x : X) (R : CanonicalSingletonRecorder N C x) :
    (naturalCompletedLaw N C (fun _ : Fin 1 => x) H p (fun _ => common) r).map
      (fun s => some ((R.tree s).mapLabels (fun _ : Fin 1 => x))) =
      singletonCalendarLaw N C H p r common x := by
  have hf : (fun s => some ((R.tree s).mapLabels (fun _ : Fin 1 => x))) =
      singletonCalendarReadout N C x := by
    funext s
    exact every_canonical_singleton_recorder_is_exact N C x R s
  rw [hf]
  rfl

/-- The canonical recorder itself is CONSTRUCTED from actual source shape. -/
noncomputable def actualCanonicalSingletonRecorder (N : RootedBinary V E X)
    (C : Calendar N.graph) (x : X) : CanonicalSingletonRecorder N C x where
  tree := fun _ => .leaf 0 (C.age (N.leaf x))
  actual_topology := fun s => (actual_singleton_genealogy N s).symm
  original_leaf_dates := fun _ => rfl

/-- Actual empty-copy source initialization and execution with the ordinary
empty-observation convention. Fin 0 supplies no original sample labels. -/
noncomputable def emptyCalendarLaw (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (common : Bool) : PMF (Option (SingletonCalendarGenealogy X)) :=
  (naturalCompletedLaw N C (Fin.elim0 : Fin 0 → X) H p (fun _ => common) r).map
    (Function.const _ none)

lemma actual_empty_calendar_law (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (common : Bool) : emptyCalendarLaw N C H p r common = PMF.pure none := by
  exact PMF.map_const _ _

#print axioms singleton_source_has_no_legal_merge
#print axioms singleton_source_clock_catalogue_empty
#print axioms actual_singleton_genealogy
#print axioms canonical_singleton_calendar_genealogy_complete
#print axioms every_canonical_singleton_recorder_is_exact
#print axioms canonical_singleton_calendar_observation_binding
#print axioms actual_singleton_calendar_law
#print axioms actual_empty_calendar_law
end GProgram.G5.Sharpness
