import SelectedMAGValidity
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Card

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

E1--E3 structural component: the original, unbounded-size finite source class
has exactly the same marked TCM image as a finite registry of common sources,
filtered by its FULL elementary graphical signature. This does not assert the
optimized B-query certificate, probability witnesses, or an extracted executable
decoder. The Finset definition is explicitly noncomputable until the finite
graph decision procedures replace the classical predicates.
-/

namespace RestrictedCausal.FiniteTargetImage

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open HPLTarget ProfileRegistry

universe u

/-- Original finite sources, with no bound on either hidden carrier. The
carrier lives one universe above its finite labels; it is not the registry.
In particular every finite pair of natural hidden/selection counts occurs. -/
structure FiniteSource (X : Type u) where
  selections : Type u
  latents : Type u
  selectionFintype : Fintype selections
  latentFintype : Fintype latents
  dag : SourceDAG X selections latents

def InvarianceCondition {X : Type u} (Z : X → Prop) : Option X → Prop
  | none => False
  | some x => Z x

/-- Graphical version of HPL Definition 6, using all legal elementary
coordinates. Set-valued separation is the conjunction over endpoint pairs;
selection is included by SelectedCondition. Named-root invariance uses one
source and one fixed augmented graph for each available target. -/
structure SameElementarySignature {X : Type u} (T : X → Prop)
    (D E : FiniteSource X) : Prop where
  baseline : ∀ (Z : X → Prop) (x y : X), x ≠ y → ¬ Z x → ¬ Z y →
    (ActiveConnection (arrowGraph D.dag.arrow) (SelectedCondition Z) (Observed x) (Observed y) ↔
      ActiveConnection (arrowGraph E.dag.arrow) (SelectedCondition Z) (Observed x) (Observed y))
  invariance : ∀ (t : {x : X // T x}) (Z : X → Prop) (x : X), ¬ Z x →
    (ActiveConnection (arrowGraph (augmentSource D.dag t.val).arrow)
        (SelectedCondition (InvarianceCondition Z)) (Observed none) (Observed (some x)) ↔
      ActiveConnection (arrowGraph (augmentSource E.dag t.val).arrow)
        (SelectedCondition (InvarianceCondition Z)) (Observed none) (Observed (some x)))

theorem SameElementarySignature.refl {X : Type u} (T : X → Prop) (D : FiniteSource X) :
    SameElementarySignature T D D where
  baseline := fun _ _ _ _ _ _ => Iff.rfl
  invariance := fun _ _ _ _ => Iff.rfl

theorem SameElementarySignature.symm {X : Type u} {T : X → Prop} {D E : FiniteSource X}
    (h : SameElementarySignature T D E) : SameElementarySignature T E D where
  baseline := fun Z x y hne hx hy => (h.baseline Z x y hne hx hy).symm
  invariance := fun t Z x hx => (h.invariance t Z x hx).symm

theorem SameElementarySignature.trans {X : Type u} {T : X → Prop} {D E F : FiniteSource X}
    (h : SameElementarySignature T D E) (k : SameElementarySignature T E F) :
    SameElementarySignature T D F where
  baseline := fun Z x y hne hx hy =>
    (h.baseline Z x y hne hx hy).trans (k.baseline Z x y hne hx hy)
  invariance := fun t Z x hx => (h.invariance t Z x hx).trans (k.invariance t Z x hx)

theorem same_signature_of_preserves {X : Type u} (T : X → Prop) (D E : FiniteSource X)
    (hbase : SourcePreserves D.dag E.dag)
    (haug : ∀ t : {x : X // T x}, SourcePreserves (augmentSource D.dag t.val) (augmentSource E.dag t.val)) :
    SameElementarySignature T D E where
  baseline := fun Z x y _ _ _ => hbase.connection Z x y
  invariance := fun t Z x _ => (haug t).connection (InvarianceCondition Z) none (some x)

def DisjointPred {X : Type u} (A B : X → Prop) : Prop := ∀ x, A x → ¬ B x

def SetsSeparated {X : Type u} (D : FiniteSource X) (A B Z : X → Prop) : Prop :=
  ∀ x, A x → ∀ y, B y →
    ¬ ActiveConnection (arrowGraph D.dag.arrow) (SelectedCondition Z) (Observed x) (Observed y)

def InvarianceSeparated {X : Type u} (D : FiniteSource X) (t : X) (A Z : X → Prop) : Prop :=
  ∀ x, A x → ¬ ActiveConnection (arrowGraph (augmentSource D.dag t).arrow)
    (SelectedCondition (InvarianceCondition Z)) (Observed none) (Observed (some x))

/-- The actual set-valued graphical conditions in HPL Definition 6, not
additional multi-indicator or jointly augmented constraints. -/
structure SameSetwiseSignature {X : Type u} (T : X → Prop) (D E : FiniteSource X) : Prop where
  baseline : ∀ A B Z : X → Prop, DisjointPred A B → DisjointPred A Z → DisjointPred B Z →
    (SetsSeparated D A B Z ↔ SetsSeparated E A B Z)
  invariance : ∀ (t : {x : X // T x}) (A Z : X → Prop), DisjointPred A Z →
    (InvarianceSeparated D t.val A Z ↔ InvarianceSeparated E t.val A Z)

theorem SameElementarySignature.setwise {X : Type u} {T : X → Prop} {D E : FiniteSource X}
    (h : SameElementarySignature T D E) : SameSetwiseSignature T D E where
  baseline A B Z hAB hAZ hBZ := by
    have hpair (x y : X) (hx : A x) (hy : B y) :
        ¬ ActiveConnection (arrowGraph D.dag.arrow) (SelectedCondition Z) (Observed x) (Observed y) ↔
        ¬ ActiveConnection (arrowGraph E.dag.arrow) (SelectedCondition Z) (Observed x) (Observed y) := by
      have hne : x ≠ y := fun heq => hAB x hx (heq.symm ▸ hy)
      exact not_congr (h.baseline Z x y hne (hAZ x hx) (hBZ y hy))
    exact ⟨fun hd x hx y hy => (hpair x y hx hy).mp (hd x hx y hy),
      fun he x hx y hy => (hpair x y hx hy).mpr (he x hx y hy)⟩
  invariance t A Z hAZ := by
    have hpair (x : X) (hx : A x) := not_congr (h.invariance t Z x (hAZ x hx))
    exact ⟨fun hd x hx => (hpair x hx).mp (hd x hx),
      fun he x hx => (hpair x hx).mpr (he x hx)⟩

theorem SameSetwiseSignature.elementary {X : Type u} {T : X → Prop} {D E : FiniteSource X}
    (h : SameSetwiseSignature T D E) : SameElementarySignature T D E where
  baseline Z x y hne hx hy := by
    classical
    have hsets := h.baseline (fun z => z = x) (fun z => z = y) Z
      (fun z hzx hzy => hne (hzx.symm.trans hzy))
      (fun z hz => hz.symm ▸ hx) (fun z hz => hz.symm ▸ hy)
    have hn : ¬ ActiveConnection (arrowGraph D.dag.arrow) (SelectedCondition Z) (Observed x) (Observed y) ↔
        ¬ ActiveConnection (arrowGraph E.dag.arrow) (SelectedCondition Z) (Observed x) (Observed y) := by
      simpa only [SetsSeparated, forall_eq] using hsets
    constructor
    · intro hd
      by_contra he
      exact (hn.mpr he) hd
    · intro he
      by_contra hd
      exact (hn.mp hd) he
  invariance t Z x hx := by
    classical
    have hsets := h.invariance t (fun z => z = x) Z (fun z hz => hz.symm ▸ hx)
    have hn : ¬ ActiveConnection (arrowGraph (augmentSource D.dag t.val).arrow)
        (SelectedCondition (InvarianceCondition Z)) (Observed none) (Observed (some x)) ↔
        ¬ ActiveConnection (arrowGraph (augmentSource E.dag t.val).arrow)
        (SelectedCondition (InvarianceCondition Z)) (Observed none) (Observed (some x)) := by
      simpa only [InvarianceSeparated, forall_eq] using hsets
    constructor
    · intro hd
      by_contra he
      exact (hn.mpr he) hd
    · intro he
      by_contra hd
      exact (hn.mp hd) he

theorem signature_iff_setwise {X : Type u} (T : X → Prop) (D E : FiniteSource X) :
    SameElementarySignature T D E ↔ SameSetwiseSignature T D E :=
  ⟨SameElementarySignature.setwise, SameSetwiseSignature.elementary⟩

noncomputable def registrySource {X : Type u} [LinearOrder X] [Fintype X]
    (Q : AdmissibleProfile X) : FiniteSource X := by
  letI : LinearOrder (CanonicalSelection.Vertex Q.val) := canonicalVertexOrder Q.val
  exact {
    selections := Selector Q.val
    latents := Root (SourceSelection.graph (SourceSelection.canonical Q.val))
    selectionFintype := inferInstance
    latentFintype := inferInstance
    dag := {
      arrow := Arrow (SourceSelection.graph (SourceSelection.canonical Q.val))
      acyclic := root_expansion_acyclic (SourceSelection.graph (SourceSelection.canonical Q.val))
        (SourceSelection.selected_directed_acyclic (SourceSelection.canonical Q.val) Q.property.2)
      selection_sink := SourceSelection.canonical_dag_selection_sinks Q.val } }

/-- Every arbitrary original finite source has an entry, and all available
indicators belong to that SAME entry. There is no separate choice per slice. -/
theorem original_registry_preserves {X : Type u} [LinearOrder X] [Fintype X]
    (D : FiniteSource X) :
    SourcePreserves D.dag (registrySource (originalProfile D.dag)).dag ∧
      ∀ t : X, SourcePreserves (augmentSource D.dag t)
        (augmentSource (registrySource (originalProfile D.dag)).dag t) := by
  letI : LinearOrder (CanonicalSelection.Vertex (sourceProfile D.dag)) :=
    canonicalVertexOrder (sourceProfile D.dag)
  exact ⟨canonical_baseline_preserves D.dag, canonical_indicator_preserves D.dag⟩

theorem original_registry_signature {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) (D : FiniteSource X) :
    SameElementarySignature T D (registrySource (originalProfile D.dag)) :=
  same_signature_of_preserves T D _ (original_registry_preserves D).1
    (fun t => (original_registry_preserves D).2 t.val)

theorem original_registry_target {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) (D : FiniteSource X) :
    tcm D.dag T = tcm (registrySource (originalProfile D.dag)).dag T :=
  tcm_eq_of_all_mags D.dag _ T (fun t => ((original_registry_preserves D).2 t.val).mag_eq)

noncomputable def registryList {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) (D : FiniteSource X) : Finset (MarkedGraph (CombinedVertex X T)) := by
  classical
  exact (Finset.univ.filter (fun Q : AdmissibleProfile X => SameElementarySignature T D (registrySource Q))).image
    (fun Q => tcm (registrySource Q).dag T)

/-- Exact marked TCM image of the ORIGINAL finite source class. Only the
right-hand existential source is unbounded. The left side filters actual
jointly realizable canonical sources, never independent MAG equivalence slices.
This is a structural finite-image theorem, not yet the B-query algorithm. -/
theorem registryList_exact {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) (D : FiniteSource X) (G : MarkedGraph (CombinedVertex X T)) :
    G ∈ registryList T D ↔ ∃ E : FiniteSource X,
      SameElementarySignature T D E ∧ tcm E.dag T = G := by
  classical
  constructor
  · intro h
    obtain ⟨Q, hQ, heq⟩ := Finset.mem_image.mp h
    exact ⟨registrySource Q, (Finset.mem_filter.mp hQ).2, heq⟩
  · rintro ⟨E, hDE, htarget⟩
    apply Finset.mem_image.mpr
    refine ⟨originalProfile E.dag, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact hDE.trans (original_registry_signature T E)
    · exact (original_registry_target T E).symm.trans htarget

theorem registryList_card_bound {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) (D : FiniteSource X) :
    (registryList T D).card ≤ 2 ^ Fintype.card X * 96 ^ ((Fintype.card X).choose 2) := by
  classical
  have himage := Finset.card_image_le (s := Finset.univ.filter
    (fun Q : AdmissibleProfile X => SameElementarySignature T D (registrySource Q)))
    (f := fun Q => tcm (registrySource Q).dag T)
  have hfilter := Finset.card_filter_le (Finset.univ : Finset (AdmissibleProfile X))
    (fun Q => SameElementarySignature T D (registrySource Q))
  have hle : (registryList T D).card ≤ Fintype.card (AdmissibleProfile X) :=
    himage.trans hfilter
  exact hle.trans (admissible_profile_card_bound X)

theorem registryList_exact_HPL_setwise {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) (D : FiniteSource X) (G : MarkedGraph (CombinedVertex X T)) :
    G ∈ registryList T D ↔ ∃ E : FiniteSource X,
      SameSetwiseSignature T D E ∧ tcm E.dag T = G := by
  rw [registryList_exact]
  exact ⟨fun ⟨E, h, heq⟩ => ⟨E, h.setwise, heq⟩,
    fun ⟨E, h, heq⟩ => ⟨E, h.elementary, heq⟩⟩

end RestrictedCausal.FiniteTargetImage
