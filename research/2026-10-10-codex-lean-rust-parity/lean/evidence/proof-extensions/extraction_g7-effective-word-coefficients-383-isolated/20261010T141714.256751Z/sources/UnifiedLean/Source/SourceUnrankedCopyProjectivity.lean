import UnifiedLean.Source.SourceCrossCarrierNatural

/-!
# Actual same-source complete rooted UNRANKED copy projectivity

Contributor: dot, 2026-10-02. Closes the chosen inherited G2 foundational port:
pruning the actual natural completed original source equals the independently
initialized selected-original-copy source, with the SAME graph/calendar/rates/
original inheritance parameters/register prior. Concrete original label lift
is proved well defined on the existing child-swap quotient. No whole-law
comparison, private posterior or terminal observation identity is assumed.
-/
namespace UnifiedLean.Source.SourceUnrankedCopyProjectivity
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCrossCarrierNatural
open scoped Classical
variable {A B : Type*} [DecidableEq A] [DecidableEq B]

lemma mapLabels_unordered (f : A → B) {a b : Genealogy A} (h : UnorderedEquiv a b) :
    UnorderedEquiv (mapLabels f a) (mapLabels f b) := by
  induction h with
  | refl a => exact UnorderedEquiv.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | graft _ _ ih1 ih2 => exact UnorderedEquiv.graft ih1 ih2
  | swap a b => exact UnorderedEquiv.swap _ _

/-- The original-copy label injection is well defined on the EXACT inherited
nonplane binary-tree quotient; it adds no associativity or leaf erasure. -/
def mapUnranked (f : A → B) : UnrankedTree A → UnrankedTree B :=
  Quotient.map (mapLabels f) (fun _ _ h => mapLabels_unordered f h)

lemma mapUnranked_toUnranked (f : A → B) (a : Genealogy A) :
    mapUnranked f (toUnranked a) = toUnranked (mapLabels f a) := rfl

lemma mapUnranked_leaves [Fintype A] [Fintype B] (f : A → B) (q : UnrankedTree A) :
    treeLeaves (mapUnranked f q) = (treeLeaves q).image f := by
  induction q using Quotient.inductionOn with
  | h a => exact mapLabels_leaves f a

lemma mapUnranked_wellLabelled [Fintype A] [Fintype B] (f : A → B)
    (hf : Function.Injective f) (q : UnrankedTree A) (hq : treeWellLabelled q) :
    treeWellLabelled (mapUnranked f q) := by
  induction q using Quotient.inductionOn with
  | h a => exact mapLabels_wellLabelled f hf a hq

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The lifted small-source observer is precisely original-label renaming of
its actual concrete unranked forest, not a supplied observation map identity. -/
theorem actual_small_unranked_label_lift (keep : Finset Copy)
    (s : State V E (SelectedCopy keep)) :
    unrankedForest (liftView keep (selectedView s Finset.univ)) =
      (sourceUnrankedForest s Finset.univ).image (mapUnranked Subtype.val) := by
  ext q
  rw [mem_unrankedForest,Finset.mem_image]
  constructor
  · rintro ⟨x,t,ht,hq⟩
    have hx : x ∈ keep := by
      by_contra hn
      simp [liftView,hn] at ht
    let y : SelectedCopy keep := ⟨x,hx⟩
    have hg := lifted_original_genealogy keep s y
    rw [hg] at ht
    have he : mapLabels Subtype.val (s.genealogy (s.ancestor y)) = t := Option.some.inj ht
    refine ⟨toUnranked (s.genealogy (s.ancestor y)),?_,?_⟩
    · exact (mem_sourceUnrankedForest s Finset.univ _).mpr
        ⟨y,Finset.mem_univ _,s.genealogy (s.ancestor y),full_prune _,rfl⟩
    · rw [mapUnranked_toUnranked,he]
      exact hq
  · rintro ⟨q0,hq0,hq⟩
    obtain ⟨y,_,t,ht,hqt⟩ := (mem_sourceUnrankedForest s Finset.univ q0).mp hq0
    rw [full_prune] at ht
    have he : s.genealogy (s.ancestor y) = t := Option.some.inj ht
    refine ⟨y.val,mapLabels Subtype.val t,?_,?_⟩
    · rw [lifted_original_genealogy,he]
    · rw [← mapUnranked_toUnranked,hqt]
      exact hq

/-- End-to-end actual ORIGINAL source projectivity of complete rooted unranked
forests. The source on selected copies is initialized and evolved INDEPENDENTLY
on its true smaller carrier, while original graph/ages/rates/site gamma/mode
and SAME once-drawn COMMON register prior are retained across the comparison.
All source equality and eventual completion premises are discharged. -/
theorem actual_complete_unranked_copy_projectivity (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (keep : Finset Copy) (hk : keep.Nonempty)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) :
    (naturalCompletedLaw N C sample H p common r).map
      (fun s => sourceUnrankedForest (state s) keep) =
      (naturalCompletedUnrankedLaw N C (selectedSample sample keep) H p common r).map
        (fun F => F.image (mapUnranked Subtype.val)) := by
  have h := congrArg (fun law : PMF (JoinedIndex N sample keep) =>
      law.map (fun v => unrankedForest v.val))
    (actual_natural_completed_cross_carrier N C sample keep hk H p common r)
  simp only [PMF.map_comp,Function.comp_def,joinedProjection,joinedView] at h
  simp_rw [actual_small_unranked_label_lift] at h
  rw [naturalCompletedUnrankedLaw,PMF.map_comp]
  exact h

#print axioms mapUnranked_leaves
#print axioms mapUnranked_wellLabelled
#print axioms actual_small_unranked_label_lift
#print axioms actual_complete_unranked_copy_projectivity
end UnifiedLean.Source.SourceUnrankedCopyProjectivity
