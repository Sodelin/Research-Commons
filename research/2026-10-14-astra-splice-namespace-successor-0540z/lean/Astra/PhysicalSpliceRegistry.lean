import G1SplicedOriginalSwitching
import G5CommonSwitchingQuartetWitness
import UnifiedLean.Source.NativeIndependentPairMixture

/-!
# Literal original-parent registry on the actual two-port splice

Source-only integration candidate. No compiler or axiom-audit receipt yet.
The retained hybrid map, parent occurrences and strict probabilities are
constructed from the original source. The final theorem transports a whole
original COMMON bank to its actual restricted switching. No demographic rate,
weighted-law equality, bank probability pushforward or bounded witness is
assumed or asserted here.
-/

namespace Astra.PhysicalSpliceRegistry

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph G1SpliceDegrees
open G1SplicedSourceAdmission G1SplicedOriginalSwitching
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.NativeCommonPairGerm
open GProgram.G5.AttainedChronology
open G1CutChildPorts
open scoped Classical

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

def removedHybrid (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : Hybrid N :=
  ⟨A.fragment.parents.hybrid, A.fragment.parents.isHybrid⟩

/-- Vertex projection retains the actual original hybrid identity. -/
noncomputable def retainedHybrid (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) :
    Hybrid (splicedNetwork N hc b hb A) ↪ Hybrid N where
  toFun h := ⟨h.val.val, (actual_splice_hybrid_iff N hc b A h.val).mp h.property⟩
  inj' := by
    intro h k he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Subtype.val he

@[simp] theorem retainedHybrid_val (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (h : Hybrid (splicedNetwork N hc b hb A)) :
    (retainedHybrid N hc b hb A h).val = h.val.val := rfl

theorem retainedHybrid_ne_removed (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (h : Hybrid (splicedNetwork N hc b hb A)) :
    retainedHybrid N hc b hb A h ≠ removedHybrid N b A := by
  intro he
  exact h.val.property.2 (congrArg Subtype.val he)

private lemma hybrid_ne_upper (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (h : Hybrid N) :
    h.val ≠ A.fragment.upper := by
  intro he
  have hd := (actual_upper_tree_degrees N hc b A).1
  have hh := h.property.1
  rw [he, hd] at hh
  omega

/-- Every old hybrid other than the deleted one has a literal retained vertex. -/
noncomputable def survivingHybrid (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (h : Hybrid N) (hne : h ≠ removedHybrid N b A) :
    Hybrid (splicedNetwork N hc b hb A) := by
  have hH : h.val ≠ A.fragment.parents.hybrid := by
    intro he
    exact hne (Subtype.ext he)
  let v : SplicedVertex N b A := ⟨h.val, hybrid_ne_upper N hc b A h, hH⟩
  exact ⟨v, (actual_splice_hybrid_iff N hc b A v).mpr h.property⟩

@[simp] theorem retained_surviving_hybrid (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (h : Hybrid N) (hne : h ≠ removedHybrid N b A) :
    retainedHybrid N hc b hb A (survivingHybrid N hc b hb A h hne) = h := by
  apply Subtype.ext
  rfl

/-- Exact image, not just an injection or a hybrid-count inequality. -/
theorem retainedHybrid_image (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (h : Hybrid N) :
    (∃ k, retainedHybrid N hc b hb A k = h) ↔ h ≠ removedHybrid N b A := by
  constructor
  · rintro ⟨k, rfl⟩
    exact retainedHybrid_ne_removed N hc b hb A k
  · intro hne
    exact ⟨survivingHybrid N hc b hb A h hne,
      retained_surviving_hybrid N hc b hb A h hne⟩

/-- The bit chooses the same ordered original edge occurrence as before. -/
noncomputable def retainedParent (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (H : OriginalParentRegistry N) (h : Hybrid (splicedNetwork N hc b hb A))
    (bit : Bool) : RetainedEdge N b A := by
  let e := (H.parents (retainedHybrid N hc b hb A h)).parent bit
  have ht : N.graph.target e = h.val.val :=
    registry_parent_target N H (retainedHybrid N hc b hb A h) bit
  have hne : e ≠ A.child := by
    intro he
    have hh := (retainedHybrid N hc b hb A h).property
    rw [he] at ht
    exact actual_child_target_not_hybrid N b A (ht.symm ▸ hh)
  exact ⟨e, actual_in_edge_kept_of_ne_child N hc b A h.val e ht hne⟩

@[simp] theorem retainedParent_val (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (H : OriginalParentRegistry N) (h : Hybrid (splicedNetwork N hc b hb A))
    (bit : Bool) :
    (retainedParent N hc b hb A H h bit).val =
      (H.parents (retainedHybrid N hc b hb A h)).parent bit := rfl

noncomputable def splicedParents (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (H : OriginalParentRegistry N) (h : Hybrid (splicedNetwork N hc b hb A)) :
    GProgram.G2.OriginalHybridParents (splicedNetwork N hc b hb A) where
  hybrid := h.val
  isHybrid := h.property
  parent0 := .inl (retainedParent N hc b hb A H h false)
  parent1 := .inl (retainedParent N hc b hb A H h true)
  target0 := by
    apply Subtype.ext
    exact registry_parent_target N H (retainedHybrid N hc b hb A h) false
  target1 := by
    apply Subtype.ext
    exact registry_parent_target N H (retainedHybrid N hc b hb A h) true
  different := by
    intro he
    have hv := congrArg Subtype.val (Sum.inl.inj he)
    exact (H.parents (retainedHybrid N hc b hb A h)).different hv

/-- No canonical reordering: the original registry determines both new parents. -/
noncomputable def splicedRegistry (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (H : OriginalParentRegistry N) : OriginalParentRegistry (splicedNetwork N hc b hb A) where
  parents := splicedParents N hc b hb A H
  original_site _ := rfl

@[simp] theorem splicedRegistry_parent (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (H : OriginalParentRegistry N) (h : Hybrid (splicedNetwork N hc b hb A))
    (bit : Bool) :
    ((splicedRegistry N hc b hb A H).parents h).parent bit =
      .inl (retainedParent N hc b hb A H h bit) := by
  cases bit <;> rfl

/-- Strict probabilities stay at their original retained hybrid identities. -/
noncomputable def splicedProbabilities (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (p : HybridProbabilities N) : HybridProbabilities (splicedNetwork N hc b hb A) where
  gamma h := p.gamma (retainedHybrid N hc b hb A h)
  positive h := p.positive (retainedHybrid N hc b hb A h)
  below_one h := p.below_one (retainedHybrid N hc b hb A h)

@[simp] theorem splicedProbabilities_gamma (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (p : HybridProbabilities N) (h : Hybrid (splicedNetwork N hc b hb A)) :
    (splicedProbabilities N hc b hb A p).gamma h =
      p.gamma (retainedHybrid N hc b hb A h) := rfl

/-- Restriction of one whole original COMMON bank; no resampling or marginal fit. -/
noncomputable def restrictBank (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (coin : CommonSeed N) : CommonSeed (splicedNetwork N hc b hb A) :=
  fun h => coin (retainedHybrid N hc b hb A h)

private lemma common_keep_iff_parent (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (coin : CommonSeed N) (h : Hybrid N)
    (e : E) (ht : N.graph.target e = h.val) :
    (commonSwitching N H coin).keep e ↔ e = (H.parents h).parent (coin h) :=
  N.switchingOfChoices_keep_at_hybrid
    (fun k => ⟨(H.parents k).parent (coin k), registry_parent_target N H k (coin k)⟩)
    h e ht

/-- The constructed original-ID selector is exactly the actual graph splice
of every complete original COMMON switching. Equal exposure is not needed for
this structural identity; it is needed later for weighted laws. -/
theorem commonSwitching_restrict (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (H : OriginalParentRegistry N) (coin : CommonSeed N) :
    commonSwitching (splicedNetwork N hc b hb A) (splicedRegistry N hc b hb A H)
        (restrictBank N hc b hb A coin) =
      restrictSwitching N hc b hb A (commonSwitching N H coin) := by
  apply switching_ext
  intro e
  cases e with
  | inl e =>
      change (commonSwitching (splicedNetwork N hc b hb A)
        (splicedRegistry N hc b hb A H) (restrictBank N hc b hb A coin)).keep (.inl e) ↔
          (commonSwitching N H coin).keep e.val
      by_cases hh : N.graph.IsHybrid (N.graph.target e.val)
      · let h : Hybrid (splicedNetwork N hc b hb A) :=
          ⟨retainedTarget N hc b A e,
            (actual_splice_hybrid_iff N hc b A (retainedTarget N hc b A e)).mpr hh⟩
        rw [common_keep_iff_parent (splicedNetwork N hc b hb A)
          (splicedRegistry N hc b hb A H) (restrictBank N hc b hb A coin) h (.inl e) rfl,
          common_keep_iff_parent N H coin (retainedHybrid N hc b hb A h) e.val rfl,
          splicedRegistry_parent]
        constructor
        · intro he
          exact congrArg Subtype.val (Sum.inl.inj he)
        · intro he
          apply congrArg Sum.inl
          apply Subtype.ext
          exact he
      · have hn : ¬(splicedNetwork N hc b hb A).graph.IsHybrid
            ((splicedNetwork N hc b hb A).graph.target (.inl e)) := by
          intro ht
          exact hh ((actual_splice_hybrid_iff N hc b A (retainedTarget N hc b A e)).mp ht)
        exact ⟨fun _ => (commonSwitching N H coin).ordinary e.val hh,
          fun _ => (commonSwitching (splicedNetwork N hc b hb A)
            (splicedRegistry N hc b hb A H) (restrictBank N hc b hb A coin)).ordinary (.inl e) hn⟩
  | inr u =>
      have hn : ¬(splicedNetwork N hc b hb A).graph.IsHybrid
          ((splicedNetwork N hc b hb A).graph.target (.inr u)) := by
        intro hh
        exact actual_child_target_not_hybrid N b A
          ((actual_splice_hybrid_iff N hc b A (descendantInterface N b A)).mp hh)
      have hk := (commonSwitching (splicedNetwork N hc b hb A)
        (splicedRegistry N hc b hb A H) (restrictBank N hc b hb A coin)).ordinary (.inr u) hn
      exact ⟨fun _ => True.intro, fun _ => hk⟩

#check retainedHybrid_image
#check splicedRegistry_parent
#check splicedProbabilities_gamma
#check commonSwitching_restrict
#print axioms retainedHybrid_image
#print axioms splicedRegistry_parent
#print axioms splicedProbabilities_gamma
#print axioms commonSwitching_restrict

end Astra.PhysicalSpliceRegistry
