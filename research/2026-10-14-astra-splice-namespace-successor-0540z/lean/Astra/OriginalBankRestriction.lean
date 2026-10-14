import Astra.PhysicalSpliceRegistry
import UnifiedLean.Source.SourceNaturalInitialization
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Logic.Equiv.Set

/-!
# Restriction of the same original COMMON Bernoulli bank

Source-only integration proposal; no elaboration or axiom-audit receipt yet.
The finite product restriction is derived from the existing measure-preserving
split, projection and coordinate equivalence. Original site-dependent parameters
are retained. This is not a CURRENT independent-lineage pulse theorem, a
factorization of a user's configuration PMF, or a physical output-law theorem.
-/

namespace Astra.OriginalBankRestriction

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Nanuq.Source GProgram.G5
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open G1ActualTwoPortBlob G1SplicedSourceAdmission
open Astra.PhysicalSpliceRegistry
open G1CutChildPorts
open scoped Classical

/-- The existing finite-product split/projection proof, with the parameter
indexed by its original site. The omitted factor has total mass one. -/
theorem indexed_coin_subtype_measurePreserving {Site : Type*} [Fintype Site]
    (gamma : Site → unitInterval) (visible : Site → Prop) [DecidablePred visible] :
    MeasurePreserving (fun coin : Site → Bool => fun h : {h // visible h} => coin h.val)
      (Measure.pi (fun h : Site => bitMeasure (gamma h)))
      (Measure.pi (fun h : {h // visible h} => bitMeasure (gamma h.val))) := by
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun h : Site => bitMeasure (gamma h)) visible
  have hproject := measurePreserving_fst
    (μ := Measure.pi (fun h : {h // visible h} => bitMeasure (gamma h.val)))
    (ν := Measure.pi (fun h : {h // ¬visible h} => bitMeasure (gamma h.val)))
  exact hproject.comp hsplit

/-- Restrict one full heterogeneous bank through an injection. Even an empty
retained type is allowed; no fresh coins, conditioning or fitted probabilities
are introduced. -/
theorem indexed_coin_restriction_measurePreserving
    {Site Kept : Type*} [Fintype Site] [Fintype Kept]
    (gamma : Site → unitInterval) (J : Kept ↪ Site) :
    MeasurePreserving (fun coin : Site → Bool => fun h : Kept => coin (J h))
      (Measure.pi (fun h : Site => bitMeasure (gamma h)))
      (Measure.pi (fun h : Kept => bitMeasure (gamma (J h)))) := by
  classical
  let K : Set.range J ≃ Kept := (Equiv.ofInjective J J.injective).symm
  have hsite (h : Set.range J) : J (K h) = h.val :=
    Equiv.apply_ofInjective_symm J.injective h
  have hrestrict := indexed_coin_subtype_measurePreserving gamma
    (fun h : Site => h ∈ Set.range J)
  have hreindex := measurePreserving_piCongrLeft
    (fun h : Kept => bitMeasure (gamma (J h))) K
  have hmeasures :
      (fun h : Set.range J => bitMeasure (gamma (J (K h)))) =
        (fun h : Set.range J => bitMeasure (gamma h.val)) := by
    funext h
    rw [hsite h]
  rw [hmeasures] at hreindex
  have hmap : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Kept => Bool) K)) =
      (fun coin : Set.range J → Bool => fun h : Kept => coin (K.symm h)) := by
    funext coin h
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [hmap] at hreindex
  exact hreindex.comp hrestrict

/-- The PMF consequence uses the already defined measures, rather than
postulating the desired marginal or rebuilding it from supplied weights. -/
theorem indexed_coin_restriction_pmf
    {Site Kept : Type*} [Fintype Site] [Fintype Kept]
    (gamma : Site → unitInterval) (J : Kept ↪ Site) :
    (Measure.pi (fun h : Site => bitMeasure (gamma h))).toPMF.map
        (fun coin : Site → Bool => fun h : Kept => coin (J h)) =
      (Measure.pi (fun h : Kept => bitMeasure (gamma (J h)))).toPMF := by
  have h := indexed_coin_restriction_measurePreserving gamma J
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun coin : Site → Bool => fun h : Kept => coin (J h))
    (Measure.pi (fun h : Site => bitMeasure (gamma h))).toPMF h.measurable]
  simp only [Measure.toPMF_toMeasure]
  exact h.map_eq

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- The reduced natural parameter is the same original retained parameter;
true still selects original parent1. -/
lemma spliced_originalGamma (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (p : HybridProbabilities N) (h : Hybrid (splicedNetwork N hc b hb A)) :
    originalGamma (splicedProbabilities N hc b hb A p) h =
      originalGamma p (retainedHybrid N hc b hb A h) := by
  apply Subtype.ext
  rfl

/-- One once-drawn original COMMON bank is restricted by the actual retained
hybrid injection. Its exact omitted-site image is proved in the registry
provider; the probability argument needs only the proved injection. -/
theorem original_bank_restriction_measurePreserving
    (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (p : HybridProbabilities N) :
    MeasurePreserving (restrictBank N hc b hb A)
      (originalRegisterMeasure N p)
      (originalRegisterMeasure (splicedNetwork N hc b hb A)
        (splicedProbabilities N hc b hb A p)) := by
  simpa only [originalRegisterMeasure, restrictBank, spliced_originalGamma] using
    indexed_coin_restriction_measurePreserving (originalGamma p)
      (retainedHybrid N hc b hb A)

theorem original_bank_restriction_pmf
    (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (p : HybridProbabilities N) :
    (originalRegisterMeasure N p).toPMF.map (restrictBank N hc b hb A) =
      (originalRegisterMeasure (splicedNetwork N hc b hb A)
        (splicedProbabilities N hc b hb A p)).toPMF := by
  simpa only [originalRegisterMeasure, restrictBank, spliced_originalGamma] using
    indexed_coin_restriction_pmf (originalGamma p) (retainedHybrid N hc b hb A)

-- Future explicit type/axiom audit requests, not executed evidence.
#check indexed_coin_restriction_measurePreserving
#check indexed_coin_restriction_pmf
#check original_bank_restriction_pmf
#print axioms indexed_coin_subtype_measurePreserving
#print axioms indexed_coin_restriction_measurePreserving
#print axioms indexed_coin_restriction_pmf
#print axioms spliced_originalGamma
#print axioms original_bank_restriction_measurePreserving
#print axioms original_bank_restriction_pmf

end Astra.OriginalBankRestriction
