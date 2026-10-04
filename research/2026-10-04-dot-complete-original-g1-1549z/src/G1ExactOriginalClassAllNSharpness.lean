import G1SharpOriginalUnboundedTaxonFace

/-! The SAME accepted all-n saturating witnesses now inhabit the exact
original outer-labelled GALLED semidirected partner class. No new extremal
family, ordinary-profile witness bound, or source-image recognition claim. -/
namespace G1ExactOriginalClassAllNSharpness
open Nanuq.Source GProgram.G5 G1ActualGraphNormalization G1ReducedCoreCounts
open G1AllNActualOuterSourceSharpness G1SharpOriginalUnboundedTaxonFace
open G1ExactSemidirectedPartnerAdmission G1SameCoreLiteralSemidirectedTargets
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeIndependentPairMixture
open scoped Classical

/-- EVERY n≥4 has the actual old positive/interior source and reduced core
attaining the accepted bounds, with faithful literal semidirected admission
and the SAME taxon unbounded component now derived by curve conversion. -/
theorem every_n_has_exact_original_class_saturating_source (n : ℕ) (hn : 4 ≤ n) :
    ∃ S : Source.{0,0,0} (Fin n), Reduced S ∧ HasGalledOuterSemidirectedPartner S ∧
      Nonempty (PositivePairRates S.Edge) ∧ Nonempty (HybridProbabilities S.network) ∧
      (hybrids S.network).card = 2*n-2 ∧ Fintype.card S.Vertex = 6*n-5 ∧
      Fintype.card S.Edge = 8*n-8 ∧ (∀ x : Fin n, S.calendar.age (S.network.leaf x) = 0) := by
  obtain ⟨S,reduced,⟨D⟩,rates,prob,hh,hv,he,htips⟩ := every_n_has_actual_saturating_outer_source n hn
  have hp : HasOuterSemidirectedPartner S :=
    (actual_partner_drawing_equivalent_rooted_drawing S.network).mpr ⟨actualOriginalSegmentOuterCurves S.network D⟩
  exact ⟨S,reduced,actual_outer_source_partner_is_galled S hp,rates,prob,hh,hv,he,htips⟩

theorem exact_class_has_no_smaller_uniform_hybrid_bound (n : ℕ) (hn : 4 ≤ n) (b : ℕ) (hb : b < 2*n-2) :
    ¬ (∀ S : Source.{0,0,0} (Fin n), Reduced S → HasGalledOuterSemidirectedPartner S →
      (hybrids S.network).card ≤ b) := by
  intro hall
  obtain ⟨S,hr,hclass,_,_,hh,_,_,_⟩ := every_n_has_exact_original_class_saturating_source n hn
  have h := hall S hr hclass
  rw [hh] at h
  omega

theorem exact_class_has_no_smaller_uniform_vertex_bound (n : ℕ) (hn : 4 ≤ n) (b : ℕ) (hb : b < 6*n-5) :
    ¬ (∀ S : Source.{0,0,0} (Fin n), Reduced S → HasGalledOuterSemidirectedPartner S →
      Fintype.card S.Vertex ≤ b) := by
  intro hall
  obtain ⟨S,hr,hclass,_,_,_,hv,_,_⟩ := every_n_has_exact_original_class_saturating_source n hn
  have h := hall S hr hclass
  rw [hv] at h
  omega

theorem exact_class_has_no_smaller_uniform_edge_bound (n : ℕ) (hn : 4 ≤ n) (b : ℕ) (hb : b < 8*n-8) :
    ¬ (∀ S : Source.{0,0,0} (Fin n), Reduced S → HasGalledOuterSemidirectedPartner S →
      Fintype.card S.Edge ≤ b) := by
  intro hall
  obtain ⟨S,hr,hclass,_,_,_,_,he,_⟩ := every_n_has_exact_original_class_saturating_source n hn
  have h := hall S hr hclass
  rw [he] at h
  omega

#print axioms every_n_has_exact_original_class_saturating_source
end G1ExactOriginalClassAllNSharpness
