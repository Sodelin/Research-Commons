import UnifiedLean.Source.NativeCurrentPortCompiler

/-!
# Full-case native fair selector moments

Contributor: dot / GPT-6.1 Sol, 2026-10-02. Finite fair original-site marginals
are reused for optional current sites: ordinary/bridge cases are constant,
while hybrid cases depend on their actual original bit. The optional-site
calculation is then instantiated on the derived native current descriptions.
No auxiliary coin is added to the biological source or observations.
-/
namespace UnifiedLean.Source.NativeFairSelectorAssembly
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5 GProgram.G5.SafePast
open GProgram.G5.OriginalCoinLaw GProgram.G5.QuartetKernel
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.NativeFairCurrentPosition UnifiedLean.Source.NativeCurrentPortCompiler
open scoped Classical BigOperators ENNReal NNReal

section OptionalFairMarginals
variable {Site α : Type*} [Fintype Site] [DecidableEq Site] [DecidableEq α]

lemma original_fair_one_site_mass (site : Site) (b : Bool) :
    (∑ a : Site → Bool, independentWeight (1/2) a * if a site = b then 1 else 0) = (1/2 : ℚ) := by
  have heq : (∑ a : Site → Bool, independentWeight (1/2) a * if a site = b then 1 else 0) =
      coinCylinderMass (1/2) {site} (fun _ => b) := by simp [coinCylinderMass]
  rw [heq,coinCylinderMass_eq_retained_product]
  simp only [Finset.prod_singleton,bitWeight_fair]

lemma original_fair_one_site_expectation (site : Site) (F : Bool → ℚ) :
    (∑ a : Site → Bool, independentWeight (1/2) a * F (a site)) =
      (F false+F true)/2 := by
  have heq : ∀ a : Site → Bool, independentWeight (1/2) a * F (a site) =
      (independentWeight (1/2) a * if a site = false then 1 else 0)*F false +
      (independentWeight (1/2) a * if a site = true then 1 else 0)*F true := by
    intro a
    cases h : a site <;> simp [h]
  simp_rw [heq]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul,
    original_fair_one_site_mass,original_fair_one_site_mass]
  ring

noncomputable def optionalRead (site : Option Site) (pos : Bool → α) (a : Site → Bool) : α :=
  pos (site.elim false a)

/-- Constant descriptions do not use a site. Distinct actual sites have the
proved independent marginal. The biological source receives no ghost bit. -/
theorem original_optional_fair_meeting_weight (s t : Option Site) (p q : Bool → α)
    (hp : s = none → ∀ b, p b = p false) (hq : t = none → ∀ b, q b = q false)
    (hsep : ∀ i j, s = some i → t = some j → i ≠ j) :
    (∑ a : Site → Bool, independentWeight (1/2) a *
      if optionalRead s p a = optionalRead t q a then 1 else 0) =
      (pairCount (binaryPositions p) (binaryPositions q) : ℚ)/4 := by
  cases s with
  | none =>
      cases t with
      | none =>
          change (∑ a : Site → Bool, independentWeight (1/2) a *
            (if p false = q false then 1 else 0)) = _
          rw [← Finset.sum_mul,independentWeight_normalized]
          simp only [pairCount,binaryPositions,hp rfl,hq rfl]
          split_ifs <;> simp_all <;> norm_num
      | some j =>
          simp only [optionalRead,Option.elim_none,Option.elim_some]
          rw [original_fair_one_site_expectation j (fun b => if p false = q b then 1 else 0)]
          simp only [pairCount,binaryPositions,hp rfl]
          split_ifs <;> simp_all <;> norm_num
  | some i =>
      cases t with
      | none =>
          simp only [optionalRead,Option.elim_some,Option.elim_none]
          rw [original_fair_one_site_expectation i (fun b => if p b = q false then 1 else 0)]
          simp only [pairCount,binaryPositions,hq rfl]
          split_ifs <;> simp_all <;> norm_num
      | some j =>
          simp only [optionalRead,Option.elim_some]
          exact fair_source_meeting_weight (hsep i j rfl rfl) p q

end OptionalFairMarginals

section OriginalSource
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma description_positions_constant (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x : X} {t : ℝ}
    (D : NativeCurrentDescription N C H x t) :
    descriptionSite D = none → ∀ b,
      descriptionPositions N C hcut H D b = descriptionPositions N C hcut H D false := by
  cases D <;> simp only [descriptionSite,descriptionPositions,Option.some_ne_none] <;> simp

lemma native_description_cooccupy (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x y : X} {t : ℝ}
    (D : NativeCurrentDescription N C H x t) (F : NativeCurrentDescription N C H y t)
    (coin : X → Hybrid N → Bool) :
    CoOccupy N (compiledRouteFamily N C H coin) C t x y ↔
      descriptionRead N C hcut H D (coin x) = descriptionRead N C hcut H F (coin y) := by
  have hx := description_read_native_source_spec N C hcut H D coin
  have hy := description_read_native_source_spec N C hcut H F coin
  constructor
  · rintro ⟨e,hex,hey,ha⟩
    have hxe := ((compiledRouteFamily N C H coin).valid x).active_unique C hex hx.1 ha hx.2
    have hye := ((compiledRouteFamily N C H coin).valid y).active_unique C hey hy.1 ha hy.2
    exact hxe.symm.trans hye
  · intro heq
    exact ⟨_,hx.1,heq ▸ hy.1,hx.2⟩

def independentDescriptionSite (N : RootedBinary V E X) {C : Calendar N.graph}
    {H : OriginalParentRegistry N} {x : X} {t : ℝ}
    (D : NativeCurrentDescription N C H x t) : Option (X × Hybrid N) :=
  (descriptionSite D).map (fun h => (x,h))

lemma independent_description_optional_read (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x : X} {t : ℝ}
    (D : NativeCurrentDescription N C H x t) (a : NativeCoinSeed N) :
    optionalRead (independentDescriptionSite N D) (descriptionPositions N C hcut H D) a =
      descriptionRead N C hcut H D (fun h => a (x,h)) := by
  cases D <;> rfl

lemma common_description_optional_read (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x : X} {t : ℝ}
    (D : NativeCurrentDescription N C H x t) (a : Hybrid N → Bool) :
    optionalRead (descriptionSite D) (descriptionPositions N C hcut H D) a =
      descriptionRead N C hcut H D a := by
  cases D <;> rfl

lemma independent_description_no_site_const (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x : X} {t : ℝ}
    (D : NativeCurrentDescription N C H x t) :
    independentDescriptionSite N D = none → ∀ b,
      descriptionPositions N C hcut H D b = descriptionPositions N C hcut H D false := by
  intro hs
  apply description_positions_constant N C hcut H D
  simpa only [independentDescriptionSite,Option.map_eq_none_iff] using hs

lemma independent_description_sites_separated (N : RootedBinary V E X) {C : Calendar N.graph}
    {H : OriginalParentRegistry N} {x y : X} {t : ℝ} (hne : x ≠ y)
    (D : NativeCurrentDescription N C H x t) (F : NativeCurrentDescription N C H y t) :
    ∀ u v, independentDescriptionSite N D = some u →
      independentDescriptionSite N F = some v → u ≠ v := by
  intro u v hu hv
  cases D <;> cases F <;> simp [independentDescriptionSite,descriptionSite] at hu hv
  subst u
  subst v
  exact fun heq => hne (congrArg Prod.fst heq)

/-- All bridge/ordinary/hybrid native cases have exact fair original-source
meeting count/4, including concentrated descriptions without a coin site. -/
theorem all_case_native_independent_fair_meeting_weight (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x y : X} (hne : x ≠ y) {t : ℝ}
    (D : NativeCurrentDescription N C H x t) (F : NativeCurrentDescription N C H y t) :
    (∑ a : NativeCoinSeed N, originalCoinMass N (fairParameters N) a *
      if CoOccupy N (seededRoutes N C H a) C t x y then 1 else 0) =
      (pairCount (binaryPositions (descriptionPositions N C hcut H D))
        (binaryPositions (descriptionPositions N C hcut H F)) : ℝ)/4 := by
  have hq := original_optional_fair_meeting_weight
    (independentDescriptionSite N D) (independentDescriptionSite N F)
    (descriptionPositions N C hcut H D) (descriptionPositions N C hcut H F)
    (independent_description_no_site_const N C hcut H D)
    (independent_description_no_site_const N C hcut H F)
    (independent_description_sites_separated N hne D F)
  have hevent (a : NativeCoinSeed N) : CoOccupy N (seededRoutes N C H a) C t x y ↔
      optionalRead (independentDescriptionSite N D) (descriptionPositions N C hcut H D) a =
        optionalRead (independentDescriptionSite N F) (descriptionPositions N C hcut H F) a := by
    rw [independent_description_optional_read,independent_description_optional_read]
    exact native_description_cooccupy N C hcut H D F (fun x h => a (x,h))
  simp_rw [hevent,originalCoinMass_fair]
  have hh := congrArg (fun z : ℚ => (z : ℝ)) hq
  push_cast at hh
  simpa only [apply_ite,Rat.cast_one,Rat.cast_zero] using hh

lemma common_description_sites_separated (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (B : Finset X) {x y : X}
    (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ} (hsafe : SafeAt N C B t)
    (D : NativeCurrentDescription N C H x t) (F : NativeCurrentDescription N C H y t) :
    ∀ u v, descriptionSite D = some u → descriptionSite F = some v → u ≠ v := by
  intro u v hu hv
  cases D <;> cases F <;> simp [descriptionSite] at hu hv
  subst u
  subst v
  exact safe_current_hybrid_sites_distinct N C H B hx hy hne hsafe _ _

/-- SAME-site COMMON original registers give the identical full-case fair
count at the safe stage; all site separation follows from original geometry. -/
theorem all_case_native_common_fair_meeting_weight (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (B : Finset X) {x y : X}
    (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ} (hsafe : SafeAt N C B t)
    (D : NativeCurrentDescription N C H x t) (F : NativeCurrentDescription N C H y t) :
    (∑ a : UnifiedLean.Source.NativeCommonPairGerm.CommonSeed N,
      UnifiedLean.Source.NativeCommonPairGerm.commonSeedWeight N (fairParameters N) a *
      if CoOccupy N (UnifiedLean.Source.NativeCommonPairGerm.commonRoutes N C H a) C t x y
        then 1 else 0) =
      (pairCount (binaryPositions (descriptionPositions N C hcut H D))
        (binaryPositions (descriptionPositions N C hcut H F)) : ℝ)/4 := by
  have hq := original_optional_fair_meeting_weight (descriptionSite D) (descriptionSite F)
    (descriptionPositions N C hcut H D) (descriptionPositions N C hcut H F)
    (description_positions_constant N C hcut H D)
    (description_positions_constant N C hcut H F)
    (common_description_sites_separated N C H B hx hy hne hsafe D F)
  have hevent (a : Hybrid N → Bool) :
      CoOccupy N (UnifiedLean.Source.NativeCommonPairGerm.commonRoutes N C H a) C t x y ↔
      optionalRead (descriptionSite D) (descriptionPositions N C hcut H D) a =
        optionalRead (descriptionSite F) (descriptionPositions N C hcut H F) a := by
    rw [common_description_optional_read,common_description_optional_read]
    exact native_description_cooccupy N C hcut H D F (fun _ h => a h)
  simp_rw [hevent,UnifiedLean.Source.NativeCommonPairGerm.commonSeedWeight_fair]
  have hh := congrArg (fun z : ℚ => (z : ℝ)) hq
  push_cast at hh
  simpa only [apply_ite,Rat.cast_one,Rat.cast_zero] using hh

/-- Every current port case now supplies the actual independent zero
coefficient/count link. SafeAt removes past survival weighting. -/
theorem all_case_safe_native_zero_coefficient (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E)
    (B : Finset X) {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ}
    (ht : t < C.age N.root) (hsafe : SafeAt N C B t)
    (D : NativeCurrentDescription N C H x t) (F : NativeCurrentDescription N C H y t) :
    UnifiedLean.Source.NativeSafePastGerm.nativeGermCoefficients N C H (fairParameters N) r x y t 0 =
      1-(pairCount (binaryPositions (descriptionPositions N C hcut H D))
        (binaryPositions (descriptionPositions N C hcut H F)) : ℝ)/4 := by
  rw [UnifiedLean.Source.NativeSafePastGerm.safe_native_zero_coefficient
    N C H (fairParameters N) r B hx hy hne ht hsafe]
  have hsum : UnifiedLean.Source.NativeSafePastGerm.nativeSeparationMass
      N C H (fairParameters N) x y t +
      (∑ a : NativeCoinSeed N, originalCoinMass N (fairParameters N) a *
        if CoOccupy N (seededRoutes N C H a) C t x y then 1 else 0) = 1 := by
    rw [UnifiedLean.Source.NativeSafePastGerm.nativeSeparationMass,← Finset.sum_add_distrib]
    convert originalCoinMass_normalized N (fairParameters N) using 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : CoOccupy N (seededRoutes N C H a) C t x y <;> simp [h]
  rw [all_case_native_independent_fair_meeting_weight N C hcut H hne D F] at hsum
  linarith

/-- The SAME actual COMMON zero coefficient has the all-case selector
count, including ordinary/bridge constants and mixed pairs. -/
theorem all_case_safe_common_zero_coefficient (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E)
    (B : Finset X) {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ}
    (ht : t < C.age N.root) (hsafe : SafeAt N C B t)
    (D : NativeCurrentDescription N C H x t) (F : NativeCurrentDescription N C H y t) :
    UnifiedLean.Source.NativeCommonPairGerm.commonGermCoefficients N C H (fairParameters N) r x y t 0 =
      1-(pairCount (binaryPositions (descriptionPositions N C hcut H D))
        (binaryPositions (descriptionPositions N C hcut H F)) : ℝ)/4 := by
  rw [UnifiedLean.Source.NativeCommonPairGerm.safe_actual_common_zero_coefficient
    N C H (fairParameters N) r B hx hy hne ht hsafe]
  have hsum : UnifiedLean.Source.NativeCommonPairGerm.commonSeparationMass
      N C H (fairParameters N) x y t +
      (∑ a : UnifiedLean.Source.NativeCommonPairGerm.CommonSeed N,
        UnifiedLean.Source.NativeCommonPairGerm.commonSeedWeight N (fairParameters N) a *
        if CoOccupy N (UnifiedLean.Source.NativeCommonPairGerm.commonRoutes N C H a) C t x y
          then 1 else 0) = 1 := by
    rw [UnifiedLean.Source.NativeCommonPairGerm.commonSeparationMass,← Finset.sum_add_distrib]
    convert UnifiedLean.Source.SourceEpochSemigroup.pmf_sum_real
      (UnifiedLean.Source.NativeCommonPairGerm.commonSeedPMF N (fairParameters N)) using 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : CoOccupy N (UnifiedLean.Source.NativeCommonPairGerm.commonRoutes N C H a) C t x y <;>
      simp [h,UnifiedLean.Source.NativeCommonPairGerm.commonSeedWeight]
  rw [all_case_native_common_fair_meeting_weight N C hcut H B hx hy hne hsafe D F] at hsum
  linarith

/-- Uniform ORIGINAL-source result at every safe below-root age: descriptions
are DERIVED, both physical coin mechanisms yield the count, and positive
unknown rates can differ. There is no supplied port/position/probability field. -/
theorem original_all_case_safe_selector_bridge (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N)
    (rIndependent rCommon : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E)
    (B : Finset X) {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ}
    (hlx : C.age (N.leaf x) ≤ t) (hly : C.age (N.leaf y) ≤ t)
    (ht : t < C.age N.root) (hsafe : SafeAt N C B t) :
    ∃ (D : NativeCurrentDescription N C H x t) (F : NativeCurrentDescription N C H y t),
      UnifiedLean.Source.NativeSafePastGerm.nativeGermCoefficients N C H (fairParameters N)
          rIndependent x y t 0 =
        1-(pairCount (binaryPositions (descriptionPositions N C hcut H D))
          (binaryPositions (descriptionPositions N C hcut H F)) : ℝ)/4 ∧
      UnifiedLean.Source.NativeCommonPairGerm.commonGermCoefficients N C H (fairParameters N)
          rCommon x y t 0 =
        1-(pairCount (binaryPositions (descriptionPositions N C hcut H D))
          (binaryPositions (descriptionPositions N C hcut H F)) : ℝ)/4 := by
  obtain ⟨D⟩ := original_current_description_exists N C H x hlx ht
  obtain ⟨F⟩ := original_current_description_exists N C H y hly ht
  exact ⟨D,F,all_case_safe_native_zero_coefficient N C hcut H rIndependent B hx hy hne ht hsafe D F,
    all_case_safe_common_zero_coefficient N C hcut H rCommon B hx hy hne ht hsafe D F⟩

#print axioms all_case_safe_native_zero_coefficient
#print axioms all_case_safe_common_zero_coefficient
#print axioms original_all_case_safe_selector_bridge
end OriginalSource

#print axioms all_case_native_independent_fair_meeting_weight
#print axioms all_case_native_common_fair_meeting_weight
#print axioms original_fair_one_site_mass
#print axioms original_fair_one_site_expectation
#print axioms original_optional_fair_meeting_weight
end UnifiedLean.Source.NativeFairSelectorAssembly
