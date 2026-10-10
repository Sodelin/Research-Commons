import G5NativeOriginalRouteCoverage
import UnifiedLean.Source.NativePairCalendarObservation
import G5PairMomentCases

/-!
# Observable pair support on safe original-tip stages
Contributor: dot / OpenAI, 2026-10-03.
The ordinary distinct-pair calendar coefficient's extreme values recover ALL
original-route sure-together / sure-separate predicates. Actual original-route
coverage is proved, while positive fair seeds and clock survival are inherited
from the hash-bound NativePairCalendarObservation provider. Different sources,
unknown rates and COMMON/I modes are allowed. No diagonal observations occur.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.SafePast
open GProgram.G5.QuartetKernel GProgram.G5.OriginalCoinLaw
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCurrentPortCompiler
open UnifiedLean.Source.NativeFairCurrentPosition UnifiedLean.Source.NativeFairSelectorAssembly
open UnifiedLean.Source.NativePairCalendarObservation UnifiedLean.Source.NativePairClockLaw
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma description_read_constant_bit (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x : X} {t : ℝ}
    (D : NativeCurrentDescription N C H x t) (b : Bool) :
    descriptionRead N C hcut H D (fun _ => b) = descriptionPositions N C hcut H D b := by
  unfold descriptionRead
  cases hs : descriptionSite D with
  | none => exact (description_positions_constant N C hcut H D hs b).symm
  | some h => rfl

lemma coOccupy_congr_routes (N : RootedBinary V E X) (C : Calendar N.graph)
    (R S : RouteFamily N) (he : ∀ x, R.edges x = S.edges x) (t : ℝ) (x y : X) :
    CoOccupy N R C t x y ↔ CoOccupy N S C t x y := by
  simp only [CoOccupy,he x,he y]

/-- Every pair of Boolean position choices is realized by an actual ORIGINAL
route family for DISTINCT original tips, including constant descriptions. -/
theorem all_routes_sure_together_iff_all_position_bits (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x y : X} (hne : x ≠ y) {t : ℝ}
    (D : NativeCurrentDescription N C H x t) (F : NativeCurrentDescription N C H y t) :
    (∀ R : RouteFamily N, CoOccupy N R C t x y) ↔
      ∀ b c : Bool, descriptionPositions N C hcut H D b = descriptionPositions N C hcut H F c := by
  constructor
  · intro hall b c
    let coin : X → Hybrid N → Bool := fun z _ => if z = x then b else c
    have hc := (native_description_cooccupy N C hcut H D F coin).mp (hall _)
    have hx : coin x = fun _ => b := by funext h; simp [coin]
    have hy : coin y = fun _ => c := by funext h; simp [coin,hne.symm]
    rw [hx,hy,description_read_constant_bit N C hcut H D b,
      description_read_constant_bit N C hcut H F c] at hc
    exact hc
  · intro hbits R
    obtain ⟨coin,hcoin⟩ := compiledRouteFamily_covers_original_routes N C H R
    apply (coOccupy_congr_routes N C _ R hcoin t x y).mp
    apply (native_description_cooccupy N C hcut H D F coin).mpr
    exact hbits _ _

theorem all_routes_sure_separate_iff_all_position_bits (N : RootedBinary V E X)
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) {x y : X} (hne : x ≠ y) {t : ℝ}
    (D : NativeCurrentDescription N C H x t) (F : NativeCurrentDescription N C H y t) :
    (∀ R : RouteFamily N, ¬CoOccupy N R C t x y) ↔
      ∀ b c : Bool, descriptionPositions N C hcut H D b ≠ descriptionPositions N C hcut H F c := by
  constructor
  · intro hall b c heq
    let coin : X → Hybrid N → Bool := fun z _ => if z = x then b else c
    apply hall (compiledRouteFamily N C H coin)
    apply (native_description_cooccupy N C hcut H D F coin).mpr
    have hx : coin x = fun _ => b := by funext h; simp [coin]
    have hy : coin y = fun _ => c := by funext h; simp [coin,hne.symm]
    rw [hx,hy,description_read_constant_bit N C hcut H D b,
      description_read_constant_bit N C hcut H F c]
    exact heq
  · intro hbits R hc
    obtain ⟨coin,hcoin⟩ := compiledRouteFamily_covers_original_routes N C H R
    have hco := (coOccupy_congr_routes N C _ R hcoin t x y).mpr hc
    have he := (native_description_cooccupy N C hcut H D F coin).mp hco
    exact hbits _ _ he

lemma count_four_iff_all_bool_equal {α : Type*} [DecidableEq α] (p q : Bool → α) :
    pairCount (binaryPositions p) (binaryPositions q) = 4 ↔ ∀ b c, p b = q c := by
  rw [pairCount_four_iff]
  simp only [binaryPositions]
  norm_num
  constructor <;> intro h <;> grind

lemma count_zero_iff_all_bool_ne {α : Type*} [DecidableEq α] (p q : Bool → α) :
    pairCount (binaryPositions p) (binaryPositions q) = 0 ↔ ∀ b c, p b ≠ q c := by
  rw [pairCount_zero_iff]
  simp only [binaryPositions]
  norm_num
  tauto

/-- The genuine observed coefficient recovers universal original-route support
at every safe stage. It is independent of posterior survivors or fitted rates. -/
theorem observed_safe_pair_support (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (B : Finset X) {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) {t : ℝ}
    (hlx : C.age (N.leaf x) ≤ t) (hly : C.age (N.leaf y) ≤ t) (ht : t < C.age N.root)
    (hsafe : SafeAt N C B t) :
    (pairCalendarCoefficients N C H (fairParameters N) r common x y t 0 = 0 ↔
      ∀ R : RouteFamily N, CoOccupy N R C t x y) ∧
    (pairCalendarCoefficients N C H (fairParameters N) r common x y t 0 = 1 ↔
      ∀ R : RouteFamily N, ¬CoOccupy N R C t x y) := by
  obtain ⟨D⟩ := original_current_description_exists N C H x hlx ht
  obtain ⟨F⟩ := original_current_description_exists N C H y hly ht
  rw [safe_calendar_constant_count N C hcut H r common B hx hy hne ht hsafe D F]
  rw [all_routes_sure_together_iff_all_position_bits N C hcut H hne D F,
    all_routes_sure_separate_iff_all_position_bits N C hcut H hne D F,
    ←count_four_iff_all_bool_equal,←count_zero_iff_all_bool_ne]
  constructor <;> constructor <;> intro h
  · exact_mod_cast (show (pairCount (binaryPositions (descriptionPositions N C hcut H D))
      (binaryPositions (descriptionPositions N C hcut H F)) : ℝ) = 4 by linarith)
  · have hcast : (pairCount (binaryPositions (descriptionPositions N C hcut H D))
      (binaryPositions (descriptionPositions N C hcut H F)) : ℝ) = 4 := by exact_mod_cast h
    linarith
  · exact_mod_cast (show (pairCount (binaryPositions (descriptionPositions N C hcut H D))
      (binaryPositions (descriptionPositions N C hcut H F)) : ℝ) = 0 by linarith)
  · have hcast : (pairCount (binaryPositions (descriptionPositions N C hcut H D))
      (binaryPositions (descriptionPositions N C hcut H F)) : ℝ) = 0 := by exact_mod_cast h
    linarith

/-- Distinct-pair support predicate expressed using only the actual observed
ordinary laws' intrinsic right-germ coefficients. -/
def ObservedSureBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (B D : Finset X) (t : ℝ) : Prop :=
  (∀ x ∈ D, ∀ y ∈ D, x ≠ y → pairCalendarCoefficients N C H (fairParameters N) r common x y t 0 = 0) ∧
  (∀ x ∈ D, ∀ y ∈ B, y ∉ D → pairCalendarCoefficients N C H (fairParameters N) r common x y t 0 = 1)

theorem pairSureBlock_iff_observed_safe (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (B D : Finset X) {t : ℝ} (hDB : D ⊆ B)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ t) (ht : t < C.age N.root)
    (hsafe : SafeAt N C B t) :
    PairSureBlock N C B D t ↔ ObservedSureBlock N C H r common B D t := by
  constructor
  · intro h
    constructor
    · intro x hx y hy hne
      exact (observed_safe_pair_support N C hcut H r common B (hDB hx) (hDB hy) hne
        (hl x (hDB hx)) (hl y (hDB hy)) ht hsafe).1.mpr (fun R => h.1 R x hx y hy hne)
    · intro x hx y hyB hyD
      have hne : x ≠ y := fun hxy => hyD (hxy ▸ hx)
      exact (observed_safe_pair_support N C hcut H r common B (hDB hx) hyB hne
        (hl x (hDB hx)) (hl y hyB) ht hsafe).2.mpr (fun R => h.2 R x hx y hyB hyD)
  · intro h
    constructor
    · intro R x hx y hy hne
      exact (observed_safe_pair_support N C hcut H r common B (hDB hx) (hDB hy) hne
        (hl x (hDB hx)) (hl y (hDB hy)) ht hsafe).1.mp (h.1 x hx y hy hne) R
    · intro R x hx y hyB hyD
      have hne : x ≠ y := fun hxy => hyD (hxy ▸ hx)
      exact (observed_safe_pair_support N C hcut H r common B (hDB hx) hyB hne
        (hl x (hDB hx)) (hl y hyB) ht hsafe).2.mp (h.2 x hx y hyB hyD) R

/-- Source-native exact blocks and observed distinct-pair support agree on
safe below-root stages. Ancestral terminal support is represented separately. -/
theorem sureExactBlock_iff_observed_safe (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (B D : Finset X) {t : ℝ} (hDB : D ⊆ B) (hD : D.Nonempty)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ t) (ht : t < C.age N.root)
    (hsafe : SafeAt N C B t) :
    SureExactBlock N C B D t ↔ ObservedSureBlock N C H r common B D t :=
  (sureExactBlock_iff_distinct_pair_predicates N C B D hDB hD hl ht).trans
    (pairSureBlock_iff_observed_safe N C hcut H r common B D hDB hl ht hsafe)

section DifferentSources
variable {V₂ E₂ : Type*} [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]

/-- Equality of fresh distinct-original-tip laws gives equality of source
sure-block support across DIFFERENT sources and COMMON/I modes on safe stages.
Both safe invariants are geometric premises proved by the chronology modules. -/
theorem equal_fair_pair_laws_sure_block_equivalence
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (common : Bool)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (r₂ : PositivePairRates E₂) (common₂ : Bool)
    (B D : Finset X) {t : ℝ} (hDB : D ⊆ B) (hD : D.Nonempty)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ t) (ht : t < C.age N.root)
    (hl₂ : ∀ x ∈ B, C₂.age (N₂.leaf x) ≤ t) (ht₂ : t < C₂.age N₂.root)
    (hsafe : SafeAt N C B t) (hsafe₂ : SafeAt N₂ C₂ B t)
    (heq : ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
      pairCalendarLaw N C H (fairParameters N) r common x y =
        pairCalendarLaw N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y) :
    SureExactBlock N C B D t ↔ SureExactBlock N₂ C₂ B D t := by
  rw [sureExactBlock_iff_observed_safe N C hcut H r common B D hDB hD hl ht hsafe,
    sureExactBlock_iff_observed_safe N₂ C₂ hcut₂ H₂ r₂ common₂ B D hDB hD hl₂ ht₂ hsafe₂]
  have hcoeff (x y : X) (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) :
      pairCalendarCoefficients N C H (fairParameters N) r common x y t 0 =
        pairCalendarCoefficients N₂ C₂ H₂ (fairParameters N₂) r₂ common₂ x y t 0 :=
    congrArg (fun f : ℝ →₀ ℝ => f 0) (equal_pair_calendar_laws_identify_coefficients
      N C H (fairParameters N) r common N₂ C₂ H₂ (fairParameters N₂) r₂ common₂
      x y hne ht ht₂ (heq x hx y hy hne))
  constructor <;> intro h <;> constructor
  · intro x hx y hy hne
    rw [←hcoeff x y (hDB hx) (hDB hy) hne]
    exact h.1 x hx y hy hne
  · intro x hx y hyB hyD
    rw [←hcoeff x y (hDB hx) hyB (fun hxy => hyD (hxy ▸ hx))]
    exact h.2 x hx y hyB hyD
  · intro x hx y hy hne
    rw [hcoeff x y (hDB hx) (hDB hy) hne]
    exact h.1 x hx y hy hne
  · intro x hx y hyB hyD
    rw [hcoeff x y (hDB hx) hyB (fun hxy => hyD (hxy ▸ hx))]
    exact h.2 x hx y hyB hyD
end DifferentSources

#print axioms sureExactBlock_iff_observed_safe
#print axioms equal_fair_pair_laws_sure_block_equivalence
#print axioms all_routes_sure_together_iff_all_position_bits
#print axioms all_routes_sure_separate_iff_all_position_bits
#print axioms observed_safe_pair_support
end GProgram.G5.AttainedChronology
