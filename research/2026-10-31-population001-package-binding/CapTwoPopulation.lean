import SamuelAlexanderResearch.CapTwoSpecies

/-! Frozen CB-POPULATION-001 original cap-two owner/type correspondence.
NOT adopted until full-card correspondence review. Classical directed line
recoding and the original target-dependent P_s classification retain credit.
Retained positive port vertices, exact three roots/two children, opposite
parent genders and FULL infinite-word language (no shifted first bit) are
preserved. The SAME actual Arc/Vertices/gender witness is specieslike,
inspecies and reflective. No least-root count, generic line-graph invention,
empirical biological admission, executable infinite-population generator or
historical novelty certification is claimed. -/
set_option autoImplicit false
noncomputable section
namespace ResearchCommons.Claims.CapTwoPopulation
open SpeciesBridge BinaryAvoidance BinaryPopulation FixedGenderLift CapTwo

theorem exact_threshold (cap : Nat) (s : Nat → Bool) :
    (∃ E S g, FixedGenderPopulation E S g cap ∧
      ¬ FixedGenderReindex.RealizesOn E S g s) ↔
      2 ≤ cap ∧ ¬ EventuallyPeriodic s := by
  exact CapTwo.avoiding_population_exists_iff cap s

theorem below_two_impossible {E : Graph} {S : NatSet}
    {g : Nat → Bool} {cap : Nat} (population : FixedGenderPopulation E S g cap)
    (hcap : cap < 2) : False := by
  exact CapTwo.fixedGender_subcritical_impossible population hcap

theorem actual_three_root_two_child_avoider (s : Nat → Bool) (hs : ¬ EventuallyPeriodic s) :
    FixedGenderPopulation Arc Vertices (gender s) 2 ∧
    (∀ x, Vertices x → ∃ a b, a ≠ b ∧ Vertices a ∧ Vertices b ∧
      ∀ y, Arc x y ↔ y = a ∨ y = b) ∧
    (∀ y, (Vertices y ∧ Root (Induced Arc Vertices) y) ↔ y = 1 ∨ y = 2 ∨ y = 3) ∧
    ¬ FixedGenderReindex.RealizesOn Arc Vertices (gender s) s := by
  exact CapTwo.cap_two_avoider s hs

theorem actual_parent_ids (x y : Nat) (hy : 2 ≤ source y) :
    Arc x y ↔ x = 2 * source y - 2 ∨ x = 2 * source y - 3 := by
  exact CapTwo.parents_exactly x y hy

theorem each_gender_parent (s : Nat → Bool) (y : Nat) (hy : Vertices y)
    (hsource : 2 ≤ source y) (b : Bool) :
    ∃ x, Vertices x ∧ Arc x y ∧ gender s x = b := by
  exact CapTwo.incoming_gender s y hy hsource b

theorem full_unshifted_language (s word : Nat → Bool) :
    FixedGenderReindex.RealizesOn Arc Vertices (gender s) word ↔
      BinaryPopulation.Realizes (BinaryAvoidance.Edge s) word := by
  exact CapTwo.realizes_iff s word

theorem cap_two_unavoidability (s : Nat → Bool) :
    FixedGenderReindex.FixedGenderUnavoidable 2 s ↔ EventuallyPeriodic s := by
  exact CapTwo.fixedGender_cap_two_classification s

theorem same_actual_specieslike_inspecies_reflective_witness (s : Nat → Bool)
    (hs : ¬BinaryAvoidance.EventuallyPeriodic s) :
    FixedGenderPopulation Arc Vertices (CapTwo.gender s) 2 ∧
    Specieslike (Induced Arc Vertices) Vertices ∧
    Inspecies (Induced Arc Vertices) Vertices ∧
    Reflection (Induced Arc Vertices) Vertices ∧
    ¬FixedGenderReindex.RealizesOn Arc Vertices (CapTwo.gender s) s := by
  exact CapTwoSpecies.cap_two_inspecies_avoider s hs

end ResearchCommons.Claims.CapTwoPopulation
