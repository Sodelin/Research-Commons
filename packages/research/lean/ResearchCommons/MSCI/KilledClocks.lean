import UnifiedLean.Source.SourceMergerClockCatalogue
import Mathlib.Tactic

/-! Downstream formalization of the retained bounded-MSCI hand proof's
positive comparable-state denominators. Actual original source mergers,
population IDs, pair rates, complete current trees and copy labels are reused.
No killed-law/JC-channel equality, source-class oracle or demographic
identifiability is assumed or concluded. -/
set_option autoImplicit false
namespace ResearchCommons.MSCI
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open scoped Classical BigOperators

variable {V E Copy X Site G : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [Fintype Site] [AddCommMonoid G] [DecidableEq G]

def nonzeroCharge (a : G) : Nat := if a = 0 then 0 else 1

lemma nonzeroCharge_add_le (a b : G) :
    nonzeroCharge (a+b) ≤ nonzeroCharge a + nonzeroCharge b := by
  by_cases ha : a = 0
  · simp [nonzeroCharge, ha]
  · by_cases hb : b = 0
    · simp [nonzeroCharge, hb]
    · by_cases hab : a+b = 0 <;> simp [nonzeroCharge, ha, hb, hab]

/-- A charge is carried by the COMPLETE current tree, by summing the assigned
characters of its original sampled copies. It is not routed once per leaf. -/
def currentCharge (s : State V E Copy) (characters : Copy → Site → G)
    (l : Copy) (j : Site) : G :=
  ∑ x ∈ (s.genealogy l).leaves, characters x j

def rootChargeCount (s : State V E Copy) (characters : Copy → Site → G)
    (l : Copy) : Nat := ∑ j : Site, nonzeroCharge (currentCharge s characters l j)

def activeChargeCount (s : State V E Copy) (characters : Copy → Site → G) : Nat :=
  ∑ l ∈ s.live, rootChargeCount s characters l

lemma currentCharge_merge_survivor (s : State V E Copy) (hs : Valid s)
    {a b : Copy} (hm : LegalMerge s a b) (characters : Copy → Site → G) (j : Site) :
    currentCharge (merge s a b) characters a j =
      currentCharge s characters a j + currentCharge s characters b j := by
  simp only [currentCharge, merge, if_pos rfl, Genealogy.leaves]
  exact Finset.sum_union (distinct_live_genealogies_disjoint s hs
    hm.first_live hm.second_live hm.different)

lemma currentCharge_merge_other (s : State V E Copy) (a b l : Copy)
    (hla : l ≠ a) (characters : Copy → Site → G) (j : Site) :
    currentCharge (merge s a b) characters l j = currentCharge s characters l j := by
  simp only [currentCharge, merge, if_neg hla]

lemma rootChargeCount_merge_survivor (s : State V E Copy) (hs : Valid s)
    {a b : Copy} (hm : LegalMerge s a b) (characters : Copy → Site → G) :
    rootChargeCount (merge s a b) characters a ≤
      rootChargeCount s characters a + rootChargeCount s characters b := by
  unfold rootChargeCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  rw [currentCharge_merge_survivor s hs hm]
  exact nonzeroCharge_add_le _ _

lemma rootChargeCount_merge_other (s : State V E Copy) (a b l : Copy)
    (hla : l ≠ a) (characters : Copy → Site → G) :
    rootChargeCount (merge s a b) characters l = rootChargeCount s characters l := by
  unfold rootChargeCount
  apply Finset.sum_congr rfl
  intro j _
  rw [currentCharge_merge_other s a b l hla]

theorem activeChargeCount_merge_le (s : State V E Copy) (hs : Valid s)
    {a b : Copy} (hm : LegalMerge s a b) (characters : Copy → Site → G) :
    activeChargeCount (merge s a b) characters ≤ activeChargeCount s characters := by
  have ha : a ∈ s.live.erase b := Finset.mem_erase.mpr ⟨hm.different, hm.first_live⟩
  calc
    activeChargeCount (merge s a b) characters
      ≤ ∑ l ∈ s.live.erase b,
          (rootChargeCount s characters l +
            if l = a then rootChargeCount s characters b else 0) := by
        apply Finset.sum_le_sum
        intro l _
        by_cases hla : l = a
        · subst l
          simpa only [if_pos rfl] using rootChargeCount_merge_survivor s hs hm characters
        · rw [rootChargeCount_merge_other s a b l hla characters, if_neg hla, Nat.add_zero]
    _ = (∑ l ∈ s.live.erase b, rootChargeCount s characters l) +
        rootChargeCount s characters b := by
      rw [Finset.sum_add_distrib]
      simp [ha]
    _ = activeChargeCount s characters :=
      Finset.sum_erase_add _ _ hm.second_live

/-- Boundary transport changes populations/history but not current charges.
The literal natural pulse is such a transport of CURRENT roots. -/
theorem activeChargeCount_transport (s : State V E Copy) (characters : Copy → Site → G)
    (place : Copy → Location V E) (event : SourceEvent V E Copy) :
    activeChargeCount (transport s place event) characters = activeChargeCount s characters := rfl

lemma activeChargeCount_decode_encode (root : V) (s : State V E Copy) (hs : Valid s)
    (characters : Copy → Site → G) :
    activeChargeCount (decodeSnapshot root (encodeSnapshot s hs)) characters =
      activeChargeCount s characters := by
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro j _
  unfold currentCharge
  rw [decode_encode_live_genealogy root s hs hl]

theorem actual_merger_charge_count_nonincreasing (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (p : Choice N s)
    (characters : Copy → Site → G) :
    activeChargeCount (state (stepDestination N s (some p))) characters ≤
      activeChargeCount (state s) characters := by
  have hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  have hmerged := merge_source_valid N sample (state s) s.property hm
  change activeChargeCount (decodeSnapshot N.root
    (encodeSnapshot (merge (state s) p.2.val.1 p.2.val.2) hmerged.forest)) characters ≤ _
  rw [activeChargeCount_decode_encode]
  exact activeChargeCount_merge_le (state s) s.property.forest hm characters

lemma actual_choiceRate_positive (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (p : Choice N s) : 0 < choiceRate N r s p :=
  div_pos (pairRate_pos r p.1) (by norm_num)

/-- Reuses the OLD actual same-rate post-merger clock embedding. At least the
positive winning clock is removed, so the TOTAL actual coalescent rate strictly
falls. No distinct unrelated-state rates or occupancy formula is assumed. -/
theorem actual_totalRate_strict_merger (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (p : Choice N s) :
    totalRate N r (stepDestination N s (some p)) < totalRate N r s := by
  let f := destinationChoiceOld N s p
  let image : Finset (Choice N s) := Finset.univ.image f
  have hinj : Function.Injective f := destinationChoiceOld_injective N s p
  have hmissing : p ∉ image := by
    intro h
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp h
    exact destinationChoiceOld_ne_winner N s p q hq
  have heq : totalRate N r (stepDestination N s (some p)) =
      ∑ q ∈ image, choiceRate N r s q := by
    dsimp only [image]
    rw [Finset.sum_image (fun a _ b _ hab => hinj hab)]
    rfl
  rw [heq]
  exact Finset.sum_lt_sum_of_subset (Finset.subset_univ image) (Finset.mem_univ p)
    hmissing (actual_choiceRate_positive N r s p)
    (fun q _ _ => (actual_choiceRate_positive N r s q).le)

noncomputable def killedRate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (mu : ℝ) (characters : Copy → Site → G)
    (s : Code N sample) : ℝ :=
  totalRate N r s + mu * (activeChargeCount (state s) characters : ℝ)

/-- For every finite current forest/site panel, actual source merger and SAME
positive rate bank. Nonnegative killing includes JC mu=4/3. Character addition
cannot increase the number of nonzero current charges. -/
theorem actual_killedRate_strict_merger (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (mu : ℝ) (hmu : 0 ≤ mu)
    (characters : Copy → Site → G) (s : Code N sample) (p : Choice N s) :
    killedRate N r mu characters (stepDestination N s (some p)) <
      killedRate N r mu characters s := by
  have hc := actual_totalRate_strict_merger N r s p
  have hq : (activeChargeCount (state (stepDestination N s (some p))) characters : ℝ) ≤
      (activeChargeCount (state s) characters : ℝ) := by
    exact_mod_cast actual_merger_charge_count_nonincreasing N s p characters
  exact add_lt_add_of_lt_of_le hc (mul_le_mul_of_nonneg_left hq hmu)

theorem actual_merger_killed_difference_positive (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (mu : ℝ) (hmu : 0 ≤ mu)
    (characters : Copy → Site → G) (s : Code N sample) (p : Choice N s) :
    0 < killedRate N r mu characters s -
      killedRate N r mu characters (stepDestination N s (some p)) :=
  sub_pos.mpr (actual_killedRate_strict_merger N r mu hmu characters s p)

end ResearchCommons.MSCI
