import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
Deterministic certification for an arbitrary (possibly unknown-support) class law.
These theorems do not assert a concentration inequality, an IID RNA sampler law,
or a numerical total-variation certificate. The actual simultaneous interval
event and empirical zero counts of undiscovered classes are explicit premises.
The top-k conclusion concerns a set; it does not certify internal ranks.
-/

namespace E8DeterministicTopKCertificate

variable {α : Type*}

/-- Strict separation from every omitted class, with the requested cardinality. -/
def IsStrictTopKSet (mass : α → ℝ) (selected : Finset α) (k : ℕ) : Prop :=
  selected.card = k ∧
    ∀ a ∈ selected, ∀ b, b ∉ selected → mass b < mass a

/-- A checked certificate uses intervals on discovered classes and a separate
cap for every undiscovered class. Its fields do not contain the desired mass
ordering conclusion. -/
def HasIntervalCertificate (discovered selected : Finset α)
    (lower upper : α → ℝ) (unseenCap : ℝ) : Prop :=
  selected ⊆ discovered ∧
    (∀ a ∈ selected, unseenCap < lower a) ∧
    ∀ a ∈ selected, ∀ b ∈ discovered, b ∉ selected → upper b < lower a

theorem interval_certificate_topK
    (mass lower upper : α → ℝ) (discovered selected : Finset α)
    (unseenCap : ℝ) (k : ℕ)
    (hcard : selected.card = k)
    (hinterval : ∀ a ∈ discovered, lower a ≤ mass a ∧ mass a ≤ upper a)
    (hunseen : ∀ a, a ∉ discovered → mass a ≤ unseenCap)
    (hcert : HasIntervalCertificate discovered selected lower upper unseenCap) :
    IsStrictTopKSet mass selected k := by
  classical
  refine ⟨hcard, ?_⟩
  intro a ha b hb
  have hla : lower a ≤ mass a := (hinterval a (hcert.1 ha)).1
  by_cases hd : b ∈ discovered
  · exact lt_of_le_of_lt (hinterval b hd).2
      (lt_of_lt_of_le (hcert.2.2 a ha b hd hb) hla)
  · exact lt_of_le_of_lt (hunseen b hd)
      (lt_of_lt_of_le (hcert.2.1 a ha) hla)

theorem absolute_error_interval (mass empirical radius : ℝ)
    (h : |mass - empirical| ≤ radius) :
    empirical - radius ≤ mass ∧ mass ≤ empirical + radius := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  constructor <;> linarith

/-- Difference of two CDF boundary values has twice the supplied CDF error.
No discreteness/order construction or DKW probability claim is hidden here. -/
theorem cdf_jump_error
    (trueRight trueLeft empiricalRight empiricalLeft b : ℝ)
    (hright : |trueRight - empiricalRight| ≤ b)
    (hleft : |trueLeft - empiricalLeft| ≤ b) :
    |(trueRight - trueLeft) - (empiricalRight - empiricalLeft)| ≤ 2 * b := by
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp hright
  obtain ⟨hllo, hlhi⟩ := abs_le.mp hleft
  apply abs_le.mpr
  constructor <;> linarith

theorem unseen_class_mass_cap (mass empirical radius : ℝ)
    (herror : |mass - empirical| ≤ radius) (hzero : empirical = 0) :
    mass ≤ radius := by
  have hi := (absolute_error_interval mass empirical radius herror).2
  simpa [hzero] using hi

/-- Every selected class is checked, not merely an arbitrarily supplied kth
class. This is the empirical-radius certificate with unseen empirical mass 0. -/
theorem empirical_radius_topK
    (mass empirical : α → ℝ) (discovered selected : Finset α)
    (radius : ℝ) (k : ℕ)
    (hcard : selected.card = k)
    (herror : ∀ a, |mass a - empirical a| ≤ radius)
    (hzero : ∀ a, a ∉ discovered → empirical a = 0)
    (hcert : HasIntervalCertificate discovered selected
      (fun a => empirical a - radius) (fun a => empirical a + radius) radius) :
    IsStrictTopKSet mass selected k := by
  apply interval_certificate_topK mass
    (fun a => empirical a - radius) (fun a => empirical a + radius)
    discovered selected radius k hcard
  · intro a _
    exact absolute_error_interval (mass a) (empirical a) radius (herror a)
  · intro a ha
    exact unseen_class_mass_cap (mass a) (empirical a) radius (herror a) (hzero a ha)
  · exact hcert

/-- A single numeric threshold implements min-selected versus max-outsider,
including the unseen cap. Its upper bound must cover all discovered outsiders. -/
theorem threshold_certificate
    (discovered selected : Finset α) (lower upper : α → ℝ)
    (unseenCap selectedMinimum outsiderMaximum : ℝ)
    (hsubset : selected ⊆ discovered)
    (hmin : ∀ a ∈ selected, selectedMinimum ≤ lower a)
    (hmax : ∀ b ∈ discovered, b ∉ selected → upper b ≤ outsiderMaximum)
    (hgap : max outsiderMaximum unseenCap < selectedMinimum) :
    HasIntervalCertificate discovered selected lower upper unseenCap := by
  refine ⟨hsubset, ?_, ?_⟩
  · intro a ha
    exact lt_of_le_of_lt (le_max_right _ _)
      (lt_of_lt_of_le hgap (hmin a ha))
  · intro a ha b hb hbs
    exact lt_of_le_of_lt (hmax b hb hbs)
      (lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hgap (hmin a ha)))

/-- Supplied simultaneous validity at every time makes every successful
certificate sound, including at a data-selected stopping time. No optional
stopping theorem or probability coverage is assumed implicitly. -/
theorem anytime_empirical_radius_topK
    (mass : α → ℝ) (empirical : ℕ → α → ℝ)
    (discovered selected : ℕ → Finset α) (radius : ℕ → ℝ) (k : ℕ)
    (hcard : ∀ t, (selected t).card = k)
    (herror : ∀ t a, |mass a - empirical t a| ≤ radius t)
    (hzero : ∀ t a, a ∉ discovered t → empirical t a = 0) :
    ∀ t, HasIntervalCertificate (discovered t) (selected t)
      (fun a => empirical t a - radius t)
      (fun a => empirical t a + radius t) (radius t) →
      IsStrictTopKSet mass (selected t) k := by
  intro t hcert
  exact empirical_radius_topK mass (empirical t) (discovered t) (selected t)
    (radius t) k (hcard t) (herror t) (hzero t) hcert

end E8DeterministicTopKCertificate

#print axioms E8DeterministicTopKCertificate.interval_certificate_topK
#print axioms E8DeterministicTopKCertificate.absolute_error_interval
#print axioms E8DeterministicTopKCertificate.cdf_jump_error
#print axioms E8DeterministicTopKCertificate.unseen_class_mass_cap
#print axioms E8DeterministicTopKCertificate.empirical_radius_topK
#print axioms E8DeterministicTopKCertificate.threshold_certificate
#print axioms E8DeterministicTopKCertificate.anytime_empirical_radius_topK
