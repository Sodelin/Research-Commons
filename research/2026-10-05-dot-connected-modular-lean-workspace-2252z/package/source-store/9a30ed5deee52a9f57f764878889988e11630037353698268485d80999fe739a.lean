import E8DeterministicTopKCertificate
import Mathlib.Tactic.Linarith

/-!
Deterministic stability and separation of the E8 set certificate.
A discrepancy bound is an explicit verified premise. In particular, this file
does not turn floating-point checks into total-variation guarantees.
-/

namespace E8CertificateStability

open E8DeterministicTopKCertificate

variable {α : Type*}

theorem coordinate_error_transfer (target actual empirical radius eta : ℝ)
    (hactual : |actual - empirical| ≤ radius)
    (hdiscrepancy : |target - actual| ≤ eta) :
    |target - empirical| ≤ radius + eta := by
  obtain ⟨haLo, haHi⟩ := abs_le.mp hactual
  obtain ⟨hdLo, hdHi⟩ := abs_le.mp hdiscrepancy
  apply abs_le.mpr
  constructor <;> linarith

/-- A verified classwise discrepancy expands the lower, upper and unseen
bounds. A true TV bound supplies this premise, but no TV/sampler proof is
manufactured by the deterministic theorem. -/
theorem discrepancy_widened_intervals
    (target actual lower upper : α → ℝ) (discovered : Finset α)
    (unseenCap eta : ℝ)
    (hinterval : ∀ a ∈ discovered, lower a ≤ actual a ∧ actual a ≤ upper a)
    (hunseen : ∀ a, a ∉ discovered → actual a ≤ unseenCap)
    (hdiscrepancy : ∀ a, |target a - actual a| ≤ eta) :
    (∀ a ∈ discovered, lower a - eta ≤ target a ∧ target a ≤ upper a + eta) ∧
    (∀ a, a ∉ discovered → target a ≤ unseenCap + eta) := by
  constructor
  · intro a ha
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hdiscrepancy a)
    obtain ⟨hl, hu⟩ := hinterval a ha
    constructor <;> linarith
  · intro a ha
    have hu := hunseen a ha
    have hhi := (abs_le.mp (hdiscrepancy a)).2
    linarith

theorem widened_certificate_topK
    (target actual lower upper : α → ℝ) (discovered selected : Finset α)
    (unseenCap eta : ℝ) (k : ℕ)
    (hcard : selected.card = k)
    (hinterval : ∀ a ∈ discovered, lower a ≤ actual a ∧ actual a ≤ upper a)
    (hunseen : ∀ a, a ∉ discovered → actual a ≤ unseenCap)
    (hdiscrepancy : ∀ a, |target a - actual a| ≤ eta)
    (hcert : HasIntervalCertificate discovered selected
      (fun a => lower a - eta) (fun a => upper a + eta) (unseenCap + eta)) :
    IsStrictTopKSet target selected k := by
  obtain ⟨hi, hu⟩ := discrepancy_widened_intervals target actual lower upper
    discovered unseenCap eta hinterval hunseen hdiscrepancy
  exact interval_certificate_topK target (fun a => lower a - eta)
    (fun a => upper a + eta) discovered selected (unseenCap + eta) k hcard hi hu hcert

/-- The familiar 4r sufficient gap is a consequence of two endpoint errors
and two interval radii. It is not a necessary condition for the certificate. -/
theorem four_radius_gap_separates (massA massB empiricalA empiricalB radius : ℝ)
    (hA : |massA - empiricalA| ≤ radius)
    (hB : |massB - empiricalB| ≤ radius)
    (hgap : 4 * radius < massA - massB) :
    empiricalB + radius < empiricalA - radius := by
  obtain ⟨haLo, haHi⟩ := abs_le.mp hA
  obtain ⟨hbLo, hbHi⟩ := abs_le.mp hB
  linarith

theorem positive_mass_beats_unseen (mass empirical radius : ℝ)
    (herror : |mass - empirical| ≤ radius)
    (hpositive : 3 * radius < mass) :
    radius < empirical - radius := by
  have hhi := (abs_le.mp herror).2
  linarith

/-- Once the chosen classes are discovered and the stated true-mass/gap
conditions hold, the deterministic certificate necessarily succeeds. -/
theorem true_gap_implies_certificate
    (mass empirical : α → ℝ) (discovered selected : Finset α) (radius : ℝ)
    (hsubset : selected ⊆ discovered)
    (herror : ∀ a, |mass a - empirical a| ≤ radius)
    (hpositive : ∀ a ∈ selected, 3 * radius < mass a)
    (hgap : ∀ a ∈ selected, ∀ b, b ∉ selected → 4 * radius < mass a - mass b) :
    HasIntervalCertificate discovered selected
      (fun a => empirical a - radius) (fun a => empirical a + radius) radius := by
  refine ⟨hsubset, ?_, ?_⟩
  · intro a ha
    exact positive_mass_beats_unseen (mass a) (empirical a) radius (herror a)
      (hpositive a ha)
  · intro a ha b _ hb
    exact four_radius_gap_separates (mass a) (mass b) (empirical a)
      (empirical b) radius (herror a) (herror b) (hgap a ha b hb)

end E8CertificateStability

#print axioms E8CertificateStability.coordinate_error_transfer
#print axioms E8CertificateStability.discrepancy_widened_intervals
#print axioms E8CertificateStability.widened_certificate_topK
#print axioms E8CertificateStability.four_radius_gap_separates
#print axioms E8CertificateStability.positive_mass_beats_unseen
#print axioms E8CertificateStability.true_gap_implies_certificate
