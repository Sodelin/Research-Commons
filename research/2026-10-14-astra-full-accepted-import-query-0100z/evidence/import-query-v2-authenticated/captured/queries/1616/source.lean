import Astra.PositiveSupportAdapter
import Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7
import Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b
import Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0

namespace Astra.PositiveSupportAdapter
open scoped BigOperators

theorem quarter_emitted_support_bound {A : Type*} [Fintype A]
    (weight value : A → ℝ) (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = 1)
    (moment1 : ∑ a, weight a * (value a)^1 = (1/4 : ℝ))
    (moment3 : ∑ a, weight a * (value a)^3 = (1/64 : ℝ)) :
    (positiveSupportValues weight value).card ≤ 2 := by
  apply positive_support_card_le_pred 3 (threeCoefficients (1/32) (-3/16) 1)
    Astra.Generated.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7.polynomial ?_ 0 Astra.Generated.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7.nonzero_value weight value
  · intro x
    rw [threeCoefficients_eval]
    norm_num [Astra.Generated.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7.polynomial]
  · intro a ha
    exact Astra.Generated.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7.finite_supported_bank weight value hw hv
      (by simpa using moment0) (by simpa using moment1) (by simpa using moment3) a ha

#print axioms quarter_emitted_support_bound

theorem half_emitted_support_bound {A : Type*} [Fintype A]
    (weight value : A → ℝ) (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = 1)
    (moment1 : ∑ a, weight a * (value a)^1 = (1/2 : ℝ))
    (moment3 : ∑ a, weight a * (value a)^3 = (1/8 : ℝ)) :
    (positiveSupportValues weight value).card ≤ 2 := by
  apply positive_support_card_le_pred 3 (threeCoefficients (1/4) (-3/4) 1)
    Astra.Generated.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.polynomial ?_ 0 Astra.Generated.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.nonzero_value weight value
  · intro x
    rw [threeCoefficients_eval]
    norm_num [Astra.Generated.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.polynomial]
  · intro a ha
    exact Astra.Generated.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.finite_supported_bank weight value hw hv
      (by simpa using moment0) (by simpa using moment1) (by simpa using moment3) a ha

#print axioms half_emitted_support_bound

theorem endpoint_emitted_support_bound {A : Type*} [Fintype A]
    (weight value : A → ℝ) (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = 1)
    (moment1 : ∑ a, weight a * (value a)^1 = (1 : ℝ))
    (moment3 : ∑ a, weight a * (value a)^3 = (1 : ℝ)) :
    (positiveSupportValues weight value).card ≤ 2 := by
  apply positive_support_card_le_pred 3 (threeCoefficients (2) (-3) 1)
    Astra.Generated.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.polynomial ?_ 0 Astra.Generated.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.nonzero_value weight value
  · intro x
    rw [threeCoefficients_eval]
    norm_num [Astra.Generated.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.polynomial]
  · intro a ha
    exact Astra.Generated.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.finite_supported_bank weight value hw hv
      (by simpa using moment0) (by simpa using moment1) (by simpa using moment3) a ha

#print axioms endpoint_emitted_support_bound

end Astra.PositiveSupportAdapter
