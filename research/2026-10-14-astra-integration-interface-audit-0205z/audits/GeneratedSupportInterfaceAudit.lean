import AstraGeneratedSupport

/-! Source-only exact selected wrapper audit. The seven certificate identities,
all declared moments and even zero-coefficient levels remain literal. These
are existing conditional signatures, not certificate acquisition or execution.
-/
set_option autoImplicit false
namespace Astra.IntegrationInterfaceAudit.GeneratedSupport
open Astra.PositiveSupportAdapter
open scoped BigOperators
universe uAtom

-- Exact namespace/certificate ID: Astra.GeneratedSupport.Certificate_185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4
example {A : Type uAtom} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 1))
    : (positiveSupportValues weight value).card ≤ 1 :=
  Astra.GeneratedSupport.Certificate_185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4.distinct_positive_support_bound weight value hw hv moment0 moment1

-- Exact namespace/certificate ID: Astra.GeneratedSupport.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7
example {A : Type uAtom} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 4))
    (moment2 : ∑ a, weight a * (value a)^3 = ((1 : ℝ) / 64))
    : (positiveSupportValues weight value).card ≤ 2 :=
  Astra.GeneratedSupport.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7.distinct_positive_support_bound weight value hw hv moment0 moment1 moment2

-- Exact namespace/certificate ID: Astra.GeneratedSupport.Certificate_8b27b817b1135ccc4377bba726845bf5466a7310028261eca750233afdd3f939
example {A : Type uAtom} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 2))
    (moment2 : ∑ a, weight a * (value a)^3 = ((1 : ℝ) / 8))
    (moment3 : ∑ a, weight a * (value a)^6 = ((1 : ℝ) / 64))
    (moment4 : ∑ a, weight a * (value a)^10 = ((1 : ℝ) / 1024))
    (moment5 : ∑ a, weight a * (value a)^15 = ((1 : ℝ) / 32768))
    (moment6 : ∑ a, weight a * (value a)^21 = ((1 : ℝ) / 2097152))
    (moment7 : ∑ a, weight a * (value a)^28 = ((1 : ℝ) / 268435456))
    : (positiveSupportValues weight value).card ≤ 7 :=
  Astra.GeneratedSupport.Certificate_8b27b817b1135ccc4377bba726845bf5466a7310028261eca750233afdd3f939.distinct_positive_support_bound weight value hw hv moment0 moment1 moment2 moment3 moment4 moment5 moment6 moment7

-- Exact namespace/certificate ID: Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b
example {A : Type uAtom} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 2))
    (moment2 : ∑ a, weight a * (value a)^3 = ((1 : ℝ) / 8))
    : (positiveSupportValues weight value).card ≤ 2 :=
  Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.distinct_positive_support_bound weight value hw hv moment0 moment1 moment2

-- Exact namespace/certificate ID: Astra.GeneratedSupport.Certificate_bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592
example {A : Type uAtom} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 2))
    (moment2 : ∑ a, weight a * (value a)^3 = ((1 : ℝ) / 8))
    (moment3 : ∑ a, weight a * (value a)^6 = ((1 : ℝ) / 64))
    : (positiveSupportValues weight value).card ≤ 3 :=
  Astra.GeneratedSupport.Certificate_bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592.distinct_positive_support_bound weight value hw hv moment0 moment1 moment2 moment3

-- Exact namespace/certificate ID: Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0
example {A : Type uAtom} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 1))
    (moment2 : ∑ a, weight a * (value a)^3 = ((1 : ℝ) / 1))
    : (positiveSupportValues weight value).card ≤ 2 :=
  Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.distinct_positive_support_bound weight value hw hv moment0 moment1 moment2

-- Exact namespace/certificate ID: Astra.GeneratedSupport.Certificate_fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766
example {A : Type uAtom} [Fintype A]
    (weight value : A → ℝ)
    (hw : ∀ a, 0 ≤ weight a)
    (hv : ∀ a, 0 < value a ∧ value a ≤ 1)
    (moment0 : ∑ a, weight a * (value a)^0 = ((1 : ℝ) / 1))
    (moment1 : ∑ a, weight a * (value a)^1 = ((1 : ℝ) / 1))
    (moment2 : ∑ a, weight a * (value a)^3 = ((1 : ℝ) / 1))
    : (positiveSupportValues weight value).card ≤ 2 :=
  Astra.GeneratedSupport.Certificate_fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766.distinct_positive_support_bound weight value hw hv moment0 moment1 moment2

end Astra.IntegrationInterfaceAudit.GeneratedSupport

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.notation false
set_option pp.proofs false

#print Astra.PositiveSupportAdapter.positiveSupportValues
#print DotG4.ActualObservableBankCertificate.sparsePolynomial
#print DotG4.ActualSparseCertificateExistence.momentLevels
#print Astra.GeneratedSupport.Certificate_185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4.coefficients
#check @Astra.GeneratedSupport.Certificate_185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4.levels_eq
#print axioms Astra.GeneratedSupport.Certificate_185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4.levels_eq
#check @Astra.GeneratedSupport.Certificate_185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4.polynomial_identity
#print axioms Astra.GeneratedSupport.Certificate_185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4.polynomial_identity
#check @Astra.GeneratedSupport.Certificate_185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4.distinct_positive_support_bound
#print axioms Astra.GeneratedSupport.Certificate_185368e637e607ab52266235a2a7b5deb7114ce499f48ab066a11089cd2895b4.distinct_positive_support_bound
#print Astra.GeneratedSupport.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7.coefficients
#check @Astra.GeneratedSupport.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7.levels_eq
#print axioms Astra.GeneratedSupport.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7.levels_eq
#check @Astra.GeneratedSupport.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7.polynomial_identity
#print axioms Astra.GeneratedSupport.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7.polynomial_identity
#check @Astra.GeneratedSupport.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7.distinct_positive_support_bound
#print axioms Astra.GeneratedSupport.Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7.distinct_positive_support_bound
#print Astra.GeneratedSupport.Certificate_8b27b817b1135ccc4377bba726845bf5466a7310028261eca750233afdd3f939.coefficients
#check @Astra.GeneratedSupport.Certificate_8b27b817b1135ccc4377bba726845bf5466a7310028261eca750233afdd3f939.levels_eq
#print axioms Astra.GeneratedSupport.Certificate_8b27b817b1135ccc4377bba726845bf5466a7310028261eca750233afdd3f939.levels_eq
#check @Astra.GeneratedSupport.Certificate_8b27b817b1135ccc4377bba726845bf5466a7310028261eca750233afdd3f939.polynomial_identity
#print axioms Astra.GeneratedSupport.Certificate_8b27b817b1135ccc4377bba726845bf5466a7310028261eca750233afdd3f939.polynomial_identity
#check @Astra.GeneratedSupport.Certificate_8b27b817b1135ccc4377bba726845bf5466a7310028261eca750233afdd3f939.distinct_positive_support_bound
#print axioms Astra.GeneratedSupport.Certificate_8b27b817b1135ccc4377bba726845bf5466a7310028261eca750233afdd3f939.distinct_positive_support_bound
#print Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.coefficients
#check @Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.levels_eq
#print axioms Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.levels_eq
#check @Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.polynomial_identity
#print axioms Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.polynomial_identity
#check @Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.distinct_positive_support_bound
#print axioms Astra.GeneratedSupport.Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.distinct_positive_support_bound
#print Astra.GeneratedSupport.Certificate_bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592.coefficients
#check @Astra.GeneratedSupport.Certificate_bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592.levels_eq
#print axioms Astra.GeneratedSupport.Certificate_bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592.levels_eq
#check @Astra.GeneratedSupport.Certificate_bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592.polynomial_identity
#print axioms Astra.GeneratedSupport.Certificate_bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592.polynomial_identity
#check @Astra.GeneratedSupport.Certificate_bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592.distinct_positive_support_bound
#print axioms Astra.GeneratedSupport.Certificate_bfb76cbdcc5acf6b4884ee8493fa0787541bb775738f6ae68ddf84543f7db592.distinct_positive_support_bound
#print Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.coefficients
#check @Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.levels_eq
#print axioms Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.levels_eq
#check @Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.polynomial_identity
#print axioms Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.polynomial_identity
#check @Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.distinct_positive_support_bound
#print axioms Astra.GeneratedSupport.Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.distinct_positive_support_bound
#print Astra.GeneratedSupport.Certificate_fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766.coefficients
#check @Astra.GeneratedSupport.Certificate_fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766.levels_eq
#print axioms Astra.GeneratedSupport.Certificate_fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766.levels_eq
#check @Astra.GeneratedSupport.Certificate_fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766.polynomial_identity
#print axioms Astra.GeneratedSupport.Certificate_fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766.polynomial_identity
#check @Astra.GeneratedSupport.Certificate_fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766.distinct_positive_support_bound
#print axioms Astra.GeneratedSupport.Certificate_fdc260acc4aa6969985fc37302a41182c845d6285ea8fe74d2fca8cc0dbe1766.distinct_positive_support_bound
