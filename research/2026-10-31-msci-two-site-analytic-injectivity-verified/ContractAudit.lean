import MSCi.TwoSite.BBRecoveryDraft
example : ∀ p q : MSCi.TwoSite.Parameters, MSCi.TwoSite.Admissible p → MSCi.TwoSite.Admissible q → MSCi.TwoSite.nineRawFeatures p = MSCi.TwoSite.nineRawFeatures q → p = q := @MSCi.TwoSite.nineRawFeatures_injective_on_admissible
#print axioms MSCi.TwoSite.nineRawFeatures_injective_on_admissible
