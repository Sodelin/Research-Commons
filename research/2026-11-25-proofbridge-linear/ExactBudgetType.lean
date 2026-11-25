import Budget187

-- The signed source coordinates, including zero coefficients, are explicit.
theorem exactBudgetType :
    ∀ (m a b : Int),
      (-1 : Int) * m + 0 * a + 0 * b ≤ -330 →
      (0 : Int) * m + 1 * a + 0 * b ≤ 98 →
      (0 : Int) * m + 0 * a + 1 * b ≤ 45 →
      (-1 : Int) * m + 1 * a + 1 * b ≤ -187 :=
  @CommonsBudget187.certificate

#print axioms exactBudgetType
