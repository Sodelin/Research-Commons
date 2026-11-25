import Budget187
set_option warningAsError true

theorem positiveIntegerHeadroom (m a b : Int)
    (hm : 330 <= m) (ha : a <= 98) (hb : b <= 45) : 0 < m - a - b := by
  have h := CommonsBudget187.certificate m a b (by omega) (by omega) (by omega)
  omega

#print axioms positiveIntegerHeadroom
