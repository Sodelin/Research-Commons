import Lean

namespace ResearchCommons.HelperSwitch

/-- A positive and a negative requirement conflict only when both are present. -/
theorem eliminateRequirements (p n : Bool) :
    (∃ h : Bool, ((!p || h) && (!n || !h)) = true) ↔
      (!(p && n)) = true := by
  cases p <;> cases n <;> simp

/-- Any finite families of requirements, already evaluated on the remaining
assignment, may be combined without independence or degree hypotheses. -/
theorem eliminateFamilies (positives negatives : List Bool) :
    (∃ h : Bool,
      ((!(positives.any id) || h) && (!(negatives.any id) || !h)) = true) ↔
      (!((positives.any id) && (negatives.any id))) = true :=
  eliminateRequirements (positives.any id) (negatives.any id)

/-- Eliminating a Boolean helper preserves feasibility for each selector outcome,
without assuming a probability law for the selectors. Positive and negative clause
requirements can already include all selector bits. -/
theorem helperExists (p n₁ n₂ : Bool) :
    (∃ h : Bool, ((!p || h) && (!n₁ || !h) && (!n₂ || !h)) = true) ↔
      ((!p || !n₁) && (!p || !n₂)) = true := by
  cases p <;> cases n₁ <;> cases n₂ <;> simp

/-- The selected clauses are (h ∨ a), (¬h ∨ b), (¬h ∨ c).
The two residual clauses are selected by s∧t and s∧u, not independent bits. -/
theorem helperProjection (a b c s t u : Bool) :
    (∃ h : Bool,
      ((!s || (h || a)) && (!t || (!h || b)) && (!u || (!h || c))) = true) ↔
    ((!(s && t) || (a || b)) && (!(s && u) || (a || c))) = true := by
  cases a <;> cases b <;> cases c <;> cases s <;> cases t <;> cases u <;>
    simp

def bits : List Bool := [false, true]

def outcomes : List (Bool × Bool) :=
  bits.flatMap fun s => bits.flatMap fun t => bits.map fun u => (s && t, s && u)

def outcomeCounts : List Nat :=
  [(false, false), (true, false), (false, true), (true, true)].map
    fun value => (outcomes.filter (· == value)).length

/-- Counts among the eight equally likely selector triples. -/
theorem fairOutcomeCounts : outcomeCounts = [5, 1, 1, 1] := by decide

#print axioms eliminateRequirements
#print axioms eliminateFamilies
#print axioms helperExists
#print axioms helperProjection
#print axioms fairOutcomeCounts

end ResearchCommons.HelperSwitch
