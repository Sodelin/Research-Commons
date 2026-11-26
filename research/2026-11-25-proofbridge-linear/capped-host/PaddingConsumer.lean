import CappedPaddingLanguage
open ResearchCommons.CappedPaddingLanguage

private def oneEdge (x y : Fin 2) : Option Unit :=
  if x.val = 0 ∧ y.val = 1 then some () else none

-- A two-vertex rank-bounded component can be added to any base.
theorem twoVertexUse {V : Type} (base : V → V → Option Unit) (word : Nat → Unit) :
    Realizes (joined base oneEdge) word ↔ Realizes base word := by
  apply padding_preserves base oneEdge Fin.val 1
  · intro x
    have hi := x.isLt
    omega
  · intro x y k h
    unfold oneEdge at h
    split at h
    · rename_i eqs
      omega
    · simp at h

-- One finite vertex with a loop adds an infinite word. Finiteness alone
-- is not a substitute for the increasing-rank hypothesis.
theorem finite_loop_control :
    Realizes (joined (fun (_ _ : Unit) => (none : Option Unit))
      (fun (_ _ : Unit) => some ())) (fun _ => ()) ∧
    ¬ Realizes (fun (_ _ : Unit) => (none : Option Unit)) (fun _ => ()) := by
  constructor
  · exact ⟨fun _ => Sum.inr (),fun _ => rfl⟩
  · intro h
    obtain ⟨f,step⟩ := h
    have h0 := step 0
    simp at h0

#print axioms twoVertexUse
#print axioms finite_loop_control
