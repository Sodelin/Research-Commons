import Std

set_option warningAsError true

namespace ResearchCommons.TwoLiftTriangle

abbrev Vertex := Nat × Bool

/-- The short step keeps its sheet. The long step may switch sheets.
The first short step is absent in the two-root ladder. -/
def Up (twist : Nat → Bool) (u v : Vertex) : Prop :=
  (0 < u.1 ∧ v.1 = u.1 + 1 ∧ v.2 = u.2) ∨
  (v.1 = u.1 + 2 ∧ v.2 = Bool.xor u.2 (twist u.1))

/-- Every triangle, oriented by increasing levels, is one untwisted
length-two chord over two short steps in the same sheet. -/
theorem triangle_iff (twist : Nat → Bool) (u v w : Vertex) :
    (Up twist u v ∧ Up twist v w ∧ Up twist u w) ↔
      (0 < u.1 ∧ v.1 = u.1 + 1 ∧ w.1 = v.1 + 1 ∧
        v.2 = u.2 ∧ w.2 = v.2 ∧ twist u.1 = false) := by
  constructor
  · rintro ⟨huv, hvw, huw⟩
    change (_ ∨ _) at huv hvw huw
    obtain ⟨hp,hv,sv⟩ : 0 < u.1 ∧ v.1 = u.1 + 1 ∧ v.2 = u.2 := by
      rcases huv with ha | ⟨hl,_⟩
      · exact ha
      · rcases hvw with ⟨_,hb,_⟩ | ⟨hb,_⟩ <;>
          rcases huw with ⟨_,hc,_⟩ | ⟨hc,_⟩ <;> omega
    obtain ⟨hw,sw⟩ : w.1 = v.1 + 1 ∧ w.2 = v.2 := by
      rcases hvw with ⟨_,hw,sw⟩ | ⟨hl,_⟩
      · exact ⟨hw,sw⟩
      · rcases huw with ⟨_,hc,_⟩ | ⟨hc,_⟩ <;> omega
    have sx : w.2 = Bool.xor u.2 (twist u.1) := by
      rcases huw with ⟨_,hc,_⟩ | ⟨_,sx⟩
      · omega
      · exact sx
    refine ⟨hp,hv,hw,sv,sw,?_⟩
    rw [sw,sv] at sx
    cases h : twist u.1
    · rfl
    · rw [h] at sx
      cases hu : u.2
      · simp [hu] at sx
      · simp [hu] at sx
  · rintro ⟨hp,hv,hw,sv,sw,ht⟩
    refine ⟨Or.inl ⟨hp,hv,sv⟩,
      Or.inl ⟨by omega,hw,sw⟩,Or.inr ⟨by omega,?_⟩⟩
    rw [sw,sv,ht]
    cases u.2 <;> rfl

#print axioms triangle_iff
end ResearchCommons.TwoLiftTriangle
