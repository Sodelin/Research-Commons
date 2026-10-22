import G7EffectivePopulationCoefficients

/-!
Contributor: dot, 2026-10-22. UNELABORATED SOURCE PROPOSAL.
Owner equivalence for equal full selected genealogies. Leaves are NOT relabelled.
The accompanying hand proof supplies the separate native algorithm alignment.
-/
namespace Dot.NativeOwnerEquivalence
open GProgram.SourceForest

variable {V E Copy : Type*} [DecidableEq Copy] [Fintype Copy]

abbrev Owner (s : State V E Copy) := {a : Copy // a ∈ s.live}

/-- The representative of x in s and x itself have the same representative in t.
This follows from actual leaf fibres, not from an assumed owner permutation. -/
theorem ancestor_factor
    (s t : State V E Copy) (hs : Valid s) (ht : Valid t)
    (h : ∀ x, s.genealogy (s.ancestor x) = t.genealogy (t.ancestor x))
    (x : Copy) : t.ancestor (s.ancestor x) = t.ancestor x := by
  have ha := hs.ancestor_live x
  have hself : s.ancestor x ∈ (s.genealogy (s.ancestor x)).leaves :=
    (hs.leaf_fiber _ ha _).mpr (hs.representative _ ha)
  rw [h x] at hself
  exact (ht.leaf_fiber _ (ht.ancestor_live x) _).mp hself

/-- Equal selected trees canonically pair CURRENT owners while keeping the
original Copy carrier and every ordered tree leaf fixed. -/
def ownerEquiv
    (s t : State V E Copy) (hs : Valid s) (ht : Valid t)
    (h : ∀ x, s.genealogy (s.ancestor x) = t.genealogy (t.ancestor x)) :
    Owner s ≃ Owner t where
  toFun a := ⟨t.ancestor a.val, ht.ancestor_live a.val⟩
  invFun b := ⟨s.ancestor b.val, hs.ancestor_live b.val⟩
  left_inv a := by
    apply Subtype.ext
    exact (ancestor_factor t s ht hs (fun x => (h x).symm) a.val).trans
      (hs.representative a.val a.property)
  right_inv b := by
    apply Subtype.ext
    exact (ancestor_factor s t hs ht h b.val).trans
      (ht.representative b.val b.property)

theorem owner_genealogy
    (s t : State V E Copy) (hs : Valid s) (ht : Valid t)
    (h : ∀ x, s.genealogy (s.ancestor x) = t.genealogy (t.ancestor x))
    (a : Owner s) :
    s.genealogy a.val = t.genealogy (ownerEquiv s t hs ht h a).val := by
  have hh := h a.val
  rw [hs.representative a.val a.property] at hh
  exact hh

theorem owner_population
    (s t : State V E Copy) (hs : Valid s) (ht : Valid t)
    (h : ∀ x, s.genealogy (s.ancestor x) = t.genealogy (t.ancestor x))
    (hp : ∀ x, copyLocation s x = copyLocation t x)
    (a : Owner s) :
    s.location a.val = t.location (ownerEquiv s t hs ht h a).val := by
  have hh := hp a.val
  unfold copyLocation at hh
  rw [hs.representative a.val a.property] at hh
  exact hh

end Dot.NativeOwnerEquivalence
