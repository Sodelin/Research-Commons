import G1AcceptedNontrivialSplitTarget
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Permutation

/-! The accepted finite circular-order carrier: EVERY original taxon occurs
exactly once, and only rotation/reversal of that list are identified.
This is not a family of chosen source-network geometric embeddings. -/
namespace G1ExactCircularOrderCarrier
set_option backward.isDefEq.respectTransparency false
open scoped Classical
variable (X : Type*) [Fintype X]

def Representative := {labels : List X // labels.Nodup ∧ labels.toFinset = Finset.univ}

lemma representative_contains_every_taxon (r : Representative X) (x : X) : x ∈ r.val := by
  have h : x ∈ r.val.toFinset := by rw [r.property.2]; exact Finset.mem_univ _
  simpa using h

lemma representative_length (r : Representative X) : r.val.length = Fintype.card X := by
  have h := List.toFinset_card_of_nodup r.property.1
  rw [r.property.2,Finset.card_univ] at h
  exact h.symm

instance representativeFinite : Finite (Representative X) := by
  let allLists : Finset (List X) := (Finset.univ.toList.permutations).toFinset
  let encode (r : Representative X) : {labels : List X // labels ∈ allLists} := ⟨r.val,by
    apply List.mem_toFinset.mpr
    apply List.mem_permutations.mpr
    exact List.perm_of_nodup_nodup_toFinset_eq r.property.1 (Finset.nodup_toList _)
      (by simpa using r.property.2)⟩
  exact Finite.of_injective encode (by
    intro r s he
    apply Subtype.ext
    exact congrArg (fun v : {labels : List X // labels ∈ allLists} => v.val) he)

/-- Exact dihedral convention of the inherited source proof. -/
def SameCircle (r s : Representative X) : Prop :=
  List.IsRotated r.val s.val ∨ List.IsRotated r.val.reverse s.val

def circleSetoid : Setoid (Representative X) where
  r := SameCircle X
  iseqv := by
    refine ⟨?_,?_,?_⟩
    · intro r; exact Or.inl (List.IsRotated.refl _)
    · intro r s h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (by simpa using h.reverse.symm)
    · intro r s t hrs hst
      rcases hrs with hrs | hrs <;> rcases hst with hst | hst
      · exact Or.inl (hrs.trans hst)
      · exact Or.inr (hrs.reverse.trans hst)
      · exact Or.inr (hrs.trans hst)
      · exact Or.inl (by simpa using hrs.reverse.trans hst)

def TaxonCircle := Quotient (circleSetoid X)

instance circularOrderFinite : Finite (TaxonCircle X) := by
  unfold TaxonCircle
  infer_instance

noncomputable instance circularOrderFintype : Fintype (TaxonCircle X) := Fintype.ofFinite _

def circleOf (r : Representative X) : TaxonCircle X := Quotient.mk (circleSetoid X) r

theorem actual_circle_identity_iff (r s : Representative X) :
    circleOf X r = circleOf X s ↔
      List.IsRotated r.val s.val ∨ List.IsRotated r.val.reverse s.val :=
  Quotient.eq

#print axioms representativeFinite
#print axioms actual_circle_identity_iff
end G1ExactCircularOrderCarrier
