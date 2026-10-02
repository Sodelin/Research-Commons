import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Choose

/-!
An elementary bounded-domain obstruction certificate for exact population blocks.
New verification contribution: Sol6.1 HG audit, 2026-10-01.
The set-intersection mechanism is classical; see Zhang--Yap (AAAI 2002,
Small Set Intersection) and Dechter--van Beek (Theorem 31).
This file proves the abstract support lemma, not the source-to-support premise
or stochastic calendar genealogy theorem.
-/

namespace GProgram.G5.BoundedSupport

variable {I P : Type*} [DecidableEq I] [DecidableEq P]

/-- With a finite anchor domain A, an unsatisfiable family of unary predicates
has a subfamily of at most |A| constraints witnessing unsatisfiability. -/
theorem bounded_unary_obstruction (A : Finset P) (B : Finset I)
    (R : I → P → Prop) (h : ¬ ∃ a ∈ A, ∀ i ∈ B, R i a) :
    ∃ U : Finset I, U ⊆ B ∧ U.card ≤ A.card ∧
      ¬ ∃ a ∈ A, ∀ i ∈ U, R i a := by
  classical
  have block : ∀ a : {a // a ∈ A}, ∃ i ∈ B, ¬ R i a := by
    intro a
    by_contra hn
    apply h
    refine ⟨a, a.property, ?_⟩
    intro i hi
    by_contra hr
    exact hn ⟨i, hi, hr⟩
  choose f hf hnot using block
  refine ⟨A.attach.image f, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
    exact hf a
  · exact (Finset.card_image_le).trans_eq Finset.card_attach
  · rintro ⟨a, ha, hR⟩
    exact hnot ⟨a, ha⟩ (hR (f ⟨a, ha⟩)
      (Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_attach _ _, rfl⟩))

/-- Existential exact-block support under Cartesian feasible position sets.
The predicate includes no inequalities among outsiders, because the prescribed
block's complement may itself have any partition. -/
def ExactBlock (S : I → Finset P) (B C : Finset I) : Prop :=
  ∃ a, ∀ i ∈ B, (i ∈ C → a ∈ S i) ∧
    (i ∉ C → ∃ b ∈ S i, b ≠ a)

/-- A failed nonempty exact block has an original-label obstruction on at most
k+1 labels. Only the chosen inside anchor needs a domain bound. -/
theorem exact_block_small_obstruction (S : I → Finset P) (B C : Finset I)
    (c : I) (hcB : c ∈ B) (hcC : c ∈ C) (k : Nat)
    (hcard : (S c).card ≤ k) (hfail : ¬ ExactBlock S B C) :
    ∃ U : Finset I, U ⊆ B ∧ c ∈ U ∧ U.card ≤ k+1 ∧
      ¬ ExactBlock S U C := by
  classical
  let R : I → P → Prop := fun i a =>
    (i ∈ C → a ∈ S i) ∧ (i ∉ C → ∃ b ∈ S i, b ≠ a)
  have h : ¬ ∃ a ∈ S c, ∀ i ∈ B, R i a := by
    rintro ⟨a, _, ha⟩
    exact hfail ⟨a, ha⟩
  obtain ⟨V, hVB, hVcard, hVfail⟩ := bounded_unary_obstruction (S c) B R h
  refine ⟨insert c V, ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · exact Finset.insert_subset hcB hVB
  · calc
      (insert c V).card ≤ V.card+1 := Finset.card_insert_le _ _
      _ ≤ k+1 := Nat.add_le_add_right (hVcard.trans hcard) 1
  · rintro ⟨a, ha⟩
    apply hVfail
    refine ⟨a, (ha c (Finset.mem_insert_self _ _)).1 hcC, ?_⟩
    intro i hi
    exact ha i (Finset.mem_insert_of_mem hi)

/-- Every nonempty prescribed Cartesian block is possible exactly when each
restriction to at most k+1 original labels is possible. The local expression
uses C as a predicate; on U it is exactly C ∩ U. -/
theorem exact_block_iff_local (S : I → Finset P) (B C : Finset I)
    (hCB : C ⊆ B) (hC : C.Nonempty) (k : Nat)
    (hcard : ∀ c ∈ C, (S c).card ≤ k) :
    ExactBlock S B C ↔
      ∀ U : Finset I, U ⊆ B → U.card ≤ k+1 →
        (U ∩ C).Nonempty → ExactBlock S U C := by
  classical
  constructor
  · rintro ⟨a, ha⟩ U hUB _ _
    exact ⟨a, fun i hi => ha i (hUB hi)⟩
  · intro hlocal
    by_contra hfail
    obtain ⟨c, hcC⟩ := hC
    obtain ⟨U, hUB, hcU, hUcard, hUfail⟩ :=
      exact_block_small_obstruction S B C c (hCB hcC) hcC k (hcard c hcC) hfail
    exact hUfail (hlocal U hUB hUcard ⟨c, Finset.mem_inter.mpr ⟨hcU, hcC⟩⟩)

#print axioms bounded_unary_obstruction
#print axioms exact_block_small_obstruction
#print axioms exact_block_iff_local

end GProgram.G5.BoundedSupport
