import Mathlib.Tactic

/-!
# Actual selector/occupancy interpretation for G5's fair two-position kernel

Contributor: dot, 2026-10-02. Theorems below hold for an arbitrary population
position type, not just a enumerated fixture. Each label has two actual route
positions. Their selector witness is proved equivalent to the block-count
predicate used by the hand Q theorem. No genealogy/Q equality is assumed.
The full six-moment absence criterion and original-source probability bridge
remain separate proof obligations.
-/
namespace GProgram.G5.QuartetKernel

variable {α : Type*} [DecidableEq α]

def blockCount (p : Fin 2 → α) (e : α) : Nat :=
  (if p 0 = e then 1 else 0) + (if p 1 = e then 1 else 0)

def pairCount (p q : Fin 2 → α) : Nat :=
  (if p 0 = q 0 then 1 else 0) + (if p 0 = q 1 then 1 else 0) +
  (if p 1 = q 0 then 1 else 0) + (if p 1 = q 1 then 1 else 0)

theorem blockCount_pos_iff (p : Fin 2 → α) (e : α) :
    0 < blockCount p e ↔ ∃ k : Fin 2, p k = e := by
  by_cases h0 : p 0 = e <;> by_cases h1 : p 1 = e
  · simp [blockCount, h0, h1]
  · constructor
    · intro _; exact ⟨0, h0⟩
    · intro _; simp [blockCount, h0, h1]
  · constructor
    · intro _; exact ⟨1, h1⟩
    · intro _; simp [blockCount, h0, h1]
  · simp only [blockCount, h0, h1, ↓reduceIte, Nat.add_zero, lt_self_iff_false,
      false_iff, not_exists]
    intro k
    fin_cases k
    · simpa using h0
    · simpa using h1

theorem blockCount_lt_two_iff (p : Fin 2 → α) (e : α) :
    blockCount p e < 2 ↔ ∃ k : Fin 2, p k ≠ e := by
  by_cases h0 : p 0 = e <;> by_cases h1 : p 1 = e
  · simp only [blockCount, h0, h1, ↓reduceIte, Nat.reduceAdd, lt_self_iff_false,
      false_iff, not_exists, not_not]
    intro k
    fin_cases k
    · simpa using h0
    · simpa using h1
  · constructor
    · intro _; exact ⟨1, h1⟩
    · intro _; simp [blockCount, h0, h1]
  · constructor
    · intro _; exact ⟨0, h0⟩
    · intro _; simp [blockCount, h0, h1]
  · constructor
    · intro _; exact ⟨0, h0⟩
    · intro _; simp [blockCount, h0, h1]

def selectorWitness (p : Fin 4 → Fin 2 → α) : Prop :=
  ∃ (ka kb kc kd : Fin 2),
    (p 0 ka = p 1 kb ∧ p 0 ka ≠ p 2 kc ∧ p 0 ka ≠ p 3 kd) ∨
    (p 2 kc = p 3 kd ∧ p 2 kc ≠ p 0 ka ∧ p 2 kc ≠ p 1 kb)

def blockWitness (p : Fin 4 → Fin 2 → α) : Prop :=
  ∃ e : α,
    (0 < blockCount (p 0) e ∧ 0 < blockCount (p 1) e ∧
      blockCount (p 2) e < 2 ∧ blockCount (p 3) e < 2) ∨
    (0 < blockCount (p 2) e ∧ 0 < blockCount (p 3) e ∧
      blockCount (p 0) e < 2 ∧ blockCount (p 1) e < 2)

theorem selectorWitness_iff_blockWitness (p : Fin 4 → Fin 2 → α) :
    selectorWitness p ↔ blockWitness p := by
  simp only [selectorWitness, blockWitness, blockCount_pos_iff,
    blockCount_lt_two_iff]
  constructor
  · rintro ⟨ka, kb, kc, kd, h | h⟩
    · refine ⟨p 0 ka, Or.inl ?_⟩
      exact ⟨⟨ka, rfl⟩, ⟨kb, h.1.symm⟩,
        ⟨kc, Ne.symm h.2.1⟩, ⟨kd, Ne.symm h.2.2⟩⟩
    · refine ⟨p 2 kc, Or.inr ?_⟩
      exact ⟨⟨kc, rfl⟩, ⟨kd, h.1.symm⟩,
        ⟨ka, Ne.symm h.2.1⟩, ⟨kb, Ne.symm h.2.2⟩⟩
  · rintro ⟨e, h | h⟩
    · rcases h with ⟨⟨ka, ha⟩, ⟨kb, hb⟩, ⟨kc, hc⟩, ⟨kd, hd⟩⟩
      refine ⟨ka, kb, kc, kd, Or.inl ?_⟩
      exact ⟨ha.trans hb.symm, by simpa [ha] using Ne.symm hc,
        by simpa [ha] using Ne.symm hd⟩
    · rcases h with ⟨⟨kc, hc⟩, ⟨kd, hd⟩, ⟨ka, ha⟩, ⟨kb, hb⟩⟩
      refine ⟨ka, kb, kc, kd, Or.inr ?_⟩
      exact ⟨hc.trans hd.symm, by simpa [hc] using Ne.symm ha,
        by simpa [hc] using Ne.symm hb⟩

theorem pairCount_four_iff (p q : Fin 2 → α) :
    pairCount p q = 4 ↔ p 0 = p 1 ∧ q 0 = q 1 ∧ p 0 = q 0 := by
  unfold pairCount
  split_ifs <;> simp_all <;> grind

theorem pairCount_one_split (p q : Fin 2 → α) (h : pairCount p q = 1) :
    p 0 ≠ p 1 ∧ q 0 ≠ q 1 := by
  unfold pairCount at h
  split_ifs at h <;> simp_all <;> grind

#print axioms selectorWitness_iff_blockWitness
#print axioms pairCount_four_iff
#print axioms pairCount_one_split
end GProgram.G5.QuartetKernel
