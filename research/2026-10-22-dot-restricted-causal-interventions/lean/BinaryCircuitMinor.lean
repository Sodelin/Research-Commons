import BinaryBoundaryCircuit

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Compute the ACTUAL finite CPT sums on a two-constant-bit conditioning
slice, using the circuit's proved positive support and uniform product
mass. This is a physical-to-polynomial calculation, not an assumed minor
or faithfulness interface. The active-path/trek construction must still
supply the circuit and the explicit endpoint/slice equations below.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open scoped BigOperators

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem matches_cell_iff (x y : V) (C : Finset V) (selected w : Assignment V)
    (a b : Bool) (different : x ≠ y) (xOutside : x ∉ C) (yOutside : y ∉ C) :
    Matches (insert x (insert y C)) (cellAssignment x y selected a b) w ↔
      w x = a ∧ w y = b ∧ Matches C selected w := by
  constructor
  · intro matching
    refine ⟨?_, ?_, ?_⟩
    · simpa only [cellAssignment, if_pos rfl] using matching x (Finset.mem_insert_self _ _)
    · have member : y ∈ insert x (insert y C) := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      simpa only [cellAssignment, if_neg different.symm, if_pos rfl] using matching y member
    · intro vertex member
      have notX : vertex ≠ x := by intro equal; subst vertex; exact xOutside member
      have notY : vertex ≠ y := by intro equal; subst vertex; exact yOutside member
      simpa only [cellAssignment, if_neg notX, if_neg notY] using
        matching vertex (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem member))
  · rintro ⟨atX, atY, rest⟩ vertex member
    rcases Finset.mem_insert.mp member with at | member
    · subst vertex; simpa only [cellAssignment, if_pos rfl] using atX
    · rcases Finset.mem_insert.mp member with at | member
      · subst vertex; simpa only [cellAssignment, if_neg different.symm, if_pos rfl] using atY
      · have notX : vertex ≠ x := by intro equal; subst vertex; exact xOutside member
        have notY : vertex ≠ y := by intro equal; subst vertex; exact yOutside member
        simpa only [cellAssignment, if_neg notX, if_neg notY] using rest vertex member

namespace BoundaryCircuit

variable {edge : V → V → Prop} {R : Type v}

/-- A nonzero contribution to a cell must be one of the two explicit
constant-bit images. Its endpoint values select which image it is. -/
theorem compatible_cell_is_constant (c : BoundaryCircuit edge R)
    (x y : V) (C : Finset V) (selected : Assignment V)
    (different : x ≠ y) (xOutside : x ∉ C) (yOutside : y ∉ C)
    (slice : ∀ bits, Matches C selected (c.value bits) ↔
      bits = (fun _ => false) ∨ bits = (fun _ => true))
    (endpoints : ∀ t, c.value (fun _ => t) x = t ∧ c.value (fun _ => t) y = t)
    (a b : Bool) (w : Assignment V)
    (matching : Matches (insert x (insert y C)) (cellAssignment x y selected a b) w)
    (nonzero : jointMass edge c.parameter w ≠ 0) :
    a = b ∧ w = c.value (fun _ => a) := by
  obtain ⟨atX, atY, onC⟩ := (matches_cell_iff x y C selected w a b different xOutside yOutside).mp matching
  have form := c.support_is_value w nonzero
  have selectedBits : Matches C selected (c.value (c.rootBits w)) := by rw [← form]; exact onC
  rcases (slice (c.rootBits w)).mp selectedBits with allFalse | allTrue
  · have wFalse : w = c.value (fun _ => false) := by rw [form, allFalse]
    have aFalse : a = false := atX.symm.trans (by rw [wFalse]; exact (endpoints false).1)
    have bFalse : b = false := atY.symm.trans (by rw [wFalse]; exact (endpoints false).2)
    exact ⟨aFalse.trans bFalse.symm, by simpa only [aFalse] using wFalse⟩
  · have wTrue : w = c.value (fun _ => true) := by rw [form, allTrue]
    have aTrue : a = true := atX.symm.trans (by rw [wTrue]; exact (endpoints true).1)
    have bTrue : b = true := atY.symm.trans (by rw [wTrue]; exact (endpoints true).2)
    exact ⟨aTrue.trans bTrue.symm, by simpa only [aTrue] using wTrue⟩

theorem cell_mass_diagonal (c : BoundaryCircuit edge R)
    (x y : V) (C : Finset V) (selected : Assignment V)
    (different : x ≠ y) (xOutside : x ∉ C) (yOutside : y ∉ C)
    (slice : ∀ bits, Matches C selected (c.value bits) ↔
      bits = (fun _ => false) ∨ bits = (fun _ => true))
    (endpoints : ∀ t, c.value (fun _ => t) x = t ∧ c.value (fun _ => t) y = t)
    (a : Bool) : cellMass edge c.parameter x y C selected a a = c.uniformMass := by
  classical
  let witness : Assignment V := c.value (fun _ => a)
  have onC : Matches C selected witness := by
    apply (slice (fun _ => a)).mpr
    cases a with
    | false => exact Or.inl rfl
    | true => exact Or.inr rfl
  have matching : Matches (insert x (insert y C)) (cellAssignment x y selected a a) witness :=
    (matches_cell_iff x y C selected witness a a different xOutside yOutside).mpr
      ⟨(endpoints a).1, (endpoints a).2, onC⟩
  unfold cellMass cylinderMass
  rw [Finset.sum_eq_single witness]
  · rw [if_pos matching]
    exact c.joint_mass_value (fun _ => a)
  · intro w member notWitness
    by_cases matchW : Matches (insert x (insert y C)) (cellAssignment x y selected a a) w
    · rw [if_pos matchW]
      by_contra nonzero
      have unique := (c.compatible_cell_is_constant x y C selected different xOutside yOutside
        slice endpoints a a w matchW nonzero).2
      exact notWitness unique
    · exact if_neg matchW
  · intro impossible
    exact (impossible (Finset.mem_univ witness)).elim

theorem cell_mass_off_diagonal (c : BoundaryCircuit edge R)
    (x y : V) (C : Finset V) (selected : Assignment V)
    (different : x ≠ y) (xOutside : x ∉ C) (yOutside : y ∉ C)
    (slice : ∀ bits, Matches C selected (c.value bits) ↔
      bits = (fun _ => false) ∨ bits = (fun _ => true))
    (endpoints : ∀ t, c.value (fun _ => t) x = t ∧ c.value (fun _ => t) y = t)
    (a b : Bool) (unequal : a ≠ b) : cellMass edge c.parameter x y C selected a b = 0 := by
  classical
  unfold cellMass cylinderMass
  apply Finset.sum_eq_zero
  intro w member
  by_cases matching : Matches (insert x (insert y C)) (cellAssignment x y selected a b) w
  · rw [if_pos matching]
    by_contra nonzero
    exact unequal (c.compatible_cell_is_constant x y C selected different xOutside yOutside
      slice endpoints a b w matching nonzero).1
  · exact if_neg matching

/-- The conclusion is the actual rational-coefficient CPT minor, not a
new summary target. Its circuit/slice premises still need the graph proof. -/
theorem minor_ne_zero_of_constant_slice (c : BoundaryCircuit edge R)
    (x y : V) (C : Finset V) (selected : Assignment V)
    (different : x ≠ y) (xOutside : x ∉ C) (yOutside : y ∉ C)
    (slice : ∀ bits, Matches C selected (c.value bits) ↔
      bits = (fun _ => false) ∨ bits = (fun _ => true))
    (endpoints : ∀ t, c.value (fun _ => t) x = t ∧ c.value (fun _ => t) y = t) :
    minorPolynomial edge x y C selected ≠ 0 := by
  intro zeroPolynomial
  have evalZero := congrArg (MvPolynomial.eval c.parameter) zeroPolynomial
  rw [eval_minor, map_zero,
    c.cell_mass_diagonal x y C selected different xOutside yOutside slice endpoints false,
    c.cell_mass_diagonal x y C selected different xOutside yOutside slice endpoints true,
    c.cell_mass_off_diagonal x y C selected different xOutside yOutside slice endpoints false true (by decide),
    c.cell_mass_off_diagonal x y C selected different xOutside yOutside slice endpoints true false (by decide)] at evalZero
  have positive := mul_pos c.uniform_mass_pos c.uniform_mass_pos
  simp only [mul_zero, sub_zero] at evalZero
  exact (ne_of_gt positive) evalZero

end BoundaryCircuit

end RestrictedCausal.ProbabilitySource.BinaryCPT
