import BinaryCPTPolynomials
import Mathlib.Tactic.NormNum

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual rational CPTs for a finite binary fair/copy/XOR/zero subcircuit of
the ORIGINAL arrow relation. Unused parents and arrows are retained. The
strict rank only orients the chosen dependencies, not every original arrow.
The later active-path geometry must construct this circuit data and prove
the endpoint/conditioning constraints. No faithful model or nonzero CI
minor is a field, and this component is not a universal D2 theorem.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open scoped BigOperators

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]

inductive Gate (edge : V → V → Prop) (rank : V → Nat) (R : Type v) (vertex : V)
  | off
  | fair (index : R)
  | copy (parent : V) (allowed : edge parent vertex) (earlier : rank parent < rank vertex)
  | xor (left right : V) (allowLeft : edge left vertex) (allowRight : edge right vertex)
      (earlierLeft : rank left < rank vertex) (earlierRight : rank right < rank vertex)

structure BoundaryCircuit (edge : V → V → Prop) (R : Type v) where
  rank : V → Nat
  gate : (vertex : V) → Gate edge rank R vertex
  source : R → V
  source_gate : ∀ i, gate (source i) = .fair i
  fair_source : ∀ vertex i, gate vertex = .fair i → source i = vertex

namespace BoundaryCircuit

variable {edge : V → V → Prop} {R : Type v}

def value (c : BoundaryCircuit edge R) (bits : R → Bool) (vertex : V) : Bool :=
  match c.gate vertex with
  | .off => false
  | .fair i => bits i
  | .copy parent _ _ => value c bits parent
  | .xor left right _ _ _ _ => Bool.xor (value c bits left) (value c bits right)
termination_by c.rank vertex
decreasing_by
  all_goals simp_wf
  all_goals omega

def parameter (c : BoundaryCircuit edge R) : Coordinate edge → ℚ
  | ⟨vertex, parents⟩ =>
    match c.gate vertex with
    | .off => 0
    | .fair _ => 1 / 2
    | .copy parent allowed _ => if parents ⟨parent, allowed⟩ then 1 else 0
    | .xor left right allowLeft allowRight _ _ =>
        if Bool.xor (parents ⟨left, allowLeft⟩) (parents ⟨right, allowRight⟩) then 1 else 0

def rootBits (c : BoundaryCircuit edge R) (w : Assignment V) : R → Bool := fun i => w (c.source i)

def uniformFactor (c : BoundaryCircuit edge R) (vertex : V) : ℚ :=
  match c.gate vertex with
  | .fair _ => 1 / 2
  | _ => 1

def uniformMass (c : BoundaryCircuit edge R) : ℚ := ∏ vertex, c.uniformFactor vertex

theorem parameter_in_cube (c : BoundaryCircuit edge R) (i : Coordinate edge) :
    0 ≤ c.parameter i ∧ c.parameter i ≤ 1 := by
  obtain ⟨vertex, parents⟩ := i
  cases h : c.gate vertex with
  | off => norm_num [parameter, h]
  | fair index => norm_num [parameter, h]
  | copy parent allowed earlier =>
      cases parents ⟨parent, allowed⟩ <;> norm_num [parameter, h]
  | xor left right allowLeft allowRight earlierLeft earlierRight =>
      cases Bool.xor (parents ⟨left, allowLeft⟩) (parents ⟨right, allowRight⟩) <;>
        norm_num [parameter, h]

theorem value_at_source (c : BoundaryCircuit edge R) (bits : R → Bool) (i : R) :
    c.value bits (c.source i) = bits i := by
  rw [value, c.source_gate]

theorem rootBits_value (c : BoundaryCircuit edge R) (bits : R → Bool) :
    c.rootBits (c.value bits) = bits := by
  funext i
  exact c.value_at_source bits i

theorem value_injective (c : BoundaryCircuit edge R) : Function.Injective c.value := by
  intro first second equal
  have roots := congrArg c.rootBits equal
  simpa only [rootBits_value] using roots

/-- Every compatible assignment has the SAME positive product mass. No
cardinality calculation or probabilistic independence axiom is used here. -/
theorem factor_at_value (c : BoundaryCircuit edge R) (bits : R → Bool) (vertex : V) :
    bernoulliMass c.parameter (row edge (c.value bits) vertex) (c.value bits vertex) =
      c.uniformFactor vertex := by
  cases h : c.gate vertex with
  | off =>
      have output : c.value bits vertex = false := by rw [value, h]
      norm_num [parameter, row, h, bernoulliMass, output, uniformFactor]
  | fair index =>
      have output : c.value bits vertex = bits index := by rw [value, h]
      cases bits index <;> norm_num [parameter, row, h, bernoulliMass, output, uniformFactor]
  | copy parent allowed earlier =>
      have output : c.value bits vertex = c.value bits parent := by rw [value, h]
      cases c.value bits parent <;> norm_num [parameter, row, h, bernoulliMass, output, uniformFactor]
  | xor left right allowLeft allowRight earlierLeft earlierRight =>
      have output : c.value bits vertex = Bool.xor (c.value bits left) (c.value bits right) := by rw [value, h]
      cases c.value bits left <;> cases c.value bits right <;>
        norm_num [parameter, row, h, bernoulliMass, output, uniformFactor]

theorem joint_mass_value (c : BoundaryCircuit edge R) (bits : R → Bool) :
    jointMass edge c.parameter (c.value bits) = c.uniformMass := by
  apply Finset.prod_congr rfl
  intro vertex _
  exact c.factor_at_value bits vertex

theorem uniform_factor_pos (c : BoundaryCircuit edge R) (vertex : V) :
    0 < c.uniformFactor vertex := by
  cases h : c.gate vertex <;> norm_num [uniformFactor, h]

theorem uniform_mass_pos (c : BoundaryCircuit edge R) : 0 < c.uniformMass :=
  Finset.prod_pos (fun vertex _ => c.uniform_factor_pos vertex)

/-- A nonzero full product forces every deterministic equation. Induction
on the chosen dependency rank then reconstructs the unique fair-bit image.
All original parents remain in row; the kernels simply ignore unused ones. -/
theorem support_is_value (c : BoundaryCircuit edge R) (w : Assignment V)
    (nonzero : jointMass edge c.parameter w ≠ 0) : w = c.value (c.rootBits w) := by
  have factorNonzero : ∀ vertex, bernoulliMass c.parameter (row edge w vertex) (w vertex) ≠ 0 := by
    intro vertex
    exact (Finset.prod_ne_zero_iff.mp nonzero) vertex (Finset.mem_univ vertex)
  have reconstruct : ∀ n, ∀ vertex, c.rank vertex = n → w vertex = c.value (c.rootBits w) vertex := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro vertex rankEq
        have local := factorNonzero vertex
        cases h : c.gate vertex with
        | off =>
            have output : c.value (c.rootBits w) vertex = false := by rw [value, h]
            rw [output]
            cases bit : w vertex <;> simp [parameter, row, h, bernoulliMass, bit] at local ⊢
        | fair index =>
            rw [value, h]
            change w vertex = w (c.source index)
            rw [c.fair_source vertex index h]
        | copy parent allowed earlier =>
            have parentValue := ih (c.rank parent) (by omega) parent rfl
            have deterministic : w vertex = w parent := by
              cases own : w vertex <;> cases fromParent : w parent <;>
                simp [parameter, row, h, bernoulliMass, own, fromParent] at local ⊢
            rw [value, h]
            exact deterministic.trans parentValue
        | xor left right allowLeft allowRight earlierLeft earlierRight =>
            have leftValue := ih (c.rank left) (by omega) left rfl
            have rightValue := ih (c.rank right) (by omega) right rfl
            have deterministic : w vertex = Bool.xor (w left) (w right) := by
              cases own : w vertex <;> cases fromLeft : w left <;> cases fromRight : w right <;>
                simp [parameter, row, h, bernoulliMass, own, fromLeft, fromRight] at local ⊢
            rw [value, h, ← leftValue, ← rightValue]
            exact deterministic
  funext vertex
  exact reconstruct (c.rank vertex) vertex rfl

theorem joint_mass_eq_zero_unless_value (c : BoundaryCircuit edge R) (w : Assignment V)
    (incompatible : w ≠ c.value (c.rootBits w)) : jointMass edge c.parameter w = 0 := by
  by_contra nonzero
  exact incompatible (c.support_is_value w nonzero)

theorem joint_mass_value_iff (c : BoundaryCircuit edge R) (w : Assignment V) :
    jointMass edge c.parameter w ≠ 0 ↔ ∃ bits, w = c.value bits := by
  constructor
  · intro nonzero
    exact ⟨c.rootBits w, c.support_is_value w nonzero⟩
  · rintro ⟨bits, rfl⟩
    rw [c.joint_mass_value]
    exact ne_of_gt c.uniform_mass_pos

end BoundaryCircuit

end RestrictedCausal.ProbabilitySource.BinaryCPT
