import BinaryActivePathMinor
import Mathlib.Tactic.Ring

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Exact D3 sink-output relabeling on one original binary DAG. Complementing
the selected sink outputs changes their CPT parameters from theta to
1-theta and changes no parent row anywhere. The joint finite sums and CI
minor evaluations are transported by an explicit involution on COMPLETE
original assignments. This is a per-polynomial boundary witness map, not
the later one common positive parameter choice across regimes.

API read: mathlib 0df444a360eaa60ab8c11dca51a86af692955474,
Algebra/BigOperators/Group/Finset/Defs.lean,
blob 0acacafe6e597bbde7cd7e354b1c6d107d37bb59: Fintype.sum_bijective.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open scoped BigOperators
open SelectedWalk CanonicalSelection LatentRoots VertexActivePaths
open InducingSeparation OriginalProjection

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

def flipSinks (S : Finset V) (w : Assignment V) : Assignment V :=
  fun v => if v ∈ S then !(w v) else w v

theorem flipSinks_involutive (S : Finset V) (w : Assignment V) :
    flipSinks S (flipSinks S w) = w := by
  funext v
  by_cases member : v ∈ S
  · simp [flipSinks, member]
  · simp only [flipSinks, if_neg member]

theorem flipSinks_bijective (S : Finset V) : Function.Bijective (flipSinks S) := by
  constructor
  · intro «first» second same
    have twice := congrArg (flipSinks S) same
    simpa only [flipSinks_involutive] using twice
  · intro w
    exact ⟨flipSinks S w, flipSinks_involutive S w⟩

def complementSinkParameters (D : V → V → Prop) (S : Finset V)
    (θ : Coordinate D → ℚ) : Coordinate D → ℚ :=
  fun coordinate => if coordinate.1 ∈ S then 1 - θ coordinate else θ coordinate

theorem complement_parameters_in_cube (D : V → V → Prop) (S : Finset V)
    (θ : Coordinate D → ℚ) (cube : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) (i : Coordinate D) :
    0 ≤ complementSinkParameters D S θ i ∧ complementSinkParameters D S θ i ≤ 1 := by
  by_cases member : i.1 ∈ S
  · simp only [complementSinkParameters, if_pos member]
    exact ⟨sub_nonneg.mpr (cube i).2, sub_le_self 1 (cube i).1⟩
  · simpa only [complementSinkParameters, if_neg member] using cube i

theorem sink_flip_row (D : V → V → Prop) (S : Finset V)
    (sinks : ∀ s ∈ S, ∀ v, ¬ D s v) (w : Assignment V) (v : V) :
    row D (flipSinks S w) v = row D w v := by
  have parentValues : (fun p : {p // D p v} => flipSinks S w p.val) = (fun p => w p.val) := by
    funext p
    have outside : p.val ∉ S := fun member => sinks p.val member v p.property
    simp only [flipSinks, if_neg outside]
  exact congrArg (fun parents => (⟨v, parents⟩ : Coordinate D)) parentValues

theorem sink_flip_joint_mass (D : V → V → Prop) (S : Finset V)
    (sinks : ∀ s ∈ S, ∀ v, ¬ D s v) (θ : Coordinate D → ℚ) (w : Assignment V) :
    jointMass D (complementSinkParameters D S θ) (flipSinks S w) = jointMass D θ w := by
  apply Finset.prod_congr rfl
  intro v _
  rw [sink_flip_row D S sinks w v]
  by_cases member : v ∈ S
  · cases value : w v <;>
      simp [flipSinks, member, value, bernoulliMass, complementSinkParameters, row]
    all_goals ring
  · cases value : w v <;>
      simp [flipSinks, member, value, bernoulliMass, complementSinkParameters, row]

theorem matches_flipSinks (S C : Finset V) (c w : Assignment V) :
    Matches C (flipSinks S c) (flipSinks S w) ↔ Matches C c w := by
  constructor
  · intro matching v member
    have equation := matching v member
    by_cases selected : v ∈ S
    · cases atW : w v <;> cases atC : c v <;>
        simp [flipSinks, selected, atW, atC] at equation ⊢
    · simpa only [flipSinks, if_neg selected] using equation
  · intro matching v member
    unfold flipSinks
    rw [matching v member]

theorem sink_flip_cylinder_mass (D : V → V → Prop) (S : Finset V)
    (sinks : ∀ s ∈ S, ∀ v, ¬ D s v) (θ : Coordinate D → ℚ)
    (C : Finset V) (c : Assignment V) :
    cylinderMass D (complementSinkParameters D S θ) C (flipSinks S c) = cylinderMass D θ C c := by
  classical
  unfold cylinderMass
  symm
  apply Fintype.sum_bijective (flipSinks S) (flipSinks_bijective S)
  intro w
  rw [sink_flip_joint_mass D S sinks θ w]
  by_cases matching : Matches C c w
  · rw [if_pos matching, if_pos ((matches_flipSinks S C c w).mpr matching)]
  · rw [if_neg matching, if_neg (fun h => matching ((matches_flipSinks S C c w).mp h))]

theorem flip_cell_assignment (S : Finset V) (x y : V) (xOutside : x ∉ S) (yOutside : y ∉ S)
    (c : Assignment V) (a b : Bool) :
    flipSinks S (cellAssignment x y c a b) = cellAssignment x y (flipSinks S c) a b := by
  funext v
  by_cases atX : v = x
  · subst v
    simp only [flipSinks, if_neg xOutside, cellAssignment, if_pos rfl]
  · by_cases atY : v = y
    · subst v
      simp only [flipSinks, if_neg yOutside, cellAssignment, if_neg atX, if_pos rfl]
    · simp only [flipSinks, cellAssignment, if_neg atX, if_neg atY]

theorem sink_flip_cell_mass (D : V → V → Prop) (S : Finset V)
    (sinks : ∀ s ∈ S, ∀ v, ¬ D s v) (θ : Coordinate D → ℚ)
    (x y : V) (C : Finset V) (c : Assignment V) (a b : Bool)
    (xOutside : x ∉ S) (yOutside : y ∉ S) :
    cellMass D (complementSinkParameters D S θ) x y C (flipSinks S c) a b =
      cellMass D θ x y C c a b := by
  unfold cellMass
  rw [← flip_cell_assignment S x y xOutside yOutside c a b]
  exact sink_flip_cylinder_mass D S sinks θ _ _

theorem sink_flip_minor_eval (D : V → V → Prop) (S : Finset V)
    (sinks : ∀ s ∈ S, ∀ v, ¬ D s v) (θ : Coordinate D → ℚ)
    (x y : V) (C : Finset V) (c : Assignment V) (xOutside : x ∉ S) (yOutside : y ∉ S) :
    MvPolynomial.eval (complementSinkParameters D S θ)
      (minorPolynomial D x y C (flipSinks S c)) = MvPolynomial.eval θ (minorPolynomial D x y C c) := by
  rw [eval_minor, eval_minor]
  rw [sink_flip_cell_mass D S sinks θ x y C c false false xOutside yOutside,
    sink_flip_cell_mass D S sinks θ x y C c true true xOutside yOutside,
    sink_flip_cell_mass D S sinks θ x y C c false true xOutside yOutside,
    sink_flip_cell_mass D S sinks θ x y C c true false xOutside yOutside]

end RestrictedCausal.ProbabilitySource.BinaryCPT

namespace RestrictedCausal.ProbabilitySource

open SelectedWalk CanonicalSelection LatentRoots VertexActivePaths
open InducingSeparation OriginalProjection BinaryCPT

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

theorem BinaryWitnessGeometry.selected_sink_minor_witness (g : BinaryWitnessGeometry V)
    (S : Finset V) (selected : S ⊆ g.conditioned)
    (sinks : ∀ s ∈ S, ∀ v, ¬ g.arrow s v) :
    let θ := complementSinkParameters g.arrow S g.circuit.parameter
    (∀ i, 0 ≤ θ i ∧ θ i ≤ 1) ∧
      0 < MvPolynomial.eval θ
        (minorPolynomial g.arrow g.start g.finish g.conditioned (flipSinks S (fun _ => false))) := by
  dsimp only
  constructor
  · exact complement_parameters_in_cube g.arrow S g.circuit.parameter g.circuit.parameter_in_cube
  · have startOutside : g.start ∉ S := fun h => g.startOutside (selected h)
    have finishOutside : g.finish ∉ S := fun h => g.finishOutside (selected h)
    rw [sink_flip_minor_eval g.arrow S sinks g.circuit.parameter g.start g.finish g.conditioned
      (fun _ => false) startOutside finishOutside]
    rw [eval_minor,
      g.circuit.cell_mass_diagonal g.start g.finish g.conditioned (fun _ => false)
        g.distinct g.startOutside g.finishOutside g.constant_slice g.constant_endpoints false,
      g.circuit.cell_mass_diagonal g.start g.finish g.conditioned (fun _ => false)
        g.distinct g.startOutside g.finishOutside g.constant_slice g.constant_endpoints true,
      g.circuit.cell_mass_off_diagonal g.start g.finish g.conditioned (fun _ => false)
        g.distinct g.startOutside g.finishOutside g.constant_slice g.constant_endpoints false true (by decide),
      g.circuit.cell_mass_off_diagonal g.start g.finish g.conditioned (fun _ => false)
        g.distinct g.startOutside g.finishOutside g.constant_slice g.constant_endpoints true false (by decide)]
    simpa only [mul_zero, sub_zero] using mul_pos g.circuit.uniform_mass_pos g.circuit.uniform_mass_pos

/-- The displayed slice fixes every designated selection sink to one and
every other conditioning coordinate to zero. This theorem does not join
different regimes' parameter coordinates or choose a common positive
point. Its source carrier and all arrows are the original ones. -/
theorem binary_selected_sink_minor_nonzero
    (D : V → V → Prop) (acyclic : ∀ a xs, Route D a xs a → xs = [])
    (x y : V) (C S : Finset V) (selected : S ⊆ C)
    (sinks : ∀ s ∈ S, ∀ v, ¬ D s v)
    (different : x ≠ y) (xOutside : x ∉ C) (yOutside : y ∉ C)
    (connected : ActiveConnection (arrowGraph D) (fun v => v ∈ C) x y) :
    minorPolynomial D x y C (flipSinks S (fun _ => false)) ≠ 0 := by
  obtain ⟨vertices, minimal⟩ := exists_collider_minimal (arrowGraph D)
    (arrow_single_edges D acyclic) (fun v => v ∈ C) x y connected
  let geometry : BinaryWitnessGeometry V :=
    ⟨D, acyclic, C, x, y, different, xOutside, yOutside, vertices, minimal⟩
  have positive := (geometry.selected_sink_minor_witness S selected sinks).2
  intro zero
  rw [zero, map_zero] at positive
  exact (lt_irrefl (0 : ℚ)) positive

end RestrictedCausal.ProbabilitySource
