import G6RationalAffineWitness
import GParity.Affine

/-!
# The actual native solver's exact projection-cap precondition

Contributor: Codex / lean_reuse_recovery, 10 October 2026.
This characterizes answer versus UNKNOWN for the executable list algorithm.
It supplies no feasible/infeasible soundness by itself and no small complexity
bound. `requiredCap` computes every projection size along this finite matrix.
-/
namespace UnifiedLean.G6.WireAffineCapSemantics

def requiredCap : Nat → List GParity.Affine.Row → Nat
  | 0, _ => 0
  | n+1, rows => max (GParity.Affine.projectedSize rows)
      (requiredCap n (GParity.Affine.projectList n rows))

def Answered : GParity.Affine.Outcome → Prop
  | .sat _ => True
  | .unsat _ => True
  | .unknown _ _ _ => False

/-- This is an exact condition on the actual capped implementation; the
unbounded mathematical solver's totality is never silently used as a runtime
completeness premise. Row/vector well-formedness belongs to certificate
semantics and is not required merely to characterize the cap branch. -/
theorem solve_answered_iff (n : Nat) (rows : List GParity.Affine.Row) (cap : Nat) :
    Answered (GParity.Affine.solve n rows cap) ↔ requiredCap n rows ≤ cap := by
  induction n generalizing rows with
  | zero =>
    cases h : rows.find? (fun r => !(r.holds [])) <;>
      simp [GParity.Affine.solve, h, Answered, requiredCap]
  | succ n ih =>
    by_cases hcap : cap < GParity.Affine.projectedSize rows
    · have hn : ¬ requiredCap (n+1) rows ≤ cap := by
        intro h
        exact (not_le_of_gt hcap) (max_le_iff.mp h).1
      simp only [GParity.Affine.solve, if_pos hcap, Answered, hn]
    · have hsize : GParity.Affine.projectedSize rows ≤ cap := le_of_not_gt hcap
      have hrequired : requiredCap (n+1) rows ≤ cap ↔
          requiredCap n (GParity.Affine.projectList n rows) ≤ cap := by
        simp only [requiredCap, max_le_iff, hsize, true_and]
      rw [hrequired, ← ih (GParity.Affine.projectList n rows)]
      simp only [GParity.Affine.solve, if_neg hcap]
      cases GParity.Affine.solve n (GParity.Affine.projectList n rows) cap <;> rfl

theorem solve_not_unknown (n : Nat) (rows : List GParity.Affine.Row) (cap : Nat)
    (hcap : requiredCap n rows ≤ cap) (k required emittedCap : Nat) :
    GParity.Affine.solve n rows cap ≠ .unknown k required emittedCap := by
  intro h
  have ha := (solve_answered_iff n rows cap).mpr hcap
  rw [h] at ha
  exact ha

#print axioms solve_answered_iff
#print axioms solve_not_unknown

end UnifiedLean.G6.WireAffineCapSemantics
