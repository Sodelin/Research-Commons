import Std

/-! Elementary results separating network reach, membership, and incentives.
These are model implications, not empirical or normative conclusions.
Only Lean's bundled standard library is needed. -/
namespace Solidarity

def Adj (a b : Nat) : Prop := b = a + 1 ∨ a = b + 1

inductive Reach : Nat → Nat → Prop where
  | refl (a : Nat) : Reach a a
  | step {a b c : Nat} : Reach a b → Adj b c → Reach a c

theorem adj_symm {a b : Nat} (h : Adj a b) : Adj b a := Or.symm h

theorem reach_trans {a b c : Nat} (h : Reach a b) (g : Reach b c) : Reach a c := by
  induction g with
  | refl => exact h
  | step _ edge ih => exact Reach.step ih edge

theorem reach_symm {a b : Nat} (h : Reach a b) : Reach b a := by
  induction h with
  | refl => exact Reach.refl _
  | step _ edge ih =>
    exact reach_trans (Reach.step (Reach.refl _) (adj_symm edge)) ih

theorem zero_reaches (n : Nat) : Reach 0 n := by
  induction n with
  | zero => exact Reach.refl 0
  | succ n ih => exact Reach.step ih (Or.inl rfl)

theorem path_connected (a b : Nat) : Reach a b :=
  reach_trans (reach_symm (zero_reaches a)) (zero_reaches b)

/-- Each vertex's neighbors are contained in a set of at most two vertices. -/
theorem at_most_two_neighbors (a b : Nat) (h : Adj a b) :
    b = a + 1 ∨ b = a - 1 := by
  rcases h with h | h
  · exact Or.inl h
  · right; omega

/-- Arbitrarily many distinct vertices remain reachable with this degree bound. -/
theorem unbounded_reachable (bound : Nat) :
    ∃ n, bound < n ∧ Reach 0 n :=
  ⟨bound + 1, Nat.lt_succ_self bound, zero_reaches (bound + 1)⟩

def Included {α : Type} (localGroup largerGroup : α → Prop) : Prop :=
  ∀ x, localGroup x → largerGroup x

theorem membership_nesting {α : Type} {a b c : α → Prop}
    (ab : Included a b) (bc : Included b c) : Included a c :=
  fun x hx => bc x (ab x hx)

/-- Overlap, A-only, and B-only witnesses inside one common population. -/
theorem overlapping_memberships :
    ∃ (a b common : Nat → Prop),
      Included a common ∧ Included b common ∧
      (∃ x, a x ∧ b x) ∧ (∃ x, a x ∧ ¬ b x) ∧ (∃ x, b x ∧ ¬ a x) := by
  refine ⟨(fun n => n = 0 ∨ n = 1), (fun n => n = 0 ∨ n = 2),
    (fun _ => True), ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _; trivial
  · intro _ _; trivial
  · exact ⟨0, Or.inl rfl, Or.inl rfl⟩
  · refine ⟨1, Or.inr rfl, ?_⟩; omega
  · refine ⟨2, Or.inr rfl, ?_⟩; omega

/-- Connectedness places no constraint on an independent trust relation. -/
theorem connected_without_trust :
    ∃ trust : Nat → Nat → Prop,
      (∀ a b, Reach a b) ∧ ¬ trust 0 1 := by
  exact ⟨(fun _ _ => False), path_connected, fun h => h⟩

/- A two-player donation game. True = contribute, false = defect.
Benefit accrues from the other's contribution. Each contributor pays cost.
A reliable external institution charges sanction to each defector.
Payoffs are integer tokens. Institution financing and legitimacy are omitted. -/
def payoff (benefit cost sanction : Int) (own other : Bool) : Int :=
  (if other then benefit else 0) - (if own then cost else sanction)

def StableCC (benefit cost sanction : Int) : Prop :=
  ∀ deviation : Bool,
    payoff benefit cost sanction deviation true ≤ payoff benefit cost sanction true true

/-- Exact condition for mutual contribution to resist unilateral deviation. -/
theorem cooperation_stable_iff (benefit cost sanction : Int) :
    StableCC benefit cost sanction ↔ cost ≤ sanction := by
  constructor
  · intro h
    have hfalse := h false
    simp [payoff] at hfalse
    omega
  · intro h deviation
    cases deviation <;> simp [payoff] <;> omega

theorem no_sanction_failure (benefit cost : Int) (positive : 0 < cost) :
    ¬ StableCC benefit cost 0 := by
  intro h
  have hc := (cooperation_stable_iff benefit cost 0).mp h
  omega

/-- Attribute labels play no payoff role in this specified model. -/
theorem heterogeneous_cooperation_exists :
    ∃ labels : Bool → Bool,
      labels false ≠ labels true ∧ StableCC 3 1 2 := by
  refine ⟨id, by decide, ?_⟩
  exact (cooperation_stable_iff 3 1 2).mpr (by decide)

theorem homogeneous_cooperation_can_fail :
    ∃ labels : Bool → Bool,
      labels false = labels true ∧ ¬ StableCC 3 1 0 := by
  exact ⟨(fun _ => false), rfl, no_sanction_failure 3 1 (by decide)⟩

/-- Same symbols cannot change stability when they do not enter the payoffs. -/
theorem symbols_alone_insufficient :
    ∃ marker : Bool → Nat,
      marker false = marker true ∧ ¬ StableCC 3 1 0 := by
  exact ⟨(fun _ => 7), rfl, no_sanction_failure 3 1 (by decide)⟩

/-- Mutual contribution also improves on mutual defection when this holds. -/
theorem mutual_gain (benefit cost sanction : Int) (h : cost < benefit + sanction) :
    payoff benefit cost sanction false false < payoff benefit cost sanction true true := by
  simp [payoff]
  omega

#print axioms path_connected
#print axioms at_most_two_neighbors
#print axioms unbounded_reachable
#print axioms membership_nesting
#print axioms overlapping_memberships
#print axioms connected_without_trust
#print axioms cooperation_stable_iff
#print axioms heterogeneous_cooperation_exists
#print axioms homogeneous_cooperation_can_fail
#print axioms symbols_alone_insufficient
#print axioms mutual_gain
end Solidarity
