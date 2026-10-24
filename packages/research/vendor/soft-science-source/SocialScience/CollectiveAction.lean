import Std

namespace SocialScience.CollectiveAction

/-- Every required task has a capable member. Congestion and time are omitted. -/
def Feasible {Agent Task : Type} (canDo : Agent → Task → Prop)
    (group : Agent → Prop) : Prop := ∀ task, ∃ agent, group agent ∧ canDo agent task

/-- Individual participation constraints relative to a zero outside option. -/
def Accepts {Agent : Type} (cost reward : Agent → Int) (group : Agent → Prop) : Prop :=
  ∀ agent, group agent → cost agent ≤ reward agent

def Ready {Agent Task : Type} (canDo : Agent → Task → Prop)
    (cost reward : Agent → Int) (group : Agent → Prop) : Prop :=
  Feasible canDo group ∧ Accepts cost reward group

theorem adding_members_preserves_feasibility {Agent Task : Type}
    {canDo : Agent → Task → Prop} {small large : Agent → Prop}
    (included : ∀ agent, small agent → large agent) (h : Feasible canDo small) :
    Feasible canDo large := by
  intro task
  rcases h task with ⟨agent, member, capable⟩
  exact ⟨agent, included agent member, capable⟩

theorem restricting_members_preserves_acceptance {Agent : Type}
    {cost reward : Agent → Int} {small large : Agent → Prop}
    (included : ∀ agent, small agent → large agent) (h : Accepts cost reward large) :
    Accepts cost reward small := fun agent member => h agent (included agent member)

theorem union_accepts_iff {Agent : Type} (cost reward : Agent → Int)
    (first second : Agent → Prop) :
    Accepts cost reward (fun a => first a ∨ second a) ↔
      Accepts cost reward first ∧ Accepts cost reward second := by
  constructor
  · intro h
    exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  · rintro ⟨hf, hs⟩ a (ha | ha)
    · exact hf a ha
    · exact hs a ha

theorem indispensable_member_withdrawal {Agent Task : Type}
    (canDo : Agent → Task → Prop) (group : Agent → Prop) (agent : Agent) (task : Task)
    (unique : ∀ other, group other → canDo other task → other = agent) :
    ¬ Feasible canDo (fun other => group other ∧ other ≠ agent) := by
  intro h
  rcases h task with ⟨other, ⟨member, distinct⟩, capable⟩
  exact distinct (unique other member capable)

/-- A two-role economy: each agent can perform precisely their own role. -/
def specialist (agent task : Bool) : Prop := agent = task

theorem complementary_pair_feasible : Feasible specialist (fun _ => True) := by
  intro task
  exact ⟨task, trivial, rfl⟩

theorem no_specialist_alone_feasible (agent : Bool) :
    ¬ Feasible specialist (fun other => other = agent) := by
  intro h
  cases agent with
  | false =>
    rcases h true with ⟨other, member, capable⟩
    simp [specialist, member] at capable
  | true =>
    rcases h false with ⟨other, member, capable⟩
    simp [specialist, member] at capable

def unitCost (_ : Bool) : Int := 1
def unequalReward (agent : Bool) : Int := if agent then 3 else 0
def repairedReward (agent : Bool) : Int := if agent then 2 else 1

/-- Positive aggregate surplus does not entail individual willingness. -/
theorem aggregate_surplus_not_participation :
    unitCost false + unitCost true < unequalReward false + unequalReward true ∧
    ¬ Ready specialist unitCost unequalReward (fun _ => True) := by
  constructor
  · decide
  · intro h
    have bad := h.2 false trivial
    simp [unitCost, unequalReward] at bad

theorem repaired_allocation_ready :
    Ready specialist unitCost repairedReward (fun _ => True) := by
  refine ⟨complementary_pair_feasible, ?_⟩
  intro agent _
  cases agent <;> decide

/-- Exact feasible-transfer condition; transfers are unrestricted integers. -/
theorem two_person_budget_iff (costA costB budget : Int) :
    (∃ share : Int, costA ≤ share ∧ costB ≤ budget - share) ↔ costA + costB ≤ budget := by
  constructor
  · rintro ⟨share, first, second⟩
    omega
  · intro h
    exact ⟨costA, by omega, by omega⟩

theorem acceptable_share_interval (costA costB budget share : Int) :
    (costA ≤ share ∧ costB ≤ budget - share) ↔
      (costA ≤ share ∧ share ≤ budget - costB) := by omega

end SocialScience.CollectiveAction
