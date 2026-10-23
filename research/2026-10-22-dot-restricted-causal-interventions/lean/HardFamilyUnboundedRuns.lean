import HardFamilyExactGame
import Mathlib.Data.Nat.Find

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY UNELABORATED CANDIDATE. No execution.

Actual possibly nonterminating adaptive policies. A stopped state is
absorbing and keeps its executed history. No uniform horizon, finite seed
space, or almost-sure termination is assumed in these pathwise proofs.
-/

namespace RestrictedCausal.HardFamily

open PartialQueries ProbabilitySource FiniteTargetImage TranscriptDecoder
open GProgram.G7.ExactLawResourceGame

universe uS uA uQ

structure RunState (A : Type uA) (Q : Type uQ) where
  history : History A Bool
  output : Option Q

/-- `none` is silent divergence: no next query and no terminal answer.
It is counted as failure without artificially charging extra queries. -/
abbrev Policy (A : Type uA) (Q : Type uQ) := History A Bool → Option (Sum Q A)

def advance {S : Type uS} {A : Type uA} {Q : Type uQ}
    (E : Experiment S A Bool Q Nat) (policy : Policy A Q) (source : S)
    (state : RunState A Q) : RunState A Q :=
  match state.output with
  | some _ => state
  | none => match policy state.history with
    | none => state
    | some (.inl q) => ⟨state.history, some q⟩
    | some (.inr action) => ⟨(action, E.response source action) :: state.history, none⟩

def policyState {S : Type uS} {A : Type uA} {Q : Type uQ}
    (E : Experiment S A Bool Q Nat) (policy : Policy A Q) (source : S) : Nat → RunState A Q
  | 0 => ⟨[], none⟩
  | n + 1 => advance E policy source (policyState E policy source n)

theorem advance_retains {S : Type uS} {A : Type uA} {Q : Type uQ}
    (E : Experiment S A Bool Q Nat) (policy : Policy A Q) (source : S)
    (state : RunState A Q) (row : A × Bool) (member : row ∈ state.history) :
    row ∈ (advance E policy source state).history := by
  cases output : state.output with
  | some q => simpa only [advance, output] using member
  | none =>
      cases decision : policy state.history with
      | none => simpa only [advance, output, decision] using member
      | some choice => cases choice with
        | inl q => simpa only [advance, output, decision] using member
        | inr a => simpa only [advance, output, decision] using List.mem_cons_of_mem (a, E.response source a) member

theorem policy_history_retains {S : Type uS} {A : Type uA} {Q : Type uQ}
    (E : Experiment S A Bool Q Nat) (policy : Policy A Q) (source : S)
    (m n : Nat) (le : m ≤ n) (row : A × Bool)
    (member : row ∈ (policyState E policy source m).history) :
    row ∈ (policyState E policy source n).history := by
  revert le
  induction n with
  | zero => intro le; have same : m = 0 := by omega; simpa only [same] using member
  | succ n ih =>
      intro le
      by_cases equal : m = n + 1
      · simpa only [equal] using member
      · have earlier : m ≤ n := by omega
        exact advance_retains E policy source _ row (ih earlier)

theorem advance_output_fixed {S : Type uS} {A : Type uA} {Q : Type uQ}
    (E : Experiment S A Bool Q Nat) (policy : Policy A Q) (source : S)
    (state : RunState A Q) (q : Q) (stopped : state.output = some q) :
    advance E policy source state = state := by simp only [advance, stopped]

theorem policy_output_persists {S : Type uS} {A : Type uA} {Q : Type uQ}
    (E : Experiment S A Bool Q Nat) (policy : Policy A Q) (source : S)
    (m n : Nat) (le : m ≤ n) (q : Q)
    (stopped : (policyState E policy source m).output = some q) :
    (policyState E policy source n).output = some q := by
  revert le
  induction n with
  | zero => intro le; have same : m = 0 := by omega; simpa only [same] using stopped
  | succ n ih =>
      intro le
      by_cases equal : m = n + 1
      · simpa only [equal] using stopped
      · have earlier : m ≤ n := by omega
        have fixed := advance_output_fixed E policy source _ q (ih earlier)
        change (advance E policy source (policyState E policy source n)).output = some q
        rw [fixed]
        exact ih earlier

theorem policy_output_unique {S : Type uS} {A : Type uA} {Q : Type uQ}
    (E : Experiment S A Bool Q Nat) (policy : Policy A Q) (source : S)
    (m n : Nat) (q r : Q)
    («first» : (policyState E policy source m).output = some q)
    (second : (policyState E policy source n).output = some r) : q = r := by
  rcases le_total m n with before | after
  · exact Option.some.inj ((policy_output_persists E policy source m n before q «first»).symm.trans second)
  · exact Option.some.inj («first».symm.trans (policy_output_persists E policy source n m after r second))

def PolicyError {S : Type uS} {A : Type uA} {Q : Type uQ}
    (E : Experiment S A Bool Q Nat) (policy : Policy A Q) (source : S) : Prop :=
  ¬ ∃ n, (policyState E policy source n).output = some (E.target source)

def EverTests {k u : Nat} [LinearOrder (Labels k u)]
    (policy : Policy (ElementaryAction (Labels k u) Available)
      (Finset (TargetCode (Labels k u) Available))) (q : Index u) : Prop :=
  ∃ n, ∃ row ∈ (policyState promisedGame policy none n).history, TestsIndex q row.1

theorem state_eq_if_never_tests {k u : Nat} [LinearOrder (Labels k u)]
    (policy : Policy (ElementaryAction (Labels k u) Available)
      (Finset (TargetCode (Labels k u) Available))) (q : Index u) (never : ¬ EverTests policy q) :
    ∀ n, policyState promisedGame policy (some q) n = policyState promisedGame policy none n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [policyState, ih]
      cases output : (policyState promisedGame policy none n).output with
      | some value => simp only [advance, output]
      | none =>
          cases decision : policy (policyState promisedGame policy none n).history with
          | none => simp only [advance, output, decision]
          | some choice => cases choice with
            | inl value => simp only [advance, output, decision]
            | inr action =>
                have untested : ¬ TestsIndex q action := by
                  intro tested
                  apply never
                  refine ⟨n + 1, (action, promisedGame.response none action), ?_, tested⟩
                  simp [policyState, advance, output, decision]
                have same := physical_responses_agree_off_index q action untested
                simp only [advance, output, decision]
                rw [same]

theorem different_outputs_require_test {k u : Nat} [LinearOrder (Labels k u)]
    (policy : Policy (ElementaryAction (Labels k u) Available)
      (Finset (TargetCode (Labels k u) Available))) (q : Index u) (m n : Nat)
    (a b : Finset (TargetCode (Labels k u) Available)) (different : a ≠ b)
    (baseOutput : (policyState promisedGame policy none m).output = some a)
    (rivalOutput : (policyState promisedGame policy (some q) n).output = some b) :
    EverTests policy q := by
  by_contra never
  rw [state_eq_if_never_tests policy q never n] at rivalOutput
  exact different (policy_output_unique promisedGame policy none m n a b baseOutput rivalOutput)

/-- The event has a literal first finite history time; every earlier
baseline history contains no distinguishing action. This is a statement
about the actual adaptive run, not a fresh rival fitted at each prefix. -/
theorem first_test_time {k u : Nat} [LinearOrder (Labels k u)]
    (policy : Policy (ElementaryAction (Labels k u) Available)
      (Finset (TargetCode (Labels k u) Available))) (q : Index u) (tested : EverTests policy q) :
    ∃ n, (∃ row ∈ (policyState promisedGame policy none n).history, TestsIndex q row.1) ∧
      ∀ m < n, ∀ row ∈ (policyState promisedGame policy none m).history, ¬ TestsIndex q row.1 := by
  classical
  refine ⟨Nat.find tested, Nat.find_spec tested, ?_⟩
  intro m earlier row member tests
  have least : Nat.find tested ≤ m := Nat.find_min' tested ⟨row, member, tests⟩
  omega

theorem original_physical_policy_state {k u : Nat} [LinearOrder (Labels k u)]
    (policy : Policy (ElementaryAction (Labels k u) Available)
      (Finset (TargetCode (Labels k u) Available))) (source : Option (Index u)) (n : Nat) :
    policyState (PhysicalSource.physicalGame Available) policy (physicalSource source) n =
      policyState promisedGame policy source n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [policyState, ih]
      cases output : (policyState promisedGame policy source n).output with
      | some q => simp only [advance, output]
      | none =>
          cases decision : policy (policyState promisedGame policy source n).history with
          | none => simp only [advance, output, decision]
          | some choice => cases choice <;> simp only [advance, output, decision] <;> rfl

theorem original_physical_policy_error {k u : Nat} [LinearOrder (Labels k u)]
    (policy : Policy (ElementaryAction (Labels k u) Available)
      (Finset (TargetCode (Labels k u) Available))) (source : Option (Index u)) :
    PolicyError (PhysicalSource.physicalGame Available) policy (physicalSource source) ↔
      PolicyError promisedGame policy source := by
  unfold PolicyError
  simp only [original_physical_policy_state]
  rfl

/-- Nontermination is failure by definition. If neither run fails, each
has a finite correct stopping time, and absorbing output uniqueness yields
the contradiction. No termination hypothesis is needed for this coupling. -/
theorem never_test_implies_error {k u : Nat} [LinearOrder (Labels k u)]
    (nonemptyTargets : 0 < k)
    (policy : Policy (ElementaryAction (Labels k u) Available)
      (Finset (TargetCode (Labels k u) Available))) (q : Index u) (never : ¬ EverTests policy q) :
    PolicyError promisedGame policy none ∨ PolicyError promisedGame policy (some q) := by
  by_cases baseError : PolicyError promisedGame policy none
  · exact Or.inl baseError
  · right
    have baseSuccess : ∃ m, (policyState promisedGame policy none m).output = some (promisedGame.target none) := by
      by_contra «impossible»
      exact baseError «impossible»
    obtain ⟨m, baseCorrect⟩ := baseSuccess
    rintro ⟨n, rivalCorrect⟩
    rw [state_eq_if_never_tests policy q never n] at rivalCorrect
    have targets := policy_output_unique promisedGame policy none m n
      (promisedGame.target none) (promisedGame.target (some q)) baseCorrect rivalCorrect
    exact baseline_class_ne_rival nonemptyTargets q targets

end RestrictedCausal.HardFamily
