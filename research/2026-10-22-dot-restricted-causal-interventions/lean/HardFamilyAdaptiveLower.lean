import HardFamilyIndexCount

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY UNELABORATED CANDIDATE. No execution.

The lower adapter is applied to the actual ALL-physical-source experiment,
not just an abstract one-hot game. One rival is chosen after examining the
entire fixed-baseline adaptive run. That same original graph and common
positive binary mechanism reproduces every row of the whole history.
-/

namespace RestrictedCausal.HardFamily

open PartialQueries ProbabilitySource FiniteTargetImage TranscriptDecoder
open GProgram.G7.ExactLawResourceGame

universe uS uA uQ

def executedActions {S : Type uS} {A : Type uA} {Q : Type uQ}
    (E : Experiment S A Bool Q Nat) : {n : Nat} → Plan A Bool Q n → S → List A
  | _, .«stop» _, _ => []
  | _, .ask action «next», source =>
      action :: executedActions E («next» (E.response source action)) source

theorem executed_length_le_horizon {S : Type uS} {A : Type uA} {Q : Type uQ}
    (E : Experiment S A Bool Q Nat) {n : Nat} (plan : Plan A Bool Q n) (source : S) :
    (executedActions E plan source).length ≤ n := by
  induction plan with
  | «stop» q => simp only [executedActions, List.length_nil]; exact Nat.zero_le _
  | ask action «next» ih =>
      simpa only [executedActions, List.length_cons] using
        Nat.succ_le_succ (ih (E.response source action))

theorem executed_length_le_budget {S : Type uS} {A : Type uA} {Q : Type uQ}
    (admitted : S → Prop) (target : S → Q) (response : S → A → Bool) (allowed : A → Prop)
    {n : Nat} (plan : Plan A Bool Q n) (h : History A Bool) (budget : Nat)
    (valid : Valid (QueryPlan.budgetExperiment admitted target response allowed) plan h budget)
    (source : S) :
    (executedActions (QueryPlan.budgetExperiment admitted target response allowed) plan source).length ≤ budget := by
  induction plan generalizing h budget with
  | «stop» q => simp only [executedActions, List.length_nil]; exact Nat.zero_le _
  | ask action «next» ih =>
      have positive : 0 < budget := valid.1.1
      have tail := ih (response source action) ((action, response source action) :: h)
        (budget - 1) (valid.2 (response source action))
      simp only [executedActions, List.length_cons]
      omega

/-- Adaptivity is handled by induction on the ACTUAL baseline branch.
Agreement only on that complete branch suffices; no per-row rival choice. -/
theorem run_eq_of_agree_on_executed {S : Type uS} {A : Type uA} {Q : Type uQ}
    (E : Experiment S A Bool Q Nat) {n : Nat} (plan : Plan A Bool Q n) (baseline rival : S)
    (agree : ∀ action ∈ executedActions E plan baseline,
      E.response rival action = E.response baseline action) :
    run E plan rival = run E plan baseline := by
  induction plan with
  | «stop» q => rfl
  | ask action «next» ih =>
      have «first» := agree action List.mem_cons_self
      simp only [run, «first»]
      apply ih (E.response baseline action)
      intro later member
      exact agree later (List.mem_cons_of_mem _ member)

def baselineHistory {S : Type uS} {A : Type uA} {Q : Type uQ}
    (E : Experiment S A Bool Q Nat) {n : Nat} (plan : Plan A Bool Q n) (source : S) : History A Bool :=
  (executedActions E plan source).map (fun a => (a, E.response source a))

theorem whole_baseline_history_consistent {S : Type uS} {A : Type uA} {Q : Type uQ}
    (E : Experiment S A Bool Q Nat) {n : Nat} (plan : Plan A Bool Q n) (baseline rival : S)
    (admitted : E.admitted rival)
    (agree : ∀ action ∈ executedActions E plan baseline,
      E.response rival action = E.response baseline action) :
    Consistent E (baselineHistory E plan baseline) rival := by
  refine ⟨admitted, ?_⟩
  intro row member
  obtain ⟨action, present, rfl⟩ := List.mem_map.mp member
  exact agree action present

noncomputable def testedIndices {k u : Nat}
    (actions : List (ElementaryAction (Labels k u) Available)) : Finset (Index u) := by
  classical
  exact match actions with
  | [] => ∅
  | action :: tail => (Finset.univ.filter (fun q => TestsIndex q action)) ∪ testedIndices tail

theorem mem_testedIndices {k u : Nat} (q : Index u)
    (actions : List (ElementaryAction (Labels k u) Available)) :
    q ∈ testedIndices actions ↔ ∃ action ∈ actions, TestsIndex q action := by
  classical
  induction actions with
  | nil => simp only [testedIndices, Finset.notMem_empty, List.not_mem_nil, false_and, exists_false]
  | cons action tail ih =>
      simp only [testedIndices, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, ih,
        List.mem_cons]
      constructor
      · rintro («first» | ⟨later, member, tests⟩)
        · exact ⟨action, Or.inl rfl, «first»⟩
        · exact ⟨later, Or.inr member, tests⟩
      · rintro ⟨later, same | member, tests⟩
        · subst later; exact Or.inl tests
        · exact Or.inr ⟨later, member, tests⟩

theorem testedIndices_card_le {k u : Nat}
    (actions : List (ElementaryAction (Labels k u) Available)) :
    (testedIndices actions).card ≤ actions.length := by
  classical
  induction actions with
  | nil => simp only [testedIndices, Finset.card_empty, List.length_nil, le_refl]
  | cons action tail ih =>
      have one : (Finset.univ.filter (fun q : Index u => TestsIndex q action)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro q qMem r rMem
        exact tests_index_unique q r action (Finset.mem_filter.mp qMem).2 (Finset.mem_filter.mp rMem).2
      have union := Finset.card_union_le
        (Finset.univ.filter (fun q : Index u => TestsIndex q action)) (testedIndices tail)
      change ((Finset.univ.filter (fun q : Index u => TestsIndex q action)) ∪ testedIndices tail).card ≤
        (action :: tail).length
      simp only [List.length_cons]
      omega

theorem exists_untested_index {k u : Nat}
    (actions : List (ElementaryAction (Labels k u) Available))
    (short : actions.length < Fintype.card (Index u)) :
    ∃ q : Index u, ∀ action ∈ actions, ¬ TestsIndex q action := by
  classical
  have missing : ∃ q : Index u, q ∉ testedIndices actions := by
    by_contra none
    have all : Finset.univ ⊆ testedIndices actions := by
      intro q _
      by_contra absent
      exact none ⟨q, absent⟩
    have lower := Finset.card_le_card all
    rw [Finset.card_univ] at lower
    have upper := testedIndices_card_le actions
    omega
  obtain ⟨q, absent⟩ := missing
  exact ⟨q, fun action member tested => absent ((mem_testedIndices q actions).mpr ⟨action, member, tested⟩)⟩

/-- The original full physical class, arbitrary horizon n, and a genuine
query resource budget b. The condition k>0 is essential for the literal
marked-TCM target; k=0 is separately zero-query solvable. -/
theorem no_short_physical_plan {k u n budget : Nat} [LinearOrder (Labels k u)]
    (nonemptyTargets : 0 < k) (short : budget < u.choose 2 * 2 ^ (u - 2))
    (plan : Plan (ElementaryAction (Labels k u) Available) Bool
      (Finset (TargetCode (Labels k u) Available)) n) :
    ¬ Valid (PhysicalSource.physicalGame Available) plan [] budget := by
  intro valid
  let E := PhysicalSource.physicalGame (@Available k u)
  let base := physicalSource (k := k) (u := u) none
  have lengthBound := executed_length_le_budget (fun _ => True)
    (fun P : PhysicalSource.PhysicalSource (@Available k u) => classTarget Available P.graph)
    (PhysicalSource.physicalResponse Available) (LegalAction Available) plan [] budget valid base
  have shortPath : (executedActions E plan base).length < Fintype.card (Index u) := by
    rw [index_card]
    exact lt_of_le_of_lt lengthBound short
  obtain ⟨q, untouched⟩ := exists_untested_index (executedActions E plan base) shortPath
  have agreement : ∀ action ∈ executedActions E plan base,
      E.response (physicalSource (some q)) action = E.response base action := by
    intro action member
    exact physical_responses_agree_off_index q action (untouched action member)
  have runs := run_eq_of_agree_on_executed E plan base (physicalSource (some q)) agreement
  have baseCorrect := valid_run_identifies E plan [] budget valid base
    ⟨True.intro, fun _ member => (List.not_mem_nil member).elim⟩
  have rivalCorrect := valid_run_identifies E plan [] budget valid (physicalSource (some q))
    ⟨True.intro, fun _ member => (List.not_mem_nil member).elim⟩
  have same := baseCorrect.symm.trans (runs.symm.trans rivalCorrect)
  exact baseline_class_ne_rival nonemptyTargets q same

theorem no_short_physical_winning {k u n budget : Nat} [LinearOrder (Labels k u)]
    (nonemptyTargets : 0 < k) (short : budget < u.choose 2 * 2 ^ (u - 2)) :
    ¬ Winning (PhysicalSource.physicalGame (@Available k u)) n [] budget := by
  intro winning
  obtain ⟨plan, valid⟩ := winning_has_plan (PhysicalSource.physicalGame Available) n [] budget winning
  exact no_short_physical_plan nonemptyTargets short plan valid

end RestrictedCausal.HardFamily
