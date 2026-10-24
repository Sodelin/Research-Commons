import HardFamilyAdaptiveLower

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY UNELABORATED CANDIDATE. No execution.

Exact promised-family optimum for the SAME original full marked-class
target. The upper plan is an explicit list scan with Boolean replies;
no rank theorem, winning-plan choice, or source-dependent action selection
is used to construct it. The list enumeration is supplied, not extracted
from classical Finset.toList. Targets/physical responses remain semantic
specifications, not an executed numerical CPT implementation.
-/

namespace RestrictedCausal.HardFamily

open PartialQueries ProbabilitySource FiniteTargetImage TranscriptDecoder QueryPlan
open GProgram.G7.ExactLawResourceGame

theorem original_family_target_injective {k u : Nat} [LinearOrder (Labels k u)]
    (nonemptyTargets : 0 < k) :
    Function.Injective (fun source : Option (Index u) => classTarget Available (originalSource (k := k) source)) := by
  intro «first» second same
  have available : ∃ t : Labels k u, Available t := ⟨.inl ⟨0, nonemptyTargets⟩, True.intro⟩
  have signals (q : Index u) : «first» = some q ↔ second = some q := by
    have legal := indexQuery_legal (k := k) q
    have baseline := equal_classes_imply_baseline_agreement Available available
      (originalSource «first») (originalSource second) same (BoolCondition (indexBits q))
      (.inr q.first) (.inr q.second) legal.1 legal.2.1 legal.2.2
    have answers : PositiveAnswer (originalSource (k := k) «first») (indexQuery q) ↔
        PositiveAnswer (originalSource second) (indexQuery q) := by
      simp only [indexQuery, PositiveAnswer, if_pos legal]
      exact not_congr baseline
    rw [← indexQuery_response_iff (k := k) «first» q, ← indexQuery_response_iff (k := k) second q]
    exact (PhysicalSource.physical_response_exact Available (physicalSource «first») (indexQuery q)).symm.trans
      (answers.trans (PhysicalSource.physical_response_exact Available (physicalSource second) (indexQuery q)))
  cases «first» with
  | none =>
      cases second with
      | none => rfl
      | some q => exact Option.noConfusion ((signals q).mpr rfl)
  | some q => exact ((signals q).mp rfl).symm

noncomputable def promisedGame {k u : Nat} [LinearOrder (Labels k u)] :
    Experiment (Option (Index u)) (ElementaryAction (Labels k u) Available) Bool
      (Finset (TargetCode (Labels k u) Available)) Nat :=
  sourceGame Available originalSource
    (fun source => PhysicalSource.physicalResponse Available (physicalSource source))

def readIndex {u : Nat} (items : List (Index u)) (reply : Index u → Bool) : Option (Index u) :=
  match items with
  | [] => none
  | q :: tail => if reply q = true then some q else readIndex tail reply

theorem readIndex_correct {u : Nat} (items : List (Index u)) (reply : Index u → Bool)
    (source : Option (Index u)) (covered : ∀ q, source = some q → q ∈ items)
    (signals : ∀ q ∈ items, reply q = true ↔ source = some q) : readIndex items reply = source := by
  induction items generalizing source with
  | nil =>
      cases source with
      | none => rfl
      | some q => exact (List.not_mem_nil (covered q rfl)).elim
  | cons q tail ih =>
      by_cases yes : reply q = true
      · rw [readIndex, if_pos yes]
        exact ((signals q List.mem_cons_self).mp yes).symm
      · rw [readIndex, if_neg yes]
        apply ih
        · intro r same
          rcases List.mem_cons.mp (covered r same) with equal | member
          · subst r
            exact (yes ((signals q List.mem_cons_self).mpr same)).elim
          · exact member
        · intro r member
          exact signals r (List.mem_cons_of_mem _ member)

noncomputable def familyPlan {k u : Nat} [LinearOrder (Labels k u)]
    (items : List (Index u)) (spare : Nat) :
    Plan (ElementaryAction (Labels k u) Available) Bool
      (Finset (TargetCode (Labels k u) Available)) (spare + items.length) := by
  classical
  exact collect items indexQuery
    (fun reply _ => Plan.stop (n := spare) (classTarget Available (originalSource (readIndex items reply))))
    (fun _ => false) []

theorem familyPlan_valid {k u : Nat} [LinearOrder (Labels k u)]
    (items : List (Index u)) (unique : items.Nodup) (complete : ∀ q, q ∈ items) (spare : Nat) :
    Valid (promisedGame (k := k)) (familyPlan items spare) [] (spare + items.length) := by
  classical
  apply collect_valid (fun _ => True) (fun source => classTarget Available (originalSource source))
    (fun source => PhysicalSource.physicalResponse Available (physicalSource source))
    (LegalAction Available) items unique indexQuery (fun q _ => indexQuery_legal q)
  intro reply fresh facts source consistent
  have signals : ∀ q ∈ items, reply q = true ↔ source = some q := by
    intro q member
    have recorded := consistent.2 (indexQuery q, reply q) (facts.answered q member)
    rw [← recorded]
    exact indexQuery_response_iff source q
  have decoded := readIndex_correct items reply source (fun q _ => complete q) signals
  change classTarget Available (originalSource source) =
    classTarget Available (originalSource (readIndex items reply))
  rw [decoded]

theorem no_short_promised_plan {k u n budget : Nat} [LinearOrder (Labels k u)]
    (nonemptyTargets : 0 < k) (short : budget < u.choose 2 * 2 ^ (u - 2))
    (plan : Plan (ElementaryAction (Labels k u) Available) Bool
      (Finset (TargetCode (Labels k u) Available)) n) :
    ¬ Valid (promisedGame (k := k)) plan [] budget := by
  intro valid
  let E := promisedGame (k := k) (u := u)
  have lengthBound := executed_length_le_budget (fun _ => True)
    (fun source => classTarget Available (originalSource (k := k) source))
    (fun source => PhysicalSource.physicalResponse Available (physicalSource source))
    (LegalAction Available) plan [] budget valid none
  have shortPath : (executedActions E plan none).length < Fintype.card (Index u) := by
    rw [index_card]
    exact lt_of_le_of_lt lengthBound short
  obtain ⟨q, untouched⟩ := exists_untested_index (executedActions E plan none) shortPath
  have agreement : ∀ action ∈ executedActions E plan none,
      E.response (some q) action = E.response none action := by
    intro action member
    exact physical_responses_agree_off_index q action (untouched action member)
  have runs := run_eq_of_agree_on_executed E plan none (some q) agreement
  have baseCorrect := valid_run_identifies E plan [] budget valid none
    ⟨True.intro, fun _ member => (List.not_mem_nil member).elim⟩
  have rivalCorrect := valid_run_identifies E plan [] budget valid (some q)
    ⟨True.intro, fun _ member => (List.not_mem_nil member).elim⟩
  exact baseline_class_ne_rival nonemptyTargets q
    (baseCorrect.symm.trans (runs.symm.trans rivalCorrect))

theorem enumeration_length {u : Nat} (items : List (Index u))
    (unique : items.Nodup) (complete : ∀ q, q ∈ items) :
    items.length = u.choose 2 * 2 ^ (u - 2) := by
  classical
  have all : items.toFinset = Finset.univ := by
    apply Finset.ext
    intro q
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact complete q
  have size := List.toFinset_card_of_nodup unique
  rw [all, Finset.card_univ, index_card] at size
  exact size.symm

/-- Exact G7 budget equivalence on the literal M+1-source registry, with
the original marked-class target. The finite label enumeration is input.
No claim is made that arbitrary full laws reduce to these query bits. -/
theorem promised_winning_iff {k u : Nat} [LinearOrder (Labels k u)]
    (nonemptyTargets : 0 < k) (items : List (Index u))
    (unique : items.Nodup) (complete : ∀ q, q ∈ items) (budget : Nat) :
    Winning (promisedGame (k := k)) budget [] budget ↔ u.choose 2 * 2 ^ (u - 2) ≤ budget := by
  constructor
  · intro winning
    by_contra notEnough
    have short : budget < u.choose 2 * 2 ^ (u - 2) := by omega
    obtain ⟨plan, valid⟩ := winning_has_plan (promisedGame (k := k)) budget [] budget winning
    exact no_short_promised_plan nonemptyTargets short plan valid
  · intro enough
    have length := enumeration_length items unique complete
    have exactBudget : budget - items.length + items.length = budget := by omega
    have winning := valid_implies_winning (promisedGame (k := k))
      (familyPlan items (budget - items.length)) [] (budget - items.length + items.length)
      (familyPlan_valid items unique complete (budget - items.length))
    simpa only [exactBudget] using winning

end RestrictedCausal.HardFamily
