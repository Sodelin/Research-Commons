import G7ResourceGamePort

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

An explicit finite response-branching batch constructor. It never evaluates
an unknown source and does not use classical winning-plan extraction.
The resource is the remaining number of elementary queries. Every response
branch is checked, including branches no admitted source can realize.
-/

namespace RestrictedCausal.QueryPlan

open GProgram.G7.ExactLawResourceGame

universe uS uA uQ uI

def budgetExperiment {S : Type uS} {A : Type uA} {Q : Type uQ}
    (admitted : S → Prop) (target : S → Q) (response : S → A → Bool)
    (allowed : A → Prop) : Experiment S A Bool Q Nat where
  admitted := admitted
  target := target
  response := response
  legal remaining action := 0 < remaining ∧ allowed action
  update remaining _ := remaining - 1

def writeReply {I : Type uI} [DecidableEq I]
    (r : I → Bool) (i : I) (answer : Bool) : I → Bool :=
  fun j => if j = i then answer else r j

theorem writeReply_same {I : Type uI} [DecidableEq I]
    (r : I → Bool) (i : I) (answer : Bool) : writeReply r i answer i = answer := by
  simp only [writeReply, if_pos rfl]

theorem writeReply_other {I : Type uI} [DecidableEq I]
    (r : I → Bool) (i j : I) (answer : Bool) (distinct : j ≠ i) :
    writeReply r i answer j = r j := by
  simp only [writeReply, if_neg distinct]

structure Collected {I : Type uI} {A : Type uA}
    (items : List I) (action : I → A) (before : I → Bool)
    (old : History A Bool) (after : I → Bool) (fresh : History A Bool) : Prop where
  retained : ∀ row ∈ old, row ∈ fresh
  outside : ∀ i, i ∉ items → after i = before i
  answered : ∀ i ∈ items, (action i, after i) ∈ fresh
  length : fresh.length = old.length + items.length

/-- The history is prepended, exactly as in the supplying G7 game. -/
def collect {I : Type uI} {A : Type uA} {Q : Type uQ} [DecidableEq I]
    (items : List I) (action : I → A) {n : Nat}
    (finish : (I → Bool) → History A Bool → Plan A Bool Q n)
    (r : I → Bool) (h : History A Bool) : Plan A Bool Q (n + items.length) :=
  match items with
  | [] => finish r h
  | i :: rest => Plan.ask (action i) (fun answer =>
      collect rest action finish (writeReply r i answer) ((action i, answer) :: h))

/-- Strong induction invariant: a completed batch retains every old row,
records every requested coordinate, changes no unqueried reply coordinate,
and has exactly the advertised length. No source is resampled or replaced. -/
theorem collect_valid {S : Type uS} {A : Type uA} {Q : Type uQ} {I : Type uI}
    [DecidableEq I] (admitted : S → Prop) (target : S → Q)
    (response : S → A → Bool) (allowed : A → Prop)
    (items : List I) (unique : items.Nodup) (action : I → A)
    (legal : ∀ i ∈ items, allowed (action i)) {n : Nat}
    (finish : (I → Bool) → History A Bool → Plan A Bool Q n)
    (r : I → Bool) (h : History A Bool)
    (terminal : ∀ after fresh, Collected items action r h after fresh →
      Valid (budgetExperiment admitted target response allowed) (finish after fresh) fresh n) :
    Valid (budgetExperiment admitted target response allowed)
      (collect items action finish r h) h (n + items.length) := by
  induction items generalizing r h with
  | nil =>
      apply terminal r h
      exact ⟨fun _ member => member, fun _ _ => rfl,
        fun _ member => False.elim (List.not_mem_nil _ member), by simp⟩
  | cons first rest ih =>
      have noFirst : first ∉ rest := (List.nodup_cons.mp unique).1
      have uniqueRest : rest.Nodup := (List.nodup_cons.mp unique).2
      have positive : 0 < n + (first :: rest).length := by simp; omega
      change (0 < n + (first :: rest).length ∧ allowed (action first)) ∧
        ∀ answer, Valid (budgetExperiment admitted target response allowed)
          (collect rest action finish (writeReply r first answer) ((action first, answer) :: h))
          ((action first, answer) :: h) ((n + (first :: rest).length) - 1)
      refine ⟨⟨positive, legal first (List.mem_cons_self _ _)⟩, ?_⟩
      intro answer
      have remaining : (n + (first :: rest).length) - 1 = n + rest.length := by
        simp only [List.length_cons]
        omega
      rw [remaining]
      apply ih uniqueRest (fun i member => legal i (List.mem_cons_of_mem _ member))
        (writeReply r first answer) ((action first, answer) :: h)
      intro after fresh facts
      apply terminal after fresh
      constructor
      · intro row member
        exact facts.retained row (List.mem_cons_of_mem _ member)
      · intro i absent
        have neq : i ≠ first := by
          intro same
          subst i
          exact absent (List.mem_cons_self _ _)
        have notRest : i ∉ rest := fun member => absent (List.mem_cons_of_mem _ member)
        exact (facts.outside i notRest).trans (writeReply_other r first i answer neq)
      · intro i member
        rcases List.mem_cons.mp member with same | later
        · subst i
          have unchanged := facts.outside first noFirst
          rw [writeReply_same] at unchanged
          rw [unchanged]
          exact facts.retained _ (List.mem_cons_self _ _)
        · exact facts.answered i later
      · have size := facts.length
        simp only [List.length_cons] at size ⊢
        omega

end RestrictedCausal.QueryPlan
