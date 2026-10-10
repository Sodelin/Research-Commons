import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

/-! Semantic F2 consumer for the original G7 exact-law/reset contract.
Attribution: formalization of the accepted GPT-6 Astra Pro F1/F2 argument,
2026-10-01; Lean source draft by dot / OpenAI, 2026-10-10.

Responses are entire exact-law vectors, not sampled observations. One source
fits the WHOLE history. Resource state is updated only on executed actions.
This file proves no effective QE/CAD selection and no F1 horizon reduction.
The classical plan-existence result is not executable policy extraction.
DRAFT: not compiler-checked, not accepted, not in the running frozen build. -/
namespace GProgram.G7.ExactLawResourceGame

universe uS uA uY uT uR
variable {S : Type uS} {A : Type uA} {Y : Type uY} {T : Type uT} {R : Type uR}

structure Experiment (S : Type uS) (A : Type uA) (Y : Type uY)
    (T : Type uT) (R : Type uR) where
  admitted : S → Prop
  target : S → T
  response : S → A → Y
  legal : R → A → Prop
  update : R → A → R

abbrev History (A : Type uA) (Y : Type uY) := List (A × Y)

def Consistent (E : Experiment S A Y T R) (h : History A Y) (s : S) : Prop :=
  E.admitted s ∧ ∀ ay ∈ h, E.response s ay.1 = ay.2

def Homogeneous (E : Experiment S A Y T R) (h : History A Y) : Prop :=
  ∀ s t, Consistent E h s → Consistent E h t → E.target s = E.target t

lemma consistent_extend (E : Experiment S A Y T R) (h : History A Y)
    (s : S) (a : A) (y : Y) :
    Consistent E ((a,y)::h) s ↔ Consistent E h s ∧ E.response s a = y := by
  simp only [Consistent, List.mem_cons, forall_eq_or_imp]
  tauto

lemma homogeneous_iff_terminal [Nonempty T] (E : Experiment S A Y T R)
    (h : History A Y) :
    Homogeneous E h ↔ ∃ q : T, ∀ s, Consistent E h s → E.target s = q := by
  classical
  constructor
  · intro hh
    by_cases he : ∃ s, Consistent E h s
    · obtain ⟨s,hs⟩ := he
      exact ⟨E.target s, fun t ht => hh t s ht hs⟩
    · exact ⟨Classical.choice inferInstance, fun s hs => (he ⟨s,hs⟩).elim⟩
  · rintro ⟨q,hq⟩ s t hs ht
    exact (hq s hs).trans (hq t ht).symm

def Winning (E : Experiment S A Y T R) : Nat → History A Y → R → Prop
  | 0,h,_ => Homogeneous E h
  | n+1,h,u => Homogeneous E h ∨
      ∃ a, E.legal u a ∧ ∀ y, Winning E n ((a,y)::h) (E.update u a)

inductive Plan (A : Type uA) (Y : Type uY) (T : Type uT) : Nat → Type (max uA uY uT)
  | stop {n : Nat} (target : T) : Plan A Y T n
  | ask {n : Nat} (action : A) (next : Y → Plan A Y T n) : Plan A Y T (n+1)

def Valid (E : Experiment S A Y T R) :
    {n : Nat} → Plan A Y T n → History A Y → R → Prop
  | _,.stop q,h,_ => ∀ s, Consistent E h s → E.target s = q
  | _,.ask a next,h,u => E.legal u a ∧
      ∀ y, Valid E (next y) ((a,y)::h) (E.update u a)

def run (E : Experiment S A Y T R) : {n : Nat} → Plan A Y T n → S → T
  | _,.stop q,_ => q
  | _,.ask a next,s => run E (next (E.response s a)) s

theorem valid_implies_winning (E : Experiment S A Y T R)
    {n : Nat} (p : Plan A Y T n) (h : History A Y) (u : R)
    (hp : Valid E p h u) : Winning E n h u := by
  induction p generalizing h u with
  | stop q =>
    have hh : Homogeneous E h := fun s t hs ht => (hp s hs).trans (hp t ht).symm
    cases n with
    | zero => exact hh
    | succ n => exact Or.inl hh
  | ask a next ih => exact Or.inr ⟨a,hp.1,fun y => ih y _ _ (hp.2 y)⟩

theorem winning_has_plan [Nonempty T] (E : Experiment S A Y T R)
    (n : Nat) (h : History A Y) (u : R) (hw : Winning E n h u) :
    ∃ p : Plan A Y T n, Valid E p h u := by
  classical
  induction n generalizing h u with
  | zero =>
    obtain ⟨q,hq⟩ := (homogeneous_iff_terminal E h).mp hw
    exact ⟨.stop q,hq⟩
  | succ n ih =>
    rcases hw with hh | ⟨a,ha,hy⟩
    · obtain ⟨q,hq⟩ := (homogeneous_iff_terminal E h).mp hh
      exact ⟨.stop q,hq⟩
    · let next := fun y => Classical.choose (ih ((a,y)::h) (E.update u a) (hy y))
      exact ⟨.ask a next,ha,fun y =>
        Classical.choose_spec (ih ((a,y)::h) (E.update u a) (hy y))⟩

theorem winning_iff_valid_plan [Nonempty T] (E : Experiment S A Y T R)
    (n : Nat) (h : History A Y) (u : R) :
    Winning E n h u ↔ ∃ p : Plan A Y T n, Valid E p h u :=
  ⟨winning_has_plan E n h u,fun ⟨p,hp⟩ => valid_implies_winning E p h u hp⟩

/-- The same original source and parameters generate every executed response.
The semantic plan identifies its actual target, not a sampled-observation label. -/
theorem valid_run_identifies (E : Experiment S A Y T R)
    {n : Nat} (p : Plan A Y T n) (h : History A Y) (u : R)
    (hp : Valid E p h u) (s : S) (hs : Consistent E h s) :
    run E p s = E.target s := by
  induction p generalizing h u with
  | stop q => exact (hp s hs).symm
  | ask a next ih =>
    exact ih (E.response s a) ((a,E.response s a)::h) (E.update u a)
      (hp.2 (E.response s a)) ((consistent_extend E h s a _).mpr ⟨hs,rfl⟩)

theorem losing_step (E : Experiment S A Y T R) (n : Nat)
    (h : History A Y) (u : R) (hl : ¬ Winning E (n+1) h u) :
    ¬ Homogeneous E h ∧
      ∀ a, E.legal u a → ∃ y, ¬ Winning E n ((a,y)::h) (E.update u a) := by
  classical
  constructor
  · exact fun hh => hl (Or.inl hh)
  · intro a ha
    by_contra hn
    have hy : ∀ y, Winning E n ((a,y)::h) (E.update u a) := by
      simpa only [not_exists,not_not] using hn
    exact hl (Or.inr ⟨a,ha,hy⟩)

/-- The lower certificate uses two admitted sources fitting the ENTIRE
transcript. It does not assert one fixed pair defeating all policies. -/
theorem losing_has_full_history_pair (E : Experiment S A Y T R) (n : Nat)
    (h : History A Y) (u : R) (hl : ¬ Winning E n h u) :
    ∃ s t, Consistent E h s ∧ Consistent E h t ∧ E.target s ≠ E.target t := by
  classical
  have hn : ¬ Homogeneous E h := by
    intro hh
    cases n with
    | zero => exact hl hh
    | succ n => exact hl (Or.inl hh)
  simpa only [Homogeneous,not_forall,not_imp] using hn

section PathResources
variable {Row Site : Type*} [DecidableEq A] [DecidableEq Row] [DecidableEq Site]

/-- `support a` denotes the positive-weight deterministic rows of a programme.
It is not the number of sampled rows observed in a single realization. -/
def usedRows (support : A → Finset Row) (path : List A) : Finset Row :=
  path.toFinset.biUnion support

def usedSites (support : A → Finset Row) (sites : Row → Finset Site)
    (path : List A) : Finset Site := (usedRows support path).biUnion sites

structure Budget where
  sites : Nat
  rows : Nat
  calls : Nat

def WithinBudget (support : A → Finset Row) (sites : Row → Finset Site)
    (B : Budget) (path : List A) : Prop :=
  (usedSites support sites path).card ≤ B.sites ∧
  (usedRows support path).card ≤ B.rows ∧ path.length ≤ B.calls

lemma usedRows_sublist (support : A → Finset Row) {small large : List A}
    (h : small.Sublist large) : usedRows support small ⊆ usedRows support large := by
  intro r hr
  obtain ⟨a,ha,hr⟩ := Finset.mem_biUnion.mp hr
  exact Finset.mem_biUnion.mpr ⟨a,List.mem_toFinset.mpr (h.subset (List.mem_toFinset.mp ha)),hr⟩

/-- Concrete G7 union-site/configuration/call upper budgets are deletion
closed on each executed path. No global programme-bank cost is substituted. -/
theorem trajectory_budget_deletion_closed (support : A → Finset Row)
    (sites : Row → Finset Site) (B : Budget) {small large : List A}
    (h : small.Sublist large) (hb : WithinBudget support sites B large) :
    WithinBudget support sites B small := by
  have hr := usedRows_sublist support h
  have hs : usedSites support sites small ⊆ usedSites support sites large := by
    intro site hm
    obtain ⟨r,hm,hs⟩ := Finset.mem_biUnion.mp hm
    exact Finset.mem_biUnion.mpr ⟨r,hr hm,hs⟩
  exact ⟨(Finset.card_le_card hs).trans hb.1,
    (Finset.card_le_card hr).trans hb.2.1,h.length_le.trans hb.2.2⟩

end PathResources
end GProgram.G7.ExactLawResourceGame
