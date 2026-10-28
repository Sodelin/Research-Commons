import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas


/-!
Proof elaboration repair by Codex coordinator, 2026-10-10.
Bind the stop constructor index explicitly and normalize proof existentials.
The original executable definitions and theorem statements are preserved.
Fresh checking and full owned audit are pending.

Semantic F2 consumer for the original G7 exact-law/reset contract.
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
  | @stop n q =>
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
  unfold Homogeneous at hn
  push_neg at hn
  exact hn

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


/-! F1 proof-level compression of pointwise-total exact-law reset strategies.
The virtual transcript remains intact. Redundant calls are skipped physically;
their uniquely determined responses are still fed to the original policy.
Termination of a run of virtual calls uses one compatible source only as a
proof witness. It does not add a source oracle to the physical experiment.
Attribution: GPT-6 Astra Pro's accepted original G7 F1 argument (2026-10-01);
formalization draft by dot / OpenAI (2026-10-10).
DRAFT: uncompiled and unreviewed. No effective extraction/QE claim. -/
/-!
Elaboration derivative by Codex / lean_reuse_successor, 2026-10-10.
Original source SHA256: 17237e5e9f927162177810fa436a32f4ea54e352f9fdf8b359f670c6836021cb.
Explicitly includes the declared affine-response premise in proofs that use it;
its dependencies include the original base, coefficient forms and offsets.
No executable definition, semantic premise or resource bound is replaced.
Fresh checking and complete audit remain required.
-/
namespace GProgram.G7.ExactLawRankCompression
open GProgram.G7.ExactLawResourceGame
open scoped Classical
variable {S A O T V : Type*} [AddCommGroup V] [Module ℝ V]

abbrev Policy (A O T : Type*) := History A (O → ℝ) → T ⊕ A

/-- Totality is pointwise in the actual source. No uniform bound on virtual
running time and no well-founded tree over impossible replies is assumed. -/
inductive CorrectRun (E : Experiment S A (O → ℝ) T (List A))
    (policy : Policy A O T) (s : S) : History A (O → ℝ) → List A → Prop
  | stop {h past} (q : T) (decision : policy h = .inl q) (correct : E.target s = q) :
      CorrectRun E policy s h past
  | ask {h past} (a : A) (decision : policy h = .inr a) (legal : E.legal past a)
      (next : CorrectRun E policy s ((a,E.response s a)::h) (a::past)) :
      CorrectRun E policy s h past

lemma correct_at_stop (E : Experiment S A (O → ℝ) T (List A))
    (policy : Policy A O T) (s : S) (h : History A (O → ℝ)) (past : List A)
    (run : CorrectRun E policy s h past) (q : T) (hd : policy h = .inl q) :
    E.target s = q := by
  cases run with
  | stop q' hd' hc =>
      have he : q' = q := Sum.inl.inj (hd'.symm.trans hd)
      exact hc.trans he
  | ask a hd' _ _ => simp [hd] at hd'

lemma correct_after_ask (E : Experiment S A (O → ℝ) T (List A))
    (policy : Policy A O T) (s : S) (h : History A (O → ℝ)) (past : List A)
    (run : CorrectRun E policy s h past) (a : A) (hd : policy h = .inr a) :
    CorrectRun E policy s ((a,E.response s a)::h) (a::past) := by
  cases run with
  | stop q hd' _ => simp [hd] at hd'
  | ask a' hd' _ hn =>
      have he : a' = a := Sum.inr.inj (hd'.symm.trans hd)
      subst a'
      exact hn

def Determined (E : Experiment S A (O → ℝ) T (List A)) (base : S → V)
    (L : Submodule ℝ (Module.Dual ℝ V)) (h : History A (O → ℝ)) : Prop :=
  ∀ s t, Consistent E h s → Consistent E h t →
    ∀ f ∈ L, f (base s) = f (base t)

def equalizer (v w : V) : Submodule ℝ (Module.Dual ℝ V) where
  carrier := {f | f v = f w}
  zero_mem' := rfl
  add_mem' := by intro f g hf hg; simp only [Set.mem_setOf_eq,LinearMap.add_apply] at *; rw [hf,hg]
  smul_mem' := by intro c f hf; simp only [Set.mem_setOf_eq,LinearMap.smul_apply] at *; rw [hf]

variable (E : Experiment S A (O → ℝ) T (List A)) (base : S → V)
variable (linear : A → O → Module.Dual ℝ V) (offset : A → O → ℝ)
variable (affine : ∀ s a o, E.response s a o = linear a o (base s) + offset a o)

include affine in
lemma redundant_response_unique (L : Submodule ℝ (Module.Dual ℝ V))
    (h : History A (O → ℝ)) (hd : Determined E base L h)
    (a : A) (ha : ∀ o, linear a o ∈ L) (s t : S)
    (hs : Consistent E h s) (ht : Consistent E h t) :
    E.response s a = E.response t a := by
  funext o
  rw [affine,affine,hd s t hs ht (linear a o) (ha o)]

include affine in
lemma determined_extend (L : Submodule ℝ (Module.Dual ℝ V))
    (h : History A (O → ℝ)) (hd : Determined E base L h) (a : A) (y : O → ℝ) :
    Determined E base (L ⊔ Submodule.span ℝ (Set.range (linear a))) ((a,y)::h) := by
  intro s t hs ht
  have hs' := (consistent_extend E h s a y).mp hs
  have ht' := (consistent_extend E h t a y).mp ht
  have heq : L ⊔ Submodule.span ℝ (Set.range (linear a)) ≤ equalizer (base s) (base t) := by
    apply sup_le
    · intro f hf
      exact hd s t hs'.1 ht'.1 f hf
    · apply Submodule.span_le.mpr
      rintro f ⟨o,rfl⟩
      change linear a o (base s) = linear a o (base t)
      have he := congrFun (hs'.2.trans ht'.2.symm) o
      rw [affine,affine] at he
      exact add_right_cancel he
  exact fun f hf => heq hf

/-- A virtual prefix of redundant calls ends at an informative call whenever
the current version set still contains different targets. -/
structure InformativeStep (policy : Policy A O T)
    (L : Submodule ℝ (Module.Dual ℝ V)) (h : History A (O → ℝ)) (past : List A) where
  virtualHistory : History A (O → ℝ)
  virtualPast : List A
  action : A
  sameSources : ∀ s, Consistent E h s ↔ Consistent E virtualHistory s
  physicalLegal : E.legal past action
  pathSublist : past.Sublist virtualPast
  informative : ∃ o, linear action o ∉ L
  continuation : ∀ s, Consistent E virtualHistory s →
    CorrectRun E policy s ((action,E.response s action)::virtualHistory) (action::virtualPast)

include affine in
lemma first_informative (policy : Policy A O T)
    (deletion : ∀ {small large : List A}, small.Sublist large →
      ∀ a, E.legal large a → E.legal small a)
    (L : Submodule ℝ (Module.Dual ℝ V))
    (physical virtual : History A (O → ℝ)) (past virtualPast : List A)
    (hd : Determined E base L physical) (hn : ¬ Homogeneous E physical)
    (same : ∀ s, Consistent E physical s ↔ Consistent E virtual s)
    (sub : past.Sublist virtualPast)
    (total : ∀ s, Consistent E virtual s → CorrectRun E policy s virtual virtualPast)
    (s₀ : S) (hs₀ : Consistent E physical s₀)
    (run : CorrectRun E policy s₀ virtual virtualPast) :
    Nonempty (InformativeStep E linear policy L physical past) := by
  classical
  induction run generalizing physical past L with
  | stop q decision correct =>
    exfalso
    apply hn
    intro s t hs ht
    exact (correct_at_stop E policy s _ _ (total s ((same s).mp hs)) q decision).trans
      (correct_at_stop E policy t _ _ (total t ((same t).mp ht)) q decision).symm
  | @ask virtual virtualPast a decision legal next ih =>
    by_cases info : ∃ o, linear a o ∉ L
    · exact ⟨⟨virtual,virtualPast,a,same,deletion sub a legal,sub,info,
        fun s hs => correct_after_ask E policy s _ _ (total s hs) a decision⟩⟩
    · have hr : ∀ o, linear a o ∈ L := by simpa only [not_exists,not_not] using info
      have newSame : ∀ s, Consistent E physical s ↔
          Consistent E ((a,E.response s₀ a)::virtual) s := by
        intro s
        rw [consistent_extend]
        constructor
        · intro hs
          exact ⟨(same s).mp hs,redundant_response_unique E base linear offset affine
            L physical hd a hr s s₀ hs hs₀⟩
        · exact fun hs => (same s).mpr hs.1
      have newTotal : ∀ s, Consistent E ((a,E.response s₀ a)::virtual) s →
          CorrectRun E policy s ((a,E.response s₀ a)::virtual) (a::virtualPast) := by
        intro s hs
        have he := (consistent_extend E virtual s a _).mp hs
        have ht := correct_after_ask E policy s _ _ (total s he.1) a decision
        rw [he.2] at ht
        exact ht
      exact ih (physical := physical) (past := past) (L := L)
        hd hn newSame (sub.cons a) newTotal hs₀

variable [FiniteDimensional ℝ V]

include affine in
theorem total_strategy_wins_with_rank_budget (policy : Policy A O T)
    (deletion : ∀ {small large : List A}, small.Sublist large →
      ∀ a, E.legal large a → E.legal small a)
    (update : ∀ past a, E.update past a = a::past)
    (d : Nat) (L : Submodule ℝ (Module.Dual ℝ V))
    (physical virtual : History A (O → ℝ)) (past virtualPast : List A)
    (capacity : Module.finrank ℝ (Module.Dual ℝ V) ≤ Module.finrank ℝ L + d)
    (hd : Determined E base L physical)
    (same : ∀ s, Consistent E physical s ↔ Consistent E virtual s)
    (sub : past.Sublist virtualPast)
    (total : ∀ s, Consistent E virtual s → CorrectRun E policy s virtual virtualPast) :
    Winning E d physical past := by
  classical
  induction d using Nat.strong_induction_on generalizing L physical virtual past virtualPast with
  | h d ih =>
    by_cases homogeneous : Homogeneous E physical
    · cases d with
      | zero => exact homogeneous
      | succ d => exact Or.inl homogeneous
    · have inhabited : ∃ s, Consistent E physical s := by
        by_contra hempty
        apply homogeneous
        intro s t hs ht
        exact (hempty ⟨s,hs⟩).elim
      obtain ⟨s₀,hs₀⟩ := inhabited
      obtain ⟨step⟩ := first_informative E base linear offset affine policy deletion L
        physical virtual past virtualPast hd homogeneous same sub total s₀ hs₀
        (total s₀ ((same s₀).mp hs₀))
      let L' := L ⊔ Submodule.span ℝ (Set.range (linear step.action))
      have strict : L < L' := by
        apply lt_of_le_of_ne le_sup_left
        intro he
        obtain ⟨o,ho⟩ := step.informative
        apply ho
        exact (congrArg (fun M : Submodule ℝ (Module.Dual ℝ V) =>
          linear step.action o ∈ M) he).mpr
          (Submodule.mem_sup_right (Submodule.subset_span ⟨o,rfl⟩))
      have grows := Submodule.finrank_lt_finrank_of_lt strict
      have bounded := Submodule.finrank_le L'
      cases d with
      | zero => omega
      | succ n =>
        apply Or.inr
        refine ⟨step.action,step.physicalLegal,?_⟩
        intro y
        rw [update]
        apply ih n (Nat.lt_succ_self n) L' ((step.action,y)::physical)
          ((step.action,y)::step.virtualHistory) (step.action::past) (step.action::step.virtualPast)
        · omega
        · exact determined_extend E base linear offset affine L physical hd step.action y
        · intro s
          simp only [consistent_extend,step.sameSources]
        · exact step.pathSublist.cons_cons step.action
        · intro s hs
          have he := (consistent_extend E step.virtualHistory s step.action y).mp hs
          have ht := step.continuation s he.1
          rw [he.2] at ht
          exact ht

include affine in
/-- Full F1 semantic horizon implication, with pointwise totality and concrete
physical legality preserved under deletion. This does not extract an effective
simulator, decide its span tests, or prove the separate CAD selection endpoint.
The subspace starts at bottom and is extended ONLY by physically queried
coefficient rows. No extra affine forms inferred from nonlinear source
constraints are inserted; affine offsets are subtracted in determined_extend. -/
theorem pointwise_total_strategy_has_finite_informative_horizon (policy : Policy A O T)
    (deletion : ∀ {small large : List A}, small.Sublist large →
      ∀ a, E.legal large a → E.legal small a)
    (update : ∀ past a, E.update past a = a::past)
    (total : ∀ s, E.admitted s → CorrectRun E policy s [] []) :
    Winning E (Module.finrank ℝ V) [] [] := by
  apply total_strategy_wins_with_rank_budget E base linear offset affine policy deletion update
    (Module.finrank ℝ V) ⊥ [] [] [] []
  · simp [Subspace.dual_finrank_eq]
  · intro s t hs ht f hf
    have hf0 : f = 0 := (Submodule.mem_bot ℝ).mp hf
    simp [hf0]
  · intro s; rfl
  · exact List.Sublist.refl []
  · intro s hs
    exact total s hs.1

end GProgram.G7.ExactLawRankCompression


/-!
Semantic resource adapter for finite unions of the EXISTING path budgets,
with optional permitted original row/site sets. No new solver, programme
semantics, source oracle or Rust mutation/parser refinement is supplied.
-/
namespace Astra.G7FinitePathBudgetBridge

open GProgram.G7.ExactLawResourceGame

variable {A Row Site Region : Type*}
variable [DecidableEq A] [DecidableEq Row] [DecidableEq Site] [DecidableEq Region]
variable [Fintype Row] [Fintype Site]

def permitted {ι : Type*} [Fintype ι] (allowed : Option (Finset ι)) : Finset ι :=
  allowed.getD Finset.univ

def RegionFits (support : A → Finset Row) (sites : Row → Finset Site)
    (budget : Budget) (allowedRows : Option (Finset Row))
    (allowedSites : Option (Finset Site)) (path : List A) : Prop :=
  WithinBudget support sites budget path ∧
    usedRows support path ⊆ permitted allowedRows ∧
    usedSites support sites path ⊆ permitted allowedSites

def WithinRegions (support : A → Finset Row) (sites : Row → Finset Site)
    (regions : Finset Region) (budget : Region → Budget)
    (allowedRows : Region → Option (Finset Row))
    (allowedSites : Region → Option (Finset Site)) (path : List A) : Prop :=
  ∃ i ∈ regions, RegionFits support sites (budget i) (allowedRows i) (allowedSites i) path

theorem usedSites_sublist (support : A → Finset Row) (sites : Row → Finset Site)
    {small large : List A} (h : small.Sublist large) :
    usedSites support sites small ⊆ usedSites support sites large := by
  intro site hs
  obtain ⟨r,hr,hs⟩ := Finset.mem_biUnion.mp hs
  exact Finset.mem_biUnion.mpr ⟨r,usedRows_sublist support h hr,hs⟩

theorem regionFits_deletion_closed (support : A → Finset Row) (sites : Row → Finset Site)
    (budget : Budget) (allowedRows : Option (Finset Row))
    (allowedSites : Option (Finset Site)) {small large : List A}
    (h : small.Sublist large)
    (hf : RegionFits support sites budget allowedRows allowedSites large) :
    RegionFits support sites budget allowedRows allowedSites small := by
  exact ⟨trajectory_budget_deletion_closed support sites budget h hf.1,
    (usedRows_sublist support h).trans hf.2.1,
    (usedSites_sublist support sites h).trans hf.2.2⟩

variable (support : A → Finset Row) (sites : Row → Finset Site)
variable (regions : Finset Region) (budget : Region → Budget)
variable (allowedRows : Region → Option (Finset Row))
variable (allowedSites : Region → Option (Finset Site))

theorem finite_union_deletion_closed {small large : List A}
    (h : small.Sublist large)
    (hf : WithinRegions support sites regions budget allowedRows allowedSites large) :
    WithinRegions support sites regions budget allowedRows allowedSites small := by
  obtain ⟨i,hi,hfit⟩ := hf
  exact ⟨i,hi,regionFits_deletion_closed support sites (budget i)
    (allowedRows i) (allowedSites i) h hfit⟩

/-- The exact physical legality premise consumed by the retained rank proof. -/
theorem next_action_legal_deletion {small large : List A}
    (h : small.Sublist large) (a : A)
    (ha : WithinRegions support sites regions budget allowedRows allowedSites (a::large)) :
    WithinRegions support sites regions budget allowedRows allowedSites (a::small) :=
  finite_union_deletion_closed support sites regions budget allowedRows allowedSites
    (h.cons_cons a) ha

/-- Semantic maximum over currently fitting regions. This is not a native
callable or proof of the BTreeSet implementation. -/
noncomputable def remainingCalls (path : List A) : Nat := by
  classical
  exact regions.sup (fun i =>
    if RegionFits support sites (budget i) (allowedRows i) (allowedSites i) path
    then (budget i).calls - path.length else 0)

theorem extension_call_bound {past future : List A} (hsub : past.Sublist future)
    (hf : WithinRegions support sites regions budget allowedRows allowedSites future) :
    future.length ≤ past.length + remainingCalls support sites regions budget
      allowedRows allowedSites past := by
  classical
  obtain ⟨i,hi,hfit⟩ := hf
  have hp := regionFits_deletion_closed support sites (budget i)
    (allowedRows i) (allowedSites i) hsub hfit
  have hc := hfit.1.2.2
  have hl := hsub.length_le
  have hm : (budget i).calls - past.length ≤ remainingCalls support sites regions budget
      allowedRows allowedSites past := by
    unfold remainingCalls
    simpa only [if_pos hp] using (Finset.le_sup (f := fun j =>
      if RegionFits support sites (budget j) (allowedRows j) (allowedSites j) past
      then (budget j).calls - past.length else 0) hi)
  omega

theorem zero_remaining_no_legal_action (past : List A)
    (hz : remainingCalls support sites regions budget allowedRows allowedSites past = 0) :
    ∀ a, ¬ WithinRegions support sites regions budget allowedRows allowedSites (a::past) := by
  intro a ha
  have h := extension_call_bound support sites regions budget allowedRows allowedSites
    ((List.Sublist.refl past).cons a) ha
  simp only [List.length_cons] at h
  omega

end Astra.G7FinitePathBudgetBridge


/-!
Compose the retained exact-law game/rank theorem with the finite union of
original path budgets. This proves a semantic horizon cap, not a Rust AST,
physical prefix, original source/QE supplier or effective policy refinement.
-/
namespace Astra.G7FinitePathGame

open GProgram.G7.ExactLawResourceGame GProgram.G7.ExactLawRankCompression
open Astra.G7FinitePathBudgetBridge

variable {S A Y T R Row Site Region : Type*}
variable [DecidableEq A] [DecidableEq Row] [DecidableEq Site] [DecidableEq Region]
variable [Fintype Row] [Fintype Site]

theorem homogeneous_winning (E : Experiment S A Y T R)
    {h : History A Y} (hh : Homogeneous E h) (n : Nat) (u : R) :
    Winning E n h u := by
  cases n with
  | zero => exact hh
  | succ n => exact Or.inl hh

theorem winning_mono (E : Experiment S A Y T R) {m n : Nat}
    {h : History A Y} {u : R} (hmn : m ≤ n) (hw : Winning E m h u) :
    Winning E n h u := by
  induction m generalizing n h u with
  | zero => exact homogeneous_winning E hw n u
  | succ m ih =>
    cases n with
    | zero => omega
    | succ n =>
      rcases hw with hh | ⟨a,ha,hy⟩
      · exact Or.inl hh
      · exact Or.inr ⟨a,ha,fun y => ih (Nat.le_of_succ_le_succ hmn) (hy y)⟩

/-- A decreasing physical call potential caps the whole game, including
arbitrary response branches; Homogeneous still permits immediate stopping. -/
theorem winning_iff_call_cap (E : Experiment S A Y T R) (potential : R → Nat)
    (decrease : ∀ u a, E.legal u a → potential (E.update u a) < potential u)
    (n : Nat) (h : History A Y) (u : R) :
    Winning E n h u ↔ Winning E (min n (potential u)) h u := by
  constructor
  · intro hw
    induction n generalizing h u with
    | zero => simpa using hw
    | succ n ih =>
      rcases hw with hh | ⟨a,ha,hy⟩
      · exact homogeneous_winning E hh _ _
      · have hd := decrease u a ha
        have hcap : min (n+1) (potential u) = min n (potential u-1)+1 := by omega
        rw [hcap]
        apply Or.inr
        refine ⟨a,ha,fun y => ?_⟩
        apply winning_mono E (m := min n (potential (E.update u a)))
        · omega
        · exact ih ((a,y)::h) (E.update u a) (hy y)
  · intro hw
    exact winning_mono E (Nat.min_le_left _ _) hw

variable (support : A → Finset Row) (sites : Row → Finset Site)
variable (regions : Finset Region) (budget : Region → Budget)
variable (allowedRows : Region → Option (Finset Row))
variable (allowedSites : Region → Option (Finset Site))

theorem remaining_after_legal (past : List A) (a : A)
    (ha : WithinRegions support sites regions budget allowedRows allowedSites (a::past)) :
    remainingCalls support sites regions budget allowedRows allowedSites (a::past) <
      remainingCalls support sites regions budget allowedRows allowedSites past := by
  classical
  let r := remainingCalls support sites regions budget allowedRows allowedSites past
  have hpos : 0 < r := by
    have h := extension_call_bound support sites regions budget allowedRows allowedSites
      ((List.Sublist.refl past).cons a) ha
    simp only [List.length_cons] at h
    change past.length+1 ≤ past.length+r at h
    omega
  have hle : remainingCalls support sites regions budget allowedRows allowedSites (a::past)
      ≤ r-1 := by
    change regions.sup (fun i =>
      if RegionFits support sites (budget i) (allowedRows i) (allowedSites i) (a::past)
      then (budget i).calls - (a::past).length else 0) ≤ r-1
    apply Finset.sup_le
    intro i hi
    split_ifs with hf
    · have hp := regionFits_deletion_closed support sites (budget i)
        (allowedRows i) (allowedSites i) ((List.Sublist.refl past).cons a) hf
      have hm : (budget i).calls - past.length ≤ r := by
        dsimp only [r,remainingCalls]
        simpa only [if_pos hp] using (Finset.le_sup (f := fun j =>
          if RegionFits support sites (budget j) (allowedRows j) (allowedSites j) past
          then (budget j).calls-past.length else 0) hi)
      have hc := hf.1.2.2
      simp only [List.length_cons] at hc ⊢
      omega
    · omega
  change _ < r
  omega

/-- Keep the supplied admitted sources/targets/responses, replace only the
resource contract with the declared finite union of original path budgets. -/
def withRegions (E : Experiment S A Y T R) (allowed : A → Prop) :
    Experiment S A Y T (List A) where
  admitted := E.admitted
  target := E.target
  response := E.response
  legal := fun past a => allowed a ∧
    WithinRegions support sites regions budget allowedRows allowedSites (a::past)
  update := fun past a => a::past

theorem regional_legal_deletion (E : Experiment S A Y T R) (allowed : A → Prop)
    {small large : List A} (h : small.Sublist large) (a : A)
    (ha : (withRegions support sites regions budget allowedRows allowedSites E allowed).legal large a) :
    (withRegions support sites regions budget allowedRows allowedSites E allowed).legal small a := by
  exact ⟨ha.1,next_action_legal_deletion support sites regions budget
    allowedRows allowedSites h a ha.2⟩

theorem regional_winning_iff_capped (E : Experiment S A Y T R) (allowed : A → Prop)
    (n : Nat) (h : History A Y) (past : List A) :
    Winning (withRegions support sites regions budget allowedRows allowedSites E allowed) n h past ↔
      Winning (withRegions support sites regions budget allowedRows allowedSites E allowed)
        (min n (remainingCalls support sites regions budget allowedRows allowedSites past)) h past := by
  apply winning_iff_call_cap
  intro past a ha
  exact remaining_after_legal support sites regions budget allowedRows allowedSites past a ha.2

variable {O V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Pointwise totality starts at the exact supplied free history and physical
past. Legal/reachable-prefix admission and actual affine programme semantics
are separate suppliers; this theorem does not infer them from a query value. -/
theorem total_policy_capped_at_history (E : Experiment S A (O → ℝ) T R)
    (allowed : A → Prop) (base : S → V) (linear : A → O → Module.Dual ℝ V)
    (offset : A → O → ℝ)
    (affine : ∀ s a o, E.response s a o = linear a o (base s)+offset a o)
    (policy : Policy A O T) (h : History A (O → ℝ)) (past : List A)
    (total : ∀ s, Consistent
      (withRegions support sites regions budget allowedRows allowedSites E allowed) h s →
      CorrectRun (withRegions support sites regions budget allowedRows allowedSites E allowed)
        policy s h past) :
    Winning (withRegions support sites regions budget allowedRows allowedSites E allowed)
      (min (Module.finrank ℝ V)
        (remainingCalls support sites regions budget allowedRows allowedSites past)) h past := by
  apply (regional_winning_iff_capped support sites regions budget allowedRows allowedSites
    E allowed (Module.finrank ℝ V) h past).mp
  apply total_strategy_wins_with_rank_budget
    (withRegions support sites regions budget allowedRows allowedSites E allowed)
    base linear offset affine policy
    (fun hs a ha => regional_legal_deletion support sites regions budget
      allowedRows allowedSites E allowed hs a ha)
    (fun _ _ => rfl) (Module.finrank ℝ V) ⊥ h h past past
  · simp [Subspace.dual_finrank_eq]
  · intro s t hs ht f hf
    have hf0 : f = 0 := (Submodule.mem_bot ℝ).mp hf
    simp [hf0]
  · intro s; rfl
  · exact List.Sublist.refl past
  · exact total

theorem capped_loss_excludes_total_policy (E : Experiment S A (O → ℝ) T R)
    (allowed : A → Prop) (base : S → V) (linear : A → O → Module.Dual ℝ V)
    (offset : A → O → ℝ)
    (affine : ∀ s a o, E.response s a o = linear a o (base s)+offset a o)
    (h : History A (O → ℝ)) (past : List A)
    (loss : ¬ Winning (withRegions support sites regions budget allowedRows allowedSites E allowed)
      (min (Module.finrank ℝ V)
        (remainingCalls support sites regions budget allowedRows allowedSites past)) h past) :
    ¬ ∃ policy : Policy A O T, ∀ s, Consistent
      (withRegions support sites regions budget allowedRows allowedSites E allowed) h s →
      CorrectRun (withRegions support sites regions budget allowedRows allowedSites E allowed)
        policy s h past := by
  rintro ⟨policy,total⟩
  exact loss (total_policy_capped_at_history support sites regions budget allowedRows allowedSites
    E allowed base linear offset affine policy h past total)

end Astra.G7FinitePathGame
