import G7ExactLawResourceGame
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! F1 proof-level compression of pointwise-total exact-law reset strategies.
The virtual transcript remains intact. Redundant calls are skipped physically;
their uniquely determined responses are still fed to the original policy.
Termination of a run of virtual calls uses one compatible source only as a
proof witness. It does not add a source oracle to the physical experiment.
Attribution: GPT-6 Astra Pro's accepted original G7 F1 argument (2026-10-01);
formalization draft by dot / OpenAI (2026-10-10).
DRAFT: uncompiled and unreviewed. No effective extraction/QE claim. -/
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

lemma redundant_response_unique (L : Submodule ℝ (Module.Dual ℝ V))
    (h : History A (O → ℝ)) (hd : Determined E base L h)
    (a : A) (ha : ∀ o, linear a o ∈ L) (s t : S)
    (hs : Consistent E h s) (ht : Consistent E h t) :
    E.response s a = E.response t a := by
  funext o
  rw [affine,affine,hd s t hs ht (linear a o) (ha o)]

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
        rw [he]
        exact le_sup_right (Submodule.subset_span ⟨o,rfl⟩)
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
    have hf0 : f = 0 := Submodule.mem_bot.mp hf
    simp [hf0]
  · intro s; rfl
  · exact List.Sublist.refl []
  · intro s hs
    exact total s hs.1

end GProgram.G7.ExactLawRankCompression
