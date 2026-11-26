import G7FinitePathBudgetBridge
import G7ExactLawRankCompression

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
