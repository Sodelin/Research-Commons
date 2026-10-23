/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Actual TM2 time-to-tape-length bound for a fixed finite program. A TM2
transition executes an entire nested Stmt, so ONE push per transition is
NOT assumed. Pinned definitions read: mathlib StackTuringMachine.lean,
0df444a360eaa60ab8c11dca51a86af692955474, blob 916694942a3bfefa0bd9085e2f48735dbe8e0f5b;
Lax218471 Subroutine and proof-side Runs, 7fadbfd005b359a66ccc1165b2d1becddb2906b8.
The source lemma counts private and public tapes, on every actual path.

Historical independent source, retained rather than deleted. Subsequent
primary-source comparison found the same push/run principle in the pinned
Lax218471Proofs.OutputBounds (blob e9a4fb8de36a17b85e17bf4c9ab9d06a598362a6),
which credits Lax759944Proofs.TMToRam.Safety. The active finite restricted
verifier now uses that prior theorem through PolytomyRoutineOutputBoundAdapter;
the greater nonfinite-caller generality here is not required by its endpoint.
No historical novelty, execution or theorem acceptance is claimed here.
-/
import PolytomyRestrictedVerifierOriginalSemantics

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471Proofs

variable {K Λ σ : Type} {Γ : K → Type}

/-- Maximum pushes along a branch of this single finite statement. -/
def statementPushCap : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => statementPushCap q + 1
  | .peek _ _ q => statementPushCap q
  | .pop _ _ q => statementPushCap q
  | .load _ q => statementPushCap q
  | .branch _ q r => max (statementPushCap q) (statementPushCap r)
  | .goto _ => 0
  | .halt => 0

theorem statement_stack_bound [DecidableEq K] (q : TM2.Stmt Γ Λ σ)
    (v : σ) (stk : ∀ k, List (Γ k)) (M : ℕ) (hs : ∀ k, (stk k).length ≤ M) :
    ∀ k, ((TM2.stepAux q v stk).stk k).length ≤ M + statementPushCap q := by
  induction q generalizing v stk M with
  | push k f q ih =>
      have hb : ∀ j, ((Function.update stk k (f v :: stk k)) j).length ≤ M + 1 := by
        intro j
        by_cases hj : j = k
        · subst j
          simpa using Nat.add_le_add_right (hs k) 1
        · simpa [Function.update_of_ne hj] using (show (stk j).length ≤ M + 1 by have h := hs j; omega)
      have ht := ih v _ (M + 1) hb
      intro j
      simpa only [TM2.stepAux, statementPushCap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht j
  | peek k f q ih => exact ih _ _ M hs
  | pop k f q ih =>
      have hb : ∀ j, ((Function.update stk k (stk k).tail) j).length ≤ M := by
        intro j
        by_cases hj : j = k
        · subst j
          have hk := hs k
          cases h : stk k <;> simp_all
        · simpa [Function.update_of_ne hj] using hs j
      exact ih _ _ M hb
  | load f q ih => exact ih _ _ M hs
  | branch f q r ihq ihr =>
      cases hf : f v with
      | false =>
          intro j
          have h := ihr v stk M hs j
          have hm := Nat.le_max_right (statementPushCap q) (statementPushCap r)
          simpa [TM2.stepAux, hf, statementPushCap] using
            h.trans (Nat.add_le_add_left hm M)
      | true =>
          intro j
          have h := ihq v stk M hs j
          have hm := Nat.le_max_left (statementPushCap q) (statementPushCap r)
          simpa [TM2.stepAux, hf, statementPushCap] using
            h.trans (Nat.add_le_add_left hm M)
  | goto f => simpa only [TM2.stepAux, statementPushCap, Nat.add_zero] using hs
  | halt => simpa only [TM2.stepAux, statementPushCap, Nat.add_zero] using hs

def listMaximum : List ℕ → ℕ
  | [] => 0
  | n :: ns => max n (listMaximum ns)

theorem member_le_listMaximum (ns : List ℕ) (n : ℕ) (hn : n ∈ ns) : n ≤ listMaximum ns := by
  induction ns with
  | nil => simp at hn
  | cons a ns ih =>
      rcases List.mem_cons.mp hn with h | h
      · subst n
        exact Nat.le_max_left _ _
      · exact (ih h).trans (Nat.le_max_right _ _)

/-- A finite code-dependent constant, not a number supplied by the input.
It is the maximum syntactic push count over the fixed label inventory. -/
noncomputable def codePushCap [Fintype Λ] (code : Λ → TM2.Stmt Γ Λ σ) : ℕ :=
  listMaximum ((Finset.univ : Finset Λ).toList.map (fun l => statementPushCap (code l)))

theorem statementPushCap_le_code [Fintype Λ] (code : Λ → TM2.Stmt Γ Λ σ) (l : Λ) :
    statementPushCap (code l) ≤ codePushCap code := by
  classical
  apply member_le_listMaximum
  exact List.mem_map.mpr ⟨l, by simp, rfl⟩

theorem step_stack_bound [DecidableEq K] [Fintype Λ]
    (code : Λ → TM2.Stmt Γ Λ σ) (a b : TM2.Cfg Γ Λ σ) (M : ℕ)
    (ha : ∀ k, (a.stk k).length ≤ M) (he : TM2.step code a = some b) :
    ∀ k, (b.stk k).length ≤ M + codePushCap code := by
  rcases a with ⟨label, v, stk⟩
  cases label with
  | none => simp [TM2.step] at he
  | some l =>
      have hb : TM2.stepAux (code l) v stk = b := Option.some.inj he
      rw [← hb]
      intro k
      exact (statement_stack_bound (code l) v stk M ha k).trans
        (Nat.add_le_add_left (statementPushCap_le_code code l) M)

theorem runs_stack_bound [DecidableEq K] [Fintype Λ]
    (code : Λ → TM2.Stmt Γ Λ σ) (a b : TM2.Cfg Γ Λ σ) (n M : ℕ)
    (he : Runs (TM2.step code) a b n) (ha : ∀ k, (a.stk k).length ≤ M) :
    ∀ k, (b.stk k).length ≤ M + codePushCap code * n := by
  induction he generalizing M with
  | refl a => simpa using ha
  | @cons a b c n hab hbc ih =>
      have hb := step_stack_bound code a b M ha hab
      have hc := ih (M + codePushCap code) hb
      intro k
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc k

/-- The routine boundary has EMPTY private tapes at both ends. All its
private intermediate tapes were nevertheless included in the induction.
No success/validity promise appears in this all-path resource theorem. -/
theorem routine_executes_stack_bound [DecidableEq K]
    (p : Routine Γ σ) (s t : Store Γ σ) (n M : ℕ)
    (he : p.Executes s t n) (hs : ∀ k, (s.stk k).length ≤ M) :
    ∀ k, (t.stk k).length ≤ M + codePushCap p.code * n := by
  have hr : Runs (TM2.step p.code) (p.boundary (some p.entry) s) (p.boundary none t) n :=
    Runs.of_iterate he
  have hb : ∀ j, ((p.boundary (some p.entry) s).stk j).length ≤ M := by
    intro j
    cases j with
    | inl k => exact hs k
    | inr w => exact Nat.zero_le M
  have hout := runs_stack_bound p.code _ _ n M hr hb
  intro k
  exact hout (.inl k)

theorem cleanupMass_uniform_bound {K F : Type} [DecidableEq K]
    (ks : List K) (s : CountdownStore K F) (M : ℕ)
    (hs : ∀ k, (s.stk k).length ≤ M) : cleanupMass ks s ≤ ks.length * M := by
  induction ks with
  | nil => simp [cleanupMass]
  | cons k ks ih =>
      have hk := hs k
      simp only [cleanupMass, List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul] at *
      omega

end PolytomyReductionModel.WholeVerifierController
