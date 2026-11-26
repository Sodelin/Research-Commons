import G7ExactLawResourceGame

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
