import G7ExactLawSourceTransfer
import Mathlib.Data.Real.Basic

/-!
Terminal-result semantics for the existing supplied source-family frontend.
The native use takes Case = Fin model_count. Each source retains its case and
ONE real parameter bank throughout the whole history. Constants are fixed in
the supplied domain/response functions before these definitions are used.
This does not prove native AST evaluation, source/action coverage, a backend
result's origin or an effective selector. Representation remains the existing
two-sided physical-source contract, not a new admission flag.
-/
namespace Astra.G7FiniteTargetReceiver

open GProgram.G7.ExactLawResourceGame
open Astra.G7ExactLawSourceTransfer

variable {Case A Y T R S : Type*}

structure Family (Case A Y T R : Type*) where
  parameterCount : Case → Nat
  domain : (i : Case) → (Fin (parameterCount i) → ℝ) → Prop
  target : Case → T
  response : (i : Case) → (Fin (parameterCount i) → ℝ) → A → Y
  legal : R → A → Prop
  update : R → A → R

abbrev Source (F : Family Case A Y T R) :=
  Σ i : Case, (Fin (F.parameterCount i) → ℝ)

def experiment (F : Family Case A Y T R) : Experiment (Source F) A Y T R where
  admitted s := F.domain s.1 s.2
  target s := F.target s.1
  response s a := F.response s.1 s.2 a
  legal := F.legal
  update := F.update

def Fits (F : Family Case A Y T R) (h : History A Y)
    (i : Case) (x : Fin (F.parameterCount i) → ℝ) : Prop :=
  F.domain i x ∧ ∀ ay ∈ h, F.response i x ay.1 = ay.2

def Reachable (F : Family Case A Y T R) (h : History A Y) : Prop :=
  ∃ i x, Fits F h i x

def TargetClause (F : Family Case A Y T R) (h : History A Y) (q : T) : Prop :=
  ∀ i x, Fits F h i x → F.target i = q

/-- This is the new native target query's intended per-piece meaning:
exclude EVERY different-tag piece with ONE bank fitting the ENTIRE history. -/
def OtherTargetsExcluded (F : Family Case A Y T R) (h : History A Y)
    (q : T) : Prop :=
  ∀ i, F.target i ≠ q → ¬ ∃ x, Fits F h i x

/-- These are the ACTUAL constant/prefix predicates at the exact free values.
The declaration supplies no proof that native query syntax denotes them. -/
def GuardedTarget (constantsValid prefixLegal : Prop)
    (F : Family Case A Y T R) (h : History A Y) (q : T) : Prop :=
  constantsValid ∧ prefixLegal ∧ TargetClause F h q

theorem consistent_piece (F : Family Case A Y T R) (h : History A Y)
    (i : Case) (x : Fin (F.parameterCount i) → ℝ) :
    Consistent (experiment F) h ⟨i,x⟩ ↔ Fits F h i x := Iff.rfl

theorem reachable_iff_consistent_source (F : Family Case A Y T R)
    (h : History A Y) :
    Reachable F h ↔ ∃ s : Source F, Consistent (experiment F) h s := by
  constructor
  · rintro ⟨i,x,hx⟩
    exact ⟨⟨i,x⟩,hx⟩
  · rintro ⟨⟨i,x⟩,hx⟩
    exact ⟨i,x,hx⟩

/-- A positive target clause certifies this SAME stop label, rather than
merely the existence of an unspecified homogeneous label. -/
theorem target_clause_iff_valid_stop (F : Family Case A Y T R)
    (h : History A Y) (q : T) (n : Nat) (u : R) :
    TargetClause F h q ↔ Valid (experiment F) (Plan.stop (n := n) q) h u := by
  constructor
  · intro hq s hs
    exact hq s.1 s.2 hs
  · intro hq i x hx
    exact hq ⟨i,x⟩ hx

theorem target_clause_iff_exclusions (F : Family Case A Y T R)
    (h : History A Y) (q : T) :
    TargetClause F h q ↔ OtherTargetsExcluded F h q := by
  classical
  constructor
  · intro hq i hi hx
    obtain ⟨x,hx⟩ := hx
    exact hi (hq i x hx)
  · intro he i x hx
    by_cases hi : F.target i = q
    · exact hi
    · exact (he i hi ⟨x,hx⟩).elim

/-- Specialize the universally guarded constant tuple ONCE, before all
piece/bank/history equations. Root uniqueness or native syntax is not proved
by this elementary implication; those retain their original obligations. -/
theorem target_of_shared_constant_guard {C : Type*}
    (families : C → Family Case A Y T R) (roots : C → Prop)
    (c : C) (hc : roots c) (h : History A Y) (q : T)
    (he : ∀ c', roots c' → OtherTargetsExcluded (families c') h q) :
    TargetClause (families c) h q :=
  (target_clause_iff_exclusions (families c) h q).mpr (he c hc)

theorem reachable_target_unique (F : Family Case A Y T R)
    (h : History A Y) (hr : Reachable F h) (q r : T)
    (hq : TargetClause F h q) (hr' : TargetClause F h r) : q = r := by
  obtain ⟨i,x,hx⟩ := hr
  exact (hq i x hx).symm.trans (hr' i x hx)

theorem reachable_homogeneous_unique_target (F : Family Case A Y T R)
    (h : History A Y) (hr : Reachable F h)
    (hh : Homogeneous (experiment F) h) : ∃! q, TargetClause F h q := by
  obtain ⟨i,x,hx⟩ := hr
  refine ⟨F.target i,?_,?_⟩
  · intro j y hy
    exact hh ⟨j,y⟩ ⟨i,x⟩ hy hx
  · intro q hq
    exact (hq i x hx).symm

/-- A vacuous target clause is not a witness of a reachable physical source. -/
theorem unreachable_all_targets (F : Family Case A Y T R)
    (h : History A Y) (hn : ¬ Reachable F h) : ∀ q, TargetClause F h q := by
  intro q i x hx
  exact (hn ⟨i,x,hx⟩).elim

theorem empty_cases_unreachable [IsEmpty Case] (F : Family Case A Y T R)
    (h : History A Y) : ¬ Reachable F h := by
  rintro ⟨i,x,hx⟩
  exact isEmptyElim i

/-- Actual target identification consumes an actual entire-history source
and the EXISTING representation. No target function of response vectors is
assumed; overlapping case images with different labels remain distinct. -/
theorem physical_target_of_guarded_clause
    (F : Family Case A Y T R) (physical : Experiment S A Y T R)
    (rep : Representation physical (experiment F)) (h : History A Y) (q : T)
    {constantsValid prefixLegal : Prop}
    (hq : GuardedTarget constantsValid prefixLegal F h q)
    (s : S) (hs : Consistent physical h s) : physical.target s = q := by
  obtain ⟨m,hm,hc⟩ := consistent_has_model rep h s hs
  exact (rep.target_eq s m hm).trans (hq.2.2 m.1 m.2 hc)

/-- Transfer preserves the same stop plan and original resource/action types.
The consistent physical source supplies the nonvacuous execution witness. -/
theorem physical_stop_identifies
    (F : Family Case A Y T R) (physical : Experiment S A Y T R)
    (rep : Representation physical (experiment F)) (n : Nat)
    (h : History A Y) (u : R) (q : T) {constantsValid prefixLegal : Prop}
    (hq : GuardedTarget constantsValid prefixLegal F h q)
    (s : S) (hs : Consistent physical h s) :
    run physical (Plan.stop (n := n) q) s = physical.target s := by
  exact physical_run_of_symbolic_valid rep (Plan.stop (n := n) q) h u
    ((target_clause_iff_valid_stop F h q n u).mp hq.2.2) s hs

end Astra.G7FiniteTargetReceiver
