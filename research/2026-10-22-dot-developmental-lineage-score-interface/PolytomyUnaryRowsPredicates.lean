/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Concrete finite Boolean accumulator meanings for the actual nested rows
visitor: equality membership and strict range. Duplicate identifiers are
allowed. These are exactly the predicates needed by the original internal
range/coverage rewrite, not a replacement source language.
-/
import PolytomyUnaryRowsWithCount
import PolytomyUnaryDownstreamValidation

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

variable {K : Type} [DecidableEq K]

theorem visitFold_or (C : ℕ) (xs : List ℕ) : ∀ acc : Bool,
    xs.foldl (unaryVisitStep .equal (fun a b => a || b) C) acc = acc || decide (C ∈ xs) := by
  induction xs with
  | nil => intro acc; simp [unaryVisitStep]
  | cons x xs ih =>
      intro acc
      rw [List.foldl_cons, ih]
      by_cases hx : x = C <;> by_cases hm : C ∈ xs <;> cases acc <;>
        simp_all [unaryVisitStep, unaryVisitTest, eq_comm]

theorem visitFold_and (C : ℕ) (xs : List ℕ) : ∀ acc : Bool,
    xs.foldl (unaryVisitStep .less (fun a b => a && b) C) acc =
      acc && xs.all (fun x => decide (x < C)) := by
  induction xs with
  | nil => intro acc; simp [unaryVisitStep]
  | cons x xs ih =>
      intro acc
      rw [List.foldl_cons, ih]
      by_cases hx : x < C <;> cases htail : xs.all (fun x => decide (x < C)) <;> cases acc <;>
        simp [unaryVisitStep, unaryVisitTest, hx, htail]

theorem visitFold_append {A F : Type} (step : F → A → F) (xs ys : List A) : ∀ acc,
    (xs ++ ys).foldl step acc = ys.foldl step (xs.foldl step acc) := by
  induction xs with
  | nil => intro acc; rfl
  | cons x xs ih => intro acc; exact ih (step acc x)

theorem visitFold_rows {A F : Type} (step : F → A → F) (rows : List (List A)) : ∀ acc,
    rows.foldl (fun a row => row.foldl step a) acc = rows.flatten.foldl step acc := by
  induction rows with
  | nil => intro acc; rfl
  | cons row rows ih =>
      intro acc
      simpa only [List.foldl_cons, List.flatten_cons, visitFold_append] using ih (row.foldl step acc)

theorem unaryRows_membership_observation (q : UnaryRowsPorts K) (C L : ℕ)
    (s : CountdownStore (NumericStack K) Bool) (hs : UnaryVisitInv q.p C L s)
    (hc : s.stk (.inr q.c) = []) :
    unaryVisitObservation (unaryRowsEval q .equal (fun a b => a || b) C s) =
      if s.state.2 then (readFramedList (readFramedList readUnaryFrame) (s.stk (.inl .source))).map
        (fun z => (z.2, s.state.1.1 || decide (C ∈ z.1.flatten))) else none := by
  rw [unaryRows_observation q .equal (fun a b => a || b) C L s hs hc]
  split
  · apply congrArg
    funext z
    rw [visitFold_rows, visitFold_or]
  · rfl

theorem unaryRows_range_observation (q : UnaryRowsPorts K) (C L : ℕ)
    (s : CountdownStore (NumericStack K) Bool) (hs : UnaryVisitInv q.p C L s)
    (hc : s.stk (.inr q.c) = []) :
    unaryVisitObservation (unaryRowsEval q .less (fun a b => a && b) C s) =
      if s.state.2 then (readFramedList (readFramedList readUnaryFrame) (s.stk (.inl .source))).map
        (fun z => (z.2, s.state.1.1 && z.1.flatten.all (fun a => decide (a < C)))) else none := by
  rw [unaryRows_observation q .less (fun a b => a && b) C L s hs hc]
  split
  · apply congrArg
    funext z
    rw [visitFold_rows, visitFold_and]
  · rfl

theorem visitReadMany_length {A : Type} (reader : List Bool → Option (A × List Bool))
    (n : ℕ) : ∀ bits xs rest, readMany reader n bits = some (xs, rest) → xs.length = n := by
  induction n with
  | zero => intro bits xs rest h; simp [readMany] at h; rcases h with ⟨rfl, rfl⟩; rfl
  | succ n ih =>
      intro bits xs rest h
      cases hp : reader bits with
      | none => simp [readMany, hp] at h
      | some q =>
          rcases q with ⟨a, after⟩
          cases ht : readMany reader n after with
          | none => simp [readMany, hp, ht] at h
          | some z =>
              rcases z with ⟨tail, suffix⟩
              simp only [readMany, hp, ht, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              simpa only [List.length_cons] using congrArg Nat.succ (ih after tail suffix ht)

theorem unaryRows_saved_length_on_success {F : Type} (q : UnaryRowsPorts K)
    (mode : UnaryVisitMode) (bump : F → Bool → F) (C L : ℕ)
    (s : CountdownStore (NumericStack K) F) (hs : UnaryVisitInv q.p C L s)
    (hc : s.stk (.inr q.c) = []) (hz : s.stk (.inr q.saved) = []) (hf : s.state.2 = true)
    (rows : List (List ℕ)) (suffix : List Bool)
    (hp : readFramedList (readFramedList readUnaryFrame) (s.stk (.inl .source)) = some (rows, suffix)) :
    (unaryRowsEval q mode bump C s).stk (.inr q.saved) = List.replicate rows.length true := by
  cases hh : readUnaryFrame (s.stk (.inl .source)) with
  | none => simp [readFramedList, hh] at hp
  | some z =>
      rcases z with ⟨n, rest⟩
      have htail : readMany (readFramedList readUnaryFrame) n rest = some (rows, suffix) := by
        simpa [readFramedList, hh] using hp
      have hlen := visitReadMany_length (readFramedList readUnaryFrame) n rest rows suffix htail
      simpa only [hlen] using unaryRows_saved_count q mode bump C L s hs hc hz hf n rest hh

/- Initial false with equality/OR yields membership; initial true with
strict-less/AND yields universal range. These accumulator values are NOT
the independent syntactic-success flag. Full record acceptance must still
require syntax, empty suffix, saved row count = declared m, and every
physical query i < N found. The previous exact validity rewrite remains
the whole logical endpoint; its replay/coverage controller is still open.
-/

end PolytomyReductionModel
