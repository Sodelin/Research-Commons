import VertexDiscriminatingSections

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Finite interval-dependency acyclicity for the remaining collider-order proof.
A dependency a -> b means that position a is strictly between b and b's
chosen discriminating-section start. This module proves that excluding
two-cycles excludes every finite cycle, by explicit largest-position removal.
The graph-specific exclusion of two-cycles is not assumed as proved here.
-/

namespace RestrictedCausal.IntervalDependency

open SelectedWalk

def PeakShortcut (R : Nat → Nat → Prop) : Prop :=
  ∀ a b c, R a b → R b c → a < b → c < b → R a c

theorem drop_top_aux (R : Nat → Nat → Prop) (irreflexive : ∀ a, ¬ R a a)
    (shortcut : PeakShortcut R) (top n : Nat) :
    ∀ a xs b, xs.length = n → Route R a xs b → a < top → b < top →
      (∀ v ∈ a :: xs, v ≤ top) →
      ∃ ys, Route R a ys b ∧ (∀ v ∈ a :: ys, v < top) ∧ (xs ≠ [] → ys ≠ []) := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro a xs b length route ha hb bounded
      cases route with
      | nil a =>
          exact ⟨[], .nil a, by
            intro v mem
            have eq : v = a := by simpa only [List.mem_singleton] using mem
            exact eq.symm ▸ ha, fun impossible => (impossible rfl).elim⟩
      | @cons a next b rest first tail =>
          have nextBound := bounded next (List.mem_cons_of_mem _ List.mem_cons_self)
          by_cases nextSmall : next < top
          · have shorter : rest.length < n := by simp only [List.length_cons] at length; omega
            obtain ⟨ys, path, small, _⟩ := ih rest.length shorter next rest b rfl tail nextSmall hb
              (fun v mem => bounded v (List.mem_cons_of_mem _ mem))
            refine ⟨next :: ys, .cons first path, ?_, ?_⟩
            · intro v mem
              rcases List.mem_cons.mp mem with eq | mem
              · exact eq.symm ▸ ha
              · exact small v mem
            · intro _ eq
              cases eq
          · have nextTop : next = top := by omega
            subst next
            cases tail with
            | nil => omega
            | @cons top after b tailRest second remaining =>
                have afterBound := bounded after (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
                have different : after ≠ top := by intro eq; exact irreflexive top (eq ▸ second)
                have afterSmall : after < top := by omega
                have newStep := shortcut a top after first second ha afterSmall
                have shorter : tailRest.length < n := by simp only [List.length_cons] at length; omega
                obtain ⟨ys, path, small, _⟩ := ih tailRest.length shorter after tailRest b rfl remaining afterSmall hb
                  (fun v mem => bounded v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem)))
                refine ⟨after :: ys, .cons newStep path, ?_, ?_⟩
                · intro v mem
                  rcases List.mem_cons.mp mem with eq | mem
                  · exact eq.symm ▸ ha
                  · exact small v mem
                · intro _ eq
                  cases eq

theorem bounded_closed_empty (R : Nat → Nat → Prop) (irreflexive : ∀ a, ¬ R a a)
    (shortcut : PeakShortcut R) (bound : Nat) :
    ∀ a xs, Route R a xs a → (∀ v ∈ a :: xs, v ≤ bound) → xs = [] := by
  induction bound with
  | zero =>
      intro a xs route bounded
      cases route with
      | nil => rfl
      | @cons a next finish rest first tail =>
          have ha := bounded a List.mem_cons_self
          have hn := bounded next (List.mem_cons_of_mem _ List.mem_cons_self)
          have eq : next = a := by omega
          exact (irreflexive a (eq ▸ first)).elim
  | succ bound ih =>
      have oldClosed : ∀ a xs, a ≤ bound → Route R a xs a →
          (∀ v ∈ a :: xs, v ≤ bound + 1) → xs = [] := by
        intro a xs ha route bounded
        obtain ⟨ys, path, small, positive⟩ := drop_top_aux R irreflexive shortcut (bound + 1)
          xs.length a xs a rfl route (by omega) (by omega) bounded
        have nil := ih a ys path (by intro v mem; have hv := small v mem; omega)
        by_contra nonempty
        exact positive nonempty nil
      intro a xs route bounded
      by_cases small : a ≤ bound
      · exact oldClosed a xs small route bounded
      · have ha := bounded a List.mem_cons_self
        have top : a = bound + 1 := by omega
        cases route with
        | nil => rfl
        | @cons a next finish rest first tail =>
            have nextBound := bounded next (List.mem_cons_of_mem _ List.mem_cons_self)
            have different : next ≠ a := by intro eq; exact irreflexive a (eq ▸ first)
            have nextSmall : next ≤ bound := by omega
            have rotated : Route R next (rest ++ [next]) next :=
              tail.append (.cons first (.nil next))
            have rotatedBound : ∀ v ∈ next :: (rest ++ [next]), v ≤ bound + 1 := by
              intro v mem
              rcases List.mem_cons.mp mem with eq | mem
              · exact eq.symm ▸ nextBound
              · rcases List.mem_append.mp mem with mem | mem
                · exact bounded v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem))
                · have eq : v = next := by simpa only [List.mem_singleton] using mem
                  exact eq.symm ▸ nextBound
            have nil := oldClosed next (rest ++ [next]) nextSmall rotated rotatedBound
            have length := congrArg List.length nil
            simp only [List.length_append, List.length_cons, List.length_nil] at length
            omega

theorem finite_list_bound (xs : List Nat) : ∃ n, ∀ v ∈ xs, v ≤ n := by
  induction xs with
  | nil => exact ⟨0, by intro v mem; cases mem⟩
  | cons a as ih =>
      obtain ⟨n, bound⟩ := ih
      refine ⟨a + n, ?_⟩
      intro v mem
      rcases List.mem_cons.mp mem with eq | mem
      · subst v
        omega
      · have hv := bound v mem
        omega

theorem peak_relation_acyclic (R : Nat → Nat → Prop) (irreflexive : ∀ a, ¬ R a a)
    (shortcut : PeakShortcut R) : ∀ a xs, Route R a xs a → xs = [] := by
  intro a xs route
  obtain ⟨bound, bounded⟩ := finite_list_bound (a :: xs)
  exact bounded_closed_empty R irreflexive shortcut bound a xs route bounded

def BetweenStart (start : Nat → Nat) (a b : Nat) : Prop :=
  (start b < a ∧ a < b) ∨ (b < a ∧ a < start b)

theorem between_irreflexive (start : Nat → Nat) (a : Nat) : ¬ BetweenStart start a a := by
  rintro (h | h) <;> omega

theorem between_peak_shortcut (start : Nat → Nat)
    (noTwoCycle : ∀ a b, BetweenStart start a b → ¬ BetweenStart start b a) :
    PeakShortcut (BetweenStart start) := by
  intro a b c ab bc aBelow cBelow
  have startBelow : start b < a := by rcases ab with h | h <;> omega
  have otherAbove : b < start c := by rcases bc with h | h <;> omega
  by_cases cBelowA : c < a
  · exact Or.inr ⟨cBelowA, by omega⟩
  · have reverse : BetweenStart start c b := Or.inl ⟨by omega, cBelow⟩
    exact (noTwoCycle b c bc reverse).elim

/-- The finite-order dependency relation cannot contain a longer cycle once
its actual graphical interpretation has excluded mutual dependence. The
proof needs neither an unproved interval-graph theorem nor a finite oracle. -/
theorem between_acyclic (start : Nat → Nat)
    (noTwoCycle : ∀ a b, BetweenStart start a b → ¬ BetweenStart start b a) :
    ∀ a xs, Route (BetweenStart start) a xs a → xs = [] :=
  peak_relation_acyclic (BetweenStart start) (between_irreflexive start) (between_peak_shortcut start noTwoCycle)

def RestrictedBetween (active : Nat → Prop) (start : Nat → Nat) (a b : Nat) : Prop :=
  active a ∧ active b ∧ BetweenStart start a b

/-- Restrict to the actual triple positions under consideration. No claim
about artificial starts or two-cycles at unused natural-number positions is
needed by the eventual finite path application. -/
theorem restricted_between_acyclic (active : Nat → Prop) (start : Nat → Nat)
    (noTwoCycle : ∀ a b, active a → active b → BetweenStart start a b → ¬ BetweenStart start b a) :
    ∀ a xs, Route (RestrictedBetween active start) a xs a → xs = [] := by
  apply peak_relation_acyclic (RestrictedBetween active start)
  · intro a h
    exact between_irreflexive start a h.2.2
  · intro a b c ab bc aBelow cBelow
    have startBelow : start b < a := by rcases ab.2.2 with h | h <;> omega
    have otherAbove : b < start c := by rcases bc.2.2 with h | h <;> omega
    refine ⟨ab.1, bc.2.1, ?_⟩
    by_cases cBelowA : c < a
    · exact Or.inr ⟨cBelowA, by omega⟩
    · have reverse : BetweenStart start c b := Or.inl ⟨by omega, cBelow⟩
      exact (noTwoCycle b c ab.2.1 bc.2.1 bc.2.2 reverse).elim

end RestrictedCausal.IntervalDependency
