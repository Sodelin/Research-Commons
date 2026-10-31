import BinaryCircuitMinor
import FiniteDAGRank

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The nontrivial all-source-bits propagation step: copy equalities on ordinary
edges and zero-XOR equalities across isolated colliders force equality at
EVERY noncollider of the original path. Actual gate-copy routes also
propagate selected zero values back to their collider. Source coverage and
the construction of those local gates remain explicit geometric work.
-/

namespace RestrictedCausal.ProbabilitySource

open SelectedWalk WeakInducing

universe u v

def AllPairs {A : Type u} (P : A → A → Prop) : List A → Prop
  | a :: b :: rest => P a b ∧ AllPairs P (b :: rest)
  | _ => True

theorem allPairs_tail {A : Type u} (P : A → A → Prop) (a : A) (rest : List A)
    (h : AllPairs P (a :: rest)) : AllPairs P rest := by
  cases rest with
  | nil => trivial
  | cons b rest => exact h.2

theorem allTriples_tail {A : Type u} (P : A → A → A → Prop) (a : A) (rest : List A)
    (h : AllTriples P (a :: rest)) : AllTriples P rest := by
  cases rest with
  | nil => trivial
  | cons b rest =>
      cases rest with
      | nil => trivial
      | cons c rest => exact h.2

def TerminalOutside {A : Type u} (collider : A → Prop) (vertices : List A) : Prop :=
  ∀ front last, vertices = front ++ [last] → ¬ collider last

theorem terminalOutside_tail {A : Type u} (collider : A → Prop) (a : A) (rest : List A)
    (h : TerminalOutside collider (a :: rest)) : TerminalOutside collider rest := by
  intro front last equation
  exact h (a :: front) last (by simpa only [List.cons_append, equation])

/-- All local equations are on the SAME original vertex list. No separate
component-wise models or weakened summary signature enter this argument. -/
theorem noncollider_values_agree {A : Type u} {B : Type v}
    (collider : A → Prop) (value : A → B) (start : A) (rest : List A)
    (startOutside : ¬ collider start) (endOutside : TerminalOutside collider (start :: rest))
    (isolated : AllPairs (fun a b => ¬ (collider a ∧ collider b)) (start :: rest))
    (ordinary : AllPairs (fun a b => ¬ collider a → ¬ collider b → value a = value b) (start :: rest))
    (across : AllTriples (fun a b c => collider b → value a = value c) (start :: rest)) :
    ∀ vertex ∈ start :: rest, ¬ collider vertex → value vertex = value start := by
  classical
  have establish : ∀ n, ∀ start rest, rest.length = n →
      ¬ collider start → TerminalOutside collider (start :: rest) →
      AllPairs (fun a b => ¬ (collider a ∧ collider b)) (start :: rest) →
      AllPairs (fun a b => ¬ collider a → ¬ collider b → value a = value b) (start :: rest) →
      AllTriples (fun a b c => collider b → value a = value c) (start :: rest) →
      ∀ vertex ∈ start :: rest, ¬ collider vertex → value vertex = value start := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro start rest length startOutside endOutside isolated ordinary across vertex member outside
        cases rest with
        | nil =>
            have same : vertex = start := by simpa only [List.mem_singleton] using member
            rw [same]
        | cons «next» tail =>
            rcases List.mem_cons.mp member with same | member
            · rw [same]
            · by_cases nextCollider : collider «next»
              · cases tail with
                | nil => exact (endOutside [start] «next» rfl nextCollider).elim
                | cons following remaining =>
                    have followingOutside : ¬ collider following :=
                      fun h => isolated.2.1 ⟨nextCollider, h⟩
                    rcases List.mem_cons.mp member with atNext | later
                    · exact (outside (atNext.symm ▸ nextCollider)).elim
                    · have smaller : remaining.length < n := by
                        simp only [List.length_cons] at length
                        omega
                      have result := ih remaining.length smaller following remaining rfl followingOutside
                        (terminalOutside_tail collider «next» (following :: remaining)
                          (terminalOutside_tail collider start («next» :: following :: remaining) endOutside))
                        (allPairs_tail _ «next» _ (allPairs_tail _ start _ isolated))
                        (allPairs_tail _ «next» _ (allPairs_tail _ start _ ordinary))
                        (allTriples_tail _ «next» _ (allTriples_tail _ start _ across)) vertex later outside
                      exact result.trans (across.1 nextCollider).symm
              · have smaller : tail.length < n := by simp only [List.length_cons] at length; omega
                have result := ih tail.length smaller «next» tail rfl nextCollider
                  (terminalOutside_tail collider start («next» :: tail) endOutside)
                  (allPairs_tail _ start _ isolated) (allPairs_tail _ start _ ordinary)
                  (allTriples_tail _ start _ across) vertex member outside
                exact result.trans (ordinary.1 startOutside nextCollider).symm
  exact establish rest.length start rest rfl startOutside endOutside isolated ordinary across

namespace BinaryCPT.BoundaryCircuit

variable {V : Type u} [Fintype V] [DecidableEq V] {edge : V → V → Prop} {R : Type v}

def Copies (c : BinaryCPT.BoundaryCircuit edge R) (parent child : V) : Prop :=
  ∃ allowed earlier, c.gate child = .copy parent allowed earlier

theorem copy_value (c : BinaryCPT.BoundaryCircuit edge R) (bits : R → Bool)
    {parent child : V} (copy : c.Copies parent child) : c.value bits child = c.value bits parent := by
  obtain ⟨allowed, earlier, equation⟩ := copy
  rw [BinaryCPT.BoundaryCircuit.value, equation]

theorem copy_route_value (c : BinaryCPT.BoundaryCircuit edge R) (bits : R → Bool)
    {start finish : V} {vertices : List V} (route : Route c.Copies start vertices finish) :
    c.value bits finish = c.value bits start := by
  induction route with
  | nil start => rfl
  | @cons start «next» finish rest copy tail ih => exact ih.trans (c.copy_value bits copy)

theorem selected_copy_forces_zero (c : BinaryCPT.BoundaryCircuit edge R) (bits : R → Bool)
    (C : Finset V) {start finish : V} {vertices : List V}
    (route : Route c.Copies start vertices finish) (selected : finish ∈ C)
    (conditioned : Matches C (fun _ => false) (c.value bits)) : c.value bits start = false :=
  (c.copy_route_value bits route).symm.trans (conditioned finish selected)

theorem ordinary_copy_equality (c : BinaryCPT.BoundaryCircuit edge R) (bits : R → Bool)
    (a b : V) (copy : c.Copies a b ∨ c.Copies b a) : c.value bits a = c.value bits b := by
  rcases copy with forward | backward
  · exact (c.copy_value bits forward).symm
  · exact c.copy_value bits backward

theorem zero_xor_equal_inputs (c : BinaryCPT.BoundaryCircuit edge R) (bits : R → Bool)
    (a b d : V) (allowA : edge a b) (allowD : edge d b)
    (earlierA : c.rank a < c.rank b) (earlierD : c.rank d < c.rank b)
    (gate : c.gate b = .xor a d allowA allowD earlierA earlierD)
    (zero : c.value bits b = false) : c.value bits a = c.value bits d := by
  rw [BinaryCPT.BoundaryCircuit.value, gate] at zero
  cases atA : c.value bits a <;> cases atD : c.value bits d <;>
    simp [atA, atD] at zero ⊢

/-- The gate classification is local and original-arrow based. This
theorem proves the constant-bit endpoint/copy direction by rank induction;
it does not assume that the whole conditioning slice is correct. -/
theorem constant_value_on_copy_region (c : BinaryCPT.BoundaryCircuit edge R)
    (region : V → Prop)
    (classification : ∀ vertex, region vertex →
      (∃ i, c.gate vertex = .fair i) ∨
      ∃ parent allowed earlier, c.gate vertex = .copy parent allowed earlier ∧ region parent)
    (t : Bool) : ∀ vertex, region vertex → c.value (fun _ => t) vertex = t := by
  have establish : ∀ n, ∀ vertex, c.rank vertex = n → region vertex →
      c.value (fun _ => t) vertex = t := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro vertex rankEq member
        rcases classification vertex member with fair | copy
        · obtain ⟨i, gate⟩ := fair
          rw [BinaryCPT.BoundaryCircuit.value, gate]
        · obtain ⟨parent, allowed, earlier, gate, parentMember⟩ := copy
          rw [BinaryCPT.BoundaryCircuit.value, gate]
          exact ih (c.rank parent) (by omega) parent rfl parentMember
  intro vertex member
  exact establish (c.rank vertex) vertex rfl member

theorem equal_constant_xor_zero (c : BinaryCPT.BoundaryCircuit edge R)
    (a b d : V) (allowA : edge a b) (allowD : edge d b)
    (earlierA : c.rank a < c.rank b) (earlierD : c.rank d < c.rank b)
    (gate : c.gate b = .xor a d allowA allowD earlierA earlierD)
    (t : Bool) («left» : c.value (fun _ => t) a = t) («right» : c.value (fun _ => t) d = t) :
    c.value (fun _ => t) b = false := by
  rw [BinaryCPT.BoundaryCircuit.value, gate]
  simp only
  rw [«left», «right»]
  cases t <;> rfl

/-- Root bits are indexed by ACTUAL source vertices. Coverage is required
for every index, so no unused fair variable escapes the equal-bit proof. -/
theorem all_source_bits_constant (c : BinaryCPT.BoundaryCircuit edge R) (bits : R → Bool)
    (collider : V → Prop) (start : V) (rest : List V)
    (coverage : ∀ i, c.source i ∈ start :: rest ∧ ¬ collider (c.source i))
    (startOutside : ¬ collider start) (endOutside : TerminalOutside collider (start :: rest))
    (isolated : AllPairs (fun a b => ¬ (collider a ∧ collider b)) (start :: rest))
    (ordinary : AllPairs (fun a b => ¬ collider a → ¬ collider b →
      c.value bits a = c.value bits b) (start :: rest))
    (across : AllTriples (fun a b d => collider b → c.value bits a = c.value bits d) (start :: rest)) :
    bits = (fun _ => false) ∨ bits = (fun _ => true) := by
  have common := noncollider_values_agree collider (c.value bits) start rest
    startOutside endOutside isolated ordinary across
  have same : ∀ i, bits i = c.value bits start := by
    intro i
    rw [← c.value_at_source bits i]
    exact common (c.source i) (coverage i).1 (coverage i).2
  cases initial : c.value bits start with
  | false => exact Or.inl (funext (fun i => (same i).trans initial))
  | true => exact Or.inr (funext (fun i => (same i).trans initial))

end BinaryCPT.BoundaryCircuit

end RestrictedCausal.ProbabilitySource
