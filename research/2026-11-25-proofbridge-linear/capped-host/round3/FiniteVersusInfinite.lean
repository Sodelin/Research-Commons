import CappedPaddingLanguage

namespace ResearchCommons.AlexanderRouteB
open CappedPaddingLanguage

def Prefix {V K : Type} (edge : V → V → Option K) (word : Nat → K) (length : Nat) : Prop :=
  ∃ path : Nat → V, ∀ n, n < length → edge (path n) (path (n+1)) = some (word n)

def chainEdge (a b : Nat × Nat) : Option Unit :=
  if a.1 = b.1 ∧ b.2 = a.2 + 1 ∧ b.2 ≤ b.1 then some () else none

def rayEdge (a b : Nat) : Option Unit :=
  if b = a+1 then some () else none

theorem chainAllPrefixes (word : Nat → Unit) (length : Nat) : Prefix chainEdge word length := by
  refine ⟨fun n => (length,n),?_⟩
  intro n hn
  have hw : word n = () := Subsingleton.elim _ _
  simp [chainEdge, hw, Nat.succ_le_of_lt hn]

theorem chainNoRealization (word : Nat → Unit) : ¬ Realizes chainEdge word := by
  rintro ⟨path, step⟩
  have rules (n : Nat) : (path n).1 = (path (n+1)).1 ∧
      (path (n+1)).2 = (path n).2 + 1 ∧ (path (n+1)).2 ≤ (path (n+1)).1 := by
    have h := step n
    unfold chainEdge at h
    split at h
    · assumption
    · contradiction
  have first (n : Nat) : (path n).1 = (path 0).1 := by
    induction n with
    | zero => rfl
    | succ n ih => exact (rules n).1.symm.trans ih
  have second (n : Nat) : n ≤ (path n).2 := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => rw [(rules n).2.1]; omega
  let N := (path 0).1
  have h := (rules N).2.2
  rw [first (N+1)] at h
  have q := second (N+1)
  omega

theorem rayRealizes (word : Nat → Unit) : Realizes rayEdge word := by
  refine ⟨id, ?_⟩
  intro n
  have hw : word n = () := Subsingleton.elim _ _
  simp [rayEdge, hw]

theorem sameFiniteButDifferentInfinite :
    (∀ word n, Prefix chainEdge word n ↔ Prefix rayEdge word n) ∧
    (∃ word, ¬Realizes chainEdge word ∧ Realizes rayEdge word) := by
  constructor
  · intro word n
    constructor
    · intro _
      obtain ⟨p,h⟩ := rayRealizes word
      exact ⟨p, fun i _ => h i⟩
    · intro _
      exact chainAllPrefixes word n
  · exact ⟨fun _ => (), chainNoRealization _, rayRealizes _⟩

#print axioms sameFiniteButDifferentInfinite
end ResearchCommons.AlexanderRouteB
