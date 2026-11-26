import Lean
namespace ResearchCommons.CappedPaddingLanguage

def Realizes {V K : Type} (edge : V → V → Option K) (word : Nat → K) : Prop :=
  ∃ path : Nat → V, ∀ n, edge (path n) (path (n+1)) = some (word n)

def joined {V W K : Type} (base : V → V → Option K) (pad : W → W → Option K) :
    Sum V W → Sum V W → Option K
  | .inl x, .inl y => base x y
  | .inr x, .inr y => pad x y
  | _, _ => none

private theorem impossible_pad_path {W K : Type} (pad : W → W → Option K)
    (rank : W → Nat) (limit : Nat) (bounded : ∀ x, rank x ≤ limit)
    (rise : ∀ x y k, pad x y = some k → rank x < rank y) (word : Nat → K) :
    ¬ Realizes pad word := by
  intro h
  obtain ⟨path,step⟩ := h
  have level (n : Nat) : n ≤ rank (path n) := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have next := rise (path n) (path (n+1)) (word n) (step n)
      omega
  have low := level (limit+1)
  have top := bounded (path (limit+1))
  omega

/-- Adding an isolated acyclic component of bounded rank changes no infinite word. -/
theorem padding_preserves {V W K : Type} (base : V → V → Option K)
    (pad : W → W → Option K) (rank : W → Nat) (limit : Nat)
    (bounded : ∀ x, rank x ≤ limit)
    (rise : ∀ x y k, pad x y = some k → rank x < rank y)
    (word : Nat → K) :
    Realizes (joined base pad) word ↔ Realizes base word := by
  constructor
  · intro h
    obtain ⟨path, step⟩ := h
    cases first : path 0 with
    | inl v =>
      have left (n : Nat) : ∃ a, path n = Sum.inl a := by
        induction n with
        | zero => exact ⟨v,first⟩
        | succ n ih =>
          obtain ⟨a,ha⟩ := ih
          cases next : path (n+1) with
          | inl b => exact ⟨b,rfl⟩
          | inr b =>
            have no := step n
            simp [ha,next,joined] at no
      let f := fun n => Classical.choose (left n)
      have lift (n : Nat) : path n = Sum.inl (f n) := Classical.choose_spec (left n)
      exact ⟨f,fun n => by simpa only [lift n,lift (n+1),joined] using step n⟩
    | inr v =>
      have right (n : Nat) : ∃ a, path n = Sum.inr a := by
        induction n with
        | zero => exact ⟨v,first⟩
        | succ n ih =>
          obtain ⟨a,ha⟩ := ih
          cases next : path (n+1) with
          | inr b => exact ⟨b,rfl⟩
          | inl b =>
            have no := step n
            simp [ha,next,joined] at no
      let f := fun n => Classical.choose (right n)
      have lift (n : Nat) : path n = Sum.inr (f n) := Classical.choose_spec (right n)
      have pr : Realizes pad word :=
        ⟨f,fun n => by simpa only [lift n,lift (n+1),joined] using step n⟩
      exact False.elim (impossible_pad_path pad rank limit bounded rise word pr)
  · intro h
    obtain ⟨path,step⟩ := h
    exact ⟨fun n => Sum.inl (path n), step⟩

#print axioms padding_preserves
end ResearchCommons.CappedPaddingLanguage
