import PresentedCappedHost
import CappedPaddingLanguage

namespace ResearchCommons.AlexanderRouteB
open CappedPaddingLanguage PresentedCappedHost

def hostRay (a b : Nat) : Option Nat :=
  if b = a+1 then some 0 else none

def starPad (a b : Option (Fin 3)) : Option Nat :=
  match a,b with
  | none,some _ => some 0
  | _,_ => none

def paddedRay := joined hostRay starPad

theorem control_same_realizes (word : Nat → Nat) :
    Realizes paddedRay word ↔ Realizes hostRay word := by
  apply padding_preserves hostRay starPad (fun x => if x.isSome then 1 else 0) 1
  · intro x; cases x <;> simp
  · intro x y l h
    cases x <;> cases y <;> simp_all [starPad]

theorem control_different_admissibility :
    Embeds hostRay hostRay ∧ ¬ Embeds paddedRay hostRay := by
  constructor
  · exact ⟨id,fun _ _ e => e,fun _ _ e => e⟩
  rintro ⟨f,inj,preserve⟩
  let center : Nat ⊕ Option (Fin 3) := .inr none
  let leaf (n : Fin 3) : Nat ⊕ Option (Fin 3) := .inr (some n)
  have steps (n : Fin 3) : f (leaf n) = f center+1 ∨ f center = f (leaf n)+1 := by
    have h := preserve center (leaf n) (Or.inl rfl)
    unfold hostRay at h
    by_cases e : f (leaf n) = f center + 1
    · exact Or.inl e
    · right
      by_cases e2 : f center = f (leaf n) + 1
      · exact e2
      · exfalso
        simp only [if_neg e, if_neg e2, Option.isSome_none, Bool.false_eq_true, or_self] at h
  have distinct (a b : Fin 3) (hab : a ≠ b) : f (leaf a) ≠ f (leaf b) := by
    intro e
    apply hab
    have h := inj _ _ e
    exact Option.some.inj (Sum.inr.inj h)
  have n01 := distinct 0 1 (by decide)
  have n02 := distinct 0 2 (by decide)
  have n12 := distinct 1 2 (by decide)
  have s0 := steps 0
  have s1 := steps 1
  have s2 := steps 2
  generalize f (leaf 0) = a at n01 n02 s0
  generalize f (leaf 1) = b at n01 n12 s1
  generalize f (leaf 2) = c at n02 n12 s2
  generalize f center = d at s0 s1 s2
  omega

#print axioms control_same_realizes
#print axioms control_different_admissibility
end ResearchCommons.AlexanderRouteB
